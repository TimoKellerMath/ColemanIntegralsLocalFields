#!/usr/bin/env python3
"""Regression tests for the Magma scripts of the article.

Each script NAME.m writes NAME.log (and possibly data files); the committed versions are the
reference output.  For every selected test this runner copies the tracked files of the
repository (as they are in the working tree) into a fresh temporary directory, runs the
script there with Magma, and compares the files it writes with the committed ones after
masking run times and memory figures.  A results file NAME.results (tests/magma/results.m)
is compared numerically (tests/compare_results.py: p-adic numbers to the smaller of the two
precisions); the log of a test with a results file is then compared only for information.
A test fails if Magma reports an error (e.g. a failed
assert), the script times out, or an output differs; tests marked xfail in the registry are
expected to fail (XFAIL), and a run fails if one of them passes (XPASS).  The working tree is never modified,
except with --update.  The tests run in parallel, one job per core by default, the longest ones
(by the CPU time recorded in their committed logs) first.

    python3 tests/regression.py                  # fast tier (about 14 minutes of CPU time)
    python3 tests/regression.py --tier all -j 4  # adds the two long Example 8.4 runs; 4 jobs
    python3 tests/regression.py example-8.3      # selected tests
    python3 tests/regression.py --update         # overwrite the committed logs with new output
    python3 tests/regression.py --list

Environment: MAGMA (default "magma") is the Magma executable.
"""
import argparse
import concurrent.futures as cf
import difflib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import compare_results  # noqa: E402
from registry import TESTS  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
MAGMA_ERROR = re.compile(r"(Runtime|User|Internal) error|Assertion failed")
# timings: "12.340 s", "(53.980 s)", "total time (s): 9.350", Magma's "Time (s) :" lines, and the
# "resources: CPU time ... s, maximum memory ... MB" line that every script prints at the end
TIMING = re.compile(r"\d+(?:\.\d+)?(?:E[+-]?\d+)?\s*s\b")
DROP = re.compile(r"Total time|Time \(s\)|Memory \(Mb\)|[Mm]emory usage|CPU time|time \(s\):")


def normalize(text):
    """The lines of a log with run times and memory figures masked or dropped."""
    out = []
    for line in text.splitlines():
        line = line.rstrip()
        if not line.strip() or DROP.search(line):
            continue
        out.append(TIMING.sub("<T> s", line))
    return out


def default_jobs():
    """The number of processing units that nproc reports (it honours OMP_NUM_THREADS, as
    the Makefile does), or else the number of cores available to this process; at least 1."""
    try:
        return max(1, int(subprocess.run(["nproc"], capture_output=True, text=True, check=True).stdout))
    except (OSError, ValueError, subprocess.CalledProcessError):   # no nproc (e.g. macOS)
        pass
    try:
        return max(1, len(os.sched_getaffinity(0)))
    except AttributeError:
        return max(1, os.cpu_count() or 1)


def recorded_cpu_time(test):
    """The CPU time on the "resources:" line of the committed log of test, or 0 if there is none."""
    try:
        text = (ROOT / test.files()[0]).read_text()
    except OSError:
        return 0.0
    times = re.findall(r"resources: CPU time ([0-9.]+) s", text)
    return float(times[-1]) if times else 0.0


def longest_first(tests):
    """The tests ordered by their recorded CPU time, longest first: with several jobs the run
    then ends soon after its longest test."""
    return sorted(tests, key=recorded_cpu_time, reverse=True)


def tracked_files():
    res = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True)
    return [f for f in res.stdout.decode().split("\0") if f]


def copy_tree(dest):
    for f in tracked_files():
        src = ROOT / f
        if src.is_file():
            (dest / f).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest / f)


def compare_output(f, ref_text, new_text, numeric=False):
    """The verdict on the new version of the output file f against the committed one, and the
    messages: "same", "diff" (the test fails), or "info" (a difference in the log of a test
    whose numbers are compared in its results file, numeric = True: reported, no failure).
    A results file is compared numerically (compare_results), other files after normalize."""
    if f.endswith(".results"):
        try:
            problems = compare_results.compare(ref_text, new_text)
        except ValueError as e:
            return "diff", [f"{f}: {e}"]
        return ("diff" if problems else "same"), [f"{f}: {p}" for p in problems[:40]]
    a, b = normalize(ref_text), normalize(new_text)
    if a == b:
        return "same", []
    diff = list(difflib.unified_diff(a, b, f"{f} (committed)", f"{f} (new)", lineterm="", n=1))
    if numeric and f.endswith(".log"):
        return "info", [f"{f} differs (for information; the numbers are compared in the results file):"] + diff[:12]
    return "diff", diff[:40]


def run_test(test, magma, keep_dir=None):
    """Run one test in a scratch copy; return (status, seconds, messages, produced files)."""
    t0 = time.time()
    with tempfile.TemporaryDirectory(prefix=f"magma-{test.name}-") as tmp:
        tmp = Path(tmp)
        copy_tree(tmp)
        for f in test.files():          # the script must produce these afresh
            (tmp / f).unlink(missing_ok=True)
        cmd = [magma, "-b", *test.args, test.script]
        try:
            res = subprocess.run(cmd, cwd=tmp, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, timeout=test.timeout)
            stdout = res.stdout.decode(errors="replace")
        except subprocess.TimeoutExpired:
            return "TIMEOUT", time.time() - t0, [f"no result after {test.timeout} s"], {}
        produced, msgs, status = {}, [], "PASS"
        numeric = any(f.endswith(".results") for f in test.files())
        for f in test.files():
            p = tmp / f
            produced[f] = p.read_text(errors="replace") if p.exists() else None
        texts = [stdout] + [t for t in produced.values() if t]
        errs = [line for t in texts for line in t.splitlines() if MAGMA_ERROR.search(line)]
        if errs:
            status = "ERROR"
            msgs += ["Magma reported: " + e.strip() for e in errs[:5]]
        for f, new in produced.items():
            ref = ROOT / f
            if new is None:
                status = "ERROR"
                msgs.append(f"{f} was not written")
            elif not ref.exists():
                if status == "PASS":
                    status = "NEW"
                msgs.append(f"{f} has no committed reference (use --update)")
            else:
                verdict, m = compare_output(f, ref.read_text(errors="replace"), new, numeric)
                if verdict == "diff" and status == "PASS":
                    status = "DIFF"
                msgs += m
        if keep_dir is not None and status != "PASS":
            for f, new in produced.items():
                if new is not None:
                    (keep_dir / f).parent.mkdir(parents=True, exist_ok=True)
                    (keep_dir / f).write_text(new)
            (keep_dir / f"{test.name}.stdout").write_text(stdout)
        return status, time.time() - t0, msgs, produced


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tests", nargs="*", help="names of tests to run (default: the selected tier)")
    ap.add_argument("--tier", choices=("fast", "all"), default="fast")
    ap.add_argument("-j", "--jobs", type=int, default=default_jobs(),
                    help="number of tests run in parallel (default: nproc, the number of cores)")
    ap.add_argument("--update", action="store_true",
                    help="write the new outputs into the working tree (only for tests without Magma errors)")
    ap.add_argument("--artifacts", type=Path, help="directory for the outputs of failing tests")
    ap.add_argument("--list", action="store_true")
    args = ap.parse_args()

    if args.list:
        for t in TESTS:
            print(f"{t.name:30} {t.tier:5} {t.group:8} {t.article}")
        return 0
    if args.tests:
        known = {t.name: t for t in TESTS}
        unknown = [n for n in args.tests if n not in known]
        if unknown:
            ap.error(f"unknown tests: {unknown}; see --list")
        selected = [known[n] for n in args.tests]
    else:
        selected = [t for t in TESTS if args.tier == "all" or t.tier == "fast"]

    magma = os.environ.get("MAGMA", "magma")
    if shutil.which(magma) is None:
        print(f"Magma executable '{magma}' not found (set MAGMA)", file=sys.stderr)
        return 2
    if args.artifacts:
        args.artifacts.mkdir(parents=True, exist_ok=True)

    print(f"running {len(selected)} tests with {args.jobs} jobs")
    results = {}
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_test, t, magma, args.artifacts): t for t in longest_first(selected)}
        for fut in cf.as_completed(futs):
            t = futs[fut]
            status, secs, msgs, produced = fut.result()
            if t.xfail:                 # expected failure: report, but do not fail the run
                status = "XPASS" if status == "PASS" else "XFAIL"
                msgs = [f"expected failure: {t.xfail}"] + (msgs[:3] if status == "XFAIL" else [])
            results[t.name] = (status, secs, msgs)
            print(f"{status:7} {t.name:30} {secs:7.1f} s", flush=True)
            for m in msgs:
                print("        " + m)
            if args.update and status in ("PASS", "DIFF", "NEW", "XFAIL", "XPASS"):
                for f, new in produced.items():
                    if new is not None:
                        (ROOT / f).write_text(new)

    good = ("PASS", "XFAIL") + (("DIFF", "NEW") if args.update else ())
    bad = [n for n, (s, _, _) in results.items() if s not in good]
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write("| test | status | time |\n| --- | --- | --- |\n")
            for t in selected:
                s, secs, _ = results[t.name]
                fh.write(f"| `{t.name}` | {s} | {secs:.0f} s |\n")
    if os.environ.get("GITHUB_ACTIONS"):
        for n in bad:
            t = next(t for t in selected if t.name == n)
            print(f"::error file={t.script}::{n}: {results[n][0]}")
    print(f"\n{len(selected) - len(bad)} of {len(selected)} tests passed" + (f"; failed: {bad}" if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
