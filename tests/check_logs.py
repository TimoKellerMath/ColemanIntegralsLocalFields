#!/usr/bin/env python3
"""Consistency of the committed logs with the registry.  Needs no Magma (runs on GitHub's runners).

Checks
  1. every script of tests/registry.py exists, together with the files it writes;
  2. no committed log of the registry contains a Magma error;
  3. every committed results file (tests/magma/results.m) can be read by compare_results.

    python3 tests/check_logs.py
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import compare_results  # noqa: E402
from registry import TESTS  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
MAGMA_ERROR = re.compile(r"(Runtime|User|Internal) error|Assertion failed")


class Report:
    def __init__(self):
        self.fails, self.oks = [], 0

    def ok(self, msg):
        self.oks += 1
        print(f"  ok    {msg}")

    def fail(self, msg):
        self.fails.append(msg)
        print(f"  FAIL  {msg}")


def log(name):
    p = ROOT / name
    return p.read_text(errors="replace") if p.exists() else None


def results_readable(text):
    try:
        return len(compare_results.parse(text)) > 0
    except ValueError:
        return False


def check_registry(rep):
    print("scripts of the registry, their outputs, and Magma errors in the logs")
    for t in TESTS:
        if not (ROOT / t.script).exists():
            rep.fail(f"{t.script} missing")
            continue
        for f in t.files():
            text = log(f)
            if t.xfail and text is not None:
                rep.ok(f"{f} (expected failure: {t.xfail})")
                continue
            if text is None:
                rep.fail(f"{f} (written by {t.script}) missing")
            elif any(MAGMA_ERROR.search(line) for line in text.splitlines()):
                rep.fail(f"{f} contains a Magma error")
            elif f.endswith(".results") and not results_readable(text):
                rep.fail(f"{f} is not a readable results file (or has no entries)")
            else:
                rep.ok(f"{f}")


def main():
    rep = Report()
    check_registry(rep)
    print(f"\n{rep.oks} ok, {len(rep.fails)} failures")
    return 1 if rep.fails else 0


if __name__ == "__main__":
    sys.exit(main())
