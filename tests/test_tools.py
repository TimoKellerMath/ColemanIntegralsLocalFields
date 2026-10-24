"""Unit tests for the test tools (regression.py, check_logs.py, registry.py).

    python3 -m unittest discover -s tests -v
"""
import contextlib
import io
import re
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import check_logs  # noqa: E402
import compare_results  # noqa: E402
import make_api  # noqa: E402
import make_package  # noqa: E402
import regression  # noqa: E402
from registry import TESTS  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


class Package(unittest.TestCase):
    """tools/make_package.py: the parsing of the library functions and the committed package."""

    def test_split_top_level(self):
        self.assertEqual(make_package.split_top_level('a:=[1,2], b:="x,y", c:=f(1,2)', ","),
                         ['a:=[1,2]', 'b:="x,y"', 'c:=f(1,2)'])

    def test_parse_function(self):
        src = (ROOT / "integrals.m").read_text()
        pos, opts, help_text = make_package.parse_function(src, "coleman_integrals_on_basis")
        self.assertEqual(pos, ["P1", "P2", "data"])
        self.assertIn(("return_side", "false"), opts)
        self.assertTrue(help_text.startswith("The Coleman integrals of the basis forms"))
        self.assertNotIn("}", help_text)          # it is put between braces

    def test_committed_package_is_up_to_date(self):
        self.assertEqual(make_package.PACKAGE.read_text(), make_package.build())

    def test_package_test_attaches_the_spec(self):
        text = (ROOT / "tests" / "magma" / "unit-package.m").read_text()
        self.assertIn('AttachSpec("package/ColemanIntegralsLocalFields.spec")', text)

    def test_only_the_sources_of_the_package_are_tracked(self):
        # Magma writes a signature cache (.sig) next to an attached package file; it is
        # rewritten on every AttachSpec and must not be committed
        tracked = regression.tracked_files()
        package = sorted(f for f in tracked if f.startswith("package/"))
        self.assertEqual(package, ["package/ColemanIntegralsLocalFields.m",
                                   "package/ColemanIntegralsLocalFields.spec"])


class Api(unittest.TestCase):
    """tools/make_api.py: the committed API reference, its entries and its index."""

    def test_committed_reference_is_up_to_date(self):
        self.assertEqual(make_api.API.read_text(), make_api.build())

    def test_every_function_is_documented(self):
        text = make_api.build()
        for name in make_package.USER_FUNCTIONS:
            self.assertIn(f"### {name}\n", text, name)
            self.assertIn(f"](#{make_api.anchor(name)})", text, name)
        for f in make_package.LIBRARY:
            for m in make_api.DEFINITION.finditer((ROOT / f).read_text()):
                if m.group(1) not in make_package.USER_FUNCTIONS:
                    self.assertIn(f"* `{m.group(1)}(", text, m.group(1))

    def test_first_sentence(self):
        self.assertEqual(make_api.first_sentence("The value of f at P. More text.\n\nNext"), "The value of f at P.")
        self.assertEqual(make_api.first_sentence("Driver: the points of a curve.\nDetails."), "Driver: the points of a curve.")
        self.assertEqual(make_api.first_sentence("Points w.r.t. the basis (in L; see below). Next."),
                         "Points w.r.t. the basis (in L; see below).")
        long = "The reduction modulo P of the record R of the model M as a point of the plane curve: " + "x " * 60 + "."
        self.assertEqual(make_api.first_sentence(long),
                         "The reduction modulo P of the record R of the model M as a point of the plane curve.")

    def test_signature_and_anchor(self):
        self.assertEqual(make_api.signature("f", ["a", "b"], [("e", "0"), ("v", "true")]), "f(a, b : e := 0, v := true)")
        self.assertEqual(make_api.anchor("Qq_points"), "qq_points")


class Scheduling(unittest.TestCase):
    """The default number of jobs and the order in which the tests are started."""

    def test_default_jobs(self):
        self.assertGreaterEqual(regression.default_jobs(), 1)

    def test_longest_first(self):
        times = [regression.recorded_cpu_time(t) for t in regression.longest_first(TESTS)]
        self.assertEqual(times, sorted(times, reverse=True))
        self.assertGreater(times[0], 0)   # the committed logs record their CPU time
        slow = {t.name for t in TESTS if t.tier == "slow"}
        self.assertTrue(slow & {t.name for t in regression.longest_first(TESTS)[:3]})


class Normalize(unittest.TestCase):
    """regression.normalize masks run times and drops memory figures, nothing else."""

    def test_timings_are_masked(self):
        a = regression.normalize("coleman_data: 37.420 s ; g = 3 ; residue field F_361\n"
                                 "integral 1/2 done (precision 12, 0.770 s).\n"
                                 "120 * z is principal: true   (53.980 s)\n"
                                 "coleman_data: total time (s): 9.350")
        b = regression.normalize("coleman_data: 48.310 s ; g = 3 ; residue field F_361\n"
                                 "integral 1/2 done (precision 12, 0.950 s).\n"
                                 "120 * z is principal: true   (66.760 s)\n"
                                 "coleman_data: total time (s): 15.110")
        self.assertEqual(a, b)
        self.assertEqual(len(a), 3)       # the "total time (s)" line is dropped

    def test_resource_lines_are_dropped(self):
        text = ("DONE\n\nresources: CPU time 2.100 s, maximum memory 32 MB\n"
                "Time (s) :     0.080\nMemory (Mb) :  32 \nTotal time: 0.720 seconds, Total memory usage: 32.09MB")
        self.assertEqual(regression.normalize(text), ["DONE"])

    def test_mathematical_content_is_kept(self):
        a = regression.normalize("(O(7^17) O(7^18) O(7^18) -33021872169318 + O(7^17))")
        b = regression.normalize("(O(7^17) O(7^17) O(7^18) -33021872169318 + O(7^17))")
        self.assertNotEqual(a, b)
        self.assertNotEqual(regression.normalize("#W = 158 classes"), regression.normalize("#W = 157 classes"))
        # a number followed by "s" that is not a time unit stays
        self.assertEqual(regression.normalize("8 doubles 2P"), ["8 doubles 2P"])

    def test_magma_errors_are_detected(self):
        for line in ("Runtime error in 'Append': Cannot coerce element into the universe",
                     "User error: bad syntax", "Internal error in permutation group code",
                     ">> assert x eq 1; Assertion failed"):
            self.assertTrue(regression.MAGMA_ERROR.search(line), line)
        self.assertFalse(regression.MAGMA_ERROR.search("no error here: 0 failures"))


class CompareResults(unittest.TestCase):
    """compare_results: exact values exactly, p-adic numbers modulo the smaller precision, and a
    lower precision than the committed one is a failure; regression.compare_output uses it
    for results files and then reports log differences only for information."""

    REF = ("# results\n"
           "count\tint\t5\n"
           "ratio\trat\t-3/49\n"
           "label\tstr\thello world\n"
           "flag\tbool\ttrue\n"
           "I[1]\tpadic\t7\t10\t12345\n"
           "I[2]\tpadic\t7\t3\t1/49\n"
           "zero\tpadic\t7\t5\t0\n")

    @staticmethod
    def changed(text, name, line):
        return "\n".join(line if l.split("\t")[0] == name else l for l in text.splitlines())

    def test_identical_results_agree(self):
        self.assertEqual(compare_results.compare(self.REF, self.REF), [])

    def test_padic_numbers_agree_modulo_the_smaller_precision(self):
        new = self.changed(self.REF, "I[1]", f"I[1]\tpadic\t7\t12\t{12345 + 7**10}")   # more digits
        new = self.changed(new, "zero", f"zero\tpadic\t7\t6\t{7**5}")                 # 7^5 = 0 mod 7^5
        self.assertEqual(compare_results.compare(self.REF, new), [])

    def test_differences_are_reported(self):
        cases = {
            "I[1]": f"I[1]\tpadic\t7\t10\t{12345 + 7**9}",    # differs modulo 7^10
            "I[2]": "I[2]\tpadic\t7\t2\t1/49",                 # fewer digits than committed
            "count": "count\tint\t6",
            "label": "label\tstr\thello",
            "flag": "flag\tpadic\t7\t3\t1",                    # another kind
        }
        for name, line in cases.items():
            problems = compare_results.compare(self.REF, self.changed(self.REF, name, line))
            self.assertEqual(len(problems), 1, name)
            self.assertTrue(problems[0].startswith(name + ":"), problems)
        self.assertIn("precision 2, less than the committed 3",
                      compare_results.compare(self.REF, self.changed(self.REF, "I[2]", cases["I[2]"]))[0])

    def test_missing_and_new_entries_are_reported(self):
        new = self.REF.replace("ratio\trat\t-3/49\n", "") + "extra\tint\t1\n"
        self.assertEqual(sorted(compare_results.compare(self.REF, new)),
                         ["extra: not among the committed results", "ratio: missing"])

    def test_malformed_files_are_rejected(self):
        with self.assertRaises(ValueError):
            compare_results.parse("name only\n")
        with self.assertRaises(ValueError):
            compare_results.parse("a\tint\t1\na\tint\t2\n")

    def test_compare_output_verdicts(self):
        f = "tests/magma/x.results"
        self.assertEqual(regression.compare_output(f, self.REF, self.REF), ("same", []))
        verdict, msgs = regression.compare_output(f, self.REF, self.changed(self.REF, "count", "count\tint\t6"))
        self.assertEqual(verdict, "diff")
        self.assertTrue(msgs[0].startswith(f + ": count:"))
        log_a, log_b = "integral done (precision 9, 0.120 s).\n", "integral finished (precision 9, 0.130 s).\n"
        self.assertEqual(regression.compare_output("x.log", log_a, log_a.replace("0.120", "0.990")), ("same", []))
        self.assertEqual(regression.compare_output("x.log", log_a, log_b)[0], "diff")
        self.assertEqual(regression.compare_output("x.log", log_a, log_b, numeric=True)[0], "info")

    def test_committed_results_files_are_written_by_their_scripts(self):
        for t in TESTS:
            for f in t.files():
                if f.endswith(".results"):
                    self.assertIn(f, (ROOT / t.script).read_text(), f"{t.script} does not write {f}")
                    self.assertTrue(check_logs.results_readable((ROOT / f).read_text()), f)


class Registry(unittest.TestCase):
    """The registry is consistent with the repository."""

    def test_names_and_outputs_are_unique(self):
        names = [t.name for t in TESTS]
        self.assertEqual(len(names), len(set(names)))
        outputs = [f for t in TESTS for f in t.files()]
        self.assertEqual(len(outputs), len(set(outputs)), "two tests write the same file")

    def test_scripts_exist_and_write_their_logs(self):
        for t in TESTS:
            script = ROOT / t.script
            self.assertTrue(script.exists(), t.script)
            src = script.read_text()
            for f in t.files():
                if f.endswith(".log"):
                    # appendix-A-localdata-19.log is written via Sprintf("appendix-A-localdata-%o.log", q)
                    stem = re.sub(r"-\d+$", "-", Path(f).name[:-len(".log")])
                    self.assertIn("SetLogFile(", src, t.script)
                    self.assertIn(stem, src, f"{t.script} does not seem to write {f}")

    def test_scripts_overwrite_their_logs_and_record_resources(self):
        for t in {t.script for t in TESTS}:
            src = (ROOT / t).read_text()
            self.assertIn(": Overwrite", src, f"{t} appends to its log")
            self.assertIn("resources: CPU time", src, f"{t} does not record its resources")

    def test_tiers_and_groups(self):
        for t in TESTS:
            self.assertIn(t.tier, ("fast", "slow"))
            self.assertIn(t.group, ("article", "library", "unit", "example"))


class CheckLogs(unittest.TestCase):
    """check_logs passes on the committed logs and detects a Magma error in a log."""

    def test_committed_logs_pass(self):
        rep = check_logs.Report()
        with contextlib.redirect_stdout(io.StringIO()):
            check_logs.check_registry(rep)
        self.assertEqual(rep.fails, [])

    def test_magma_errors_are_detected(self):
        self.assertTrue(check_logs.MAGMA_ERROR.search("Runtime error in 'Append': bad"))
        self.assertFalse(check_logs.MAGMA_ERROR.search("no error here: 0 failures"))


if __name__ == "__main__":
    unittest.main()
