import importlib.util
import io
import os
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "proof_profile.py"
SPEC = importlib.util.spec_from_file_location("proof_profile", PATH)
profile = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(profile)

TIMED = """\
@start 1000.0 nproc=8
@1001.5 ✔ [1/4] Built A (1.5s)
@1003.5 ⚠ [2/4] Built B (2s)
@1003.6 warning: B.lean:1:0: something about Built C (9s) in a message
@1004.0 ✔ [3/4] Built C (500ms)
@1065.0 ✔ [4/4] Built D (1m 1s)
@1065.1 Build completed successfully (4 jobs).
@cpu user=70.5 sys=2.5
@end 1065.2 rc=0
"""


def write(text):
    f = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False, encoding="utf-8")
    f.write(text)
    f.close()
    return f.name


class ParseTests(unittest.TestCase):
    def test_durations(self):
        self.assertAlmostEqual(profile.time_of("260ms"), 0.26)
        self.assertAlmostEqual(profile.time_of("6.9s"), 6.9)
        self.assertAlmostEqual(profile.time_of("1m 5s"), 65.0)

    def test_timed_log(self):
        p = write(TIMED)
        try:
            log = profile.parse_build_log(p)
        finally:
            os.unlink(p)
        self.assertEqual(log["times"], {"A": 1.5, "B": 2.0, "C": 0.5, "D": 61.0})
        self.assertEqual(log["finish"]["D"], 1065.0)
        self.assertEqual((log["start"], log["end"], log["cpu"], log["nproc"], log["rc"]),
                         (1000.0, 1065.2, 73.0, 8, 0))
        # a message that merely quotes "Built C (9s)" is not a record
        self.assertEqual(log["dropped"], 0)

    def test_plain_log_has_times_but_no_timeline(self):
        p = write("✔ [1/2] Built A (1.5s)\n✔ [2/2] Built B (2s)\n")
        try:
            log = profile.parse_build_log(p)
        finally:
            os.unlink(p)
        self.assertEqual(log["times"], {"A": 1.5, "B": 2.0})
        self.assertEqual(log["finish"], {})
        self.assertIsNone(log["start"])

    def test_a_garbled_record_is_counted_not_guessed(self):
        p = write("✔ [1/2] Built A (1.5s)\n✔ [2/2] Built B (2s✔ [3/3] Built\n")
        try:
            log = profile.parse_build_log(p)
        finally:
            os.unlink(p)
        self.assertEqual(log["times"], {"A": 1.5})
        self.assertEqual(log["dropped"], 1)

    def test_missing_log_degrades(self):
        log = profile.parse_build_log("/nonexistent/lake.log")
        self.assertEqual(log["times"], {})


class AnalysisTests(unittest.TestCase):
    G = {"A": [], "B": ["A"], "C": ["A"], "D": ["B", "C"]}
    T = {"A": 1.0, "B": 5.0, "C": 2.0, "D": 3.0}

    def test_critical_path_follows_the_heaviest_import(self):
        finish, pred = profile.critical_path(self.G, self.T)
        self.assertEqual(finish["D"], 9.0)
        self.assertEqual(profile.path_to("D", pred), ["A", "B", "D"])

    def test_modules_without_a_time_weigh_nothing(self):
        finish, _ = profile.critical_path({"A": [], "B": ["A"]}, {"B": 2.0})
        self.assertEqual(finish["B"], 2.0)

    def test_deep_chains_do_not_recurse(self):
        n = 5000
        g = {f"M{i}": ([f"M{i - 1}"] if i else []) for i in range(n)}
        finish, _ = profile.critical_path(g, {m: 1.0 for m in g})
        self.assertEqual(finish[f"M{n - 1}"], float(n))

    def test_timeline_and_serial_time(self):
        times = {"A": 2.0, "B": 2.0, "C": 1.0}
        finish = {"A": 102.0, "B": 103.0, "C": 106.0}
        iv, span = profile.build_timeline(times, finish, start=100.0)
        self.assertEqual(span, 6.0)
        steps = profile.concurrency_steps(iv)
        self.assertEqual(max(c for _, c in steps), 2)
        # [0,1) one job, [1,2) two, [2,3) one, [3,5) none, [5,6) one
        self.assertAlmostEqual(profile.serial_seconds(steps, span), 5.0)

    def test_report_renders_without_a_graph_or_timestamps(self):
        log = dict(times={"A": 1.0}, finish={}, start=None, end=None, cpu=None, nproc=None,
                   dropped=2, rc=None)
        md, summary = profile.report(log, None, "no graph")
        self.assertIn("Proof build profile", md)
        self.assertIn("2 `Built` line(s) dropped", md)
        self.assertIn("no dependency data", md)
        self.assertIn("critical path 0s", summary)

    def test_main_never_fails(self):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            rc = profile.main(["--build-log", "/nonexistent/lake.log",
                               "--repo", tempfile.gettempdir()])
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
