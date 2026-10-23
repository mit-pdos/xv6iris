"""Unit tests of tools/tcb/selftest.py's pure parts (no Lean, no built tree): the doctoring
of a baseline and the judgement of the problem list the tool must then produce."""
import importlib.util
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("tcb_selftest", TOOLS / "tcb" / "selftest.py")
st = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(st)

BASELINE = {
    "comment": ["..."],
    "theorems": [{"name": "Xv6.t", "modules": ["Xv6.A"], "axioms": [], "opaques": []}],
    "declarations": {
        "Xv6.alpha": {"Xv6.alpha": "00000000ffffffff", "Xv6.alpha.match_1": "1111111122222222"},
        "Xv6.beta": {"Xv6.beta": "3333333344444444"},
        "Xv6.gamma": {"Xv6.gamma": "5555555566666666"},
        "Xv6.delta": {"Xv6.delta": "7777777788888888"},
    },
}


def problems_for(expect, changed_from="00000000ffffffff"):
    """The three messages the tool prints for `expect`, in its message forms."""
    return [
        "`Xv6.alpha` (Xv6/A.lean:1-2): the content of `%s` CHANGED (%s -> 00000000fffffff0)"
        % (expect["changed"], changed_from),
        "`Xv6.beta` (Xv6/A.lean:3-4): `%s` ENTERED the trusted base (3333333344444444)" % expect["entered"],
        "`Xv6.delta` (Xv6/A.lean:5-6): `%s` LEFT the trusted base" % expect["left"],
    ]


class DoctorTest(unittest.TestCase):
    def test_three_doctorings_in_name_order(self):
        doctored, expect = st.doctor(BASELINE)
        decls = doctored["declarations"]
        # name order: alpha (hash altered), beta (constant removed), delta (bogus added)
        self.assertEqual(expect, {"changed": "Xv6.alpha", "entered": "Xv6.beta",
                                  "left": "Xv6.delta" + st.BOGUS_SUFFIX})
        self.assertEqual(decls["Xv6.alpha"]["Xv6.alpha"], "00000000fffffff0")
        self.assertEqual(decls["Xv6.alpha"]["Xv6.alpha.match_1"], "1111111122222222")
        self.assertNotIn("Xv6.beta", decls)          # its only constant was removed, so the unit went too
        self.assertEqual(decls["Xv6.delta"]["Xv6.delta" + st.BOGUS_SUFFIX], "0123456789abcdef")
        self.assertEqual(decls["Xv6.gamma"], {"Xv6.gamma": "5555555566666666"})
        # the sets are untouched, and the input was not modified
        self.assertEqual(doctored["theorems"], BASELINE["theorems"])
        self.assertEqual(BASELINE["declarations"]["Xv6.alpha"]["Xv6.alpha"], "00000000ffffffff")
        self.assertIn("Xv6.beta", BASELINE["declarations"])

    def test_flip_hex_changes_exactly_the_last_digit(self):
        self.assertEqual(st.flip_hex("0123456789abcdef"), "0123456789abcde0")
        self.assertEqual(st.flip_hex("0123456789abcde0"), "0123456789abcde1")
        self.assertEqual(len(st.flip_hex("0000000000000000")), 16)

    def test_refuses_a_baseline_without_enough_declarations(self):
        with self.assertRaises(ValueError):
            st.doctor({"theorems": []})
        with self.assertRaises(ValueError):
            st.doctor({"declarations": {"a": {"a": "0000000000000000"}, "b": {"b": "0000000000000000"}}})


class JudgeTest(unittest.TestCase):
    def setUp(self):
        _, self.expect = st.doctor(BASELINE)

    def test_exactly_the_three_expected_problems_pass(self):
        self.assertEqual(st.judge(problems_for(self.expect), self.expect), [])

    def test_a_missing_verdict_fails(self):
        ps = problems_for(self.expect)[1:]
        reasons = st.judge(ps, self.expect)
        self.assertTrue(any("exactly 3" in r for r in reasons))
        self.assertTrue(any("CHANGED" in r for r in reasons))

    def test_a_wrong_constant_fails(self):
        ps = problems_for(self.expect)
        ps[2] = ps[2].replace(self.expect["left"], "Xv6.somethingElse")
        reasons = st.judge(ps, self.expect)
        self.assertTrue(any("LEFT" in r for r in reasons))

    def test_a_set_problem_fails(self):
        ps = problems_for(self.expect) + ["Xv6.t: module `Xv6.B` ENTERED the statement's trusted base"]
        reasons = st.judge(ps, self.expect)
        self.assertTrue(any("module/axiom/opaque" in r for r in reasons))
        self.assertTrue(any("exactly 3" in r for r in reasons))

    def test_an_extra_content_problem_fails(self):
        ps = problems_for(self.expect) + ["`Xv6.gamma` (Xv6/A.lean:7-8): the content of `Xv6.gamma` CHANGED (5555555566666666 -> 5555555566666660)"]
        self.assertTrue(st.judge(ps, self.expect))


if __name__ == "__main__":
    unittest.main()
