#!/usr/bin/env python3
"""Fixture tests for tools/integrity/integrity.py: a throwaway git repo per test class.
Run: python3 tools/integrity/tests/test_integrity.py"""
import os, subprocess, sys, tempfile, unittest, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location("integrity", os.path.join(HERE, "..", "integrity.py"))
I = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(I)

BASE_V = """(* header: never Admitted, no Axiom here *)
Module Type SPEC.
  Parameter wp_f : nat -> Prop.
End SPEC.
Section S.
  Variable n : nat.
  Lemma keep : n = n. Proof. reflexivity. Qed.
  Lemma dropme : n = n. Proof. reflexivity. Qed.
End S.
"""
COQPROJECT = "-R . xv6iris\n-arg -w\n-arg +notation-incompatible-prefix\nA.v\n# SystemAssumptions.v\n"

def sh(*a, cwd, env=None):
    return subprocess.run(a, cwd=cwd, check=True, capture_output=True, text=True, env=env).stdout

class Repo:
    def __init__(self):
        self.d = tempfile.mkdtemp(); self.iris = os.path.join(self.d, "iris"); os.makedirs(self.iris)
        sh("git", "init", "-q", "-b", "main", cwd=self.d)
        sh("git", "config", "user.email", "t@t", cwd=self.d); sh("git", "config", "user.name", "t", cwd=self.d)
        self.write("iris/A.v", BASE_V); self.write("iris/_CoqProject", COQPROJECT); self.write("Makefile", "audit-only:\n\tcoqc x\n")
        self.commit("base")
    def write(self, p, s):
        with open(os.path.join(self.d, p), "w") as f: f.write(s)
    def commit(self, m):
        sh("git", "add", "-A", cwd=self.d); sh("git", "commit", "-q", "-m", m, cwd=self.d)
        return sh("git", "rev-parse", "HEAD", cwd=self.d).strip()
    def check(self, upstream=None):
        os.chdir(self.d)
        base = I.resolve_tree("HEAD"); tree = I.resolve_tree("WORK")
        return I.check(base, tree, upstream, I.resolve_tree("INDEX"))

def kinds(rep):
    return sorted((who, k) for who, k, _, _ in rep.block), sorted((who, k) for who, k, _, _ in rep.review)

class T(unittest.TestCase):
    def setUp(self): self.r = Repo()
    def test_comment_and_string_are_ignored(self):
        self.r.write("iris/A.v", BASE_V + "(* we would admit nothing; Axiom-free *)\nDefinition s := \"Admitted\".\n")
        b, r = kinds(self.r.check()); self.assertEqual(b, [("ours", "NOT-AUDITED")]); self.assertEqual(r, [])
    def test_module_type_field_is_review_not_block(self):
        self.r.write("iris/A.v", BASE_V.replace("End SPEC.", "  Parameter wp_g : nat -> Prop.\nEnd SPEC."))
        b, r = kinds(self.r.check()); self.assertEqual(b, [("ours", "NOT-AUDITED")]); self.assertEqual(r, [("ours", "MT-FIELD")])
    def test_toplevel_axiom_blocks(self):
        self.r.write("iris/A.v", BASE_V + "Axiom leak : False.\n")
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "AXIOM"), b)
    def test_admitted_blocks_and_gone_is_review(self):
        self.r.write("iris/A.v", BASE_V.replace("Lemma dropme : n = n. Proof. reflexivity. Qed.", "Lemma other : True. Proof. Admitted."))
        b, r = kinds(self.r.check()); self.assertIn(("ours", "ADMIT"), b); self.assertIn(("ours", "GONE"), r)
    def test_variable_outside_section_is_an_axiom(self):
        self.r.write("iris/A.v", BASE_V + "Variable loose : nat.\n")
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "AXIOM"), b)
    def test_disabled_checker_blocks(self):
        self.r.write("iris/A.v", BASE_V + "Unset Guard Checking.\n")
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "CHECKER"), b)
    def test_coqproject_flags_block_rows_review(self):
        self.r.write("iris/_CoqProject", COQPROJECT.replace("+notation", "-notation") + "B.v\n"); self.r.write("iris/B.v", "")
        b, r = kinds(self.r.check()); self.assertIn(("ours", "FLAGS"), b); self.assertIn(("ours", "ROWS"), r)
    def test_coqproject_missing_row_file_blocks(self):
        self.r.write("iris/_CoqProject", COQPROJECT + "Ghost.v\n")
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "ROWS"), b)
    def test_deleted_file_still_required_blocks(self):
        self.r.write("iris/B.v", "Require Import A.\n"); self.r.write("iris/_CoqProject", COQPROJECT + "B.v\n"); self.r.commit("b")
        os.remove(os.path.join(self.r.iris, "A.v")); self.r.write("iris/_CoqProject", "-R . xv6iris\n-arg -w\n-arg +notation-incompatible-prefix\nB.v\n# SystemAssumptions.v\n")
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "DELETED"), b)
    def test_deleted_file_only_mentioned_in_comment_is_review(self):
        self.r.write("iris/B.v", "(* see A *)\n"); self.r.write("iris/_CoqProject", COQPROJECT + "B.v\n"); self.r.commit("b")
        os.remove(os.path.join(self.r.iris, "A.v")); self.r.write("iris/_CoqProject", "-R . xv6iris\n-arg -w\n-arg +notation-incompatible-prefix\nB.v\n# SystemAssumptions.v\n")
        b, r = kinds(self.r.check()); self.assertNotIn(("ours", "DELETED"), b); self.assertIn(("ours", "DELETED"), r)
    def test_upstream_attribution(self):
        # an "upstream" commit adds the axiom; our tree carries the same line -> upstream's, review only
        sh("git", "checkout", "-q", "-b", "up", cwd=self.r.d)
        self.r.write("iris/A.v", BASE_V + "Axiom theirs : False.\n"); up = self.r.commit("upstream adds")
        sh("git", "checkout", "-q", "main", cwd=self.r.d)
        self.r.write("iris/A.v", BASE_V + "Axiom theirs : False.\nAxiom mine : False.\n")
        rep = self.r.check(upstream=up)   # both block (same rule for everyone); the label says whose
        self.assertEqual(sorted((w, k) for w, k, _, t in rep.block if k == "AXIOM"), [("ours", "AXIOM"), ("upstream", "AXIOM")])
    def test_statement_change_blocks_unchanged_moves_do_not(self):
        self.r.write("iris/A.v", BASE_V.replace("Lemma keep : n = n.", "Lemma keep : n = n + 0."))
        b, _ = kinds(self.r.check()); self.assertIn(("ours", "STATEMENT"), b)
        self.r.write("iris/A.v", "(* moved *)\n" + BASE_V.replace("  Lemma keep : n = n. Proof. reflexivity. Qed.\n", "")
                     + "Section S2.\n  Variable n : nat.\n  Lemma keep :\n    n = n. Proof. reflexivity. Qed.\nEnd S2.\n")
        b, _ = kinds(self.r.check()); self.assertNotIn(("ours", "STATEMENT"), b)
    def test_statement_change_attributed_to_upstream(self):
        sh("git", "checkout", "-q", "-b", "up2", cwd=self.r.d)
        self.r.write("iris/A.v", BASE_V.replace("Lemma keep : n = n.", "Lemma keep : n = n + 0.")); up = self.r.commit("upstream restates")
        sh("git", "checkout", "-q", "main", cwd=self.r.d)
        self.r.write("iris/A.v", BASE_V.replace("Lemma keep : n = n.", "Lemma keep : n = n + 0."))
        self.assertIn(("upstream", "STATEMENT"), [(w, k) for w, k, _, _ in self.r.check(upstream=up).block])
    def test_sentence_end(self):
        code = "Lemma f : Nat.add 1 2 = x.(p) /\\ P. Proof. Admitted."
        self.assertEqual(code[:I.sentence_end(code, 0)], "Lemma f : Nat.add 1 2 = x.(p) /\\ P.")
    def test_makefile_trust_line_blocks_pin_bump_reviews(self):
        self.r.write("Makefile", "XV6_REV ?= abc\naudit-only:\n\tcoqc y\n")
        b, r = kinds(self.r.check()); self.assertIn(("ours", "MAKEFILE"), b)
        self.r.write("Makefile", "XV6_REV ?= abc\naudit-only:\n\tcoqc x\n"); self.r.commit("m")
        self.r.write("Makefile", "XV6_REV ?= def\naudit-only:\n\tcoqc x\n")
        b, r = kinds(self.r.check()); self.assertNotIn(("ours", "MAKEFILE"), b); self.assertIn(("ours", "MAKEFILE"), r)
    def test_fingerprint_ignores_line_numbers(self):
        self.r.write("iris/A.v", BASE_V + "Axiom leak : False.\n"); f1 = self.r.check().fingerprint()
        self.r.write("iris/A.v", "(* moved *)\n\n" + BASE_V + "Axiom leak : False.\n"); f2 = self.r.check().fingerprint()
        self.assertEqual(f1, f2)
    def test_audit_log_parser(self):
        log = "cd iris && coqc -noglob SystemAssumptions.v\nAxioms:\nA.b : T\nC.d :\n  forall x, T\nE : U\n"
        self.assertEqual(I.parse_audit_log(log), {"SystemAssumptions.v": ["A.b", "C.d", "E"]})

if __name__ == "__main__":
    unittest.main(verbosity=1)
