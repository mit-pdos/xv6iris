import hashlib
import os
import sys
import tempfile
import unittest
from pathlib import Path

IRIS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(IRIS_DIR))

import find_weak_imports as weak


def span(text, needle, start=0):
    offset = text.index(needle, start)
    return f"{offset}:{offset + len(needle) - 1}"


def write_module(root, name, source, records):
    (root / f"{name}.v").write_text(source)
    digest = hashlib.md5(source.encode()).hexdigest()
    body = "\n".join([f"DIGEST {digest}", f"Fx.{name}", *records, ""])
    (root / f"{name}.glob").write_text(body)


class WeakImportTests(unittest.TestCase):
    def test_complete_import_parser_handles_comments_and_multiline(self):
        source = (
            'Definition s := "Require Import Fake.".\n'
            '(* Require Import AlsoFake. (* nested *) *)\n'
            'Require Import ProcGeom. (* cpus_ptr *)\n'
            'Require Import\n'
            '  LinkArgstr ProofSysLink.\n'
        )
        statements = weak.parse_complete_imports(source)
        self.assertEqual(
            [statement.modules for statement in statements],
            [["ProcGeom"], ["LinkArgstr", "ProofSysLink"]],
        )
        self.assertEqual([statement.lineno for statement in statements], [3, 4])

    def make_project(self):
        temp = tempfile.TemporaryDirectory()
        root = Path(temp.name)
        (root / "_CoqProject").write_text("-R . x\nA.v\nB.v\n")

        definitions = ["Definition leaf := 0.", "Definition mid := leaf."]
        definitions += [f"Definition unused{i} := {i}." for i in range(10)]
        source_a = "\n".join(definitions) + "\n"
        records_a = [
            f"def {span(source_a, 'leaf')} <> leaf",
            f"def {span(source_a, 'mid')} <> mid",
            f"R{span(source_a, 'leaf', source_a.index('mid'))} x.A <> leaf def",
        ]
        for i in range(10):
            records_a.append(
                f"def {span(source_a, f'unused{i}')} <> unused{i}"
            )
        write_module(root, "A", source_a, records_a)

        source_b = "Require Import A.\nCheck mid.\n"
        records_b = [
            f"R{span(source_b, 'A')} x.A <> <> lib",
            f"R{span(source_b, 'mid')} x.A <> mid def",
        ]
        write_module(root, "B", source_b, records_b)
        return temp, root

    def test_finds_transitive_two_unit_fragment(self):
        temp, root = self.make_project()
        self.addCleanup(temp.cleanup)
        result = weak.analyze(
            str(root), max_fraction=0.20,
        )
        self.assertEqual(len(result.candidates), 1)
        candidate = result.candidates[0]
        self.assertEqual(candidate.consumer, "B.v")
        self.assertEqual(candidate.producer, "A.v")
        self.assertEqual(candidate.direct_units, ["mid"])
        self.assertEqual(candidate.closure_units, ["leaf", "mid"])
        self.assertEqual(candidate.producer_units, 12)
        detail = result.edge_weaknesses[("B", "A")]
        self.assertEqual(detail.status, "weak")
        self.assertEqual(
            detail.annotation(), "weak — 16.7% (2/12); symbols: `mid`"
        )

    def test_fraction_threshold_filters_candidate(self):
        temp, root = self.make_project()
        self.addCleanup(temp.cleanup)
        result = weak.analyze(
            str(root), max_fraction=0.10,
        )
        self.assertEqual(result.candidates, [])
        self.assertEqual(result.live_symbol_edges, 1)
        detail = result.edge_weaknesses[("B", "A")]
        self.assertEqual(detail.status, "not_weak")
        self.assertEqual(detail.closure_count, 2)
        self.assertEqual(detail.producer_units, 12)

    def test_many_direct_roots_qualify_when_total_fraction_is_small(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "_CoqProject").write_text("-R . x\nA.v\nB.v\n")
            definitions = [f"Definition item{i} := {i}." for i in range(50)]
            source_a = "\n".join(definitions) + "\n"
            records_a = [
                f"def {span(source_a, f'item{i}')} <> item{i}"
                for i in range(50)
            ]
            write_module(root, "A", source_a, records_a)

            source_b = "Require Import A.\nCheck item0.\nCheck item1.\n" \
                       "Check item2.\nCheck item3.\n"
            records_b = [f"R{span(source_b, 'A')} x.A <> <> lib"]
            records_b += [
                f"R{span(source_b, f'item{i}')} x.A <> item{i} def"
                for i in range(4)
            ]
            write_module(root, "B", source_b, records_b)

            result = weak.analyze(str(root), max_fraction=0.10)
            self.assertEqual(len(result.candidates), 1)
            self.assertEqual(result.candidates[0].direct_count, 4)
            self.assertEqual(result.candidates[0].closure_count, 4)
            self.assertEqual(result.candidates[0].fraction, 0.08)

    def test_unmatched_root_suppresses_whole_edge(self):
        temp, root = self.make_project()
        self.addCleanup(temp.cleanup)
        source_b = (root / "B.v").read_text()
        source_b += "Check generated_only.\n"
        records_b = [
            f"R{span(source_b, 'A')} x.A <> <> lib",
            f"R{span(source_b, 'mid')} x.A <> mid def",
            f"R{span(source_b, 'generated_only')} "
            "x.A <> generated_only mod",
        ]
        write_module(root, "B", source_b, records_b)

        result = weak.analyze(str(root), max_fraction=0.20)
        self.assertEqual(result.candidates, [])
        self.assertEqual(result.unmatched_symbols, 1)

    def test_other_imports_multi_hop_closure_suppresses_edge(self):
        temp, root = self.make_project()
        self.addCleanup(temp.cleanup)
        (root / "_CoqProject").write_text(
            "-R . x\nA.v\nB.v\nC.v\nD.v\n"
        )

        source_c = "Require Import A.\nDefinition c := 0.\n"
        write_module(root, "C", source_c, [
            f"R{span(source_c, 'A')} x.A <> <> lib",
            f"def {span(source_c, 'c')} <> c",
        ])
        # Export edges are excluded from candidate reporting by default, but
        # still load their target and therefore belong in the build DAG.
        source_d = "Require Export C.\nDefinition d := 0.\n"
        write_module(root, "D", source_d, [
            f"R{span(source_d, 'C')} x.C <> <> lib",
            f"def {span(source_d, 'd')} <> d",
        ])

        source_b = "Require Import A D.\nCheck mid.\n"
        write_module(root, "B", source_b, [
            f"R{span(source_b, 'A')} x.A <> <> lib",
            f"R{span(source_b, 'D')} x.D <> <> lib",
            f"R{span(source_b, 'mid')} x.A <> mid def",
        ])

        result = weak.analyze(str(root), max_fraction=0.20)
        self.assertEqual(result.candidates, [])
        self.assertEqual(result.transitively_covered_edges, 1)
        self.assertEqual(
            result.edge_weaknesses[("B", "A")].status, "covered"
        )

    def test_kernel_decode_producers_are_expected_and_suppressed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "_CoqProject").write_text(
                "-R . x\nKernelDecode01.v\nB.v\n"
            )
            definitions = [f"Definition kd{i} := {i}." for i in range(20)]
            source_kd = "\n".join(definitions) + "\n"
            write_module(root, "KernelDecode01", source_kd, [
                f"def {span(source_kd, f'kd{i}')} <> kd{i}"
                for i in range(20)
            ])
            source_b = "Require Import KernelDecode01.\nCheck kd0.\n"
            write_module(root, "B", source_b, [
                f"R{span(source_b, 'KernelDecode01')} "
                "x.KernelDecode01 <> <> lib",
                f"R{span(source_b, 'kd0')} x.KernelDecode01 <> kd0 def",
            ])

            result = weak.analyze(str(root), max_fraction=0.10)
            self.assertEqual(result.candidates, [])
            self.assertEqual(result.expected_producer_edges, 1)
            self.assertEqual(
                result.edge_weaknesses[("B", "KernelDecode01")].status,
                "expected",
            )
            self.assertFalse(weak.is_expected_producer("KernelRvcDecode.v"))

    def test_record_projection_is_grouped_with_record(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = (
                "Record pair := { left : nat; right : nat }.\n"
                "Arguments Build_pair _ _.\n"
            )
            records = [
                f"rec {span(source, 'pair')} <> pair",
                f"proj {span(source, 'left')} <> left",
                f"proj {span(source, 'right')} <> right",
                f"R{span(source, 'Build_pair')} x.A <> Build_pair constr",
            ]
            write_module(root, "A", source, records)
            info = weak.parse_module(str(root / "A.v"), str(root / "A.glob"))
            self.assertEqual(len(info.units), 1)
            self.assertEqual(info.alias_to_unit[("<>", "Build_pair")], 0)
            self.assertEqual(info.alias_to_unit[("<>", "left")], 0)
            self.assertEqual(info.alias_to_unit[("<>", "right")], 0)


if __name__ == "__main__":
    unittest.main()
