#!/usr/bin/env python3
"""weak_rocq2lean.py -- PRE-TRANSLATOR for the Rocq->Lean weak-memory port.

Turns one Rocq weak file (`../xv6iris-spinlock/iris/<Name>.v`) into a Lean
DRAFT that a worker then fixes.  The draft is never committed: it is a
starting point that does the mechanical part (header skeleton, imports, the
name map, binder/vocabulary/syntax translation, the easy tactics) so the
worker spends its effort on the parts that need thought.

USAGE
  tools/weak_rocq2lean.py WeakFoo                 # draft to stdout
  tools/weak_rocq2lean.py WeakFoo -o Weak/WeakFoo.lean
  tools/weak_rocq2lean.py WeakFoo --stmt-only     # every proof `by sorry`
  tools/weak_rocq2lean.py WeakFoo --rocq-comments # each tactic line followed
                                                  #   by its Rocq source
  tools/weak_rocq2lean.py --names WeakFoo         # print the name map only
  tools/weak_rocq2lean.py --eval A B C --tree ../xv6iris-weak-w5x
        # evaluation: draft each (already ported) file with the file's own Lean
        # port HIDDEN from the name table, write Weak/Draft/<A>{S,P}.lean
        # into the scratch tree, build both on the VM (lean-gcp) and report
        # the % of statements / proofs that elaborate as emitted.

WHAT THE DRAFT CONTAINS
  * the tree-style header (Rocq path, the Rocq header comment, a Deviations
    skeleton, the auto-generated Rocq->Lean name map, file-qualified dup names);
  * `import`s (weak deps -> `Weak.<Name>`, plus the Lean file of every
    resolved name that is not reachable from those -- e.g. `execNil` lives in
    `Weak.WeakAxiomatic2`; stdpp/iris/SC imports -> the shims / Lean
    counterparts of notes/weak-port-map.md section 2);
  * every Definition/Fixpoint/Inductive/Record/Lemma, names translated by a
    GLOBAL table built from every ported Weak/*.lean (their declarations and
    header name maps), the shims' declarations and the Rocq sources of the
    ported files (record fields -> `Struct.field`, constructors ->
    `Type.Ctor`, record constructors -> `Type.mk`, dup names ->
    `<File>.<name>` of the file actually imported);
  * section variables made explicit leading arguments (only those a
    declaration uses, transitively through the section lemmas it cites);
  * proofs transliterated tactic by tactic.  A tactic the translator cannot
    handle becomes

        all_goals sorry  -- ROCQ: <the Rocq tactic>

    and the rest of that goal block is kept as `-- ROCQ:` comment lines, so
    the worker sees exactly what to replace.  Translated-but-guessed spots
    are marked `-- XLAT?:` (e.g. `<[i:=x]>` assumed to be a LIST update).

  THE DRAFT CONTAINS `sorry`.  Workers must remove every one (lint bans them).

MEASURED (2026-10-06, own port + downstream hidden, built on the VM):
  non-Iris files (Lock/Kill/LitmusProj/ProbeSwap/PromiseLitmus): statements
  elaborate 99%, theorem statements implied by the real port 96%, proofs build
  as emitted 72%; with WeakErase/WeakRvwmoNorm/WeakRobust added: 97% / 82% / 64%.
  MonPred/Iris files (WeakVProp, WeakView): statements 15% -- use the draft only
  for header, name map and the pure lemmas there.

EVAL NOTE: the scratch tree's lakefile needs moreLeanArgs = ["-DmaxErrors=100000"]
on the Weak lib, and must be re-rsynced when new ports land.

Read notes/weak-port-pretranslate.md for the worker workflow and the measured
hit rates.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Optional

TREE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROCQ_DIR = "/home/bsdinis/dev/xv6iris-spinlock/iris"
SHIMS = ["Rel", "StdppSet", "StdppMap", "SetSolver", "OrdKeys", "StdppList",
         "QpLemmas", "FinToSet", "MonPredExtra"]

# ---------------------------------------------------------------------------
# Vocabulary tables (WeakMem deviation 2, WeakRvwmoGraph deviation 2, the
# shims' vocabulary tables).
# ---------------------------------------------------------------------------

# plain identifier -> Lean identifier
IDENT_MAP = {
    "nat": "Nat", "Z": "Int", "bool": "Bool", "list": "List", "option": "Option",
    "prod": "Prod", "unit": "Unit", "string": "String", "positive": "Nat",
    "N": "Nat", "Qp": "Qp", "sum": "Sum",
    "bv": "BitVec", "gmap": "GMapF", "gset": "GSet",
    "agent": "Nat", "wreg": "Nat",
    "Σ": "GF", "gFunctors": "BundledGFunctors", "iProp": "IProp", "iPropI": "IProp",
    "bi_entails": "BI.Entails", "monPred_at": "MonPred.monPred_at", "monPred_in": "MonPred.monPred_in",
    "Some": "some", "None": "none", "inl": "Sum.inl", "inr": "Sum.inr",
    "pair": "Prod.mk", "fst": "Prod.fst", "snd": "Prod.snd",
    "tt": "()", "I": "trivial",
    "length": "List.length", "app": "HAppend.hAppend", "rev": "List.reverse",
    "reverse": "List.reverse", "take": "List.take", "drop": "List.drop",
    "map": "List.map", "fmap": "Functor.map", "mjoin": "List.flatten",
    "concat": "List.flatten", "seq": "List.range'", "zip": "List.zip",
    "zip_with": "List.zipWith", "foldl": "List.foldl", "foldr": "List.foldr",
    "replicate": "List.replicate", "NoDup": "List.Nodup", "last": "List.getLast?",
    "head": "List.head?", "tail": "List.tail", "lookup": "List.get?",
    "Forall2": "List.Forall₂", "list_sum": "List.sum", "sum_list": "List.sum",
    "Nat.max": "max", "Nat.min": "min", "Z.max": "max", "Z.min": "min",
    "max": "max", "min": "min",
    "Z.to_nat": "Int.toNat", "Z.of_nat": "Int.ofNat", "Z.abs": "Int.natAbs",
    "Nat.succ": "Nat.succ", "Nat.pred": "Nat.pred",
    "negb": "not", "andb": "and", "orb": "or", "xorb": "xor",
    "bool_decide": "decide", "decide": "decide",
    "Nat.eqb": "Nat.beq", "Nat.leb": "Nat.ble", "Nat.ltb": "Nat.blt",
    "Z.eqb": "Int.beq", "option_map": "Option.map",
    "is_Some": "Option.isSome", "is_true": "id",
    "True": "True", "False": "False", "Prop": "Prop", "Type": "Type",
    "Set": "Type", "eq": "Eq", "not": "Not", "iff": "Iff", "and": "And",
    "or": "Or", "ex": "Exists",
    "EqDecision": "DecidableEq", "Decision": "Decidable", "Inhabited": "Inhabited",
    "Countable": "Ord", "elements": "FiniteSet.toList", "dom": "FiniteMap.dom_set",
    "id": "id", "const": "Function.const",
    "prefix_of": "List.IsPrefix", "suffix_of": "List.IsSuffix",
    "Z.add_0_r": "Int.add_zero", "Z.add_0_l": "Int.zero_add",
    "Nat.add_0_r": "Nat.add_zero", "Nat.add_0_l": "Nat.zero_add",
    "Nat.add_comm": "Nat.add_comm", "Nat.add_assoc": "Nat.add_assoc",
    "Nat.lt_irrefl": "Nat.lt_irrefl", "Nat.le_refl": "Nat.le_refl",
    "Nat.add_1_r": "Nat.succ_eq_add_one", "Z.sub_diag": "Int.sub_self",
    "f_equal": "congrArg", "eq_refl": "rfl", "eq_sym": "Eq.symm",
    "eq_trans": "Eq.trans", "conj": "And.intro", "or_introl": "Or.inl",
    "or_intror": "Or.inr", "ex_intro": "Exists.intro", "proj1": "And.left",
    "proj2": "And.right", "False_ind": "False.elim", "injective_projections": "Prod.ext",
    "elem_of_list_In": "List.mem_iff_get",
    "fmap_Some": "Option.map_eq_some_iff", "fmap_is_Some": "Option.isSome_map",
    "fmap_None": "Option.map_eq_none_iff", "option_fmap_id": "Option.map_id",
    "bool_decide_eq_true_2": "decide_eq_true", "bool_decide_eq_false_2": "decide_eq_false",
    "bool_decide_eq_true": "decide_eq_true_iff", "bool_decide_eq_false": "decide_eq_false_iff_not",
    "bool_decide_spec": "decide_eq_true_iff", "bool_decide_true": "decide_true",
    "bool_decide_false": "decide_false", "Z.leb_le": "Int.le_iff_lt_add_one",
    "Nat.lt_succ_r": "Nat.lt_succ_iff", "Nat.le_succ_l": "Nat.succ_le", "classic": "Classical.em",
    "NNPP": "Classical.byContradiction",
}

# head identifier -> (arity, template).  {0},{1},.. are the emitted arguments.
TEMPLATES = {
    "S": (1, "({0} + 1)"),
    "is_Some": (1, "({0}).isSome"),
    "Forall": (2, "(∀ x ∈ {1}, {0} x)"),
    "Exists": (2, "(∃ x ∈ {1}, {0} x)"),
    "existsb": (2, "(List.any {1} {0})"),
    "forallb": (2, "(List.all {1} {0})"),
    "In": (2, "({0} ∈ {1})"),
    "default": (2, "(({1}).getD {0})"),
    "from_option": (3, "(Option.elim {2} {1} {0})"),
    "Z_to_bv": (2, "(BitVec.ofInt {0} {1})"),
    "bv_unsigned": (1, "((({0}).toNat : Nat) : Int)"),
    "bv_to_nat": (1, "(({0}).toNat)"),
    "Z.of_nat": (1, "(({0} : Nat) : Int)"),
    "filter": (2, "(List.filter (fun x => decide ({0} x)) {1})"),
    "NoDup": (1, "({0}).Nodup"),
    "length": (1, "({0}).length"),
}

TYPE_KINDS_UPPER = ("Record", "Structure", "Variant", "Class")

ROCQ_LIB_IMPORTS = {   # Rocq stdlib / stdpp / iris module -> Lean imports
    "stdpp.gmap": ["MachCSL.StdppMap", "MachCSL.StdppSet", "MachCSL.SetSolver"],
    "stdpp.list": ["MachCSL.StdppList"],
    "stdpp.relations": ["MachCSL.Rel"],
    "stdpp.sets": ["MachCSL.StdppSet", "MachCSL.SetSolver"],
    "stdpp.fin_sets": ["MachCSL.StdppSet", "MachCSL.SetSolver"],
    "stdpp.fin_maps": ["MachCSL.StdppMap"],
    "stdpp.finite": ["MachCSL.FinToSet"],
    "stdpp.numbers": ["MachCSL.QpLemmas"],
    "iris.bi.monpred": ["MachCSL.MonPredExtra"],
    "iris.proofmode.monpred": ["MachCSL.MonPredExtra"],
    "iris.proofmode.proofmode": ["Iris.ProofMode"],
    "iris.base_logic.lib.own": ["Iris.BaseLogic"],
}


# ---------------------------------------------------------------------------
# Naming
# ---------------------------------------------------------------------------

def camel(n: str) -> str:
    """Rocq snake_case -> the tree's lowerCamelCase (WeakMem deviation 1)."""
    prime = ""
    m = re.match(r"^(.*?)('*)$", n)
    base, prime = m.group(1), m.group(2)
    segs = [s for s in base.split("_") if s != ""]
    if not segs:
        return n
    out = segs[0]
    for s in segs[1:]:
        out += s[0].upper() + s[1:]
    return out + prime


def upper(n: str) -> str:
    c = camel(n)
    return c[0].upper() + c[1:] if c else c


# ---------------------------------------------------------------------------
# Rocq lexing: comments, sentences
# ---------------------------------------------------------------------------

@dataclass
class Sentence:
    text: str            # comment-free text, without the final '.'
    comments: list       # comments (raw, with delimiters) seen just before it
    line: int


def split_sentences(src: str) -> list[Sentence]:
    out: list[Sentence] = []
    i, n = 0, len(src)
    buf: list[str] = []
    pending_comments: list[str] = []
    line = 1
    start_line = 1
    while i < n:
        c = src[i]
        if src.startswith("(*", i):
            depth, j = 0, i
            while j < n:
                if src.startswith("(*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*)", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                elif src[j] == '"':
                    k = j + 1
                    while k < n and src[k] != '"':
                        k += 1
                    j = k + 1
                else:
                    j += 1
            com = src[i:j]
            line += com.count("\n")
            if "".join(buf).strip() == "":
                pending_comments.append(com)
            buf.append(" ")
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if src[j] == '"':
                    if j + 1 < n and src[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            buf.append(src[i:j + 1])
            line += src[i:j + 1].count("\n")
            i = j + 1
            continue
        if c == "." and (i + 1 >= n or src[i + 1] in " \t\r\n") and \
                not (i > 0 and src[i - 1] == "."):
            text = "".join(buf)
            if text.strip():
                out.append(Sentence(text.strip(), pending_comments, start_line))
            pending_comments = []
            buf = []
            i += 1
            continue
        if c == "\n":
            line += 1
        if not buf or "".join(buf).strip() == "":
            if not c.isspace():
                start_line = line
        buf.append(c)
        i += 1
    if "".join(buf).strip():
        out.append(Sentence("".join(buf).strip(), pending_comments, start_line))
    return out


# ---------------------------------------------------------------------------
# Rocq term tokenizer
# ---------------------------------------------------------------------------

OPS = sorted("""⊣⊢ |==> -∗ ={ }=∗ ∗-∗ <-> -> <- => := :> !!! !! .. <$> ++ :: <[ ]> {[ ]} && || =? <=? <? <= >= <>
.*1 .*2 ≤ ≥ ≠ → ↔ ∧ ∨ ¬ ∀ ∃ ∈ ∉ ⊆ ⊂ ∪ ∩ ∖ ∅ ≡ ## |- ⊢ /\\ \\/ ⊆+ ≡ₚ
.1 .2 ( ) [ ] { } , ; : | @ ' = < > + - * / ^ % ! ? & ~ # $ ` ∘ ⊤ ⊥ λ""".split(),
             key=len, reverse=True)

ID_START = re.compile(r"[A-Za-z_À-ʯͰ-κμ-Ͽᴀ-ᶿἀ-῿℀-⅏]")
ID_CHAR = re.compile(r"[A-Za-z0-9_'À-ʯͰ-Ͽᴀ-ᶿἀ-῿₀-ₜ℀-⅏]")


@dataclass
class Tok:
    kind: str   # id, num, str, op
    val: str
    sp: bool    # preceded by whitespace

    def __repr__(self):
        return f"{self.kind}:{self.val}"


# Rocq identifiers that are Lean keywords (renamed consistently, binders and uses alike)
LEAN_RESERVED = {k: k + "'" for k in (
    "at from open where deriving instance section namespace variable universe example local "
    "notation macro syntax import export structure inductive theorem def abbrev mutual private "
    "protected partial unsafe calc suffices obtain nomatch nofun").split()}
LEAN_RESERVED["Σ"] = "GF"


def tokenize(s: str) -> list[Tok]:
    toks: list[Tok] = []
    i, n = 0, len(s)
    sp = False
    while i < n:
        c = s[i]
        if c.isspace():
            sp = True
            i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 1
            toks.append(Tok("str", s[i:j + 1], sp))
            i = j + 1
            sp = False
            continue
        if c.isdigit():
            j = i
            while j < n and s[j].isdigit():
                j += 1
            toks.append(Tok("num", s[i:j], sp))
            i = j
            sp = False
            continue
        if ID_START.match(c) and c != "λ":
            j = i + 1
            while True:
                while j < n and ID_CHAR.match(s[j]):
                    j += 1
                if j + 1 < n and s[j] == "." and ID_START.match(s[j + 1]) and s[j + 1] != "λ":
                    j += 1
                    continue
                break
            v = s[i:j]
            toks.append(Tok("id", LEAN_RESERVED.get(v, v), sp))
            i = j
            sp = False
            continue
        for op in OPS:
            if s.startswith(op, i):
                # `.1` only directly after an atom
                if op in (".1", ".2") and (sp or not toks):
                    continue
                toks.append(Tok("op", op, sp))
                i += len(op)
                break
        else:
            toks.append(Tok("op", c, sp))
            i += 1
        sp = False
    # drop scope delimiters: `%nat`, `%Z`, ...
    out: list[Tok] = []
    k = 0
    while k < len(toks):
        t = toks[k]
        if t.kind == "op" and t.val == "%" and k + 1 < len(toks) and \
                toks[k + 1].kind == "id" and not toks[k + 1].sp and not t.sp:
            k += 2
            continue
        out.append(t)
        k += 1
    return out


# ---------------------------------------------------------------------------
# Tree of bracket groups
# ---------------------------------------------------------------------------

OPEN = {"(": ")", "[": "]", "{[": "]}", "<[": "]>", "{": "}"}


@dataclass
class Group:
    open: str
    items: list
    sp: bool = False


def build_tree(toks: list[Tok]):
    stack = [Group("", [])]
    for t in toks:
        if t.kind == "op" and t.val in OPEN:
            stack.append(Group(t.val, [], t.sp))
        elif t.kind == "id" and t.val == "match":
            stack.append(Group("match", [], t.sp))
        elif t.kind == "op" and len(stack) > 1 and t.val == OPEN.get(stack[-1].open):
            g = stack.pop()
            stack[-1].items.append(g)
        elif t.kind == "id" and t.val == "end" and len(stack) > 1 and stack[-1].open == "match":
            g = stack.pop()
            stack[-1].items.append(g)
        else:
            stack[-1].items.append(t)
    while len(stack) > 1:      # unbalanced: flatten
        g = stack.pop()
        stack[-1].items.append(Tok("op", g.open, g.sp))
        stack[-1].items.extend(g.items)
    return stack[0].items


def merge_ltac(items):
    out = []
    k = 0
    while k < len(items):
        y = items[k]
        if is_tok(y, "id", "ltac") and k + 2 < len(items) and is_tok(items[k + 1], "op", ":") and \
                isinstance(items[k + 2], Group) and items[k + 2].open == "(":
            out.append(Group("ltac", items[k + 2].items, y.sp))
            k += 3
            continue
        out.append(y)
        k += 1
    return out


def merge_ipm(items):
    """Glue Iris pattern prefixes: `%H`, `#H`, `>H`, `-#H`, `!>`, `!%`, `/=`, `//`, `$`."""
    out = []
    k = 0
    while k < len(items):
        y = items[k]
        if is_tok(y, "op") and y.val in ("%", "#", ">", "-", "!", "/", "*", "$") and k + 1 < len(items):
            z = items[k + 1]
            if y.val == "-" and is_tok(z, "op", "#") and k + 2 < len(items):
                out.append(Tok("id", "-#" + tok_text(items[k + 2]), y.sp))
                k += 3
                continue
            if isinstance(z, Tok) and not z.sp and (z.kind == "id" or z.val in (">", "%", "=", "/", "*")):
                out.append(Tok("id", y.val + z.val, y.sp))
                k += 2
                continue
        out.append(y)
        k += 1
    return out


def is_tok(x, kind=None, val=None):
    return isinstance(x, Tok) and (kind is None or x.kind == kind) and (val is None or x.val == val)


def split_top(items, sep):
    parts, cur = [], []
    for x in items:
        if is_tok(x, "op", sep):
            parts.append(cur)
            cur = []
        else:
            cur.append(x)
    parts.append(cur)
    return parts


# ---------------------------------------------------------------------------
# Global symbol table
# ---------------------------------------------------------------------------

@dataclass
class RocqDecl:
    name: str
    kind: str
    file: str
    sort_prop: bool = False
    ctors: list = field(default_factory=list)
    fields: list = field(default_factory=list)
    record_ctor: Optional[str] = None
    alias: Optional[str] = None   # Notation x := (body)
    is_map: bool = False          # a Definition whose type is a gmap
    ret_option: bool = False      # a Definition/Fixpoint returning an option


def scan_rocq_decls(path: str, modname: str) -> list[RocqDecl]:
    try:
        src = open(path).read()
    except OSError:
        return []
    out = []
    for s in split_sentences(src):
        d = parse_rocq_decl_head(s.text, modname)
        if d:
            out.append(d)
    return out


DECL_KW = ("Definition", "Fixpoint", "CoFixpoint", "Lemma", "Theorem", "Corollary",
           "Fact", "Remark", "Proposition", "Example", "Inductive", "CoInductive",
           "Variant", "Record", "Structure", "Class", "Instance", "Notation", "Let",
           "Program Definition", "Program Fixpoint", "Infix")


def strip_attrs(t: str) -> tuple[str, list[str]]:
    attrs = []
    while True:
        m = re.match(r"^(#\[[^\]]*\]|Local|Global|Program|Polymorphic|Monomorphic|Private|Canonical)\s+", t)
        if not m:
            return t, attrs
        attrs.append(m.group(1))
        t = t[m.end():]


def parse_rocq_decl_head(text: str, modname: str) -> Optional[RocqDecl]:
    t, attrs = strip_attrs(text)
    m = re.match(r"^(Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Corollary|Fact|Remark|Proposition|"
                 r"Example|Inductive|CoInductive|Variant|Record|Structure|Class|Instance|Notation|Let)\s+"
                 r"([^\s:({\[]+)", t)
    if not m:
        return None
    kind, name = m.group(1), m.group(2)
    if kind == "Notation":
        name = name.strip('"')
        if not re.match(r"^[\w']+$", name):
            return None
        mm = re.match(r'^Notation\s+"?([\w\']+)"?\s*:=\s*(.*?)(\s*\((only parsing|at level[^)]*)\))?\s*$', t, re.S)
        alias = mm.group(2).strip() if mm else None
        return RocqDecl(name, kind, modname, alias=alias)
    d = RocqDecl(name, kind, modname)
    if kind == "Definition" and re.search(r":\s*gmap\b", top_level_head(t)):
        d.is_map = True
    if kind in ("Definition", "Fixpoint"):
        _, ty, _ = split_sig(top_level_head(t)[len(m.group(0)):] + " := x")
        if ty and re.match(r"^option\b", ty.strip()):
            d.ret_option = True
    if kind in ("Inductive", "CoInductive", "Variant"):
        head, _, body = t.partition(":=")
        d.sort_prop = bool(re.search(r"Prop\s*$", head.strip()))
        for c in re.findall(r"\|\s*([A-Za-z_][\w']*)", body):
            d.ctors.append(c)
        if not body.strip().startswith("|"):
            mm = re.match(r"\s*([A-Za-z_][\w']*)", body)
            if mm and mm.group(1) not in d.ctors:
                d.ctors.insert(0, mm.group(1))
    if kind in ("Record", "Structure", "Class"):
        head, _, body = t.partition(":=")
        d.sort_prop = bool(re.search(r"Prop\s*$", head.strip()))
        mm = re.match(r"\s*([A-Za-z_][\w']*)?\s*\{(.*)\}", body, re.S)
        if mm:
            d.record_ctor = mm.group(1)
            for f in mm.group(2).split(";"):
                fm = re.match(r"\s*([A-Za-z_][\w']*)\s*:", f)
                if fm:
                    d.fields.append(fm.group(1))
    return d


LEAN_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|irreducible_def)\s+"
    r"([^\s:({\[]+)")


@dataclass
class LeanSyms:
    names: dict = field(default_factory=dict)        # full name -> file
    fields: dict = field(default_factory=dict)       # struct full name -> [fields]
    ctors: dict = field(default_factory=dict)        # type full name -> [ctors]
    imports: dict = field(default_factory=dict)      # module -> [imports]
    header: dict = field(default_factory=dict)       # file stem -> header text


def scan_lean_file(path: str, mod: str, syms: LeanSyms):
    try:
        lines = open(path).read().split("\n")
    except OSError:
        return
    ns: list[str] = []
    imps = []
    cur_struct = None
    cur_ind = None
    in_header = False
    header = []
    for idx, ln in enumerate(lines):
        if idx == 0 and ln.startswith("/-"):
            in_header = True
        if in_header:
            header.append(ln)
            if ln.rstrip().endswith("-/"):
                in_header = False
            continue
        m = re.match(r"^import\s+(\S+)", ln)
        if m:
            imps.append(m.group(1))
            continue
        m = re.match(r"^namespace\s+(\S+)", ln)
        if m:
            ns.extend(m.group(1).split("."))
            continue
        m = re.match(r"^end\s+(\S+)", ln)
        if m:
            k = len(m.group(1).split("."))
            if ns[-k:] == m.group(1).split("."):
                del ns[-k:]
            continue
        m = LEAN_DECL_RE.match(ln)
        if m:
            kind, nm = m.group(1), m.group(2)
            full = ".".join(ns + [nm])
            syms.names[full] = mod
            cur_struct = full if kind in ("structure", "class") else None
            cur_ind = full if kind == "inductive" else None
            if cur_struct:
                syms.fields.setdefault(full, [])
                mm = re.search(r"\bwhere\b\s*$", ln)
            if cur_ind:
                syms.ctors.setdefault(full, [])
                for c in re.findall(r"\|\s*([A-Za-z_][\w']*)", ln.split("where", 1)[-1] if "where" in ln else ""):
                    syms.ctors[full].append(c)
                    syms.names[full + "." + c] = mod
            continue
        if cur_struct and re.match(r"^\s+\S", ln):
            fm = re.match(r"^\s+(?:\(?)([A-Za-z_][\w']*)\s*(?:[A-Za-z_][\w' ]*)?:\s", ln)
            mk = re.match(r"^\s+([A-Za-z_][\w']*)\s*::", ln)
            if mk:
                syms.names[cur_struct + "." + mk.group(1)] = mod
                syms.ctors.setdefault(cur_struct, []).append(mk.group(1))
            elif fm and not ln.strip().startswith("--") and not ln.strip().startswith("deriving"):
                for f in re.findall(r"([A-Za-z_][\w']*)", ln.split(":")[0]):
                    syms.fields[cur_struct].append(f)
                    syms.names[cur_struct + "." + f] = mod
            continue
        if cur_ind and re.match(r"^\s+\|", ln):
            c = re.match(r"^\s+\|\s*([A-Za-z_][\w']*)", ln)
            if c:
                syms.ctors[cur_ind].append(c.group(1))
                syms.names[cur_ind + "." + c.group(1)] = mod
            continue
        if ln and not ln[0].isspace():
            cur_struct = None
            cur_ind = None
    syms.imports[mod] = imps
    if mod.startswith("Weak."):
        syms.header[mod.split(".", 1)[1]] = "\n".join(header)
    for s in list(syms.fields):
        if s in syms.names and s not in syms.ctors:
            syms.ctors[s] = []
    for s in syms.fields:
        if s.split(".")[-1] and s + ".mk" not in syms.names and not any(
                (s + "." + c) in syms.names for c in syms.ctors.get(s, [])):
            syms.names[s + ".mk"] = syms.names.get(s, mod)


def lean_scan_tree(exclude: set[str]) -> LeanSyms:
    syms = LeanSyms()
    for d in ("Weak", "MachCSL", "Xv6"):
        root = os.path.join(TREE, d)
        for dp, _, fs in os.walk(root):
            if "Draft" in dp.split(os.sep):
                continue
            for f in fs:
                if not f.endswith(".lean"):
                    continue
                rel = os.path.relpath(os.path.join(dp, f), TREE)[:-5]
                mod = rel.replace(os.sep, ".")
                if mod in exclude:
                    continue
                scan_lean_file(os.path.join(dp, f), mod, syms)
    return syms


def header_name_pairs(header: str) -> list[tuple[str, str]]:
    pairs = []
    for m in re.finditer(r"`([^`\s]+)`\s*(?:↦|→|->|\|->)\s*`([^`\s]+)`", header):
        pairs.append((m.group(1), m.group(2)))
    i = header.lower().find("name map")
    if i >= 0:
        for m in re.finditer(r"`([^`\s]+)`[ ]`([^`\s]+)`", header[i:]):
            pairs.append((m.group(1), m.group(2)))
    return pairs


class NameTable:
    """Resolves Rocq identifiers to Lean ones for one target file."""

    LEAN_NS = ["Weak.", "MachCSL.Stdpp.", "MachCSL.", "Iris.Std.", "Iris.", "Xv6.", ""]

    def __init__(self, target: str, exclude_self: bool):
        self.target = target
        excl = {f"Weak.{target}"} if exclude_self else set()
        if exclude_self:
            for k in range(2, 6):
                excl.add(f"Weak.{target}{k}")
            # ... and every module that (transitively) imports it: in real use they cannot exist yet
            imps = {}
            for d in ("Weak",):
                for f in os.listdir(os.path.join(TREE, d)):
                    if f.endswith(".lean"):
                        txt = open(os.path.join(TREE, d, f)).read()
                        imps[f"{d}.{f[:-5]}"] = re.findall(r"^import\s+(\S+)", txt, re.M)
            changed = True
            while changed:
                changed = False
                for m, ims in imps.items():
                    if m not in excl and any(i in excl for i in ims):
                        excl.add(m)
                        changed = True
        self.lean = lean_scan_tree(excl)
        self.dag = json.load(open(os.path.join(TREE, "notes", "weak-port-dag.json")))
        self.dups = json.load(open(os.path.join(TREE, "notes", "weak-port-dupnames.json")))
        # transitive Rocq deps of the target
        self.deps_order = self._dep_order(target)
        self.rocq: dict[str, list[RocqDecl]] = {}
        self.by_name: dict[str, list[RocqDecl]] = defaultdict(list)
        for f in self.deps_order:
            ds = scan_rocq_decls(os.path.join(ROCQ_DIR, f + ".v"), f)
            self.rocq[f] = ds
            for d in ds:
                self.by_name[d.name].append(d)
        self.ported = {f for f in self.deps_order if self._lean_mod_of(f)}
        self.explicit: dict[tuple[str, str], str] = {}
        for f in self.deps_order:
            hdr = self.lean.header.get(f, "")
            rnames = {d.name for d in self.rocq.get(f, [])}
            for d in self.rocq.get(f, []):
                rnames.update(d.fields)
                rnames.update(d.ctors)
            for a, b in header_name_pairs(hdr):
                if a in rnames and self.lean_exists(b):
                    self.explicit.setdefault((f, a), b)
        self.used_modules: set[str] = set()
        self.local: dict[str, str] = {}     # names declared in the target
        self.local_kind: dict[str, RocqDecl] = {}
        self.unresolved: set[str] = set()
        self.alias_cache: dict[str, str] = {}
        self.quiet = False
        self.map_names: set = set()
        self.uses_partialmap = False

    def _lean_mod_of(self, f):
        return f"Weak.{f}" in self.lean.imports

    def _dep_order(self, target):
        seen, order = set(), []

        def go(f, depth=0):
            if f in seen or depth > 200:
                return
            seen.add(f)
            for d in self.dag.get(f, {}).get("weak_deps", []):
                go(d, depth + 1)
            order.append(f)
        go(target)
        # nearest first: direct deps, then the rest
        direct = self.dag.get(target, {}).get("weak_deps", [])
        rest = [f for f in reversed(order) if f not in direct and f != target]
        return [target] + list(direct) + rest

    def lean_exists(self, n) -> Optional[str]:
        for p in self.LEAN_NS:
            if (p + n) in self.lean.names:
                return p + n
        return None

    def lean_file(self, n) -> Optional[str]:
        full = self.lean_exists(n)
        return self.lean.names.get(full) if full else None

    def note_use(self, lean_name):
        f = self.lean_file(lean_name)
        if f:
            self.used_modules.add(f)

    # ----- the resolution proper
    def resolve_decl(self, d: RocqDecl) -> Optional[str]:
        """Lean name of a Rocq declaration of an already ported file."""
        f = d.file
        if (f, d.name) in self.explicit:
            return self.explicit[(f, d.name)]
        cands = []
        is_type = d.kind in ("Record", "Structure", "Variant", "Class") or \
            (d.kind in ("Inductive", "CoInductive") and not d.sort_prop)
        base = [camel(d.name), upper(d.name), d.name] if not is_type else \
            [upper(d.name), camel(d.name), d.name]
        if d.name in self.dups:
            cands += [f"{f}.{b}" for b in base]
        cands += base
        for c in cands:
            if self.lean_exists(c):
                return c
        return None

    def lean_for_local(self, d: RocqDecl) -> str:
        is_type = d.kind in ("Record", "Structure", "Variant", "Class") or \
            (d.kind in ("Inductive", "CoInductive") and not d.sort_prop)
        b = upper(d.name) if is_type else camel(d.name)
        if d.name in self.dups:
            return f"{self.target}.{b}"
        return b

    def register_local(self, d: RocqDecl):
        ln = self.lean_for_local(d)
        self.local[d.name] = ln
        self.local_kind[d.name] = d
        for c in d.ctors:
            self.local[c] = f"{ln}.{c}"
        for fl in d.fields:
            self.local[fl] = f"{ln}.{camel(fl)}"
        if d.record_ctor:
            self.local[d.record_ctor] = f"{ln}.mk"
        return ln

    def resolve(self, n: str) -> str:
        """A Rocq identifier occurrence -> Lean text."""
        if n in self.local:
            return self.local[n]
        # module-qualified Rocq names: WeakLitmus.img0
        qual = None
        if "." in n:
            q, _, rest = n.partition(".")
            if q in self.rocq or q in self.dag:
                qual, n = q, rest
        decls = self.by_name.get(n, [])
        if n in IDENT_MAP and not qual and all(d.kind == "Notation" for d in decls):
            return IDENT_MAP[n]
        if qual:
            decls = [d for d in decls if d.file == qual] or decls
        for d in decls:
            ln = self.resolve_decl(d)
            if ln:
                self.note_use(ln)
                return ln
        # fields / constructors of ported records & inductives
        for f in ([qual] if qual else self.deps_order):
            for d in self.rocq.get(f, []):
                if n in d.fields or n in d.ctors or n == d.record_ctor:
                    tl = self.resolve_decl(d)
                    if not tl:
                        continue
                    full = self.lean_exists(tl)
                    if n == d.record_ctor:
                        cs = self.lean.ctors.get(full, [])
                        mk = cs[0] if cs else "mk"
                        self.note_use(tl)
                        return f"{tl}.{mk}"
                    if n in d.ctors:
                        if self.lean_exists(f"{tl}.{n}"):
                            self.note_use(tl)
                            return f"{tl}.{n}"
                        for c in (camel(n), upper(n)):
                            if self.lean_exists(f"{tl}.{c}"):
                                return f"{tl}.{c}"
                    if n in d.fields:
                        flds = self.lean.fields.get(full, [])
                        for c in (camel(n), n):
                            if c in flds:
                                self.note_use(tl)
                                return f"{tl}.{c}"
                        low = n.replace("_", "").lower()
                        for c in flds:
                            if c.lower() == low:
                                return f"{tl}.{c}"
        # notation aliases of the deps (agent := nat ...)
        for d in decls:
            if d.kind == "Notation" and d.alias:
                return None if False else ("(" + self.alias(d) + ")")
        if n in IDENT_MAP:
            return IDENT_MAP[n]
        # shims / library names: kept stdpp spelling, or camelCase
        for c in (n, camel(n), re.sub(r"_L$", "", n), camel(re.sub(r"_L$", "", n))):
            if self.lean_exists(c):
                self.note_use(c)
                return c
        # names from the dep files that are not ported (or not found)
        if decls:
            if not self.quiet:
                self.unresolved.add(n)
            return self.lean_for_local(decls[0]) if decls[0].kind != "Notation" else n
        if "_" in n and not n.startswith("_"):
            if not self.quiet:
                self.unresolved.add(n)
            return camel(n)
        return n

    def alias(self, d: RocqDecl) -> str:
        if d.name in self.alias_cache:
            return self.alias_cache[d.name]
        self.alias_cache[d.name] = d.name
        txt = TermX(self).term(d.alias)
        self.alias_cache[d.name] = txt
        return txt


# ---------------------------------------------------------------------------
# Term translation
# ---------------------------------------------------------------------------

INFIX = {"⊑": "≤", "⊒": "⊒", "<->": "↔", "->": "→", "/\\": "∧", "\\/": "∨", "<>": "≠", "<=": "≤", ">=": "≥",
         "~": "¬", "∖": "\\", "=?": "==", "|-": "⊢", "≡ₚ": "~", "⊆+": "<+~"}
KEYWORDS = {"forall": "∀", "exists": "∃", "fun": "fun", "if": "if", "then": "then",
            "else": "else", "let": "let", "in": "in", "with": "with", "as": "as",
            "return": "return", "mod": "%", "div": "/", "Type": "Type", "Prop": "Prop"}
BINARY_STOP = {"=", "≠", "<", ">", "≤", "≥", "+", "-", "*", "/", "^", "++", "::", "∧", "∨",
               "→", "↔", "->", "<->", "∈", "∉", "⊆", "⊂", "∪", "∩", "∖", ",", ";", ":", ":=",
               "=>", "|", "≡", "&&", "||", "<=", ">=", "<>", "/\\", "\\/", "!!", "!!!",
               "<$>", "∘", "=?", "<=?", "<?", "##", "%", "~", "¬", "∀", "∃", "λ", "@", "'"}


class TermX:
    def __init__(self, names: NameTable, bound: Optional[set] = None):
        self.N = names
        self.notes: list[str] = []
        self.bound = set(bound or [])
        self.map_vars: set = set()

    def term(self, s: str) -> str:
        return self.emit(build_tree(tokenize(s)))

    # an "atom" for application purposes
    def is_atom(self, x) -> bool:
        if isinstance(x, Group):
            return x.open in ("(", "[", "{[", "match", "{", "ltac")
        if x.kind in ("num", "str"):
            return True
        if x.kind == "id":
            return x.val not in ("fun", "forall", "exists", "if", "then", "else", "let", "in",
                                 "with", "as", "return", "mod", "div", "end", "is")
        if x.kind == "op" and x.val in ("∅", "⊤", "⊥", "_", ".1", ".2", ".*1", ".*2", "?"):
            return True
        return False

    def emit(self, items) -> str:
        items = merge_ltac(items)
        out: list[str] = []
        i = 0
        n = len(items)
        while i < n:
            x = items[i]
            # binders: λ / fun / ∀ / ∃
            if is_tok(x, "op", "λ") or is_tok(x, "id", "fun"):
                sep = "," if x.val == "λ" else "=>"
                j = i + 1
                while j < n and not (is_tok(items[j], "op", sep) or (sep == "," and is_tok(items[j], "op", "=>"))):
                    j += 1
                out.append("fun " + self.binders(items[i + 1:j]) + " => " + self.emit(items[j + 1:]))
                return self.join(out)
            if is_tok(x, "op", "∀") or is_tok(x, "op", "∃") or is_tok(x, "id", "forall") or \
                    is_tok(x, "id", "exists"):
                q = "∀" if x.val in ("∀", "forall") else "∃"
                j = i + 1
                if j < n and is_tok(items[j], "op", "!"):
                    q += "!"
                    j += 1
                k = j
                while k < n and not is_tok(items[k], "op", ","):
                    k += 1
                out.append(q + " " + self.binders(items[j:k]) + ", " + self.emit(items[k + 1:]))
                return self.join(out)
            if is_tok(x, "id", "let"):
                # let x := e in b  /  let '(a, b) := e in b
                depth, k = 0, i + 1
                while k < n:
                    if is_tok(items[k], "id", "let"):
                        depth += 1
                    if is_tok(items[k], "id", "in"):
                        if depth == 0:
                            break
                        depth -= 1
                    k += 1
                inner = items[i + 1:k]
                parts = split_top(inner, ":=")
                lhs = parts[0]
                if lhs and is_tok(lhs[0], "op", "'"):
                    lhs = lhs[1:]
                rhs = ":=".join(self.emit(p) for p in parts[1:]) if len(parts) > 1 else ""
                out.append("let " + self.emit(lhs) + " := " + rhs + "; " + self.emit(items[k + 1:]))
                return self.join(out)
            if is_tok(x, "id", "if"):
                out.append(self.emit_if(items[i:]))
                return self.join(out)

            # application chunk
            if self.is_atom(x) or is_tok(x, "op", "@"):
                j = i
                while j < n and (self.is_atom(items[j]) or is_tok(items[j], "op", "@")):
                    j += 1
                app = items[i:j]
                # infix !! / !!! / <$> bind tighter than everything here
                text = self.emit_app(app)
                while j < n and is_tok(items[j], "op") and items[j].val in ("!!", "!!!", "<$>", ".*1", ".*2"):
                    op = items[j].val
                    if op in (".*1", ".*2"):
                        text = f"({text}).map Prod.{'fst' if op == '.*1' else 'snd'}"
                        j += 1
                        continue
                    k = j + 1
                    # right operand: one application chunk (prefix ops allowed)
                    while k < n and (self.is_atom(items[k]) or is_tok(items[k], "op", "@")):
                        k += 1
                    rhs = self.emit_app(items[j + 1:k])
                    if op == "!!" and self.is_map_operand(app):
                        text = f"get? {self.paren_unless_atom(text)} {self.paren_unless_atom(rhs)}"
                    elif op == "!!":
                        text = f"{self.paren_unless_atom(text)}[{rhs}]?"
                    elif op == "!!!":
                        text = f"{self.paren_unless_atom(text)}[{rhs}]!"
                    else:
                        rapp = items[j + 1:k]
                        if self.is_option_operand(rapp):
                            text = f"(Option.map {self.paren_unless_atom(text)} {self.paren_unless_atom(rhs)})"
                        else:
                            text = f"(List.map {self.paren_unless_atom(text)} {self.paren_unless_atom(rhs)})"
                    j = k
                out.append(text)
                i = j
                continue
            if isinstance(x, Group) and x.open == "<[":
                # <[ i := x ]> m
                j = i + 1
                k = j
                while k < n and self.is_atom(items[k]):
                    k += 1
                parts = split_top(x.items, ":=")
                idx = self.emit(parts[0])
                val = self.emit(parts[1]) if len(parts) > 1 else "?"
                tgt = self.emit_app(items[j:k]) if k > j else "?"
                if self.is_map_operand(items[j:k]):
                    out.append(f"(insert {self.paren_unless_atom(tgt)} {self.paren_unless_atom(idx)} "
                               f"{self.paren_unless_atom(val)})")
                else:
                    out.append(f"(List.set {self.paren_unless_atom(tgt)} {self.paren_unless_atom(idx)} "
                               f"{self.paren_unless_atom(val)})")
                    self.notes.append("`<[i:=x]>` read as a LIST update (List.set); a map wants `insert m i x`")
                i = k
                continue
            if isinstance(x, Tok) and x.kind == "op":
                v = INFIX.get(x.val, x.val)
                if x.val == "'":
                    i += 1
                    continue
                if x.val == "*" and out and re.match(r"^\(?[A-Z][\w.]*", out[-1]) and i + 1 < n and \
                        (is_tok(items[i + 1], "id") and re.match(r"^\(?[A-Z]", self.emit_atom(items[i + 1]))
                         or isinstance(items[i + 1], Group)):
                    v = "×"
                out.append(v)
                i += 1
                continue
            if isinstance(x, Tok) and x.kind == "id" and x.val in KEYWORDS:
                out.append(KEYWORDS[x.val])
                i += 1
                continue
            out.append(self.emit_atom(x))
            i += 1
        return self.join(out)

    def join(self, parts):
        s = " ".join(p for p in parts if p != "")
        s = re.sub(r"\s+,", ",", s)
        s = re.sub(r"\(\s+", "(", s)
        s = re.sub(r"\s+\)", ")", s)
        s = re.sub(r"\[\s+", "[", s)
        s = re.sub(r"\s+\]", "]", s)
        s = re.sub(r"¬\s+", "¬ ", s)
        return s

    def paren_unless_atom(self, s: str) -> str:
        s = s.strip()
        if re.match(r"^[\w.'@?!₀-₉]+$", s) or self.balanced_wrapped(s):
            return s
        return f"({s})"

    @staticmethod
    def balanced_wrapped(s):
        if not s or s[0] not in "([⟨{" :
            return False
        close = {"(": ")", "[": "]", "⟨": "⟩", "{": "}"}[s[0]]
        if s[-1] != close and not re.search(r"[\])][?!]$", s):
            return False
        depth = 0
        for i, c in enumerate(s):
            if c in "([⟨{":
                depth += 1
            elif c in ")]⟩}":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    rest = s[i + 1:]
                    return rest in ("?", "!") or bool(re.match(r"^(\.[\w]+)+$", rest)) or \
                        bool(re.match(r"^\[[^\]]*\][?!]$", rest))
        return True

    def is_option_operand(self, app) -> bool:
        if len(app) == 1 and isinstance(app[0], Group) and app[0].open == "(":
            app = app[0].items
        if not app:
            return False
        h = app[0]
        if is_tok(h, "id"):
            if h.val in ("Some", "None"):
                return True
            for d in self.N.by_name.get(h.val, []):
                if d.ret_option:
                    return True
        if len(app) >= 2 and any(is_tok(z, "op", "!!") for z in app):
            return True
        return False

    def is_map_operand(self, app) -> bool:
        if len(app) != 1:
            return False
        y = app[0]
        if isinstance(y, Group) and y.open == "{[" and any(is_tok(z, "op", ":=") for z in y.items):
            return True
        if isinstance(y, Group) and y.open == "<[":
            return False
        if is_tok(y, "op", "∅"):
            return True
        if is_tok(y, "id"):
            if y.val in self.map_vars or y.val in self.N.map_names:
                return True
            return any(d.is_map for d in self.N.by_name.get(y.val, []))
        return False

    def emit_if(self, items) -> str:
        # if c then a else b
        k1 = next((k for k, x in enumerate(items) if is_tok(x, "id", "then")), None)
        if k1 is None:
            return "if " + self.emit(items[1:])
        depth, k2 = 0, None
        for k in range(k1 + 1, len(items)):
            if is_tok(items[k], "id", "if"):
                depth += 1
            if is_tok(items[k], "id", "else"):
                if depth == 0:
                    k2 = k
                    break
                depth -= 1
        cond = items[1:k1]
        if k2 is None:
            return f"if {self.emit(cond)} then {self.emit(items[k1 + 1:])}"
        return f"if {self.emit(cond)} then {self.emit(items[k1 + 1:k2])} else {self.emit(items[k2 + 1:])}"

    def emit_app(self, app) -> str:
        if not app:
            return ""
        at = False
        if is_tok(app[0], "op", "@"):
            at = True
            app = app[1:]
        if not app:
            return "@"
        head = app[0]
        args = app[1:]
        if isinstance(head, Tok) and head.kind == "id" and not at and head.val not in self.N.local \
                and head.val in TEMPLATES and head.val not in self.bound:
            ar, tpl = TEMPLATES[head.val]
            if head.val in self.N.by_name and self.N.resolve(head.val) != IDENT_MAP.get(head.val, head.val):
                pass
            elif len(args) >= ar:
                if head.val in ("Forall", "Exists") and isinstance(args[0], Group) and args[0].items and \
                        (is_tok(args[0].items[0], "op", "λ") or is_tok(args[0].items[0], "id", "fun")):
                    lam = args[0].items
                    k = next((k for k, y in enumerate(lam) if is_tok(y, "op", ",") or is_tok(y, "op", "=>")), None)
                    if k == 2 and is_tok(lam[1], "id"):
                        v = lam[1].val
                        inner = TermX(self.N, self.bound | {v})
                        body = inner.emit(lam[k + 1:])
                        q = "∀" if head.val == "Forall" else "∃"
                        core = f"({q} {v} ∈ {self.paren_unless_atom(self.emit_atom(args[1]))}, {body})"
                        rest = [self.emit_atom(x) for x in args[2:]]
                        return "(" + core + " " + " ".join(rest) + ")" if rest else core
                a = [self.paren_unless_atom(self.emit_atom(x)) for x in args[:ar]]
                core = tpl.format(*a)
                rest = [self.emit_atom(x) for x in args[ar:]]
                if rest:
                    return "(" + core + " " + " ".join(rest) + ")"
                return core
        parts = [("@" if at else "") + self.emit_atom(head)] + [self.emit_atom(x) for x in args]
        # `.1` / `.2` glue
        out: list[str] = []
        for p in parts:
            if p in (".1", ".2") and out:
                out[-1] = self.paren_unless_atom(out[-1]) + p
            else:
                out.append(p)
        return " ".join(out)

    def emit_atom(self, x) -> str:
        if isinstance(x, Group):
            if x.open == "(":
                inner = self.emit(x.items)
                return f"({inner})"
            if x.open == "[":
                parts = split_top(x.items, ";")
                if len(parts) == 1 and not parts[0]:
                    return "[]"
                return "[" + ", ".join(self.emit(p) for p in parts) + "]"
            if x.open == "{[":
                if any(is_tok(y, "op", ":=") for y in x.items):
                    self.N.uses_partialmap = True
                    return "{[" + self.emit(x.items) + "]}"
                parts = split_top(x.items, ";")
                return "{" + ", ".join(self.emit(p) for p in parts) + "}"
            if x.open == "match":
                return "(" + self.emit_match(x.items) + ")"
            if x.open == "ltac":
                try:
                    tt = TacX(self.N, self.bound).texpr(x.items)
                except Exception:
                    tt = "sorry"
                    self.notes.append("an `ltac:(...)` argument became `sorry`")
                return f"(by {tt})"
            if x.open == "{":
                return "{" + self.emit(x.items) + "}"
            return self.emit(x.items)
        if x.kind == "id":
            if x.val in self.bound:
                return x.val
            if x.val in KEYWORDS:
                return KEYWORDS[x.val]
            return self.N.resolve(x.val)
        if x.kind == "op":
            return INFIX.get(x.val, x.val)
        return x.val

    def emit_match(self, items) -> str:
        # match e (as x) (return T) with | p => b | ... (end stripped)
        k = next((k for k, y in enumerate(items) if is_tok(y, "id", "with")), None)
        if k is None:
            return "match " + self.emit(items)
        scrut = items[:k]
        # drop `as x return T`
        cut = next((j for j, y in enumerate(scrut) if is_tok(y, "id", "return") or is_tok(y, "id", "as")), None)
        if cut is not None:
            scrut = scrut[:cut]
        alts = split_top(items[k + 1:], "|")
        if alts and not alts[0]:
            alts = alts[1:]
        out = []
        for a in alts:
            parts = split_top(a, "=>")
            pat = parts[0]
            body = []
            for p in parts[1:]:
                body = body + ([Tok("op", "=>", True)] if body else []) + p
            pv = self.pattern(pat)
            bt = TermX(self.N, self.bound | self.pat_vars(pat))
            out.append(f"| {pv} => {bt.emit(body)}")
            self.notes.extend(bt.notes)
        return "match " + self.emit(scrut) + " with " + " ".join(out)

    def pat_vars(self, pat) -> set:
        vs = set()
        for y in pat:
            if isinstance(y, Group):
                vs |= self.pat_vars(y.items)
            elif y.kind == "id" and y.val[0].islower() and y.val not in self.N.local and \
                    not self.N.by_name.get(y.val):
                vs.add(y.val)
        return vs

    def pattern(self, pat) -> str:
        bt = TermX(self.N, self.pat_vars(pat))
        s = bt.emit(pat)
        return s

    def binders(self, items) -> str:
        """λ/∀/∃ binders: `x y`, `(x : T)`, `'(a, b)`, `x : T`."""
        out = []
        # bare `x y : T` form
        if any(is_tok(y, "op", ":") for y in items) and not any(isinstance(y, Group) for y in items):
            k = next(k for k, y in enumerate(items) if is_tok(y, "op", ":"))
            names = [y.val for y in items[:k] if isinstance(y, Tok)]
            self.bound.update(names)
            return " ".join(names) + " : " + self.emit(items[k + 1:])
        i = 0
        while i < len(items):
            y = items[i]
            if is_tok(y, "op", "'") and i + 1 < len(items) and isinstance(items[i + 1], Group):
                g = items[i + 1]
                vs = self.pat_vars(g.items)
                self.bound |= vs
                out.append("⟨" + ", ".join(self.emit(p) for p in split_top(g.items, ",")) + "⟩")
                i += 2
                continue
            if isinstance(y, Group) and y.open in ("(", "{", "["):
                parts = split_top(y.items, ":")
                if len(parts) >= 2:
                    names = [z.val for z in parts[0] if isinstance(z, Tok)]
                    self.bound.update(names)
                    ty = ":".join(self.emit(p) for p in parts[1:])
                    o, c = ("(", ")") if y.open == "(" else ("{", "}")
                    out.append(f"{o}{' '.join(names)} : {ty}{c}")
                else:
                    names = [z.val for z in y.items if isinstance(z, Tok)]
                    self.bound.update(names)
                    out.append(" ".join(names))
                i += 1
                continue
            if isinstance(y, Tok) and y.kind == "id":
                self.bound.add(y.val)
                out.append(y.val)
            elif isinstance(y, Tok) and y.val == "_":
                out.append("_")
            i += 1
        return " ".join(out)


# ---------------------------------------------------------------------------
# Tactic translation
# ---------------------------------------------------------------------------

SPLIT_AND = "(apply And.intro <;> repeat' (with_reducible apply And.intro))"
SIMPL_LEMMAS = ("List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil, List.length_cons, "
                "List.length_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append, "
                "Option.some.injEq, Prod.mk.injEq")
CLOSE = "(first | done | rfl | assumption | trivial | contradiction | omega | (simp_all; done))"
AUTO = "(first | done | assumption | rfl | omega | (simp_all; done) | grind)"
SIMPEQ = ("(try simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq] at *)"
          " <;> (try subst_vars)")


class Untranslatable(Exception):
    pass


class TacX:
    def __init__(self, names: NameTable, bound: set):
        self.N = names
        self.bound = set(bound)
        self.pending_next: list[list[str]] = []
        self.pending_cont: list[str] = []
        self.notes: list[str] = []

    def term(self, toks_or_str) -> str:
        tx = TermX(self.N, self.bound)
        if isinstance(toks_or_str, str):
            r = tx.term(toks_or_str)
        else:
            r = tx.emit(build_tree(toks_or_str))
        self.notes.extend(tx.notes)
        return r

    # ---- intro patterns
    def ipat(self, items) -> str:
        """A sequence of Rocq intro patterns (tree items) -> rcases patterns list."""
        out = []
        for y in items:
            p = self.ipat1(y)
            if p is not None:
                out.append(p)
        return out

    def ipat1(self, y) -> Optional[str]:
        if isinstance(y, Tok):
            if y.kind == "id":
                self.bound.add(y.val)
                return y.val
            if y.val in ("?", "_"):
                return "_"
            if y.val in ("->", "<-"):
                return "rfl"
            if y.val in ("/=", "//", "//=", "/", "=", "!", "*", "**"):
                if y.val in ("*", "**"):
                    raise Untranslatable("intro *")
                return None
            if y.val == "%":
                raise Untranslatable("view pattern")
            raise Untranslatable(f"pattern {y.val}")
        if isinstance(y, Group):
            if y.open == "(":
                parts = split_top(y.items, "&")
                if len(parts) == 1:
                    parts = split_top(y.items, ",")
                ps = []
                for p in parts:
                    q = self.ipat(p)
                    ps.append(q[0] if len(q) == 1 else ("⟨" + ", ".join(q) + "⟩" if q else "_"))
                return ps[0] if len(ps) == 1 else "⟨" + ", ".join(ps) + "⟩"
            if y.open == "[":
                alts = split_top(y.items, "|")
                ps = []
                for a in alts:
                    q = self.ipat(a)
                    if len(q) == 0:
                        ps.append("_" if len(alts) > 1 else "⟨⟩")
                    elif len(q) == 1:
                        ps.append(q[0])
                    else:
                        ps.append("⟨" + ", ".join(q) + "⟩")
                if len(alts) == 1:
                    return ps[0] if ps[0] != "_" else "⟨⟩"
                return "(" + " | ".join(ps) + ")"
        raise Untranslatable("pattern")

    def branch_names(self, g) -> list[list[str]]:
        """`[|x l IH]` -> [[], [x, l, IH]] (for induction)."""
        if not (isinstance(g, Group) and g.open == "["):
            raise Untranslatable("induction pattern")
        res = []
        for a in split_top(g.items, "|"):
            names = []
            for y in a:
                if is_tok(y, "id"):
                    names.append(y.val)
                    self.bound.add(y.val)
                elif is_tok(y, "op", "?") or is_tok(y, "op", "_"):
                    names.append("_")
                else:
                    raise Untranslatable("induction pattern")
            res.append(names)
        return res

    # ---- tactic expressions
    def tactic(self, text: str) -> str:
        toks = tokenize(text)
        items = build_tree(toks)
        return self.texpr(items)

    def texpr(self, items) -> str:
        # `t1; t2; [a|b]` and `t1 || t2`
        parts = split_top(items, ";")
        r = self.induction_chain(parts)
        if r is not None:
            return r
        if len(parts) > 1:
            res = self.texpr_noseq(parts[0])
            for p in parts[1:]:
                if len(p) == 1 and isinstance(p[0], Group) and p[0].open == "[" and \
                        any(is_tok(z, "op", "|") for z in p[0].items) or \
                        (len(p) == 1 and isinstance(p[0], Group) and p[0].open == "[" and not p[0].items):
                    alts = split_top(p[0].items, "|")
                    if alts and alts[0] and is_tok(alts[0][-1], "op", ".."):
                        # `t; [tac..| a | b |]`: explicit tails by negative index, then `tac` everywhere
                        steps = [self.wrap(res)]
                        k = len(alts) - 1
                        for j in range(k, 0, -1):
                            if alts[j]:
                                steps.append(f"(on_goal {j - k - 1} => {self.texpr(alts[j])})")
                        head = alts[0][:-1]
                        ht = self.texpr(head) if head else "skip"
                        if ht == CLOSE:
                            ht = "(first | assumption | rfl)"
                        steps.append(f"(all_goals try {self.wrap(ht)})")
                        self.notes.append("`[tac..| ...]` became `all_goals try tac` (it may also hit the tail goals)")
                        res = "(" + "; ".join(steps) + ")"
                        continue
                    if p is parts[-1] and not any(len(a) == 1 and is_tok(a[0], "op", "..") for a in alts) \
                            and not any(a and is_tok(a[-1], "op", "..") for a in alts):
                        # the LAST combinator of the chain: per-goal blocks, last goal first, so a
                        # Lean `apply` producing extra (mvar) goals does not shift the indices
                        steps = [self.wrap(res)]
                        for k in range(len(alts), 0, -1):
                            a = alts[k - 1]
                            if a:
                                steps.append(f"(on_goal {k} => {self.texpr(a)})")
                        res = "(" + "; ".join(steps) + ")"
                        continue
                    tacs = [self.texpr(a) if a else "skip" for a in alts]
                    res = f"{self.wrap(res)} <;> [{'; '.join(tacs)}]"
                elif len(p) == 1 and isinstance(p[0], Group) and p[0].open == "[":
                    res = f"{self.wrap(res)} <;> [{self.texpr(p[0].items) if p[0].items else 'skip'}]"
                else:
                    res = f"{self.wrap(res)} <;> {self.wrap(self.texpr_noseq(p))}"
            return res
        return self.texpr_noseq(items)

    def induction_chain(self, parts):
        """`induction x as [p1|..|pn]; T; [B1|..|Bn]` -> `induction x` + one `next` per branch."""
        if len(parts) < 2 or not parts[0] or not is_tok(parts[0][0], "id", "induction"):
            return None
        last = parts[-1]
        if not (len(last) == 1 and isinstance(last[0], Group) and last[0].open == "["):
            return None
        alts = split_top(last[0].items, "|")
        saved = list(self.pending_next)
        head = self.atomic(parts[0])
        branches = self.pending_next
        self.pending_next = saved
        if not branches or len(branches) != len(alts):
            return None
        mid = parts[1:-1]
        T = " <;> ".join(self.wrap(self.texpr_noseq(p)) for p in mid) if mid else ""
        out = [head]
        for k, (nm, a) in enumerate(zip(branches, alts)):
            names = " ".join(nm)
            if a:
                body = self.texpr(a)
                body = f"({T}) <;> {self.wrap(body)}" if T else body
                out.append(f"next {names} => {body}".replace("next  =>", "next =>"))
            elif k == len(alts) - 1:
                if any(x != "_" for x in nm):
                    out.append(f"rename_i {names}")
                if T:
                    out.append(T)
            else:
                return None
        return "\n".join(out)

    @staticmethod
    def wrap(s: str) -> str:
        s = s.strip()
        if re.match(r"^[\w_']+$", s) or (s.startswith("(") and TermX.balanced_wrapped(s)):
            return s
        return f"({s})"

    def texpr_noseq(self, items) -> str:
        parts = split_top(items, "||")
        if len(parts) > 1:
            return "first | " + " | ".join(self.wrap(self.texpr_noseq(p)) for p in parts)
        if not items:
            return "skip"
        return self.atomic(items)

    def rest_text(self, items) -> str:
        return " ".join(tok_text(x) for x in items)

    def atomic(self, items) -> str:
        h = items[0]
        if isinstance(h, Group) and h.open == "(":
            return self.wrap(self.texpr(h.items))
        if not isinstance(h, Tok):
            raise Untranslatable("tactic")
        w = h.val
        args = items[1:]

        def term_of(xs):
            tx = TermX(self.N, self.bound)
            r = tx.emit(xs)
            self.notes.extend(tx.notes)
            return r

        # ssreflect `by tac`
        if w == "by":
            if not args:
                return CLOSE
            if len(args) == 1 and isinstance(args[0], Group) and args[0].open == "[" and not args[0].items:
                return CLOSE
            t = self.texpr(args)
            if t in ("decide", "rfl", "omega", "set_solver", "exact trivial"):
                return t
            return f"{self.wrap(t)} <;> {CLOSE}"
        if w in ("done", "easy", "trivial", "now_done"):
            return CLOSE
        if w in ("lia", "omega", "nia", "lra", "Lia.lia"):
            return "omega"
        if w in ("set_solver", "set_solver_L"):
            extra = [x for x in args if is_tok(x, "id")]
            return "set_solver"
        if w in ("set_unfold",):
            return "set_solver_unfold"
        if w in ("naive_solver", "auto", "eauto", "tauto", "intuition", "firstorder", "itauto",
                 "congruence", "lia_done", "solve_proper"):
            if "using" in [tok_text(a) for a in args]:
                k = [tok_text(a) for a in args].index("using")
                lemmas = [term_of([a]) for a in args[k + 1:] if not is_tok(a, "op", ",")]
                return f"(first | done | assumption | omega | (simp_all [{', '.join(lemmas)}]; done) | grind [{', '.join(lemmas)}])"
            return AUTO
        if w in ("reflexivity", "f_equal_refl"):
            return "rfl"
        if w == "symmetry":
            if args:
                raise Untranslatable("symmetry in")
            return "symm"
        if w in ("exfalso", "left", "right", "contradiction", "assumption", "constructor"):
            if args:
                raise Untranslatable(w + " args")
            return w
        if w == "eassumption":
            return "assumption"
        if w == "econstructor":
            return "constructor"
        if w == "discriminate":
            return "contradiction"
        if w == "idtac":
            return "skip"
        if w in ("split",):
            if args:
                raise Untranslatable("split args")
            return "(first | constructor | apply And.intro)"
        if w in ("split_and", "split_and!", "split_and?") or (w == "split_and" and args and tok_text(args[0]) == "!"):
            return SPLIT_AND
        if w == "repeat" and args and tok_text(args[0]) == "split":
            return SPLIT_AND
        if w in ("subst",):
            if not args:
                return "subst_vars"
            return "subst " + " ".join(tok_text(a) for a in args)
        if w in ("simplify_eq", "simplify_option_eq", "simpl_eq", "injections", "inv_eq"):
            return SIMPEQ
        if w in ("simpl", "cbn", "cbv", "hnf", "simpl_list"):
            if args and is_tok(args[0], "id", "in"):
                loc = self.location(args[1:])
                return f"try simp only [{SIMPL_LEMMAS}] {loc}"
            if args:
                raise Untranslatable("simpl args")
            return f"try simp only [{SIMPL_LEMMAS}]"
        if w in ("vm_compute", "compute", "native_compute", "lazy"):
            if args:
                raise Untranslatable("compute in")
            return "(first | decide | rfl | simp)"
        if w == "decide":
            return "decide"
        if w in ("bv_simplify", "bitblast", "bv_solve"):
            return "bv_decide"
        if w in ("intros", "intro"):
            if not args:
                return "intros" if w == "intros" else "intro"
            pats = self.ipat(args)
            if not pats:
                return "intros"
            if all(re.match(r"^[\w']+$", p) and p != "_" for p in pats):
                return "intro " + " ".join(pats)
            return "rintro " + " ".join(pats)
        if w == "move":
            # move=> pats / move: H
            if args and tok_text(args[0]) == "=" and len(args) > 1 and tok_text(args[1]) == ">":
                pats = self.ipat(args[2:])
                if not pats:
                    return "try dsimp only"
                return "rintro " + " ".join(pats)
            if args and tok_text(args[0]) == "=>":
                pats = self.ipat(args[1:])
                return "rintro " + " ".join(pats) if pats else "try dsimp only"
            if args and tok_text(args[0]) == ":":
                hs = [tok_text(a) for a in args[1:]]
                if all(re.match(r"^[\w']+$", x) for x in hs):
                    return "revert " + " ".join(hs)
            raise Untranslatable("move")
        if w in ("destruct", "case", "inversion", "inversion_clear", "inv", "elim", "edestruct",
                 "induction"):
            return self.destruct(w, args)
        if w in ("rewrite", "erewrite", "rewrite_strat", "setoid_rewrite", "rewrite!"):
            if w == "rewrite_strat":
                raise Untranslatable("rewrite_strat")
            return self.rewrite(args, setoid=(w == "setoid_rewrite"))
        if w == "unfold":
            if any(is_tok(a, "id", "in") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "in"))
                names = [self.N.resolve(tok_text(a)) for a in args[:k] if is_tok(a, "id")]
                return f"unfold {' '.join(names)} {self.location(args[k + 1:])}"
            names = [self.N.resolve(tok_text(a)) for a in args if is_tok(a, "id")]
            return "unfold " + " ".join(names)
        if w in ("apply", "eapply", "simple"):
            if w == "simple":
                args = args[1:]
            if args and is_tok(args[0], "op", ":"):
                args = args[1:]
            if any(is_tok(a, "id", "in") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "in"))
                lem = term_of(args[:k])
                rest = args[k + 1:]
                hs = rest
                pat = None
                if any(is_tok(a, "id", "as") for a in rest):
                    j = next(j for j, a in enumerate(rest) if is_tok(a, "id", "as"))
                    hs, pat = rest[:j], rest[j + 1:]
                if len(hs) != 1 or not is_tok(hs[0], "id"):
                    raise Untranslatable("apply in")
                H = hs[0].val
                L = self.wrap(lem)
                alts = " | ".join(f"replace {H} := {L} {'_ ' * u}{H}" for u in range(0, 5))
                alts += " | " + " | ".join(f"replace {H} := ({L} {'_ ' * u}).{d} {H}".replace(" ).", ").")
                                           for u in range(0, 4) for d in ("mp", "mpr"))
                alts = alts.replace(f"({L}).", f"(({L})).") if re.match(r"^[\w.']+$", L) else alts
                r = f"first | {alts}"
                if pat:
                    p = self.ipat(pat)
                    r = f"({r}); rcases {H} with {p[0] if len(p) == 1 else '⟨' + ', '.join(p) + '⟩'}"
                return r
            ts = split_top(args, ",")

            def ap(t):
                tm = term_of(t)
                if re.match(r"^\(?[A-Z]", tm) or "." in tm.split(" ")[0] and tm.split(".")[0][:1].isupper():
                    return "eapply " + tm      # a constructor / qualified name: no iff
                return f"first | eapply {tm} | eapply ({tm}).mpr | eapply ({tm}).mp"
            if len(ts) == 1:
                return ap(ts[0])
            return "(" + "; ".join(f"({ap(t)})" for t in ts) + ")"
        if w in ("exact", "eexact", "refine"):
            if args and is_tok(args[0], "op", ":"):
                args = args[1:]
            if w == "refine":
                raise Untranslatable("refine")
            return "exact " + term_of(args)
        if w in ("exists", "eexists", "∃"):
            if w == "eexists" or not args:
                return "(first | apply Exists.intro | (rw [Option.isSome_iff_exists]; apply Exists.intro))"
            ts = split_top(args, ",")
            w0 = ", ".join(term_of(t) for t in ts)
            return f"first | refine ⟨{w0}, ?_⟩ | (rw [Option.isSome_iff_exists]; refine ⟨{w0}, ?_⟩)"
        if w in ("pose", "epose"):
            if args and is_tok(args[0], "id", "proof"):
                rest = args[1:]
                if any(is_tok(a, "id", "as") for a in rest):
                    k = next(k for k, a in enumerate(rest) if is_tok(a, "id", "as"))
                    p = self.ipat(rest[k + 1:])
                    tm = term_of(rest[:k])
                    if len(p) == 1 and re.match(r"^[\w']+$", p[0]):
                        return f"have {p[0]} := {tm}"
                    if re.match(r"^[\w']+$", tm):
                        tm = f"id {tm}"     # Rocq `pose proof` keeps the hypothesis
                    return f"obtain {p[0] if len(p) == 1 else '⟨' + ', '.join(p) + '⟩'} := {tm}"
                return f"have := {term_of(rest)}"
            raise Untranslatable("pose")
        if w == "have":
            if any(is_tok(a, "id", "by") for a in args) or (args and is_tok(args[0], "id")):
                # have H : P by tac.   (ssreflect)
                by = None
                if any(is_tok(a, "id", "by") for a in args):
                    k = next(k for k, a in enumerate(args) if is_tok(a, "id", "by"))
                    by, args = args[k + 1:], args[:k]
                parts = split_top(args, ":")
                if len(parts) >= 2 and len(parts[0]) == 1 and is_tok(parts[0][0], "id"):
                    nm = parts[0][0].val
                    prop = term_of([y for p in parts[1:] for y in p])
                    self.bound.add(nm)
                    if by is not None:
                        return f"have {nm} : {prop} := by {self.texpr(by)}"
                    return f"have {nm} : {prop} := ?_; pick_goal 2"
                if len(parts) == 1 and len(parts[0]) >= 3 and is_tok(parts[0][1], "op", ":="):
                    nm = parts[0][0].val
                    self.bound.add(nm)
                    return f"have {nm} := {term_of(parts[0][2:])}"
            raise Untranslatable("have")
        if w in ("assert", "enough"):
            return self.assert_(args, enough=(w == "enough"))
        if w == "specialize":
            if len(args) == 1 and isinstance(args[0], Group) and args[0].open == "(":
                inner = args[0].items
                return "specialize " + term_of(inner)
            return "specialize " + term_of(args)
        if w in ("revert", "clear", "generalize"):
            if w == "generalize" and args and is_tok(args[0], "id", "dependent"):
                return "revert " + " ".join(tok_text(a) for a in args[1:])
            if w == "generalize":
                raise Untranslatable("generalize")
            if any(not is_tok(a, "id") for a in args):
                raise Untranslatable(w)
            return w + " " + " ".join(a.val for a in args)
        if w == "injection":
            if any(is_tok(a, "id", "as") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "as"))
                return f"injection {term_of(args[:k])} with {' '.join(tok_text(a) for a in args[k + 1:])}"
            return f"injection {term_of(args)}"
        if w == "change":
            if any(is_tok(a, "id", "in") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "in"))
                return f"change {term_of(args[:k])} {self.location(args[k + 1:])}"
            return "change " + term_of(args)
        if w == "f_equal":
            return "congr 1"
        if w == "try":
            return "try " + self.wrap(self.texpr(args))
        if w == "repeat":
            return "repeat " + self.wrap(self.texpr(args))
        if w == "do" and args and is_tok(args[0], "num"):
            return f"iterate {args[0].val} {self.wrap(self.texpr(args[1:]))}"
        if w in ("first", "solve"):
            if len(args) == 1 and isinstance(args[0], Group) and args[0].open == "[":
                alts = split_top(args[0].items, "|")
                if w == "solve":
                    return "first | " + " | ".join(f"({self.texpr(a)}; done)" for a in alts)
                return "first | " + " | ".join(self.wrap(self.texpr(a)) for a in alts)
            raise Untranslatable(w)
        if w == "all" and args and tok_text(args[0]) == ":":
            return "all_goals " + self.wrap(self.texpr(args[1:]))
        if w in ("by_contra", "by_contradiction"):
            return "by_contra" + ("".join(" " + tok_text(a) for a in args))
        if w == "transitivity" or w == "etransitivity" or w == "trans":
            if args:
                return "apply Trans.trans (b := " + term_of(args) + ")"
            raise Untranslatable("transitivity")
        if w == "case_decide" or w == "case_match" or w == "case_bool_decide" or \
                w == "destruct_and" or w == "destruct_and!" or w == "destruct_and?" or w == "destruct_or!":
            raise Untranslatable(w)
        if w == "exact_eq":
            raise Untranslatable(w)
        if w == "fold":
            raise Untranslatable("fold")
        if w.startswith("i") and w[1:2].isupper():
            return self.iris(w, args, term_of)
        raise Untranslatable(w)

    # ---- Iris proof mode (iris-lean's `Iris/ProofMode/Porting.lean` table)
    def ipm_pat(self, s: str) -> str:
        toks = tokenize(s)
        items = build_tree(toks)
        return " ".join(self.ipm1(y) for y in merge_ipm(items))

    def ipm1(self, y) -> str:
        if isinstance(y, Group):
            if y.open == "[":
                alts = split_top(y.items, "|")
                if len(alts) == 1:
                    return "⟨" + ", ".join(self.ipm1(z) for z in merge_ipm(alts[0])) + "⟩"
                return "(" + " | ".join(" ".join(self.ipm1(z) for z in merge_ipm(a)) or "-" for a in alts) + ")"
            if y.open == "(":
                parts = split_top(y.items, "&")
                return "⟨" + ", ".join(" ".join(self.ipm1(z) for z in merge_ipm(p)) for p in parts) + "⟩"
            if y.open == "{":
                return "{" + ", ".join(tok_text(z) for z in y.items) + "}"
            raise Untranslatable("ipm pattern")
        v = y.val
        if v == "?":
            return "_"
        if v == "_":
            return "-"
        if v in ("->", "<-"):
            return "%rfl"
        if v.startswith("-#"):
            return "∗" + v[2:]
        return v

    def iris(self, w, args, term_of) -> str:
        def strs():
            return [a.val[1:-1] for a in args if is_tok(a, "str")]
        simple = {"iSplit": "isplit", "iPureIntro": "ipureintro", "iModIntro": "imodintro",
                  "iNext": "inext", "iLeft": "ileft", "iRight": "iright", "iAssumption": "iassumption",
                  "iExFalso": "iexfalso", "iStartProof": "istart", "iEmpIntro": "iempintro"}
        if w in simple and not args:
            return simple[w]
        if w == "iIntros":
            out = []
            for a in args:
                if isinstance(a, Group) and a.open == "(":
                    out.extend("%" + tok_text(z) for z in a.items if is_tok(z, "id"))
                    self.bound.update(tok_text(z) for z in a.items if is_tok(z, "id"))
                elif is_tok(a, "str"):
                    out.append(self.ipm_pat(a.val[1:-1]))
                elif is_tok(a, "op", "%") or is_tok(a, "id"):
                    raise Untranslatable("iIntros")
            return "iintro " + " ".join(x for x in out if x)
        if w in ("iSplitL", "iSplitR"):
            ss = strs()
            nm = "isplitl" if w == "iSplitL" else "isplitr"
            return nm + (f" [{ss[0]}]" if ss else "")
        if w == "iFrame":
            ss = strs()
            if any(not is_tok(a, "str") for a in args):
                raise Untranslatable("iFrame args")
            return "iframe" + ((" " + " ".join(ss)) if ss else "")
        if w in ("iApply", "iExact", "iClear", "iRevert"):
            nm = {"iApply": "iapply", "iExact": "iexact", "iClear": "iclear", "iRevert": "irevert"}[w]
            if len(args) == 1 and is_tok(args[0], "str"):
                return f"{nm} {args[0].val[1:-1]}"
            if any(is_tok(a, "id", "with") for a in flat_toks(args)):
                raise Untranslatable("iris spec pattern")
            if w == "iApply":
                return f"iapply {term_of(args)}"
            raise Untranslatable(w)
        if w == "iExists":
            ts = split_top(args, ",")
            return "iexists " + ", ".join(term_of(t) for t in ts)
        if w in ("iDestruct", "iMod"):
            if any(is_tok(a, "id", "as") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "as"))
                src, pat = args[:k], args[k + 1:]
                if any(is_tok(a, "id", "with") for a in flat_toks(src)):
                    raise Untranslatable("iris spec pattern")
                st = src[0].val[1:-1] if len(src) == 1 and is_tok(src[0], "str") else term_of(src)
                if len(pat) == 1 and is_tok(pat[0], "str"):
                    p = self.ipm_pat(pat[0].val[1:-1])
                    return f"{'icases' if w == 'iDestruct' else 'imod'} {st} with {p}"
            if w == "iMod" and len(args) == 1 and is_tok(args[0], "str"):
                return f"imod {args[0].val[1:-1]}"
            raise Untranslatable(w)
        if w == "iPoseProof":
            if any(is_tok(a, "id", "as") for a in args):
                k = next(k for k, a in enumerate(args) if is_tok(a, "id", "as"))
                src, pat = args[:k], args[k + 1:]
                if len(pat) == 1 and is_tok(pat[0], "str") and not any(is_tok(a, "id", "with") for a in flat_toks(src)):
                    return f"ihave {self.ipm_pat(pat[0].val[1:-1])} := {term_of(src)}"
            raise Untranslatable(w)
        raise Untranslatable("iris proof mode: " + w)

    def location(self, items) -> str:
        ts = [tok_text(a) for a in items]
        if ts == ["*"]:
            return "at *"
        hs = []
        for t in ts:
            if t == ",":
                continue
            if t in ("|-", "⊢"):
                hs.append("⊢")
            elif t == "*":
                continue
            else:
                hs.append(t)
        return "at " + " ".join(hs)

    def rewrite(self, args, setoid=False) -> str:
        loc = ""
        if any(is_tok(a, "id", "in") for a in args):
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "in"))
            loc = " " + self.location(args[k + 1:])
            args = args[:k]
        steps: list[str] = []
        rws: list[str] = []

        def flush():
            if rws:
                steps.append(f"rewrite [{', '.join(rws)}]{loc}")
                rws.clear()
        i = 0
        while i < len(args):
            a = args[i]
            t = tok_text(a)
            if t in ("/=",):
                flush()
                steps.append("<;> try dsimp only" if steps else "try dsimp only")
                i += 1
                continue
            if t in ("//", "//="):
                flush()
                steps.append(f"<;> try {CLOSE}")
                i += 1
                continue
            if t == "/" and i + 1 < len(args):
                flush()
                nxt = args[i + 1]
                if is_tok(nxt, "op", "="):
                    steps.append("<;> try dsimp only" if steps else "try dsimp only")
                elif is_tok(nxt, "op", "/"):
                    steps.append(f"<;> try {CLOSE}")
                else:
                    steps.append(f"unfold {self.N.resolve(tok_text(nxt))}{loc}")
                i += 2
                continue
            mult = ""
            rev = False
            if t in ("-", "<-"):
                rev = True
                i += 1
                a = args[i]
                t = tok_text(a)
            if t in ("!", "?"):
                mult = t
                i += 1
                a = args[i]
                t = tok_text(a)
            if t == "->":
                i += 1
                continue
            if isinstance(a, Group) and a.open == "{":
                raise Untranslatable("rewrite occurrence")
            tm = TermX(self.N, self.bound).emit_atom(a)
            item = ("← " if rev else "") + tm
            if mult:
                flush()
                steps.append(("try " if mult == "?" else "") + f"simp only [{item}]{loc}")
            elif setoid:
                flush()
                steps.append(f"simp only [{item}]{loc}")
            else:
                rws.append(item)
            i += 1
        flush()
        out = ""
        for s in steps:
            if s.startswith("<;>"):
                out = f"({out}) {s}" if out else s[4:]
            else:
                out = f"{out}; {s}" if out else s
        return out or "skip"

    def assert_(self, args, enough=False) -> str:
        # assert (H : P) by tac / assert (P) as pat by tac / assert P as H
        by = None
        if any(is_tok(a, "id", "by") for a in args):
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "by"))
            by = args[k + 1:]
            args = args[:k]
        pat = None
        if any(is_tok(a, "id", "as") for a in args):
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "as"))
            pat = args[k + 1:]
            args = args[:k]
        name = None
        if len(args) == 1 and isinstance(args[0], Group) and args[0].open == "(":
            inner = args[0].items
            parts = split_top(inner, ":")
            if len(parts) >= 2 and len(parts[0]) == 1 and is_tok(parts[0][0], "id") and pat is None:
                name = parts[0][0].val
                prop_items = [y for p in parts[1:] for y in (p + [Tok("op", ":", True)])][:-1]
            else:
                prop_items = inner
        else:
            prop_items = args
        tx = TermX(self.N, self.bound)
        prop = tx.emit(prop_items)
        if pat:
            ps = self.ipat(pat)
            p = ps[0] if len(ps) == 1 else "⟨" + ", ".join(ps) + "⟩"
        else:
            p = name or "this"
            self.bound.add(p)
        if name:
            self.bound.add(name)
        if enough:
            raise Untranslatable("enough")
        if by is not None:
            bt = self.texpr(by)
            if re.match(r"^[\w']+$", p):
                return f"have {p} : {prop} := by {bt}"
            return f"obtain {p} : {prop} := by {bt}"
        if re.match(r"^[\w']+$", p):
            return f"have {p} : {prop} := ?_; pick_goal 2"
        if p == "rfl":
            raise Untranslatable("assert as ->")
        self.pending_cont.append(f"rcases H_assert with {p}")
        return f"have H_assert : {prop} := ?_; pick_goal 2"

    def destruct(self, w, args) -> str:
        if w in ("destruct", "edestruct", "case") and any(is_tok(a, "op", ",") for a in args):
            parts = split_top(args, ",")
            if all(any(is_tok(a, "id", "as") for a in p) for p in parts):
                return "; ".join(self.destruct(w, p) for p in parts)
        if w == "induction" and args and is_tok(args[0], "num"):
            if args[0].val != "1":
                raise Untranslatable("induction N")
            self.bound.add("H_ind")
            return "intro H_ind; " + self.destruct(w, [Tok("id", "H_ind", True)] + args[1:])
        eqn = None
        if any(is_tok(a, "id", "eqn") for a in args):
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "eqn"))
            # eqn:E
            rest = args[k + 1:]
            if rest and is_tok(rest[0], "op", ":"):
                rest = rest[1:]
            eqn = tok_text(rest[0]) if rest else None
            args = args[:k] + rest[1:]
        pat = None
        if any(is_tok(a, "id", "as") for a in args):
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "as"))
            pat = args[k + 1:]
            args = args[:k]
        gen = []
        if any(is_tok(a, "id", "in") for a in args) and w == "induction":
            k = next(k for k, a in enumerate(args) if is_tok(a, "id", "in"))
            gen = [tok_text(a) for a in args[k + 1:] if tok_text(a) not in ("|-", "*", "⊢")]
            args = args[:k]
        if w == "case" and args and is_tok(args[0], "op", ":"):
            # case: H => [..]
            rest = args[1:]
            if any(is_tok(a, "op", "=>") for a in rest):
                k = next(k for k, a in enumerate(rest) if is_tok(a, "op", "=>"))
                pat = rest[k + 1:]
                rest = rest[:k]
            args = rest
        if not args:
            raise Untranslatable(w)
        # destruct (decide (P)) as [H|H]
        if len(args) == 1 and isinstance(args[0], Group) and args[0].open == "(" and \
                args[0].items and is_tok(args[0].items[0], "id") and args[0].items[0].val in ("decide", "classic"):
            prop = TermX(self.N, self.bound).emit(args[0].items[1:])
            if pat:
                ps = self.ipat(pat)
                return f"rcases {'Decidable.em' if args[0].items[0].val == 'decide' else 'Classical.em'} {self.wrap(prop)} with {ps[0] if len(ps) == 1 else '⟨' + ', '.join(ps) + '⟩'}"
            return f"by_cases {self.wrap(prop)}"
        tgt = TermX(self.N, self.bound).emit(args)
        if w == "induction":
            r = f"induction {tgt}"
            if gen:
                r += " generalizing " + " ".join(gen)
            if pat:
                if len(pat) != 1:
                    raise Untranslatable("induction pattern")
                br = self.branch_names(pat[0])
                if any(br):
                    self.pending_next = br
            return r
        if w in ("inversion", "inversion_clear", "inv", "elim"):
            if pat:
                ps = self.ipat(pat)
                return f"rcases {tgt} with {ps[0] if len(ps) == 1 else '⟨' + ', '.join(ps) + '⟩'}"
            return f"cases {tgt}"
        if pat:
            ps = self.ipat(pat)
            p = ps[0] if len(ps) == 1 else "⟨" + ", ".join(ps) + "⟩"
            if eqn:
                self.bound.add(eqn)
                return f"rcases {eqn} : {tgt} with {p}"
            return f"rcases {tgt} with {p}"
        if eqn:
            self.bound.add(eqn)
            return f"cases {eqn} : {tgt}"
        return f"cases {tgt}"


def tok_text(x) -> str:
    if isinstance(x, Tok):
        return x.val
    if isinstance(x, Group):
        close = OPEN.get(x.open, "end" if x.open == "match" else "")
        return x.open + " " + " ".join(tok_text(y) for y in x.items) + " " + close
    return str(x)


# ---------------------------------------------------------------------------
# Proof scripts
# ---------------------------------------------------------------------------

BULLET_RE = re.compile(r"^\s*(\{|\}|-+|\++|\*+)(?=\s|$|[^-+*])")


def translate_proof(sents: list[Sentence], names: NameTable, bound: set,
                    base_indent: int, rocq_comments: bool):
    """Returns (lines, n_untranslated, notes)."""
    tx = TacX(names, bound)
    lines: list[str] = []
    stack: list[str] = []          # bullet symbols / '{'
    dead_depth: Optional[int] = None
    untrans = 0
    pending_next_depth: Optional[int] = None
    consumed = False
    conts: list = []        # [depth, text, armed]: emitted when the main goal resumes

    def ind(d):
        return " " * (base_indent + 2 * d)

    for s in sents:
        text = s.text
        events = []
        while True:
            m = BULLET_RE.match(text)
            if not m:
                break
            events.append(m.group(1))
            text = text[m.end():].lstrip()
        open_block = None   # (depth) of a new block opened by this sentence
        for ev in events:
            if ev == "}":
                while stack and stack[-1] != "{":
                    stack.pop()
                if stack:
                    stack.pop()
            elif ev == "{":
                stack.append("{")
                open_block = len(stack)
            else:
                if ev in stack:
                    while stack[-1] != ev:
                        stack.pop()
                    open_block = len(stack)
                else:
                    stack.append(ev)
                    open_block = len(stack)
        depth = len(stack)
        if dead_depth is not None:
            if open_block is not None and open_block <= dead_depth:
                dead_depth = None
            elif depth < dead_depth:
                dead_depth = None
        if not text:
            # a lone bullet / brace sentence: the tactic follows in the next sentence
            # (cannot happen: the bullet is glued to the following tactic)
            continue
        if dead_depth is not None:
            lines.append(ind(max(depth - 1, 0)) + "  -- ROCQ: " + oneline(" ".join(events + [text])))
            continue
        prefix_lines = []
        if open_block is not None:
            d0 = open_block - 1
            for c in conts:
                if c[0] == d0:
                    c[2] = True
            if tx.pending_next and pending_next_depth is not None and open_block == pending_next_depth + 1:
                nm = tx.pending_next.pop(0)
                consumed = True
                head = "next " + " ".join(nm) + " =>" if nm else "next =>"
                prefix_lines.append(ind(d0) + head)
                lead = ind(open_block)
            else:
                lead = ind(d0) + "· "
        else:
            lead = ind(depth)
            if conts and conts[-1][0] == depth and conts[-1][2]:
                prefix_lines.append(ind(depth) + conts.pop()[1])
            if tx.pending_next and consumed and pending_next_depth == depth:
                nm = tx.pending_next.pop(0)
                if any(x != "_" for x in nm):
                    prefix_lines.append(ind(depth) + "rename_i " + " ".join(nm))
        try:
            t = tx.tactic(text)
            if tx.pending_next and pending_next_depth is None:
                pending_next_depth = depth
            while tx.pending_cont:
                conts.append([depth, tx.pending_cont.pop(), False])
            lines.extend(prefix_lines)
            tl = t.split("\n")
            lines.append(lead + tl[0])
            for extra in tl[1:]:
                lines.append(ind(depth) + extra)
            if rocq_comments:
                lines.append(ind(depth) + "-- ROCQ: " + oneline(text))
        except (Untranslatable, StopIteration, IndexError, KeyError) as e:
            untrans += 1
            lines.extend(prefix_lines)
            lines.append(lead + "all_goals sorry  -- ROCQ: " + text.replace("\n", " "))
            dead_depth = depth
        if tx.pending_next == [] and pending_next_depth is not None:
            pending_next_depth = None
            consumed = False
    return lines, untrans, tx.notes


# ---------------------------------------------------------------------------
# Whole-file translation
# ---------------------------------------------------------------------------

@dataclass
class OutDecl:
    rocq: str
    lean: str
    kind: str          # theorem/def/inductive/structure/notation/other
    start: int = 0
    end: int = 0
    proof_sorry: bool = False   # translator inserted sorry into the proof
    has_proof: bool = False


class FileX:
    def __init__(self, name: str, stmt_only=False, exclude_self=False, rocq_comments=False,
                 module_prefix=""):
        self.name = name
        self.stmt_only = stmt_only
        self.rocq_comments = rocq_comments
        self.N = NameTable(name, exclude_self)
        self.src = open(os.path.join(ROCQ_DIR, name + ".v")).read()
        self.sents = split_sentences(self.src)
        self.body: list[str] = []
        self.decls: list[OutDecl] = []
        self.section_vars: list[list] = []   # stack of [(name, binder_text, type_text)]
        self.section_decl_vars: dict[str, list[str]] = {}
        self.notes: list[str] = []
        self.namemap: list[tuple[str, str]] = []
        self.rocq_imports: list[str] = []
        self.lib_imports: list[str] = []
        self.untranslated_items: list[str] = []

    # ---------------- helpers
    def comment_text(self, com: str) -> str:
        body = com[2:-2]
        body = body.lstrip("*").strip()
        body = body.replace("-/", "- /").replace("/-", "/ -")

        def br(m):
            inner = m.group(1)
            if re.search(r"\.v$", inner) or "/" in inner:
                return "`" + inner + "`"
            try:
                self.N.quiet = True
                tx = TermX(self.N)
                return "`" + tx.term(inner) + "`"
            except Exception:
                return "`" + inner + "`"
            finally:
                self.N.quiet = False
        body = re.sub(r"\[([^\[\]\n]{1,80})\]", br, body)
        return body

    def emit_comments(self, comments, doc_ok=True) -> Optional[str]:
        """Section-level comments go out as `/-! -/`; returns a doc string for
        the last `(** ... *)` comment if doc_ok."""
        doc = None
        for c in comments:
            if re.match(r"^\(\*\s*[=\-*#]{5,}", c) or re.match(r"^\(\*+\s*\*+\)$", c):
                continue
            if c.startswith("(** *") or c.startswith("(** **"):
                m = re.match(r"^\(\*\*\s*(\*+)\s*", c)
                level = len(m.group(1)) if m else 1
                txt = self.comment_text(c)
                txt = txt.lstrip("* ")
                self.body.append("")
                self.body.append("/-! " + "#" * level + " " + txt + " -/")
                continue
            if c.startswith("(**"):
                if doc:
                    self.body.append("/- " + doc + " -/")
                doc = self.comment_text(c)
                continue
            # plain comment: keep as a block comment
            self.body.append("/- " + self.comment_text(c) + " -/")
        if doc and not doc_ok:
            self.body.append("/- " + doc + " -/")
            doc = None
        return doc

    def section_binders_for(self, text_tokens: set[str], proof_tokens: set[str]) -> tuple[str, list[str]]:
        """Explicit leading args for a declaration inside sections."""
        allv = [v for frame in self.section_vars for v in frame]
        if not allv:
            return "", []
        used = set()
        toks = text_tokens | proof_tokens
        # transitively through cited section decls
        for t in list(toks):
            if t in self.section_decl_vars:
                used.update(self.section_decl_vars[t])
        for (nm, _, ty_toks, _) in allv:
            if nm in toks:
                used.add(nm)
        changed = True
        while changed:
            changed = False
            for (nm, _, ty_toks, _) in allv:
                if nm in used:
                    for (nm2, _, _, _) in allv:
                        if nm2 in ty_toks and nm2 not in used:
                            used.add(nm2)
                            changed = True
        # implicit type vars used by used vars' types
        bs = []
        names = []
        for (nm, btxt, ty_toks, _) in allv:
            if nm in used:
                bs.append(btxt)
                names.append(nm)
        return " ".join(bs), names

    def add_section_vars(self, text: str):
        # Context (G : gexec) (Hwf : gwf G) {A : Type} `{EqDecision A}.
        t = re.sub(r"^(Context|Variables?|Hypothes[ie]s|Implicit Types?)\s*", "", text)
        items = build_tree(tokenize(t))
        frame = self.section_vars[-1] if self.section_vars else None
        if frame is None:
            self.section_vars.append([])
            frame = self.section_vars[-1]
        groups = []
        if items and not isinstance(items[0], Group):
            groups = [Group("(", items)]
        else:
            k = 0
            while k < len(items):
                y = items[k]
                if is_tok(y, "op", "`") and k + 1 < len(items) and isinstance(items[k + 1], Group):
                    groups.append(Group("`" + items[k + 1].open, items[k + 1].items))
                    k += 2
                    continue
                if isinstance(y, Group):
                    groups.append(y)
                k += 1
        for g in groups:
            parts = split_top(g.items, ":")
            if g.open.startswith("`"):
                txt = TermX(self.N).emit(g.items)
                frame.append(("_inst" + str(len(frame)), f"[{txt}]",
                              {y.val for y in flat_toks(g.items) if y.kind == "id"}, True))
                continue
            if len(parts) < 2:
                continue
            names = [y.val for y in parts[0] if is_tok(y, "id")]
            tyitems = [y for p in parts[1:] for y in p]
            ty = TermX(self.N).emit(tyitems)
            o, c = ("{", "}") if g.open == "{" else ("(", ")")
            idt = {y.val for y in flat_toks(tyitems) if y.kind == "id"}
            for nm in names:
                frame.append((nm, f"{o}{nm} : {ty}{c}", idt, False))

    # ---------------- the main loop
    def run(self):
        i = 0
        S = self.sents
        while i < len(S):
            s = S[i]
            t, attrs = strip_attrs(s.text)
            kw = t.split()[0] if t.split() else ""
            if kw in ("From", "Require", "Import", "Export") or t.startswith("Require"):
                self.emit_comments(s.comments, doc_ok=False)
                self.parse_require(t)
                i += 1
                continue
            if kw in ("Open", "Close", "Set", "Unset", "Arguments", "Hint", "Opaque", "Transparent",
                      "Typeclasses", "Declare", "Existing", "Create", "Remove", "Generalizable",
                      "Add", "Ltac", "Ltac2", "Tactic", "Obligation", "Next", "Import", "Coercion",
                      "Implicit", "Strategy", "Unshelve", "Print", "Check", "Compute", "Eval",
                      "Search", "About", "Locate", "Abort", "Proof"):
                self.emit_comments(s.comments, doc_ok=False)
                if kw in ("Ltac", "Ltac2", "Tactic", "Hint", "Coercion", "Existing", "Add"):
                    self.body.append("-- ROCQ (not translated): " + oneline(s.text))
                    self.untranslated_items.append(oneline(s.text)[:80])
                i += 1
                continue
            if kw == "Section":
                self.emit_comments(s.comments, doc_ok=False)
                self.section_vars.append([])
                self.body.append("")
                self.body.append(f"-- section {t.split()[1]} (Rocq): its variables are explicit arguments below")
                i += 1
                continue
            if kw == "Module":
                self.emit_comments(s.comments, doc_ok=False)
                self.body.append(f"namespace {t.split()[1]}")
                self.section_vars.append([])
                i += 1
                continue
            if kw == "End":
                self.emit_comments(s.comments, doc_ok=False)
                if self.section_vars:
                    self.section_vars.pop()
                self.body.append(f"-- end section {t.split()[1] if len(t.split()) > 1 else ''}")
                i += 1
                continue
            if kw in ("Context", "Variable", "Variables", "Hypothesis", "Hypotheses"):
                self.emit_comments(s.comments, doc_ok=False)
                if not self.section_vars:
                    self.section_vars.append([])
                self.add_section_vars(t)
                i += 1
                continue
            d = parse_rocq_decl_head(s.text, self.name)
            if d is None:
                self.emit_comments(s.comments, doc_ok=False)
                self.body.append("-- ROCQ (not translated): " + oneline(s.text))
                self.untranslated_items.append(oneline(s.text)[:80])
                i += 1
                continue
            # gather a proof
            j = i + 1
            proof: list[Sentence] = []
            needs_proof = d.kind in ("Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition",
                                     "Example") or (d.kind in ("Definition", "Instance", "Let", "Fixpoint")
                                                    and ":=" not in top_level_assign(t))
            ended_by = None
            if needs_proof:
                while j < len(S):
                    tt = S[j].text.strip()
                    if re.match(r"^(\}\s*)*(Qed|Defined|Admitted|Abort|Save)$", tt):
                        ended_by = re.sub(r"^(\}\s*)*", "", tt)
                        j += 1
                        break
                    if re.match(r"^Proof(\s+using.*|\s+with.*)?$", tt):
                        j += 1
                        continue
                    if re.match(r"^Proof\s", tt) and not re.match(r"^Proof\s+(using|with)", tt):
                        # Proof <term>.
                        proof.append(Sentence("exact " + tt[6:], S[j].comments, S[j].line))
                        j += 1
                        continue
                    proof.append(S[j])
                    j += 1
            self.translate_decl(s, t, attrs, d, proof, ended_by)
            i = j
        return self

    def parse_require(self, t: str):
        m = re.match(r"^(?:From\s+(\S+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.*)$", t, re.S)
        if not m:
            m2 = re.match(r"^(?:Import|Export)\s+(.*)$", t, re.S)
            if m2:
                return
            return
        frm, mods = m.group(1), m.group(2).split()
        for md in mods:
            full = f"{frm}.{md}" if frm else md
            if frm == "xv6iris" or (not frm and os.path.exists(os.path.join(ROCQ_DIR, md + ".v"))):
                self.rocq_imports.append(md)
            else:
                self.lib_imports.append(full)

    def translate_decl(self, s: Sentence, t: str, attrs, d: RocqDecl, proof, ended_by):
        doc = self.emit_comments(s.comments)
        is_local = any(a in ("Local", "#[local]") for a in attrs)
        if d.kind == "Notation":
            self.translate_notation(t, d, doc, is_local)
            return
        if d.kind == "Instance":
            rest = re.sub(r"^Instance\s+[^\s:({\[]+", "", t, count=1)
            binders, ty, body = split_sig(rest)
            ty = (ty or "").strip()
            m = re.match(r"^(Reflexive|Transitive|Symmetric)\s+(.+)$", ty, re.S)
            if m and body is None:
                R = m.group(2)
                stmt = {"Reflexive": f"∀ x, ({R}) x x",
                        "Transitive": f"∀ x y z, ({R}) x y → ({R}) y z → ({R}) x z",
                        "Symmetric": f"∀ x y, ({R}) x y → ({R}) y x"}[m.group(1)]
                d2 = RocqDecl(d.name, "Lemma", self.name)
                self.notes.append(f"Rocq instance `{d.name} : {m.group(1)} ...` is a theorem here (WeakMem dev. 1)")
                self.translate_decl(Sentence("", [], s.line), f"Lemma {d.name} {binders} : {stmt}", [], d2,
                                    proof, ended_by)
                return
            m = re.match(r"^Decision\s+(.+)$", ty, re.S)
            if m:
                lean_name = self.N.register_local(d)
                self.namemap.append((d.name, lean_name))
                start = len(self.body) + 1
                tx = TermX(self.N)
                bt = self.translate_binders(binders, tx)
                P = tx.term(m.group(1))
                hm = re.match(r"^\(?([\w.']+)", P)
                head = hm.group(1) if hm else ""
                kw = "local instance" if is_local else "instance"
                self.body.append("")
                self.body.extend(wrap_sig(f"{kw} {lean_name}" + (f" {bt}" if bt else "") + f" : Decidable {P} := by"))
                self.body.append(f"  first | infer_instance | (unfold {head}; infer_instance)")
                od = OutDecl(d.name, lean_name, "def", start=start, end=len(self.body))
                self.decls.append(od)
                return
            self.body.append("")
            self.body.append("-- ROCQ (instance, not translated): " + oneline(t))
            for p in proof:
                self.body.append("--   " + oneline(p.text))
            self.untranslated_items.append("Instance " + d.name)
            self.decls.append(OutDecl(d.name, d.name, "instance"))
            return
        lean_name = self.N.register_local(d)
        self.namemap.append((d.name, lean_name))
        start = len(self.body) + 1
        self.body.append("")
        if doc:
            self.body.append("/-- " + doc + " -/")
        # split header: kw name binders : type := body
        head = re.sub(r"^(Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Corollary|Fact|Remark|Proposition|"
                      r"Example|Inductive|CoInductive|Variant|Record|Structure|Class|Let)\s+[^\s:({\[]+", "", t, count=1)
        all_toks = {x.val for x in tokenize(t) if x.kind == "id"}
        proof_toks = {x.val for p in proof for x in tokenize(p.text) if x.kind == "id"}
        sec_binders, sec_names = self.section_binders_for(all_toks, proof_toks)
        if self.section_vars:
            self.section_decl_vars[d.name] = sec_names
            btxt = {v[0]: v[1] for fr in self.section_vars for v in fr}
            args_ = [n if btxt.get(n, "").startswith("(") else f"({n} := {n})"
                     for n in sec_names if btxt.get(n, "")[:1] in "({"]
            if args_:
                self.N.local[d.name] = f"({lean_name} {' '.join(args_)})"
        od = OutDecl(d.name, lean_name, "def")
        if d.kind in ("Inductive", "CoInductive", "Variant"):
            od.kind = "inductive"
            self.translate_inductive(head, d, lean_name, sec_binders)
        elif d.kind in ("Record", "Structure", "Class"):
            od.kind = "structure"
            self.translate_record(head, d, lean_name, sec_binders)
        else:
            kind = "theorem" if d.kind in ("Lemma", "Theorem", "Corollary", "Fact", "Remark",
                                            "Proposition", "Example") else "def"
            od.kind = kind
            binders, ty, body = split_sig(head)
            tx = TermX(self.N)
            bt = self.translate_binders(binders, tx)
            if sec_binders:
                bt = (sec_binders + " " + bt).strip()
            tyt = tx.emit(build_tree(tokenize(ty))) if ty is not None else None
            if tyt:
                tyt = type_forall_indices(tyt)
            bt = type_untyped_indices(bt, (tyt or "") + " " + (body or ""))
            if tyt and tyt.startswith("GMapF"):
                self.N.map_names.add(d.name)
            if body is not None:
                body = re.sub(r"\{\s*struct\s+\w+\s*\}", "", body)
                bodyt = tx.emit(build_tree(tokenize(body)))
                sig = f"{kind} {lean_name}" + (f" {bt}" if bt else "") + (f" : {tyt}" if tyt else "")
                self.body.extend(wrap_sig(sig + " :="))
                self.body.append("  " + bodyt)
            else:
                sig = f"{kind} {lean_name}" + (f" {bt}" if bt else "") + f" : {tyt}"
                od.has_proof = True
                if self.stmt_only or ended_by == "Admitted" or not proof:
                    self.body.extend(wrap_sig(sig + " := by"))
                    self.body.append("  sorry")
                    od.proof_sorry = True
                else:
                    pl, nun, notes = translate_proof(proof, self.N, set(tx.bound), 2, self.rocq_comments)
                    self.body.extend(wrap_sig(sig + " := by"))
                    self.body.extend(pl)
                    od.proof_sorry = nun > 0
                    for nt in notes:
                        if nt not in self.notes:
                            self.notes.append(nt)
            for nt in tx.notes:
                if nt not in self.notes:
                    self.notes.append(nt)
        od.start = start
        od.end = len(self.body)
        self.decls.append(od)

    def translate_binders(self, binders: str, tx: TermX) -> str:
        items = build_tree(tokenize(binders))
        out = []
        k = 0
        while k < len(items):
            y = items[k]
            if is_tok(y, "op", "`") and k + 1 < len(items) and isinstance(items[k + 1], Group):
                out.append("[" + tx.emit(items[k + 1].items) + "]")
                k += 2
                continue
            if isinstance(y, Group) and y.open in ("(", "{"):
                parts = split_top(y.items, ":")
                if len(parts) >= 2:
                    names = [z.val for z in parts[0] if isinstance(z, Tok)]
                    tx.bound.update(names)
                    ty = tx.emit([z for p in parts[1:] for z in p])
                    if ty.startswith("GMapF"):
                        tx.map_vars.update(names)
                    o, c = ("(", ")") if y.open == "(" else ("{", "}")
                    out.append(f"{o}{' '.join(names)} : {ty}{c}")
                else:
                    names = [z.val for z in y.items if isinstance(z, Tok)]
                    tx.bound.update(names)
                    out.append(("{" if y.open == "{" else "(") + " ".join(names) + ("}" if y.open == "{" else ")"))
                k += 1
                continue
            if isinstance(y, Tok) and y.kind == "id":
                tx.bound.add(y.val)
                out.append(y.val)
            k += 1
        return " ".join(out)

    def translate_inductive(self, head, d, lean_name, sec_binders):
        sig, _, body = head.partition(":=")
        binders, ty, _ = split_sig(sig + " := x")
        tx = TermX(self.N)
        bt = self.translate_binders(binders, tx)
        if sec_binders:
            bt = (sec_binders + " " + bt).strip()
        tyt = tx.emit(build_tree(tokenize(ty))) if ty else None
        line = f"inductive {lean_name}" + (f" {bt}" if bt else "") + (f" : {tyt}" if tyt else "") + " where"
        self.body.append(line)
        alts = split_ctors(body)
        for a in alts:
            m = re.match(r"\s*([A-Za-z_][\w']*)(.*)$", a, re.S)
            if not m:
                continue
            cn, rest = m.group(1), m.group(2)
            ctx = TermX(self.N, set(tx.bound))
            # binders before ':' then type
            cb, cty, _ = split_sig(rest + " := x")
            cbt = self.translate_binders(cb, ctx)
            ctyt = ctx.emit(build_tree(tokenize(cty))) if cty else None
            self.body.append(f"  | {cn}" + (f" {cbt}" if cbt else "") + (f" : {ctyt}" if ctyt else ""))
            self.namemap.append((cn, f"{lean_name}.{cn}"))
        if not d.sort_prop and (not ty or "Prop" not in ty):
            pass

    def translate_record(self, head, d, lean_name, sec_binders):
        sig, _, body = head.partition(":=")
        binders, ty, _ = split_sig(sig + " := x")
        tx = TermX(self.N)
        bt = self.translate_binders(binders, tx)
        if sec_binders:
            bt = (sec_binders + " " + bt).strip()
        kw = "class" if d.kind == "Class" else "structure"
        self.body.append(f"{kw} {lean_name}" + (f" {bt}" if bt else "") + " where")
        m = re.match(r"\s*([A-Za-z_][\w']*)?\s*\{(.*)\}", body, re.S)
        if not m:
            self.body.append("  -- ROCQ: " + oneline(body))
            return
        if d.record_ctor:
            self.namemap.append((d.record_ctor, f"{lean_name}.mk"))
        for f in m.group(2).split(";"):
            fm = re.match(r"\s*([A-Za-z_][\w']*)\s*:(.*)$", f, re.S)
            if not fm:
                continue
            fty = TermX(self.N, set(tx.bound)).term(fm.group(2))
            self.body.append(f"  {camel(fm.group(1))} : {fty}")
            self.namemap.append((fm.group(1), f"{lean_name}.{camel(fm.group(1))}"))

    def translate_notation(self, t, d, doc, is_local):
        m = re.match(r'^Notation\s+"?([\w\']+)"?\s*:=\s*(.*?)(\s*\((only parsing|at level[^)]*)\))?\s*$', t, re.S)
        if not m:
            self.body.append("-- ROCQ (notation, not translated): " + oneline(t))
            self.untranslated_items.append("Notation " + oneline(t)[:60])
            return
        nm, body = m.group(1), m.group(2)
        bt = TermX(self.N).term(body)
        self.body.append(("local " if is_local else "") + f'notation "{nm}" => {bt}')
        self.N.local[nm] = nm

    # ---------------- output
    def imports(self) -> list[str]:
        imps = []
        for m in self.rocq_imports:
            if os.path.exists(os.path.join(TREE, "Weak", m + ".lean")) and f"Weak.{m}" in self.N.lean.imports:
                imps.append(f"Weak.{m}")
            else:
                imps.append(f"-- Weak.{m}  -- NOT PORTED / not found")
        reach = set()
        todo = [x for x in imps if not x.startswith("--")]
        while todo:
            x = todo.pop()
            if x in reach:
                continue
            reach.add(x)
            todo.extend(self.N.lean.imports.get(x, []))
        extra = []
        for m in sorted(self.N.used_modules):
            if m.startswith("Weak.") and m not in reach and m != f"Weak.{self.name}":
                extra.append(m)
                reach.add(m)
                todo = [m]
                while todo:
                    x = todo.pop()
                    for y in self.N.lean.imports.get(x, []):
                        if y not in reach:
                            reach.add(y)
                            todo.append(y)
        libs = []
        for lm in self.lib_imports:
            for li in ROCQ_LIB_IMPORTS.get(lm, []):
                if li not in reach and li not in libs:
                    libs.append(li)
        return ["Batteries.Tactic.SeqFocus", "Batteries.Tactic.PermuteGoals", "Batteries.Tactic.Init"] + libs + imps + [e + "  -- XLAT: a resolved name lives here" for e in extra]

    def header(self) -> str:
        rocq_hdr = ""
        for c in (self.sents[0].comments if self.sents else []):
            if c.startswith("(**"):
                rocq_hdr = self.comment_text(c)
                break
        dups = [(r, l) for r, l in self.namemap if r in self.N.dups and "." in l]
        nm = "; ".join(f"`{r}` ↦ `{l}`" if r != l else f"`{r}`" for r, l in self.namemap)
        unres = sorted(self.N.unresolved)
        h = [
            "/-",
            f"Weak: **TODO one-line summary** (DRAFT by tools/weak_rocq2lean.py -- NOT FOR COMMIT).",
            "",
            f"Rocq: `iris/{self.name}.v` @ xxvzwolszwmp.",
            "",
            "The Rocq header, verbatim (TODO: condense to \"in substance\"):",
            "",
            rocq_hdr,
            "",
            "**Deviations from Rocq.**",
            "",
            "1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1." +
            (" File-qualified (in `notes/weak-port-dupnames.json`): " + ", ".join(f"`{r}` ↦ `{l}`" for r, l in dups) + "."
             if dups else " No name of this file is in `notes/weak-port-dupnames.json`."),
            "2. VOCABULARY: as `WeakMem` deviation 2.  TODO.",
            "3. TODO.",
            "",
            f"**Name map** (Rocq → Lean): {nm}.",
            "",
            "**Not ported:** TODO.",
            "",
            "**Statements checked** (by hand, against Rocq): TODO.",
            "",
            "DRAFT NOTES (delete):",
        ]
        for n in self.notes:
            h.append(f"  - XLAT?: {n}")
        if unres:
            h.append("  - names not found in the Lean tree (guessed camelCase): " +
                     ", ".join(f"`{u}`" for u in unres[:80]))
        if self.untranslated_items:
            h.append("  - untranslated top-level items: " + "; ".join(self.untranslated_items[:40]))
        h.append("-/")
        return "\n".join(x.replace("-/", "- /") if i not in (0, len(h) - 1) else x for i, x in enumerate(h))

    def render(self) -> tuple[str, list[OutDecl]]:
        imps = self.imports()
        hdr = self.header()
        pre = [hdr] + [("import " + x) if not x.startswith("--") else x for x in imps] + [
            "", "namespace Weak", "",
            "open MachCSL MachCSL.Stdpp Iris.Std" + (" Iris.Std.PartialMap" if self.N.uses_partialmap else "")]
        off = sum(p.count("\n") + 1 for p in pre)
        # body index -> first line number of that element (body elements may hold newlines)
        line_of = []
        ln = off + 1
        for b in self.body:
            line_of.append(ln)
            ln += b.count("\n") + 1
        line_of.append(ln)
        for d in self.decls:
            s0, e0 = d.start, d.end      # body indices: [start-1, end)
            d.start = line_of[max(s0 - 1, 0)]
            d.end = line_of[e0] - 1
        text = "\n".join(pre + self.body + ["", "end Weak", ""])
        return text, self.decls


def type_forall_indices(stmt: str) -> str:
    """`∀ i x, l[i]? = ...` -> `∀ (i : Nat) x, ...` (Rocq infers `nat` from `!!`)."""
    def fix(m):
        q, names = m.group(1), m.group(2).split()
        out = []
        for nm in names:
            if re.search(r"\[" + re.escape(nm) + r"\][?!]", stmt):
                out.append(f"({nm} : Nat)")
            else:
                out.append(nm)
        return f"{q} {' '.join(out)},"
    return re.sub(r"(∀|∃)\s+((?:[A-Za-z_][\w']*\s*)+),", fix, stmt)


def type_untyped_indices(bt: str, stmt: str) -> str:
    """An untyped binder used as a list index (`l[i]?`) is a `Nat` (Rocq infers it from `!!`)."""
    out, depth = [], 0
    for tok in re.findall(r"[({\[]|[)}\]]|[^\s(){}\[\]]+|\s+", bt):
        if tok in "({[":
            depth += 1
        elif tok in ")}]":
            depth -= 1
        elif depth == 0 and re.match(r"^[A-Za-z_][\w']*$", tok) and \
                re.search(r"\[" + re.escape(tok) + r"\][?!]", stmt):
            tok = f"({tok} : Nat)"
        out.append(tok)
    return "".join(out)


def flat_toks(items):
    for y in items:
        if isinstance(y, Group):
            yield from flat_toks(y.items)
        else:
            yield y


def oneline(s):
    return re.sub(r"\s+", " ", s).strip()


def top_level_head(t: str) -> str:
    a = top_level_assign(t)
    return t[:len(t) - len(a)] if a else t


def top_level_assign(t: str) -> str:
    """the text from the first top-level `:=` on (empty if none)."""
    depth = 0
    i = 0
    while i < len(t):
        c = t[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and t.startswith(":=", i):
            return t[i:]
        i += 1
    return ""


def split_sig(head: str):
    """`binders : type := body` -> (binders, type|None, body|None) at top level."""
    depth = 0
    colon = assign = None
    i = 0
    while i < len(head):
        c = head[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if head.startswith(":=", i):
                assign = i
                break
            if c == ":" and colon is None and not head.startswith("::", i) and \
                    not head.startswith(":>", i) and (i == 0 or head[i - 1] != ":"):
                colon = i
        i += 1
    if assign is not None:
        pre, body = head[:assign], head[assign + 2:]
    else:
        pre, body = head, None
    if colon is not None and (assign is None or colon < assign):
        return pre[:colon].strip(), pre[colon + 1:].strip(), body
    return pre.strip(), None, body


def split_ctors(body: str) -> list[str]:
    depth = 0
    parts, cur = [], []
    for c in body:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "|" and depth == 0:
            parts.append("".join(cur))
            cur = []
            continue
        cur.append(c)
    parts.append("".join(cur))
    return [p for p in parts if p.strip()]


def wrap_sig(sig: str) -> list[str]:
    if len(sig) <= 100:
        return [sig]
    # break before the statement colon
    k = None
    depth = 0
    for i, c in enumerate(sig):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and i > 0 and sig[i - 1] == " " and not sig.startswith(":=", i):
            k = i
            break
    if k is None:
        return [sig]
    return [sig[:k + 1], "    " + sig[k + 1:].strip()]


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

def eval_files(files, tree, run_build=True):
    os.makedirs(os.path.join(tree, "Weak", "Draft"), exist_ok=True)
    meta = {}
    targets = []
    for f in files:
        for mode in ("S", "P"):
            fx = FileX(f, stmt_only=(mode == "S"), exclude_self=True).run()
            text, decls = fx.render()
            mod = f"{f}{mode}"
            text = text.replace("\n\nnamespace Weak\n", "\nset_option maxErrors 100000\nnamespace Weak\n", 1)
            path = os.path.join(tree, "Weak", "Draft", mod + ".lean")
            open(path, "w").write(text)
            meta[mod] = [d.__dict__ for d in decls]
            targets.append(f"Weak.Draft.{mod}")
        # name agreement against the real port
        fx = FileX(f, exclude_self=True)
        fx.run()
        real = NameTable(f, False)
        real_names = set(real.lean.names)

        def found(l):
            l2 = l[len(f) + 1:] if l.startswith(f + ".") else l
            for x in ("Weak." + l, f"Weak.{f}.{l2}", "Weak." + l2, l):
                if x in real_names:
                    return x
            return None
        ok = sum(1 for r, l in fx.namemap if found(l))
        meta[f + "_names"] = (ok, len(fx.namemap))
        # FIDELITY (mode C): each drafted theorem statement is proved from the REAL port's theorem
        fx = FileX(f, stmt_only=True, exclude_self=True).run()
        text, decls = fx.render()
        lines = text.split("\n")
        for d in decls:
            if d.kind != "theorem" or not d.has_proof:
                continue
            rn = found(d.lean)
            for k in range(d.start - 1, min(d.end, len(lines))):
                if lines[k].strip() == "sorry":
                    lines[k] = ("  first | exact " + rn + " | (intros; apply " + rn + " <;> assumption)"
                                + " | (intros; first | exact (" + rn + " ..) | apply " + rn + ")"
                                if rn else "  exact NO_REAL_TWIN_FOUND")
                    break
        text = "\n".join(lines)
        text = text.replace("\n\nnamespace Weak\n", "\nset_option maxErrors 100000\nnamespace Weak.DraftC\n", 1).replace(
            "\nend Weak\n", "\nend Weak.DraftC\n")
        text = text.replace("\nimport Batteries.Tactic.SeqFocus", f"\nimport Weak.{f}\nimport Batteries.Tactic.SeqFocus", 1)
        mod = f"{f}C"
        open(os.path.join(tree, "Weak", "Draft", mod + ".lean"), "w").write(text)
        for d in decls:            # the extra import line
            d.start += 1
            d.end += 1
        meta[mod] = [d.__dict__ for d in decls]
        targets.append(f"Weak.Draft.{mod}")
    json.dump(meta, open(os.path.join(tree, "Weak", "Draft", "meta.json"), "w"), indent=1)
    if not run_build:
        return
    log = os.path.join(tree, "Weak", "Draft", "build.log")
    r = subprocess.run([os.path.expanduser("~/.local/bin/lean-gcp"), "-C", tree, "lake", "build",
                        "--keep-toolchain"] + targets if False else
                       [os.path.expanduser("~/.local/bin/lean-gcp"), "-C", tree, "lake", "build"] + targets,
                       capture_output=True, text=True)
    open(log, "w").write(r.stdout + r.stderr)
    report(tree, files)


def report(tree, files):
    meta = json.load(open(os.path.join(tree, "Weak", "Draft", "meta.json")))
    log = open(os.path.join(tree, "Weak", "Draft", "build.log")).read()
    errs = defaultdict(list)
    for m in re.finditer(r"error: (?:\S*/)?Weak/Draft/(\w+)\.lean:(\d+):(\d+): (.*)", log):
        errs[m.group(1)].append((int(m.group(2)), m.group(4)))
    for m in re.finditer(r"error: (?:\S*/)?Weak/Draft/(\w+)\.lean: (.*)", log):   # file-level (bad import)
        errs[m.group(1)].append((0, m.group(2)))
    tot = defaultdict(int)
    classes = defaultdict(int)
    for f in files:
        S = meta[f + "S"]
        P = meta[f + "P"]
        es = errs.get(f + "S", [])
        ep = errs.get(f + "P", [])

        def bad(d, el, _first={}):
            pre = [e for e in el if e[0] < min(x["start"] for x in S)]
            if pre:                      # a file-level (header/import) error: nothing was checked
                return pre
            cut = [e[0] for e in el if e[1].startswith("maximum number of errors")]
            if cut and d["end"] >= cut[0]:
                return [(cut[0], "maximum number of errors (not checked)")]   # conservative
            return [e for e in el if d["start"] <= e[0] <= d["end"]]
        st_ok = [d for d in S if d["kind"] in ("theorem", "def", "inductive", "structure") and not bad(d, es)]
        st_all = [d for d in S if d["kind"] in ("theorem", "def", "inductive", "structure", "instance")]
        pr_all = [d for d in P if d["has_proof"]]
        pr_ok = [d for d in pr_all if not d["proof_sorry"] and not bad(d, ep)]
        pr_clean = [d for d in pr_all if not d["proof_sorry"]]
        nm_ok, nm_all = meta[f + "_names"]
        C = meta.get(f + "C", [])
        ec = errs.get(f + "C", [])
        th_all = [d for d in C if d["kind"] == "theorem" and d["has_proof"]]
        th_ok = [d for d in th_all if not bad(d, ec)]
        tot["fid_ok"] += len(th_ok)
        tot["fid_all"] += len(th_all)
        print(f"{f:24s} statements {len(st_ok):3d}/{len(st_all):3d}   proofs built {len(pr_ok):3d}/{len(pr_all):3d}"
              f" (sorry-free emitted {len(pr_clean):3d})   names {nm_ok}/{nm_all}"
              f"   faithful(thm<-real) {len(th_ok)}/{len(th_all)}")
        tot["st_ok"] += len(st_ok)
        tot["st_all"] += len(st_all)
        tot["pr_ok"] += len(pr_ok)
        tot["pr_all"] += len(pr_all)
        tot["pr_clean"] += len(pr_clean)
        tot["nm_ok"] += nm_ok
        tot["nm_all"] += nm_all
        for d in S:
            for e in bad(d, es)[:1]:
                classes["S: " + classify(e[1])] += 1
        for d in pr_all:
            if not d["proof_sorry"]:
                for e in bad(d, ep)[:1]:
                    classes["P: " + classify(e[1])] += 1
    pct = lambda a, b: f"{100.0 * a / b:.0f}%" if b else "-"
    print(f"TOTAL statements {tot['st_ok']}/{tot['st_all']} ({pct(tot['st_ok'], tot['st_all'])})  "
          f"proofs built {tot['pr_ok']}/{tot['pr_all']} ({pct(tot['pr_ok'], tot['pr_all'])}), "
          f"emitted sorry-free {tot['pr_clean']}  names {tot['nm_ok']}/{tot['nm_all']} "
          f"({pct(tot['nm_ok'], tot['nm_all'])})  faithful theorem statements {tot['fid_ok']}/{tot['fid_all']} "
          f"({pct(tot['fid_ok'], tot['fid_all'])})")
    for k, v in sorted(classes.items(), key=lambda kv: -kv[1]):
        print(f"  {v:3d}  {k}")


def classify(msg: str) -> str:
    m = msg.lower()
    for pat, c in [
        ("unknown identifier", "unknown identifier"), ("unknown constant", "unknown constant"),
        ("unsolved goals", "unsolved goals"), ("type mismatch", "type mismatch"),
        ("application type mismatch", "application type mismatch"),
        ("failed to synthesize", "instance synthesis"), ("unexpected token", "parse error"),
        ("expected", "parse error"), ("rewrite", "rewrite failed"), ("did not find instance", "rewrite failed"),
        ("motive", "rewrite failed"), ("no goals", "no goals (over-closed)"),
        ("linarith", "omega/arith"), ("omega", "omega/arith"),
        ("function expected", "function expected (arity/vocab)"),
        ("failed to infer", "binder type inference"), ("typeclass", "instance synthesis"),
        ("unknown", "unknown name"), ("simp made no progress", "simp no progress"),
        ("rcases", "rcases pattern"), ("first", "fallback failed"), ("apply", "apply failed"),
        ("not a structure", "field notation"), ("invalid field", "field notation"),
        ("maximum recursion", "recursion/heartbeats"), ("heartbeats", "recursion/heartbeats"),
        ("ambiguous", "ambiguous"), ("deterministic", "recursion/heartbeats")]:
        if pat in m:
            return c
    return msg[:50]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("name", nargs="*")
    ap.add_argument("-o", "--output")
    ap.add_argument("--stmt-only", action="store_true")
    ap.add_argument("--rocq-comments", action="store_true")
    ap.add_argument("--names", action="store_true")
    ap.add_argument("--exclude-self", action="store_true",
                    help="hide the file's own Lean port from the name table (evaluation)")
    ap.add_argument("--eval", action="store_true")
    ap.add_argument("--report", action="store_true", help="re-report an --eval run without building")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--tree", default=os.path.join(os.path.dirname(TREE), "xv6iris-weak-w5x"))
    a = ap.parse_args()
    if a.eval:
        eval_files(a.name, a.tree, run_build=not a.no_build)
        return
    if a.report:
        report(a.tree, a.name)
        return
    for nm in a.name:
        fx = FileX(nm, stmt_only=a.stmt_only, exclude_self=a.exclude_self,
                   rocq_comments=a.rocq_comments).run()
        if a.names:
            for r, l in fx.namemap:
                print(f"{r}\t{l}")
            continue
        text, _ = fx.render()
        if a.output:
            open(a.output, "w").write(text)
        else:
            sys.stdout.write(text)


if __name__ == "__main__":
    main()
