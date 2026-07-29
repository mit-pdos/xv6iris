#!/usr/bin/env python3
"""Report which xv6 kernel functions have a proven Iris/Rocq spec.

The report is hierarchical: one section per xv6 source file (``proc.c``,
``vm.c``, ``trampoline.S``, ...), listing that file's functions and, for each,
whether the proofs under ``iris/`` establish something about it.

WHERE THE DATA COMES FROM
-------------------------

Three independent sources are joined on the *symbol name*:

1. ``kernel-rocq/KernelSyms.v`` -- the symbol table of the exact kernel image
   the proofs are about (addresses).  This, not a freshly built ELF, is the
   ground truth: ``xv6-riscv/kernel/`` is an untracked build tree that may have
   drifted from the image the proofs were generated against.

2. ``kernel-rocq/KernelInstrs.v`` -- every instruction of that image.  A symbol
   is a *function* iff an instruction starts at its address; a function's byte
   size is the instruction bytes from its entry up to the next function entry.
   So sizes and the function list are self-contained in the tracked artifacts.

3. ``xv6-riscv/kernel/*.o`` (via ``nm``) -- which source file defines each
   symbol.  Only names are read, never addresses, so a stale build tree still
   attributes correctly.  Falls back to scanning ``*.c`` / ``*.S`` for a
   definition or label when the objects are absent.

The proof side is read from the files ``iris/_CoqProject`` lists -- the build's
own target list -- and NOT from a ``iris/*.v`` glob.  A ``.v`` in the tree but
absent from the project file is compiled by nobody, so a "proven" function read
out of it would be a claim no build has ever checked; keying off ``_CoqProject``
makes the report describe exactly what CI verifies.  Drift either way is a
``--check`` error, never a silent adjustment (see ``coqproject_files``).

WHAT COUNTS AS "PROVEN"
-----------------------

Most whole-function proofs are in the spec-module shape (see
``claude-notes/design/spec-modules.md``): ``Spec<F>.v`` states a ``Module Type``
over a ``wp_<f>_..._body`` definition, ``Wp<F>.v`` proves it as a sealed
functor, and ``Link<F>.v`` applies that functor to its callees' proofs.  Those
are discovered automatically:

* a ``_body`` definition whose *entry* ``pc_is`` is ``KernelSyms.<sym>`` at
  offset 0 **and** whose continuation ``pc_is`` is the caller's return address
  (a ``let`` bound from register x1 / ``ra``, whatever it is named) is a
  WHOLE-FUNCTION spec for ``<sym>``;
* the same with a nonzero entry offset, or with a continuation that is another
  address inside the function, is a FRAGMENT spec (prologue / loop / epilogue);
* the spec is PROVEN if some ``Module <F>Proof ... : <MODTYPE>`` implements it
  and some ``Link*.v`` instantiates that functor; otherwise it is only
  ASSUMED (an interface nobody has discharged).

A handful of whole-function proofs predate that shape (the M-mode boot path and
the hand-written assembly: ``_entry``, ``start``, ``timerinit``, ``swtch``,
``kernelvec``, ``userret``, ...).  They name their entry pc through a local
``Definition``, which no textual rule can follow reliably, so they are declared
in MANIFEST below -- and every declaration is *verified* against the tree
(file exists, lemma is there), so it cannot rot silently.

Functions with neither are still reported as PARTIAL if any proof file mentions
an address inside them, which is what work-in-progress looks like.

HONESTY
-------

``Admitted.`` inside an implementing module, and ``Axiom``s reachable through a
proof's ``Require`` closure, are collected and propagated along the functor
dependency graph, so a function proved over an admitted callee is flagged.
This is a static over-approximation of ``Print Assumptions``; it needs no build.

Usage:
    tools/proof_coverage.py [--format text|md|html|json] [--out PATH]
"""

from __future__ import annotations

import argparse
import glob
import html
import json
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Whole-function proofs that do not use the Spec/Link module shape.  Each entry
# is verified against the tree; a stale one is reported as a manifest error
# rather than silently counted as coverage.
#
#   symbol -> (file, lemma, note)
MANIFEST_PROVEN = {
    "_entry": ("WpEntryNew.v", "wp_entry", "M-mode entry stub (entry.S)"),
    "start": ("WpStartNew.v", "wp_start", "M-mode boot, whole function"),
    "timerinit": ("WpTimerinit.v", "wp_timerinit", "M-mode timer setup, whole function"),
    "spin": ("ProofSpin.v", "wp_spin", "the entry.S park loop (never returns)"),
    "swtch": ("ProofSwtch.v", "wp_swtch_sconf", "context switch, whole function"),
    "kernelvec": ("ProofKernelvec.v", "wp_kernelvec",
                  "S-mode trap vector (sealed as SpecKernelvec.KERNELVEC by "
                  "LinkKernelvec.v); assumes kerneltrap_returns"),
    "userret": ("ProofUserret.v", "wp_userret_pt",
                "trampoline return-to-user path, over the user page table"),
    "uservec": ("ProofUservec.v", "wp_uservec_pt",
                "trampoline trap-from-user path, over the user page table"),
}

# Functions whose contract is *stated* but deliberately assumed (an Axiom, or a
# hypothesis threaded through callers' specs) rather than proven.
MANIFEST_ASSUMED = {
    "panic": ("SpecPanic.v", "panic_wp", "assumed as a hypothesis carried by callers"),
    "kerneltrap": ("SpecKerneltrap.v", "wp_kerneltrap_returns_body",
                   "only 'it returns' is assumed; the Axiom is LinkKerneltrap.v"),
    "consoleintr": ("SpecConsoleintr.v", "wp_consoleintr_sconf_body",
                    "uartintr's one unproven callee; the Axiom is LinkConsoleintr.v"),
}

PROVEN, ASSUMED, PARTIAL, NONE = "proven", "assumed", "partial", "none"
STATUS_ORDER = {PROVEN: 0, ASSUMED: 1, PARTIAL: 2, NONE: 3}
STATUS_MARK = {PROVEN: "+", ASSUMED: "~", PARTIAL: ".", NONE: " "}


# --------------------------------------------------------------------------
# Rocq source scanning helpers
# --------------------------------------------------------------------------

def strip_comments(src: str) -> str:
    """Blank out (* nesting *) comments, preserving line/column structure."""
    out = list(src)
    depth, i, n = 0, 0, len(src)
    while i < n:
        if src.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif src.startswith("*)", i) and depth:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        else:
            if depth and src[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


# A "chunk" is one top-level construct: from a keyword line to the next one.
CHUNK_KW = re.compile(
    r"^\s*(Definition|Lemma|Theorem|Corollary|Fact|Remark|Example|Axiom|Parameter|"
    r"Fixpoint|Inductive|Record|Notation|Module|Section|End|Require|From|Local|"
    r"Global|Instance|Context|Variable|Hypothesis|Proof|Qed|Admitted|Defined|Import)\b"
)


def chunks(src: str):
    """Yield (start_line, keyword, name, text) for each top-level construct."""
    lines = src.splitlines()
    starts = [i for i, l in enumerate(lines) if CHUNK_KW.match(l)]
    starts.append(len(lines))
    for a, b in zip(starts, starts[1:]):
        m = CHUNK_KW.match(lines[a])
        head = lines[a][m.end():]
        nm = re.match(r"\s*(?:Type\s+)?([A-Za-z_][\w']*)", head)
        yield a + 1, m.group(1), (nm.group(1) if nm else ""), "\n".join(lines[a:b])


# `pc_is (mword_of_int KernelSyms.foo)` / `let pcE := mword_of_int KernelSyms.foo`
ENTRY_PC = re.compile(
    r"(?:pc_is\s*\(|\blet\s+pcE?\d*\s*(?::[^:=]*?)?:=\s*)"
    r"\s*mword_of_int\s*\(?\s*KernelSyms\.(\w+)\s*(?:\+\s*(0x[0-9a-fA-F]+|\d+))?"
)
ANY_SYM = re.compile(r"KernelSyms\.(\w+)\s*(?:\+\s*(0x[0-9a-fA-F]+|\d+))?")
LET_BIND = re.compile(r"\blet\s+(\w+)")
# The caller's return address: bit 0 of register x1 (ra), cleared.
RA_DERIVED = re.compile(r"!!!\s*Regidx\s*\(\s*mword_of_int\s+1\b")
# Another function's entry address (a transfer OUT of this function).
SYM_ADDR = re.compile(r"mword_of_int\s*\(?\s*KernelSyms\.(\w+)\b")


def let_regions(text: str):
    """(name, binding-text) for each `let` the body opens."""
    lets = [(m.group(1), m.end()) for m in LET_BIND.finditer(text)]
    ends = [p for _, p in lets[1:]] + [len(text)]
    return [(n, text[s:e]) for (n, s), e in zip(lets, ends)]


def return_targets(text: str) -> set:
    """Names the body binds to the caller's return address (ra-derived)."""
    return {n for n, b in let_regions(text) if RA_DERIVED.search(b)}


def exit_targets(text: str, entry: str) -> set:
    """Names the body binds to a DIFFERENT function's entry address.  A
    never-returning function leaves this way instead of through `ra`: the boot
    path runs off the end of _entry into start(), and off the end of start()
    into main (via MRET)."""
    out = set()
    for n, b in let_regions(text):
        m = SYM_ADDR.search(b)
        if m and m.group(1) != entry:
            out.add(n)
    return out


def runs_to_end(text: str, entry: str, local_defs: dict | None = None) -> bool:
    """True when the spec's continuation sits past the last instruction of the
    function, i.e. the spec covers the whole function: at the caller's return
    address, or -- for a function that never returns -- at the entry of the
    function it transfers to.

    The continuation is not always spelled inline.  A body may FACTOR its
    postcondition into a named predicate and apply it (SpecVirtioDiskInit.v's
    `vdi_post`, done because carrying a twenty-wand chain as a spatial
    hypothesis across ~140 instruction steps doubled the proof's compile time).
    The `pc_is ret_tgt` then lives in that predicate, not here, and reading only
    this chunk would call a fully proven whole-function spec a mere FRAGMENT --
    silently, as a coverage downgrade rather than an error.  So when the inline
    search fails, follow same-file predicates the body APPLIES.

    The follow is deliberately narrow, or it would upgrade real fragment specs:
    it fires only when the body passes one of *these* return/exit-target names
    into the predicate AND the predicate puts that same name under a `pc_is`.  A
    fragment spec passes a mid-function address instead, which is never in
    `names`, so it stays a fragment."""
    names = (return_targets(text) | {"ret_tgt", "rettgt", "ret_target"}
             | exit_targets(text, entry))
    pc_of = lambda body, n: re.search(rf"pc_is\s+(?:\(\s*)?{re.escape(n)}\b", body)
    if any(pc_of(text, n) for n in names):
        return True
    for dname, dtext in (local_defs or {}).items():
        # the body applies `dname`, with `n` among the arguments of that
        # application (same logical line, before the separating `-∗`)
        for m in re.finditer(rf"\b{re.escape(dname)}\b([^.]*)", text):
            args = m.group(1).split("-∗")[0]
            if any(re.search(rf"\b{re.escape(n)}\b", args) and pc_of(dtext, n)
                   for n in names):
                return True
    return False
REQUIRE = re.compile(r"^\s*(?:From\s+\w+\s+)?Require\s+(?:Import|Export)?\s*([^.]*)\.", re.M)
MODTYPE_DECL = re.compile(r"^\s*Module\s+Type\s+(\w+)\s*\.", re.M)
# `Module KfreeProof (A : ACQUIRE) (B : MEMSETPAGE) : KFREE.`
# `<:` (transparent ascription) is accepted too: the tree's convention is the
# opaque `:` (see design/spec-modules.md), but a stray `<:` must not make a
# proven+linked function silently read as `assumed`.
MODIMPL_DECL = re.compile(
    r"^\s*Module\s+(\w+)\s*((?:\(\s*\w+\s*:\s*\w+\s*\)\s*)*)<?:\s*(\w+)\s*\.", re.M)
# `Module Kfree := KfreeProof Acquire MemsetPage Release.`
MODINST_DECL = re.compile(r"^\s*Module\s+(\w+)\s*:=\s*(\w+)((?:\s+\w+)*)\s*\.", re.M)


# --------------------------------------------------------------------------
# 1. the kernel image: symbols, functions, sizes
# --------------------------------------------------------------------------

@dataclass
class Func:
    name: str
    addr: int
    size: int = 0          # bytes of instructions belonging to this entry
    ninstr: int = 0
    aliases: list = field(default_factory=list)
    source: str = "(unattributed)"
    status: str = NONE
    evidence: list = field(default_factory=list)   # list of dicts
    caveats: list = field(default_factory=list)    # list of str

    @property
    def display(self) -> str:
        """All names at this entry -- several symbols can share an address
        (`trampoline` = `uservec`), and which one is 'the' function is a
        judgement the symbol table does not record."""
        return " = ".join([self.name] + self.aliases)


def load_symbols(repo: str) -> dict:
    path = os.path.join(repo, "kernel-rocq", "KernelSyms.v")
    src = open(path).read()
    syms = {m.group(1): int(m.group(2), 16)
            for m in re.finditer(r"^Definition (\w+) : Z := (0x[0-9a-fA-F]+)%Z\.", src, re.M)}
    if not syms:
        sys.exit(f"no symbols parsed from {path}")
    return syms


def load_instrs(repo: str):
    path = os.path.join(repo, "kernel-rocq", "KernelInstrs.v")
    src = open(path).read()
    out = [(int(m.group(1), 16), int(m.group(2)) // 8)
           for m in re.finditer(r"MkKInstr \((0x[0-9a-f]+)\)%Z (\d+)%nat", src)]
    if not out:
        sys.exit(f"no instructions parsed from {path}")
    out.sort()
    return out


def build_functions(syms: dict, instrs) -> dict:
    """Symbols that start an instruction are functions; size them by extent."""
    entry_addrs = {a for a, _ in instrs}
    by_addr = defaultdict(list)
    for name, addr in syms.items():
        if addr in entry_addrs:
            by_addr[addr].append(name)

    funcs = {}
    for addr, names in by_addr.items():
        # A name with a leading underscore is the aliasing/linker-script name
        # (_trampoline vs trampoline); prefer the plain one as canonical.
        names.sort(key=lambda n: (n.startswith("_"), n))
        f = Func(name=names[0], addr=addr, aliases=names[1:])
        funcs[names[0]] = f

    bounds = sorted(by_addr)
    nxt = {a: b for a, b in zip(bounds, bounds[1:])}
    for f in funcs.values():
        end = nxt.get(f.addr, 1 << 64)
        for a, w in instrs:
            if f.addr <= a < end:
                f.size += w
                f.ninstr += 1
    return funcs


def attribute_sources(repo: str, funcs: dict) -> list:
    """Map each function to the xv6 source file that defines it."""
    kdir = os.path.join(repo, "xv6-riscv", "kernel")
    notes = []
    owner = {}

    nm = next((c for c in ("riscv64-linux-gnu-nm", "riscv64-unknown-elf-nm",
                           os.environ.get("NM", ""), "nm") if c and shutil.which(c)), None)
    objs = sorted(glob.glob(os.path.join(kdir, "*.o")))
    if nm and objs:
        for o in objs:
            base = os.path.basename(o)[:-2]
            src = next((f"{base}{e}" for e in (".c", ".S")
                        if os.path.exists(os.path.join(kdir, base + e))), base + ".o")
            try:
                out = subprocess.run([nm, "--defined-only", o],
                                     capture_output=True, text=True, check=True).stdout
            except (subprocess.CalledProcessError, OSError):
                continue
            for line in out.splitlines():
                p = line.split()
                if len(p) >= 3:
                    owner.setdefault(p[-1], src)
    else:
        notes.append("no riscv nm or no *.o objects found; "
                     "falling back to a source scan for file attribution")

    # Fallback / gap filler: look for a definition or an assembler label.
    missing = [n for f in funcs.values() for n in [f.name] + f.aliases if n not in owner]
    if missing:
        for path in sorted(glob.glob(os.path.join(kdir, "*.c")) +
                           glob.glob(os.path.join(kdir, "*.S"))):
            text = open(path, errors="replace").read()
            base = os.path.basename(path)
            for n in missing:
                if n in owner:
                    continue
                if re.search(rf"^{re.escape(n)}\s*(?:\(|:)", text, re.M):
                    owner[n] = base

    for f in funcs.values():
        for n in [f.name] + f.aliases:
            if n in owner:
                f.source = owner[n]
                break
        else:
            notes.append(f"could not attribute {f.name} to a source file")
    return notes


# --------------------------------------------------------------------------
# 2. the proofs: specs, implementations, links, admits, axioms
# --------------------------------------------------------------------------

@dataclass
class Spec:
    """A `wp_..._body` definition that pins an entry pc inside a function."""
    file: str
    line: int
    body: str          # the _body Definition's name
    symbol: str
    offset: int
    whole: bool        # runs to a return target, i.e. covers the function
    modtype: str = ""  # the Module Type exporting it, if any


@dataclass
class Proofs:
    specs: list = field(default_factory=list)
    modtype_file: dict = field(default_factory=dict)      # MODTYPE -> Spec file
    impl: dict = field(default_factory=dict)              # functor -> (file, modtype)
    impl_admits: dict = field(default_factory=dict)       # functor -> [line, ...]
    instances: dict = field(default_factory=dict)         # module -> (functor, [args])
    inst_file: dict = field(default_factory=dict)         # module -> Link file
    axioms: dict = field(default_factory=lambda: defaultdict(list))   # file -> [name]
    requires: dict = field(default_factory=dict)          # file -> [file, ...]
    mentions: dict = field(default_factory=lambda: defaultdict(set))  # symbol -> {file}
    errors: list = field(default_factory=list)            # _CoqProject drift


def coqproject_files(repo: str):
    """-> ([path, ...], [error, ...]) -- the file list the BUILD compiles.

    Keyed off ``iris/_CoqProject``, not a ``*.v`` glob, because that list is
    what ``coq_makefile`` turns into the build's targets.  A ``.v`` sitting in
    the tree unlisted is never compiled by anyone, so a "proven" function read
    out of it would be a claim no build has ever checked -- green CI over an
    unverified proof, silent in both directions.  Keying off the project file
    makes that impossible by construction: the report can only describe files
    the build checks.

    Both kinds of drift are returned as errors rather than quietly resolved,
    since each is a real defect, and ``--check`` turns them into a failing step:
    an unlisted file is an unchecked proof, and a listed-but-absent one breaks
    the build outright.  Assumes the flat ``iris/*.v`` layout the report handles
    (no subdirectories); a subdirectory entry would surface as "does not exist".
    """
    idir = os.path.join(repo, "iris")
    proj = os.path.join(idir, "_CoqProject")
    if not os.path.exists(proj):
        return [], [f"_CoqProject: {proj} does not exist"]

    errors, listed = [], []
    seen = set()
    with open(proj, errors="replace") as fh:
        for raw in fh:
            entry = raw.strip()
            # skip blanks, comments, and the -R / -arg option lines
            if not entry or entry.startswith("#") or entry.startswith("-"):
                continue
            if not entry.endswith(".v"):
                continue
            if entry in seen:
                errors.append(f"_CoqProject: lists {entry} more than once")
                continue
            seen.add(entry)
            listed.append(entry)

    ondisk = {os.path.basename(p) for p in glob.glob(os.path.join(idir, "*.v"))}
    for e in sorted(seen - ondisk):
        errors.append(f"_CoqProject: lists iris/{e}, which does not exist")
    for e in sorted(ondisk - seen):
        errors.append(f"_CoqProject: iris/{e} is not listed, so the build never "
                      f"compiles it -- nothing it claims is counted here")

    files = sorted(os.path.join(idir, e) for e in listed if e in ondisk)
    return files, errors


def scan_proofs(repo: str) -> Proofs:
    p = Proofs()
    idir = os.path.join(repo, "iris")
    files, p.errors = coqproject_files(repo)
    if not files:
        sys.exit(f"no proof files listed in {os.path.join(idir, '_CoqProject')}")

    known = {os.path.basename(f) for f in files}
    body_of_modtype = {}   # body definition name -> modtype (filled from Parameters)

    for path in files:
        base = os.path.basename(path)
        src = strip_comments(open(path, errors="replace").read())

        p.requires[base] = [f"{m}.v" for r in REQUIRE.findall(src)
                            for m in r.split() if f"{m}.v" in known]

        for sym, _ in ANY_SYM.findall(src):
            p.mentions[sym].add(base)

        # Same-file `Definition`s, for runs_to_end to follow a postcondition
        # factored out of a `_body`.  A pre-pass, not the loop below, so the
        # order of definitions in the file cannot matter.
        local_defs = {nm: tx for _, kw2, nm, tx in chunks(src)
                      if kw2 == "Definition" and nm and not nm.endswith("_body")}

        cur_modtype = None
        cur_impl = None
        for line, kw, name, text in chunks(src):
            if kw == "Module":
                mt = MODTYPE_DECL.match(text)
                mi = MODIMPL_DECL.match(text)
                mn = MODINST_DECL.match(text)
                if mt:
                    cur_modtype = mt.group(1)
                    p.modtype_file[cur_modtype] = base
                elif mi:
                    cur_impl = mi.group(1)
                    p.impl[cur_impl] = (base, mi.group(3))
                elif mn:
                    p.instances[mn.group(1)] = (mn.group(2), mn.group(3).split())
                    p.inst_file[mn.group(1)] = base
            elif kw == "End":
                if name == cur_modtype:
                    cur_modtype = None
                if name == cur_impl:
                    cur_impl = None
            elif kw == "Admitted" and cur_impl:
                p.impl_admits.setdefault(cur_impl, []).append(line)
            elif kw == "Axiom":
                p.axioms[base].append(name)
            elif kw == "Parameter" and cur_modtype:
                for b in re.findall(r"\b(\w+_body)\b", text):
                    body_of_modtype[b] = cur_modtype
            elif kw == "Definition" and name.endswith("_body"):
                m = ENTRY_PC.search(text)
                if not m:
                    continue
                p.specs.append(Spec(
                    file=base, line=line, body=name,
                    symbol=m.group(1),
                    offset=int(m.group(2), 0) if m.group(2) else 0,
                    whole=runs_to_end(text, m.group(1), local_defs)))

    for s in p.specs:
        s.modtype = body_of_modtype.get(s.body, "")
    return p


def require_closure(p: Proofs, start: str) -> set:
    seen, stack = set(), [start]
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        stack.extend(p.requires.get(f, []))
    return seen


def module_status(p: Proofs, modtype: str):
    """Find the linked instance discharging `modtype`, with its caveats.

    Returns (instance_name, link_file, caveats) or None if nothing links it.
    """
    for inst, (functor, _) in p.instances.items():
        impl = p.impl.get(functor)
        if impl and impl[1] == modtype:
            return inst, p.inst_file[inst], instance_caveats(p, inst)
    return None


VIA = re.compile(r"^(?:via \w+: )+")


def dedup_caveats(cs) -> list:
    """One line per underlying fact, keeping the shortest call path to it."""
    best = {}
    for c in cs:
        k = VIA.sub("", c)
        if k not in best or len(c) < len(best[k]):
            best[k] = c
    return list(best.values())


def instance_caveats(p: Proofs, inst: str, _seen=None) -> list:
    """Admits in this instance's proof, plus everything its callees carry."""
    _seen = _seen if _seen is not None else set()
    if inst in _seen:
        return []
    _seen.add(inst)
    out = []
    ent = p.instances.get(inst)
    if not ent:
        return out
    functor, args = ent
    impl = p.impl.get(functor)
    if impl:
        file, _ = impl
        for line in p.impl_admits.get(functor, []):
            out.append(f"Admitted at {file}:{line} (in {functor})")
        for f in sorted(require_closure(p, file) | require_closure(p, p.inst_file[inst])):
            for ax in p.axioms.get(f, []):
                out.append(f"assumes Axiom {ax} ({f})")
    for a in args:
        for c in instance_caveats(p, a, _seen):
            out.append(f"via {a}: {c}")
    return dedup_caveats(out)


# --------------------------------------------------------------------------
# 3. joining the two sides
# --------------------------------------------------------------------------

def classify(funcs: dict, p: Proofs, repo: str) -> list:
    errors = []
    by_name = {}
    for f in funcs.values():
        for n in [f.name] + f.aliases:
            by_name[n] = f

    def note(f, status, ev, caveats=()):
        f.evidence.append(ev)
        f.caveats = dedup_caveats(list(f.caveats) + list(caveats))
        if STATUS_ORDER[status] < STATUS_ORDER[f.status]:
            f.status = status

    # -- automatic: the Spec / Wp / Link module shape ------------------------
    for s in p.specs:
        f = by_name.get(s.symbol)
        if f is None:
            continue
        linked = module_status(p, s.modtype) if s.modtype else None
        where = f"{s.file}:{s.line}"
        kind = "whole function" if (s.whole and s.offset == 0) else \
               f"fragment at +0x{s.offset:x}"
        if linked:
            inst, link_file, caveats = linked
            note(f, PROVEN if (s.whole and s.offset == 0) else PARTIAL,
                 {"kind": kind, "what": f"{s.modtype} ({s.body})",
                  "where": where, "how": f"proven, linked in {link_file}",
                  "caveats": caveats}, caveats)
        elif s.modtype:
            note(f, ASSUMED,
                 {"kind": kind, "what": f"{s.modtype} ({s.body})",
                  "where": where, "how": "interface stated, no Link instantiates it",
                  "caveats": []})
        else:
            note(f, PARTIAL,
                 {"kind": kind, "what": s.body, "where": where,
                  "how": "spec definition, not exported as a Module Type",
                  "caveats": []})

    # -- declared: whole-function proofs outside the module shape ------------
    idir = os.path.join(repo, "iris")
    for sym, (file, lemma, why) in MANIFEST_PROVEN.items():
        f = by_name.get(sym)
        path = os.path.join(idir, file)
        if f is None:
            errors.append(f"MANIFEST_PROVEN: {sym} is not a function in this image")
            continue
        if not os.path.exists(path):
            errors.append(f"MANIFEST_PROVEN[{sym}]: {file} does not exist")
            continue
        src = strip_comments(open(path, errors="replace").read())
        m = re.search(rf"^\s*(?:Lemma|Theorem)\s+{re.escape(lemma)}\b", src, re.M)
        if not m:
            errors.append(f"MANIFEST_PROVEN[{sym}]: {lemma} not found in {file}")
            continue
        line = src[:m.start()].count("\n") + 1
        caveats = []
        if re.search(r"^\s*Admitted\b", src, re.M):
            caveats.append(f"{file} contains an Admitted lemma")
        for rf in sorted(require_closure(p, file)):
            for ax in p.axioms.get(rf, []):
                caveats.append(f"assumes Axiom {ax} ({rf})")
        note(f, PROVEN, {"kind": "whole function", "what": lemma,
                         "where": f"{file}:{line}", "how": f"declared: {why}",
                         "caveats": caveats}, caveats)

    for sym, (file, name, why) in MANIFEST_ASSUMED.items():
        f = by_name.get(sym)
        path = os.path.join(idir, file)
        if f is None:
            errors.append(f"MANIFEST_ASSUMED: {sym} is not a function in this image")
            continue
        if not os.path.exists(path):
            errors.append(f"MANIFEST_ASSUMED[{sym}]: {file} does not exist")
            continue
        src = strip_comments(open(path, errors="replace").read())
        m = re.search(rf"\b{re.escape(name)}\b", src)
        if not m:
            errors.append(f"MANIFEST_ASSUMED[{sym}]: {name} not found in {file}")
            continue
        line = src[:m.start()].count("\n") + 1
        note(f, ASSUMED, {"kind": "whole function", "what": name,
                          "where": f"{file}:{line}", "how": why, "caveats": []})

    # -- residual: any proof file that reaches into the function at all ------
    for f in funcs.values():
        if f.status != NONE:
            continue
        files = set()
        for n in [f.name] + f.aliases:
            files |= p.mentions.get(n, set())
        if files:
            shown = ", ".join(sorted(files)[:4]) + (" ..." if len(files) > 4 else "")
            note(f, PARTIAL, {"kind": "referenced", "what": f"{len(files)} proof file(s)",
                              "where": shown, "how": "instruction-level work only",
                              "caveats": []})
    return errors


# --------------------------------------------------------------------------
# 4. rendering
# --------------------------------------------------------------------------

def group(funcs: dict):
    by_src = defaultdict(list)
    for f in funcs.values():
        by_src[f.source].append(f)
    for fs in by_src.values():
        fs.sort(key=lambda f: f.addr)
    return dict(sorted(by_src.items(),
                       key=lambda kv: (-sum(1 for f in kv[1] if f.status == PROVEN),
                                       kv[0])))


def totals(fs):
    n = len(fs)
    b = sum(f.size for f in fs)
    pn = sum(1 for f in fs if f.status == PROVEN)
    pb = sum(f.size for f in fs if f.status == PROVEN)
    return n, b, pn, pb


def pct(a, b):
    return 100.0 * a / b if b else 0.0


def render_text(rep, verbose):
    L = []
    w = L.append
    m = rep["meta"]
    w("xv6 kernel -- Iris/Rocq proof coverage")
    w("=" * 60)
    w(f"image     : {m['nsyms']} symbols, {m['nfuncs']} functions, "
      f"{m['nbytes']} text bytes ({m['ninstrs']} instructions)")
    w(f"proofs    : {m['nproof_files']} files under iris/")
    s = rep["summary"]
    w("")
    w(f"functions : {s['proven']} proven, {s['assumed']} assumed, "
      f"{s['partial']} partial, {s['none']} untouched   "
      f"(of {s['total']}, {pct(s['proven'], s['total']):.0f}% proven)")
    w(f"text bytes: {s['proven_bytes']} of {s['total_bytes']} proven "
      f"({pct(s['proven_bytes'], s['total_bytes']):.0f}%)")
    if s["proven_with_caveats"]:
        w(f"            {s['proven_with_caveats']} of the proven functions rest on an "
          f"admit or an axiom (marked !, detailed at the end)")
    w("")
    w(f"legend    : {STATUS_MARK[PROVEN]} proven   {STATUS_MARK[ASSUMED]} assumed"
      f"   {STATUS_MARK[PARTIAL]} partial   {STATUS_MARK[NONE]} no proof   "
      f"! carries an admit/axiom")
    w("")
    # One column width for the whole report; a rare over-long name (several
    # symbols sharing an entry) is allowed to push its own row instead of
    # widening every other one.
    wide = min(24, max([len(f.display) for _, fs in rep["files"] for f in fs
                        if verbose or f.status != NONE] or [12]))
    for src, fs in rep["files"]:
        n, b, pn, pb = totals(fs)
        extra = [f"{c} {st}" for st, c in
                 ((ASSUMED, sum(1 for f in fs if f.status == ASSUMED)),
                  (PARTIAL, sum(1 for f in fs if f.status == PARTIAL))) if c]
        w(f"{src:<18} {pn:>3}/{n:<3} fns proven {pct(pn, n):>5.1f}%   "
          f"{pb:>6}/{b:<6} bytes {pct(pb, b):>5.1f}%"
          + (f"   (+{', '.join(extra)})" if extra else ""))
        for f in fs:
            if f.status == NONE and not verbose:
                continue
            flag = "!" if f.caveats else " "
            w(f"  {STATUS_MARK[f.status]}{flag} {f.display:<{wide}} 0x{f.addr:08x} "
              f"{f.size:>5}B  {f.status}")
            if verbose:
                for e in f.evidence:
                    w(f"        {e['kind']}: {e['what']}  [{e['where']}]  {e['how']}")
                for c in f.caveats:
                    w(f"        ! {c}")
        w("")
    if rep["caveats"]:
        w("Assumptions carried by proven functions")
        w("-" * 60)
        for fn, cs in rep["caveats"]:
            w(f"  {fn}")
            for c in cs:
                w(f"      {c}")
        w("")
    if rep["errors"]:
        w("CONSISTENCY ERRORS (the report below does not match the tree/build)")
        w("-" * 60)
        for e in rep["errors"]:
            w(f"  {e}")
        w("")
    if rep["notes"]:
        w("Notes")
        w("-" * 60)
        for nline in rep["notes"]:
            w(f"  {nline}")
    return "\n".join(L)


def render_md(rep, verbose):
    L = []
    w = L.append
    m, s = rep["meta"], rep["summary"]
    w("# xv6 kernel — Iris/Rocq proof coverage\n")
    w(f"`{m['nfuncs']}` functions / `{m['nbytes']}` text bytes in the proved image "
      f"(`kernel-rocq/KernelSyms.v`), against `{m['nproof_files']}` proof files "
      f"under `iris/`.\n")
    w(f"| | functions | text bytes |")
    w(f"|---|---|---|")
    w(f"| **proven** | {s['proven']} ({pct(s['proven'], s['total']):.0f}%) | "
      f"{s['proven_bytes']} ({pct(s['proven_bytes'], s['total_bytes']):.0f}%) |")
    w(f"| assumed | {s['assumed']} | — |")
    w(f"| partial | {s['partial']} | — |")
    w(f"| no proof | {s['none']} | — |\n")
    for src, fs in rep["files"]:
        n, b, pn, pb = totals(fs)
        w(f"## `{src}` — {pn}/{n} functions, {pb}/{b} bytes "
          f"({pct(pb, b):.0f}%)\n")
        w("| | function | addr | bytes | status | evidence |")
        w("|---|---|---|---|---|---|")
        for f in fs:
            ev = "; ".join(f"{e['what']} (`{e['where']}`) — {e['how']}"
                           for e in f.evidence) or "—"
            if f.caveats:
                ev += " ⚠️ " + "; ".join(f.caveats)
            w(f"| {STATUS_MARK[f.status]} | `{f.display}` | `0x{f.addr:08x}` | "
              f"{f.size} | {f.status} | {ev} |")
        w("")
    if rep["errors"]:
        w("## Consistency errors\n")
        for e in rep["errors"]:
            w(f"- {e}")
        w("")
    if rep["notes"]:
        w("## Notes\n")
        for nline in rep["notes"]:
            w(f"- {nline}")
    return "\n".join(L)


HTML_CSS = """
:root { color-scheme: light dark; --bg:#fff; --fg:#1a1a1a; --mut:#6b7280;
  --line:#e5e7eb; --card:#f9fafb;
  --ok:#15803d; --okbg:#dcfce7; --as:#a16207; --asbg:#fef9c3;
  --pa:#1d4ed8; --pabg:#dbeafe; --no:#6b7280; --nobg:#f3f4f6; }
@media (prefers-color-scheme: dark) { :root { --bg:#0d1117; --fg:#e6edf3;
  --mut:#9198a1; --line:#30363d; --card:#161b22;
  --ok:#4ade80; --okbg:#052e16; --as:#fcd34d; --asbg:#3f2d04;
  --pa:#93c5fd; --pabg:#0c2d6b; --no:#9198a1; --nobg:#21262d; } }
:root[data-theme="dark"] { --bg:#0d1117; --fg:#e6edf3; --mut:#9198a1;
  --line:#30363d; --card:#161b22; --ok:#4ade80; --okbg:#052e16;
  --as:#fcd34d; --asbg:#3f2d04; --pa:#93c5fd; --pabg:#0c2d6b;
  --no:#9198a1; --nobg:#21262d; }
:root[data-theme="light"] { --bg:#fff; --fg:#1a1a1a; --mut:#6b7280;
  --line:#e5e7eb; --card:#f9fafb; --ok:#15803d; --okbg:#dcfce7;
  --as:#a16207; --asbg:#fef9c3; --pa:#1d4ed8; --pabg:#dbeafe;
  --no:#6b7280; --nobg:#f3f4f6; }
body { background:var(--bg); color:var(--fg); margin:0;
  font:15px/1.5 ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,sans-serif; }
.wrap { max-width:1100px; margin:0 auto; padding:2.5rem 1.25rem 5rem; }
h1 { font-size:1.6rem; margin:0 0 .35rem; letter-spacing:-.01em; }
.sub { color:var(--mut); font-size:.9rem; margin:0 0 2rem; }
code, .mono { font-family:ui-monospace,SFMono-Regular,Menlo,monospace; }
.cards { display:flex; flex-wrap:wrap; gap:.75rem; margin-bottom:2rem; }
.card { flex:1 1 150px; background:var(--card); border:1px solid var(--line);
  border-radius:10px; padding:.8rem .9rem; }
.card .n { font-size:1.5rem; font-weight:600; }
.card .l { color:var(--mut); font-size:.78rem; text-transform:uppercase;
  letter-spacing:.05em; }
details { border:1px solid var(--line); border-radius:10px; margin-bottom:.6rem;
  background:var(--card); overflow:hidden; }
summary { cursor:pointer; padding:.65rem .9rem; display:flex; gap:.75rem;
  align-items:center; font-weight:600; }
summary::-webkit-details-marker { display:none; }
summary .name { flex:1 1 auto; }
.bar { flex:0 0 130px; height:7px; border-radius:4px; background:var(--nobg);
  overflow:hidden; }
.bar > i { display:block; height:100%; background:var(--ok); }
.stat { flex:0 0 auto; color:var(--mut); font-size:.82rem; font-weight:400; }
.tw { overflow-x:auto; }
table { border-collapse:collapse; width:100%; font-size:.86rem; }
th,td { text-align:left; padding:.4rem .9rem; border-top:1px solid var(--line);
  vertical-align:top; }
th { color:var(--mut); font-weight:500; font-size:.76rem;
  text-transform:uppercase; letter-spacing:.04em; }
td.ev { color:var(--mut); font-size:.8rem; }
.tag { display:inline-block; padding:.05rem .45rem; border-radius:999px;
  font-size:.72rem; font-weight:600; white-space:nowrap; }
.proven { color:var(--ok); background:var(--okbg); }
.assumed { color:var(--as); background:var(--asbg); }
.partial { color:var(--pa); background:var(--pabg); }
.none { color:var(--no); background:var(--nobg); }
.warn { color:var(--as); }
h2 { font-size:1.05rem; margin:2.2rem 0 .7rem; }
ul { color:var(--mut); font-size:.85rem; }
"""


def render_html(rep, verbose):
    e = html.escape
    m, s = rep["meta"], rep["summary"]
    L = [f"<title>xv6 proof coverage</title><style>{HTML_CSS}</style>", '<div class="wrap">']
    w = L.append
    w("<h1>xv6 kernel — Iris/Rocq proof coverage</h1>")
    w(f'<p class="sub">{m["nfuncs"]} functions · {m["nbytes"]} text bytes in the '
      f'proved image (<code>kernel-rocq/KernelSyms.v</code>) · '
      f'{m["nproof_files"]} proof files under <code>iris/</code></p>')
    w('<div class="cards">')
    for label, val, extra in (
            ("proven", s["proven"], f"{pct(s['proven'], s['total']):.0f}% of functions"),
            ("bytes proven", s["proven_bytes"],
             f"{pct(s['proven_bytes'], s['total_bytes']):.0f}% of text"),
            ("assumed", s["assumed"], "spec stated, not proven"),
            ("partial", s["partial"], "fragments only"),
            ("no proof", s["none"], "untouched")):
        w(f'<div class="card"><div class="n">{val}</div>'
          f'<div class="l">{label}</div><div class="stat">{extra}</div></div>')
    w("</div>")
    for src, fs in rep["files"]:
        n, b, pn, pb = totals(fs)
        openattr = " open" if pn else ""
        w(f'<details{openattr}><summary><span class="name mono">{e(src)}</span>'
          f'<span class="bar"><i style="width:{pct(pb, b):.1f}%"></i></span>'
          f'<span class="stat">{pn}/{n} fns · {pct(pb, b):.0f}% of {b} B</span>'
          f"</summary><div class='tw'><table><tr><th>function</th><th>addr</th>"
          f"<th>bytes</th><th>status</th><th>evidence</th></tr>")
        for f in fs:
            ev = "<br>".join(
                f"{e(x['what'])} <code>{e(x['where'])}</code> — {e(x['how'])}"
                for x in f.evidence) or "—"
            if f.caveats:
                ev += '<br><span class="warn">⚠ ' + \
                      "<br>⚠ ".join(e(c) for c in f.caveats) + "</span>"
            w(f'<tr><td class="mono">{e(f.display)}</td>'
              f'<td class="mono">0x{f.addr:08x}</td><td>{f.size}</td>'
              f'<td><span class="tag {f.status}">{f.status}</span></td>'
              f'<td class="ev">{ev}</td></tr>')
        w("</table></div></details>")
    if rep["errors"]:
        w("<h2>Consistency errors</h2><ul>" +
          "".join(f"<li>{e(x)}</li>" for x in rep["errors"]) + "</ul>")
    if rep["notes"]:
        w("<h2>Notes</h2><ul>" +
          "".join(f"<li>{e(x)}</li>" for x in rep["notes"]) + "</ul>")
    w("</div>")
    return "\n".join(L)


def render_json(rep, verbose):
    out = dict(rep)
    out["files"] = [
        {"source": src,
         "functions": [{"name": f.name, "names": [f.name] + f.aliases, "addr": f"0x{f.addr:08x}", "bytes": f.size,
                        "instructions": f.ninstr, "aliases": f.aliases,
                        "status": f.status, "evidence": f.evidence,
                        "caveats": f.caveats} for f in fs]}
        for src, fs in rep["files"]]
    return json.dumps(out, indent=2)


# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO, help="repository root")
    ap.add_argument("--format", default="text", choices=("text", "md", "html", "json"))
    ap.add_argument("--out", help="write here instead of stdout")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="text format: show evidence and untouched functions")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 on any consistency error (for CI: a stale "
                         "MANIFEST_PROVEN/MANIFEST_ASSUMED entry, or _CoqProject "
                         "drift, is a real regression -- unlike a coverage "
                         "percentage, which never fails)")
    args = ap.parse_args()

    syms = load_symbols(args.repo)
    instrs = load_instrs(args.repo)
    funcs = build_functions(syms, instrs)
    notes = attribute_sources(args.repo, funcs)
    proofs = scan_proofs(args.repo)
    # _CoqProject drift first: if the report is describing files the build never
    # compiles, that undermines every number below it, so it leads.
    errors = proofs.errors + classify(funcs, proofs, args.repo)

    fs_all = list(funcs.values())
    rep = {
        "meta": {
            "nsyms": len(syms), "nfuncs": len(funcs),
            "nbytes": sum(f.size for f in fs_all), "ninstrs": len(instrs),
            "nproof_files": len(proofs.requires),
        },
        "summary": {
            "total": len(fs_all),
            "total_bytes": sum(f.size for f in fs_all),
            "proven": sum(1 for f in fs_all if f.status == PROVEN),
            "proven_bytes": sum(f.size for f in fs_all if f.status == PROVEN),
            "assumed": sum(1 for f in fs_all if f.status == ASSUMED),
            "partial": sum(1 for f in fs_all if f.status == PARTIAL),
            "none": sum(1 for f in fs_all if f.status == NONE),
            "proven_with_caveats":
                sum(1 for f in fs_all if f.status == PROVEN and f.caveats),
        },
        "files": list(group(funcs).items()),
        "caveats": [(f.name, f.caveats) for f in sorted(fs_all, key=lambda f: f.name)
                    if f.caveats],
        "errors": errors,
        "notes": notes,
    }

    render = {"text": render_text, "md": render_md,
              "html": render_html, "json": render_json}[args.format]
    text = render(rep, args.verbose or args.format != "text")
    if args.out:
        with open(args.out, "w") as fh:
            fh.write(text + "\n")
        print(f"wrote {args.out}", file=sys.stderr)
    else:
        print(text)

    if args.check and errors:
        for e in errors:
            print(f"proof_coverage: consistency error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
