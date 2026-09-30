#!/usr/bin/env python3
"""Instruction-level coverage of a user program's text (used by
tools/proof_coverage.py; the theory is here so that it can be tested alone).

A user-program proof steps an instruction only through an instruction fact
`uinstrIs γt pc rvc i`, and every such fact is read off the program's dumped
text (tools/ci/EnvFacts.lean, the `X` facts).  So the set of pcs that have a
fact INSIDE THE CONE OF THE TOP THEOREMS is exactly the set of instructions
some verified run can execute: a byte outside it is a byte no proof ever
steps.

This module explains every such byte, from the program's own control flow
(the instructions and their objdump lines in `Xv6/User/<P>Image.lean`):

  * a FUNCTION with no covered instruction is
      unreachable   not reachable from the ELF entry (`start`) in the static
                    call graph: library code the linker kept and nothing
                    calls (most of ulib);
      uncalled      statically reachable, but only through call sites that
                    are themselves uncovered (the callers' dead arms);
      FINDING       a covered instruction calls it.
  * an uncovered RUN inside a function that has covered instructions is
    explained by how control could enter it from covered code:
      branch        a covered conditional branch leads into it.  The proofs
                    step that branch and never this successor, so in every
                    verified run the branch goes the other way (an error
                    arm the contracts refute);
      switch        the function has a covered jump-table `jr`: this is an
                    arm the proofs never take;
      noreturn      it follows a covered call (or `ecall`): the proofs never
                    step the return address, so the callee (exit, exec, a
                    panic) does not return there in any verified run;
      unentered     nothing covered leads into it;
      padding       alignment padding;
      FINDING       a covered instruction whose ONLY successor is this run
                    (a plain instruction falling through, an unconditional
                    jump): something stepped it and nothing steps what it
                    runs next.  That cannot happen in a sound cone, so it
                    means the fact extraction is incomplete -- a real
                    finding either way.

A FINDING is what `proof_coverage.py --check` fails on.
"""
import bisect
import re
from collections import defaultdict
from dataclasses import dataclass, field

COND = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz",
        "bgtz", "bgt", "ble", "bgtu", "bleu"}
PADDING = {"unimp", "c.unimp", ".2byte", ".word", ".short", ".insn"}

ASM_RE = re.compile(r"^\s*-- (.*)\n\s*⟨(0x[0-9a-f]+), (\d+), (0x[0-9a-f]+)⟩", re.M)
TARGET_RE = re.compile(r"\b([0-9a-f]+) <([^>+]+)(?:\+0x[0-9a-f]+)?>\s*$")


@dataclass
class Ins:
    addr: int
    width: int
    asm: str
    kind: str = "plain"      # plain | cond | jump | call | ret | ijump | ecall | pad
    target: object = None    # int for cond / jump / call


def classify_asm(asm, enc=None):
    """objdump's line -> (kind, target)."""
    parts = asm.split("\t", 1)
    mn = parts[0].strip()
    ops = parts[1] if len(parts) > 1 else ""
    ops = ops.split("#")[0].strip()
    m = TARGET_RE.search(ops)
    tgt = int(m.group(1), 16) if m else None
    if mn in PADDING or enc == 0:
        return "pad", None
    if mn in COND:
        return "cond", tgt
    if mn == "j":
        return "jump", tgt
    if mn == "jal":
        return "call", tgt
    if mn == "ret":
        return "ret", None
    if mn == "jr":
        return "ijump", None
    if mn == "jalr":
        return "icall", None
    if mn == "ecall":
        return "ecall", None
    return "plain", None


def parse_text(src):
    """The instructions of an `…Image.lean`, with their objdump lines."""
    out = []
    for m in ASM_RE.finditer(src):
        asm, addr, width, enc = m.group(1), int(m.group(2), 16), int(m.group(3)), int(m.group(4), 16)
        kind, tgt = classify_asm(asm, enc)
        out.append(Ins(addr, width, asm.replace("\t", " "), kind, tgt))
    out.sort(key=lambda i: i.addr)
    return out


@dataclass
class Run:
    """A maximal run of consecutive uncovered instructions of one function."""
    lo: int
    hi: int                 # one past the last byte
    nbytes: int
    why: str = ""           # branch | switch | noreturn | unentered | padding | FINDING
    detail: str = ""


@dataclass
class FnCov:
    name: str
    addr: int
    size: int
    covered: int = 0
    status: str = ""        # covered | partial | never
    why: str = ""           # for `never`: unreachable | uncalled | FINDING
    detail: str = ""
    runs: list = field(default_factory=list)
    calls: set = field(default_factory=set)


class Text:
    """One program: instructions, function extents, call graph."""

    def __init__(self, instrs, funcs, entry):
        """funcs: [(name, addr, size)]; entry: the ELF entry address."""
        self.instrs = instrs
        self.at = {i.addr: i for i in instrs}
        self.addrs = [i.addr for i in instrs]
        self.funcs = sorted(funcs, key=lambda f: f[1])
        self.fstarts = [f[1] for f in self.funcs]
        self.entry = entry

    def func_of(self, a):
        k = bisect.bisect_right(self.fstarts, a) - 1
        if k < 0:
            return None
        name, addr, size = self.funcs[k]
        return name if a < addr + size else None

    def body(self, name):
        _, addr, size = next(f for f in self.funcs if f[0] == name)
        lo = bisect.bisect_left(self.addrs, addr)
        hi = bisect.bisect_left(self.addrs, addr + size)
        return self.instrs[lo:hi]

    def call_graph(self):
        """{function: {functions it transfers control to}} -- calls, and jumps
        or branches that leave the function (tail calls)."""
        g = defaultdict(set)
        for i in self.instrs:
            if i.target is None:
                continue
            f, t = self.func_of(i.addr), self.func_of(i.target)
            if f and t and f != t:
                g[f].add(t)
        return g

    def reachable(self):
        root = self.func_of(self.entry)
        g = self.call_graph()
        seen, stack = set(), [root] if root else []
        while stack:
            f = stack.pop()
            if f in seen:
                continue
            seen.add(f)
            stack.extend(g.get(f, ()))
        return seen

    def indirect(self):
        return [i for i in self.instrs if i.kind in ("ijump", "icall")]


def analyze(text, covered):
    """-> ([FnCov], [problem]).  `covered`: the pcs with an instruction fact in
    the cone.  A problem is a fact at an address that is not an instruction."""
    problems = [f"instruction fact at 0x{a:x}, which is not an instruction of the text"
                for a in sorted(covered) if a not in text.at]
    reach = text.reachable()
    # who targets each address (branches, jumps, calls)
    into = defaultdict(list)
    for i in text.instrs:
        if i.target is not None:
            into[i.target].append(i)
    out = []
    for name, addr, size in text.funcs:
        body = text.body(name)
        fc = FnCov(name, addr, size)
        fc.covered = sum(i.width for i in body if i.addr in covered)
        nonpad = [i for i in body if i.kind != "pad"]
        if all(i.addr in covered for i in nonpad) and nonpad:
            fc.status = "covered"
        elif fc.covered:
            fc.status = "partial"
        else:
            fc.status = "never"
        if fc.status == "never":
            callers = [c for c in into.get(addr, []) if text.func_of(c.addr) != name]
            cov_callers = [c for c in callers if c.addr in covered]
            if cov_callers:
                fc.why = "FINDING"
                fc.detail = ("called from covered code (" + ", ".join(
                    f"0x{c.addr:x} in {text.func_of(c.addr)}" for c in cov_callers[:4])
                    + ") but none of its instructions is stepped")
            elif name not in reach:
                fc.why = "unreachable"
                fc.detail = "not reachable from the entry in the call graph"
            else:
                fc.why = "uncalled"
                sites = sorted({text.func_of(c.addr) for c in callers} - {None})
                fc.detail = ("every call site is itself uncovered"
                             + (f" (in {', '.join(sites[:4])}{' ...' if len(sites) > 4 else ''})"
                                if sites else ""))
            out.append(fc)
            continue
        switches = [i for i in body if i.kind == "ijump" and i.addr in covered]
        # maximal uncovered runs
        run = []
        runs = []
        for i in body + [None]:
            if i is not None and i.addr not in covered:
                run.append(i)
            elif run:
                runs.append(run)
                run = []
        for r in runs:
            ru = Run(r[0].addr, r[-1].addr + r[-1].width, sum(i.width for i in r))
            if all(i.kind == "pad" for i in r):
                ru.why, ru.detail = "padding", "alignment padding"
                fc.runs.append(ru)
                continue
            inrun = {i.addr for i in r}
            entries = []        # (category, text)
            for i in r:
                # fallthrough from the instruction before
                k = bisect.bisect_left(text.addrs, i.addr) - 1
                if k >= 0:
                    p = text.instrs[k]
                    if p.addr in covered and p.addr + p.width == i.addr and p.addr not in inrun:
                        if p.kind == "cond":
                            entries.append(("branch", f"the branch at 0x{p.addr:x} (`{p.asm}`) is always taken"))
                        elif p.kind in ("call", "icall"):
                            entries.append(("noreturn", f"the call at 0x{p.addr:x} (`{p.asm}`) does not return"))
                        elif p.kind == "ecall":
                            entries.append(("noreturn", f"the `ecall` at 0x{p.addr:x} does not return"))
                        elif p.kind in ("jump", "ret", "ijump"):
                            pass
                        else:
                            entries.append(("FINDING", f"0x{p.addr:x} (`{p.asm}`) is stepped and falls "
                                                       f"through to 0x{i.addr:x}, which is not"))
                for p in into.get(i.addr, []):
                    if p.addr not in covered or p.addr in inrun:
                        continue
                    if p.kind == "cond":
                        entries.append(("branch", f"the branch at 0x{p.addr:x} (`{p.asm}`) is never taken"))
                    else:
                        entries.append(("FINDING", f"0x{p.addr:x} (`{p.asm}`) is stepped and transfers "
                                                   f"to 0x{i.addr:x}, which is not"))
            cats = {c for c, _ in entries}
            if "FINDING" in cats:
                ru.why = "FINDING"
                ru.detail = "; ".join(t for c, t in entries if c == "FINDING")
            elif entries:
                ru.why = "branch" if "branch" in cats else "noreturn"
                ru.detail = "; ".join(dict.fromkeys(t for _, t in entries))
            elif switches:
                ru.why = "switch"
                ru.detail = (f"an arm of the jump table at 0x{switches[0].addr:x} that no "
                             "verified run selects")
            else:
                ru.why = "unentered"
                ru.detail = "no covered instruction leads into it"
            fc.runs.append(ru)
        out.append(fc)
    return out, problems


def summarize(fns):
    """-> dict of byte counts by explanation."""
    s = defaultdict(int)
    for f in fns:
        s["total"] += f.size
        s["covered"] += f.covered
        if f.status == "never":
            s[f.why] += f.size
        else:
            for r in f.runs:
                s[r.why] += r.nbytes
    return dict(s)
