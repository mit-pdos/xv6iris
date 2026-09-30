#!/usr/bin/env python3
"""Report which functions of the pinned images have a proved, linked contract
that the top theorems reach.

The Lean counterpart of Rocq's tools/proof_coverage.py (main).  The report is
hierarchical: the kernel by xv6 source file, then one section per user
program, each listing its functions and, for each, whether the proofs
establish something about it.

WHERE THE DATA COMES FROM
-------------------------

1. The IMAGES, read from the checked-in dumps (never from a freshly built
   ELF): `Xv6/KernelImage.lean` (instructions and text symbols) and
   `Xv6/User/<P>Image.lean` for init, sh, cat, grep, echo, seccomp, sync.  A
   symbol is a FUNCTION iff an instruction starts at its address; its size is
   the instruction bytes from its entry up to the next function entry.

2. The PROOFS, read from the ELABORATED ENVIRONMENT -- `envfacts.tsv`, which
   tools/ci/EnvFacts.lean dumps from the built tree (tools/ci/envfacts.sh).
   Rocq's tool scrapes `.v` text for `pc_is (… KernelSyms.f)`; here the
   metaprogram reads the address argument of `pcIs` / `urun` out of the
   statement TERMS and evaluates it, so the join is on the ADDRESS and no
   naming convention (`kfreeAddr`, `KA.«kfree»`, a frame the pin is factored
   into) can hide a pin or fake one.

3. `xv6-riscv/` (optional, best-effort, as in Rocq): which source file
   defines each symbol, via `nm` on the objects or a scan of the sources.
   Only names are read.  Without the checkout every function is listed under
   "(unattributed)"; the coverage numbers do not depend on it.

WHAT COUNTS AS "PROVEN"
-----------------------

A function `f` at address `A` is PROVEN when all of these hold:

  * some INTERFACE (a `structure … : Prop` field, or a Prop-valued
    definition) has its ENTRY pin at `A`: the pc predicate is a top-level
    premise of the contract (`kctx cpu k ∗ pcIs cpu A ∗ … ⊢ wpLoop cpu`), and
  * the contract covers the WHOLE function: its continuation is the caller's
    return address, or another function's entry (a function that leaves by a
    jump: `_entry` into `start`), or there is none (it never returns) --
    never an address inside `f` itself, which is what a FRAGMENT pins, and
  * some theorem of a `Link*` module CONCLUDES that interface, and
  * that theorem is in the CONE of the top theorems (tools/ci/roots.txt):
    the closed theorems depend on it, so its hypotheses -- the callees'
    interfaces -- are discharged all the way down.

Weaker evidence gives a weaker status:

  unreached  a Link theorem concludes the contract, but no top theorem uses it
  unlinked   the contract is proved and reached, but by no `Link*` module
  assumed    the contract is stated; no theorem concludes it
  partial    only fragments: a contract or lemma pins an address in `f`
  none       nothing mentions the function

`Link` is the Spec/Proof/Link discipline's name for "the instance clients
import" (tools/check_layering.sh); requiring it keeps this report and that
discipline saying the same thing.

EXIT STATUS (`--check`)
-----------------------

Unlike Rocq's report (where coverage is a number that never fails), this
tree CLAIMS that every kernel function is proved and linked, and `--check`
holds it to that:

  * every kernel function must be PROVEN, except the rows of
    tools/ci/coverage_allow.txt (each with its reason);
  * every user function listed PROVEN in tools/ci/coverage_user_baseline.txt
    must still be PROVEN (the floor: coverage may grow, never shrink);
  * the allowlist and the baseline must not be stale (a row for a symbol
    that is not a function of the image, or an allowlisted function that is
    in fact proven);
  * envfacts.tsv must name every top theorem and be non-trivial.

`--update-baseline` rewrites the user baseline from the current state.

Usage:
    tools/proof_coverage.py --facts envfacts.tsv [--format text|md|json]
                            [--out PATH] [--check] [-v]
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

USER_PROGS = ["Init", "Sh", "Cat", "Grep", "Echo", "Seccomp", "Sync"]

PROVEN, UNREACHED, UNLINKED, ASSUMED, PARTIAL, NONE = (
    "proven", "unreached", "unlinked", "assumed", "partial", "none")
STATUS_ORDER = {PROVEN: 0, UNREACHED: 1, UNLINKED: 2, ASSUMED: 3, PARTIAL: 4, NONE: 5}
STATUS_MARK = {PROVEN: "+", UNREACHED: "?", UNLINKED: "?", ASSUMED: "~", PARTIAL: ".", NONE: " "}

# The trampoline page is mapped at the top of every address space, so the
# contracts of uservec/userret pin TRAMPOLINE-relative addresses.
PGSIZE = 0x1000
TRAMPOLINE = (1 << 38) - PGSIZE
TRAMPOLINE_SYM = "_trampoline"


# --------------------------------------------------------------------------
# 1. the images
# --------------------------------------------------------------------------

@dataclass
class Func:
    image: str             # "kernel" or the user program ("Cat")
    name: str
    addr: int
    size: int = 0
    ninstr: int = 0
    aliases: list = field(default_factory=list)
    source: str = "(unattributed)"
    status: str = NONE
    evidence: list = field(default_factory=list)
    callers: int = 0       # instructions of the image that jump to / call its entry

    @property
    def display(self):
        return " = ".join([self.name] + self.aliases)

    @property
    def key(self):
        return f"{self.image}:{self.name}"


INSTR_RE = re.compile(r"^\s*⟨(0x[0-9a-f]+), (\d+), 0x[0-9a-f]+⟩", re.M)
SYM_RE = re.compile(r"^def «([^»]+)» : Nat := (0x[0-9a-f]+)", re.M)


def parse_kernel_image(src):
    """-> (text symbols {name: addr}, [(addr, width)])."""
    a = src.index("namespace MachCSL.KernelSyms")
    b = src.index("end MachCSL.KernelSyms")
    block = src[a:b]
    # the data symbols (objects) follow a marker; only the text ones are functions
    cut = block.find("-- data symbols")
    syms = {m.group(1): int(m.group(2), 16)
            for m in SYM_RE.finditer(block if cut < 0 else block[:cut])}
    instrs = sorted((int(m.group(1), 16), int(m.group(2))) for m in INSTR_RE.finditer(src[:a]))
    return syms, instrs


def parse_user_image(src, prog):
    """-> (symbols {name: addr}, [(addr, width)]) of Xv6/User/<P>Image.lean."""
    a = src.index(f"namespace Xv6.User.{prog}.Sym")
    b = src.index(f"end Xv6.User.{prog}.Sym")
    syms = {m.group(1): int(m.group(2), 16) for m in SYM_RE.finditer(src[a:b])}
    instrs = sorted((int(m.group(1), 16), int(m.group(2))) for m in INSTR_RE.finditer(src[:a]))
    return syms, instrs


def build_functions(image, syms, instrs):
    """Symbols that start an instruction are functions; size them by extent."""
    starts = {a for a, _ in instrs}
    by_addr = defaultdict(list)
    for name, addr in syms.items():
        if addr in starts:
            by_addr[addr].append(name)
    funcs = []
    bounds = sorted(by_addr)
    for i, addr in enumerate(bounds):
        names = sorted(by_addr[addr], key=lambda n: (n.startswith("_"), n))
        f = Func(image=image, name=names[0], addr=addr, aliases=names[1:])
        end = bounds[i + 1] if i + 1 < len(bounds) else 1 << 64
        for a, w in instrs:
            if addr <= a < end:
                f.size += w
                f.ninstr += 1
        funcs.append(f)
    return funcs


def load_images(repo):
    """-> {image: [Func]} for the kernel and every user program."""
    out = {}
    src = open(os.path.join(repo, "Xv6", "KernelImage.lean"), encoding="utf-8").read()
    syms, instrs = parse_kernel_image(src)
    if not syms or not instrs:
        sys.exit("no symbols / instructions parsed from Xv6/KernelImage.lean")
    out["kernel"] = build_functions("kernel", syms, instrs)
    srcs = {"kernel": src}
    for p in USER_PROGS:
        src = open(os.path.join(repo, "Xv6", "User", f"{p}Image.lean"), encoding="utf-8").read()
        syms, instrs = parse_user_image(src, p)
        if not syms or not instrs:
            sys.exit(f"no symbols / instructions parsed from Xv6/User/{p}Image.lean")
        out[p] = build_functions(p, syms, instrs)
        srcs[p] = src
    for img, fs in out.items():
        calls = call_sites(srcs[img])
        for f in fs:
            f.callers = sum(calls.get(n, 0) for n in [f.name] + f.aliases)
    return out


class AddrMap:
    """address -> (Func, offset) within one image."""

    def __init__(self, funcs, trampoline=False):
        self.funcs = sorted(funcs, key=lambda f: f.addr)
        self.addrs = [f.addr for f in self.funcs]
        self.tramp = next((f.addr for f in funcs
                           if TRAMPOLINE_SYM in [f.name] + f.aliases), None) if trampoline else None
        self.end = max((f.addr + f.size for f in funcs), default=0)

    def find(self, a):
        if self.tramp is not None and TRAMPOLINE <= a < TRAMPOLINE + PGSIZE:
            a = self.tramp + (a - TRAMPOLINE)
        import bisect
        i = bisect.bisect_right(self.addrs, a) - 1
        if i < 0:
            return None
        f = self.funcs[i]
        # a function's extent runs to the next entry (padding included)
        nxt = self.addrs[i + 1] if i + 1 < len(self.addrs) else self.end
        if a >= max(nxt, f.addr + f.size):
            return None
        return f, a - f.addr


def attribute_sources(repo, images, xv6=None):
    """Map each function to the xv6 source file that defines it (best effort)."""
    notes = []
    xv6 = xv6 or os.path.join(repo, "xv6-riscv")
    if not os.path.isdir(xv6):
        return ["no xv6-riscv/ checkout: functions are not attributed to source files "
                "(`git clone --depth 1 https://github.com/mit-pdos/xv6-riscv`; the coverage "
                "numbers do not depend on it)"]
    nm = next((c for c in ("riscv64-linux-gnu-nm", "riscv64-unknown-elf-nm",
                           os.environ.get("NM", "")) if c and shutil.which(c)), None)
    for image, funcs in images.items():
        sub = "kernel" if image == "kernel" else "user"
        d = os.path.join(xv6, sub)
        owner = {}
        if image == "kernel":
            wanted = None
        else:
            # a user program is its own file plus the library it is linked with
            wanted = {image.lower(), "ulib", "printf", "umalloc", "usys"}
        objs = sorted(glob.glob(os.path.join(d, "*.o")))
        if nm and objs:
            for o in objs:
                base = os.path.basename(o)[:-2]
                if wanted is not None and base not in wanted:
                    continue
                srcf = next((base + e for e in (".c", ".S", ".pl")
                             if os.path.exists(os.path.join(d, base + e))), base + ".o")
                try:
                    out = subprocess.run([nm, "--defined-only", o], capture_output=True,
                                         text=True, check=True).stdout
                except (subprocess.CalledProcessError, OSError):
                    continue
                for line in out.splitlines():
                    p = line.split()
                    if len(p) >= 3:
                        owner.setdefault(p[-1], srcf)
        missing = {n for f in funcs for n in [f.name] + f.aliases if n not in owner}
        if missing:
            for path in sorted(glob.glob(os.path.join(d, "*.c")) + glob.glob(os.path.join(d, "*.S"))
                               + glob.glob(os.path.join(d, "*.pl"))):
                base = os.path.basename(path)
                if wanted is not None and base.rsplit(".", 1)[0] not in wanted:
                    continue
                text = open(path, errors="replace").read()
                for n in list(missing):
                    if n in owner:
                        continue
                    if (re.search(rf"^{re.escape(n)}\s*(?:\(|:)", text, re.M)
                            or re.search(rf'^entry\("{re.escape(n)}"\)', text, re.M)):
                        owner[n] = base
        unattr = 0
        for f in funcs:
            for n in [f.name] + f.aliases:
                if n in owner:
                    f.source = owner[n]
                    break
            else:
                unattr += 1
        if unattr:
            notes.append(f"{image}: could not attribute {unattr} function(s) to a source file")
    return notes


# --------------------------------------------------------------------------
# 2. the proofs (envfacts.tsv)
# --------------------------------------------------------------------------

@dataclass
class Pin:
    pred: str      # pcIs | urun
    prog: str      # user program, "-" none, "*" several
    addr: object   # int | "ret" | "sym"
    entry: bool    # a top-level premise of the statement


def parse_pins(s):
    out = []
    for tok in s.split():
        pred, prog, addr, lvl = tok.split(":")
        out.append(Pin(pred, prog, int(addr, 16) if addr.startswith("0x") else addr, lvl == "e"))
    return out


@dataclass
class Facts:
    roots: list = field(default_factory=list)                 # [(name, kind)]
    ifaces: dict = field(default_factory=lambda: defaultdict(list))   # iface -> [(field, [Pin], {addr})]
    links: dict = field(default_factory=lambda: defaultdict(list))    # iface -> [(thm, module, reach)]
    direct: list = field(default_factory=list)                # [(thm, module, reach, [Pin])]
    decls: dict = field(default_factory=dict)                 # name -> (module, kind, reach)
    ndecls: int = 0
    nmodules: int = 0
    cone: int = 0


def load_facts(path):
    f = Facts()
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            p = raw.rstrip("\n").split("\t")
            k = p[0]
            if k == "ROOT":
                f.roots.append((p[1], p[2]))
            elif k == "G":
                f.nmodules += 1
            elif k == "C":
                f.ndecls += 1
                f.decls[p[2]] = (p[1], p[3], int(p[5]))
            elif k == "I":
                ment = {int(x, 16) for x in (p[4].split() if len(p) > 4 else [])}
                f.ifaces[p[1]].append((p[2], parse_pins(p[3]), ment))
            elif k == "L":
                f.links[p[4]].append((p[1], p[2], int(p[3])))
            elif k == "T":
                f.direct.append((p[1], p[2], int(p[3]), parse_pins(p[4])))
            elif k == "N":
                f.cone = int(p[2])
    return f


def is_link_module(mod):
    """`Link<F>` (the Spec/Proof/Link discipline) or `<X>Link` (the user
    programs' library links: CatPrintfLink, InitPrintfLink, ...)."""
    last = mod.split(".")[-1]
    return last.startswith("Link") or last.endswith("Link")


def short(name):
    return name[4:] if name.startswith("Xv6.") else name


# --------------------------------------------------------------------------
# 3. joining the two sides
# --------------------------------------------------------------------------

def resolve(pin, maps):
    """-> (Func, offset) or None.  A kernel pin is a `pcIs`; a user pin is a
    `urun` whose address names exactly one program's constants."""
    if not isinstance(pin.addr, int):
        return None
    if pin.pred == "pcIs":
        return maps["kernel"].find(pin.addr)
    if pin.prog in maps:
        return maps[pin.prog].find(pin.addr)
    return None


def shape(pins, maps):
    """A contract's (entry function, offset, whole?) for each entry pin.

    whole: the continuation pins never land strictly inside the entry
    function -- they are the caller's return address, another function's
    entry, or absent."""
    out = []
    for e in pins:
        if not e.entry:
            continue
        r = resolve(e, maps)
        if r is None:
            continue
        f, off = r
        inside = False
        for c in pins:
            if c is e or c.entry:
                continue
            rc = resolve(c, maps)
            if rc is not None and rc[0] is f and rc[1] != 0 and c.pred == e.pred:
                inside = True
        out.append((f, off, off == 0 and not inside))
    return out


def best_theorem(facts, iface):
    """The strongest theorem concluding `iface`: a reached Link theorem, else
    a Link theorem, else a reached one, else any."""
    thms = facts.links.get(iface, [])
    link = [t for t in thms if is_link_module(t[1])]
    return (next((t for t in link if t[2] == 1), None) or (link[0] if link else None)
            or next((t for t in thms if t[2] == 1), None) or (thms[0] if thms else None))


def apply_manifest(images, facts, manifest, maps):
    """Whole-function contracts that are NOT entered through a pc premise: a
    trap vector is entered by a trap, so its contract is a handler spec that
    NAMES the vector's address instead of pinning `pcIs` at it.  No rule can
    find those, so they are declared (tools/ci/coverage_manifest.txt) -- and
    every declaration is VERIFIED, so it cannot rot: the theorem must exist,
    sit in a Link module, be reached, conclude an interface, and that
    interface must name the function's entry address.  -> [error]"""
    errs = []
    by_key = {f.key: f for fs in images.values() for f in fs}
    thm_iface = defaultdict(list)
    for iface, thms in facts.links.items():
        for t in thms:
            thm_iface[t[0]].append(iface)
    for key, (thm, why) in manifest.items():
        f = by_key.get(key)
        where = f"coverage_manifest.txt: {key}"
        if f is None:
            errs.append(f"{where}: not a function of the image -- drop the stale row")
            continue
        d = facts.decls.get(thm)
        if d is None or d[1] != "thm":
            errs.append(f"{where}: `{thm}` is not a theorem of the tree")
            continue
        if not is_link_module(d[0]):
            errs.append(f"{where}: `{thm}` is in {d[0]}, not a Link module")
            continue
        ifaces = thm_iface.get(thm, [])
        named = False
        for iface in ifaces:
            for _fld, _pins, ment in facts.ifaces.get(iface, []):
                for a in ment:
                    r = maps[f.image].find(a)
                    if r is not None and r[0] is f and r[1] == 0:
                        named = True
        if not named:
            errs.append(f"{where}: the interface `{thm}` concludes does not name the entry "
                        f"address of {f.name} (0x{f.addr:x})")
            continue
        st = PROVEN if d[2] == 1 else UNREACHED
        f.evidence.append(dict(kind="whole function (declared)", what=short(ifaces[0]), status=st,
                               how=f"linked by {short(thm)} ({d[0]})"
                                   + (", reached" if d[2] == 1 else ", but no top theorem reaches it")
                                   + f"; {why}"))
        if STATUS_ORDER[st] < STATUS_ORDER[f.status]:
            f.status = st
    return errs


def classify(images, facts, manifest=None):
    maps = {img: AddrMap(fs, trampoline=(img == "kernel")) for img, fs in images.items()}

    def note(f, status, ev):
        ev["status"] = status
        f.evidence.append(ev)
        if STATUS_ORDER[status] < STATUS_ORDER[f.status]:
            f.status = status

    unresolved = 0
    # -- interfaces, and the theorems concluding them -------------------------
    for iface, fields in facts.ifaces.items():
        best = best_theorem(facts, iface)
        for fld, pins, _ment in fields:
            for f, off, whole in shape(pins, maps):
                what = short(iface) + ("" if fld == "-" else "." + fld)
                if not whole:
                    note(f, PARTIAL, dict(kind=f"fragment at +0x{off:x}", what=what, how=(
                        f"concluded by {short(best[0])} ({best[1]})" if best else "stated only")))
                    continue
                if best is None:
                    note(f, ASSUMED, dict(kind="whole function", what=what,
                                          how="interface stated; no theorem concludes it"))
                elif is_link_module(best[1]) and best[2] == 1:
                    note(f, PROVEN, dict(kind="whole function", what=what,
                                         how=f"linked by {short(best[0])} ({best[1]}), reached"))
                elif is_link_module(best[1]):
                    note(f, UNREACHED, dict(kind="whole function", what=what, how=(
                        f"linked by {short(best[0])} ({best[1]}), but no top theorem reaches it")))
                elif best[2] == 1:
                    note(f, UNLINKED, dict(kind="whole function", what=what, how=(
                        f"proved by {short(best[0])} ({best[1]}) and reached, but no Link* module "
                        "concludes it")))
                else:
                    note(f, PARTIAL, dict(kind="whole function", what=what, how=(
                        f"proved by {short(best[0])} ({best[1]}), neither linked nor reached")))
            if any(isinstance(p.addr, int) and p.pred == "urun" and p.prog not in maps
                   for p in pins if p.entry):
                unresolved += 1
    # -- theorems that pin a pc in their own statement -------------------------
    for thm, mod, reach, pins in facts.direct:
        for f, off, whole in shape(pins, maps):
            if whole and is_link_module(mod):
                st = PROVEN if reach == 1 else UNREACHED
                note(f, st, dict(kind="whole function", what=short(thm), how=(
                    f"stated in {mod}" + (", reached" if reach == 1 else
                                         ", but no top theorem reaches it"))))
            elif f.status in (NONE, PARTIAL):
                # a proof lemma about (part of) the function
                f._lemmas = getattr(f, "_lemmas", 0) + 1
                f._lemma_mods = getattr(f, "_lemma_mods", set()) | {mod}
    for fs in images.values():
        for f in fs:
            n = getattr(f, "_lemmas", 0)
            if n and f.status in (NONE, PARTIAL) and not f.evidence:
                mods = sorted(f._lemma_mods)
                note(f, PARTIAL, dict(kind="referenced", what=f"{n} lemma(s)",
                                      how="in " + ", ".join(mods[:3]) + (" ..." if len(mods) > 3 else "")))
    errors = apply_manifest(images, facts, manifest or {}, maps)
    # one line per fact, and only the facts that carry the function's status:
    # a proven function's contract is also "stated" by its body definition,
    # which is not news
    for fs in images.values():
        for f in fs:
            seen, ev = set(), []
            for e in f.evidence:
                k = (e["what"], e["how"])
                if k not in seen and e["status"] == f.status:
                    seen.add(k)
                    ev.append(e)
            f.evidence = ev
    return unresolved, errors


# --------------------------------------------------------------------------
# 4. the floor
# --------------------------------------------------------------------------

def read_rows(path):
    """`<image>:<function>  # reason` rows -> {key: reason}."""
    rows = {}
    if os.path.exists(path):
        for raw in open(path, encoding="utf-8"):
            body, _, why = raw.partition("#")
            body = body.strip()
            if body:
                rows[body] = why.strip()
    return rows


def read_manifest(path):
    """`<image>:<function> <theorem>  # reason` rows -> {key: (theorem, reason)}."""
    rows = {}
    if os.path.exists(path):
        for raw in open(path, encoding="utf-8"):
            body, _, why = raw.partition("#")
            parts = body.split()
            if len(parts) == 2:
                rows[parts[0]] = (parts[1], why.strip())
            elif parts:
                sys.exit(f"{path}: cannot read row `{raw.strip()}`")
    return rows


CALL_RE = re.compile(r"^\s*-- \S+\t.*?\b[0-9a-f]+ <([A-Za-z0-9_.$]+)>\s*$", re.M)


def call_sites(src):
    """{function: number of instructions of the dump whose objdump line
    targets `<function>` exactly} -- jumps and calls to its entry."""
    out = defaultdict(int)
    for m in CALL_RE.finditer(src):
        out[m.group(1)] += 1
    return out


def check_floor(images, facts, allow, baseline):
    """-> [error].  See the module docstring (EXIT STATUS)."""
    errs = []
    by_key = {}
    for fs in images.values():
        for f in fs:
            by_key[f.key] = f
            for a in f.aliases:
                by_key[f"{f.image}:{a}"] = f
    tops = [r for r, k in facts.roots if k == "top"]
    if not tops:
        errs.append("envfacts names no top theorem: the cone is empty, so nothing is 'reached'")
    if facts.cone < 1000 or not facts.ifaces:
        errs.append(f"envfacts looks empty (cone {facts.cone}, {len(facts.ifaces)} interfaces): "
                    "was it produced from a built tree?")
    for key, why in allow.items():
        f = by_key.get(key)
        if f is None:
            errs.append(f"coverage_allow.txt: {key} is not a function of the image -- drop the stale row")
        elif f.status == PROVEN:
            errs.append(f"coverage_allow.txt: {key} is proven and linked now -- drop the row")
        elif not why:
            errs.append(f"coverage_allow.txt: {key} has no reason (`{key}  # why`)")
    for f in images["kernel"]:
        if f.status != PROVEN and f.key not in allow:
            ev = "; ".join(f"{e['what']}: {e['how']}" for e in f.evidence) or "nothing mentions it"
            ev += f"; {f.callers} call site(s) in the image"
            errs.append(f"kernel function `{f.display}` is {f.status}, not proven and linked ({ev}); "
                        "prove and link it, or add a row with the reason to tools/ci/coverage_allow.txt")
    for key in baseline:
        f = by_key.get(key)
        if f is None:
            errs.append(f"coverage_user_baseline.txt: {key} is not a function of the image any more "
                        "(re-dumped image? rerun with --update-baseline and review the diff)")
        elif f.status != PROVEN:
            errs.append(f"user function `{key}` was proven and linked (baseline) and is now {f.status}")
    return errs


# --------------------------------------------------------------------------
# 5. rendering
# --------------------------------------------------------------------------

def totals(fs):
    return (len(fs), sum(f.size for f in fs),
            sum(1 for f in fs if f.status == PROVEN),
            sum(f.size for f in fs if f.status == PROVEN))


def pct(a, b):
    return 100.0 * a / b if b else 0.0


def group(fs):
    by = defaultdict(list)
    for f in fs:
        by[f.source].append(f)
    for v in by.values():
        v.sort(key=lambda f: f.addr)
    return sorted(by.items(), key=lambda kv: (-sum(1 for f in kv[1] if f.status == PROVEN), kv[0]))


def summarize(images):
    rows = []
    for img, fs in images.items():
        n, b, pn, pb = totals(fs)
        c = {s: sum(1 for f in fs if f.status == s) for s in STATUS_ORDER}
        rows.append((img, n, b, pn, pb, c))
    return rows


def render_md(rep, verbose):
    images, facts = rep["images"], rep["facts"]
    L = []
    w = L.append
    w("## Proof coverage (Lean)\n")
    kn, kb, kpn, kpb = totals(images["kernel"])
    users = [f for img, fs in images.items() if img != "kernel" for f in fs]
    un, ub, upn, upb = totals(users)
    w(f"The pinned kernel image (`Xv6/KernelImage.lean`) and the seven user programs "
      f"(`Xv6/User/*Image.lean`), against {facts.nmodules} modules / {facts.ndecls} declarations; "
      f"`proven` = a `Link*` theorem concludes a whole-function contract AND is reached from "
      + ", ".join(f"`{short(r)}`" for r, k in facts.roots if k == "top") + ".\n")
    w("| image | functions | proven | text bytes | proven bytes | other |")
    w("|---|---|---|---|---|---|")
    for img, n, b, pn, pb, c in summarize(images):
        other = ", ".join(f"{v} {s}" for s, v in c.items() if v and s != PROVEN) or "—"
        name = "**kernel**" if img == "kernel" else f"`{img.lower()}`"
        w(f"| {name} | {n} | {pn} ({pct(pn, n):.0f}%) | {b} | {pb} ({pct(pb, b):.0f}%) | {other} |")
    w(f"| all user programs | {un} | {upn} ({pct(upn, un):.0f}%) | {ub} | {upb} ({pct(upb, ub):.0f}%) | |")
    w("")
    if rep["errors"]:
        w("### :x: Coverage check failed\n")
        for e in rep["errors"]:
            w(f"- {e}")
        w("")
    allow = rep["allow"]

    def table(fs):
        w("| | function | addr | bytes | status | evidence |")
        w("|---|---|---|---|---|---|")
        for f in fs:
            ev = "; ".join(f"`{e['what']}` — {e['how']}" for e in f.evidence[:3]) or "—"
            if len(f.evidence) > 3:
                ev += f"; +{len(f.evidence) - 3} more"
            if f.status != PROVEN:
                ev += f" · {f.callers} call site(s) in the image"
            if f.key in allow:
                ev += f" · allowlisted: {allow[f.key]}"
            w(f"| {STATUS_MARK[f.status]} | `{f.display}` | `0x{f.addr:08x}` | {f.size} | "
              f"{f.status} | {ev.replace('|', chr(92) + '|')} |")
        w("")

    w("### Kernel\n")
    for src, fs in group(images["kernel"]):
        n, b, pn, pb = totals(fs)
        full = pn == n
        w(f"<details{'' if full else ' open'}><summary><code>{src}</code> — {pn}/{n} functions, "
          f"{pb}/{b} bytes ({pct(pb, b):.0f}%)</summary>\n")
        table(fs)
        w("</details>\n")
    w("### User programs\n")
    w("A user program is linked with the whole library; a function no verified program path "
      "calls is not proved (and is not claimed). The floor is "
      "`tools/ci/coverage_user_baseline.txt`.\n")
    for img, fs in images.items():
        if img == "kernel":
            continue
        n, b, pn, pb = totals(fs)
        w(f"<details><summary><code>{img.lower()}</code> — {pn}/{n} functions, "
          f"{pb}/{b} bytes ({pct(pb, b):.0f}%)</summary>\n")
        shown = sorted(fs, key=lambda f: f.addr)
        if not verbose:
            rest = [f for f in shown if f.status == NONE]
            shown = [f for f in shown if f.status != NONE]
        table(shown)
        if not verbose and rest:
            w(f"No proof ({len(rest)}): " + ", ".join(f"`{f.name}`" for f in rest) + "\n")
        w("</details>\n")
    if rep["notes"]:
        w("### Notes\n")
        for n in rep["notes"]:
            w(f"- {n}")
    return "\n".join(L)


def render_text(rep, verbose):
    images, facts = rep["images"], rep["facts"]
    L = []
    w = L.append
    w("xv6 -- Lean proof coverage")
    w("=" * 64)
    w(f"proofs : {facts.nmodules} modules, {facts.ndecls} declarations, cone {facts.cone}")
    w("roots  : " + ", ".join(short(r) for r, k in facts.roots if k == "top"))
    w("")
    for img, n, b, pn, pb, c in summarize(images):
        other = ", ".join(f"{v} {s}" for s, v in c.items() if v and s != PROVEN)
        w(f"{img.lower():<10} {pn:>3}/{n:<3} functions proven {pct(pn, n):>5.1f}%   "
          f"{pb:>6}/{b:<6} bytes {pct(pb, b):>5.1f}%" + (f"   ({other})" if other else ""))
    w("")
    w(f"legend : {STATUS_MARK[PROVEN]} proven  ? unreached/unlinked  {STATUS_MARK[ASSUMED]} assumed  "
      f"{STATUS_MARK[PARTIAL]} partial")
    w("")
    for img, fs in images.items():
        for src, gfs in (group(fs) if img == "kernel" else [(img.lower(), sorted(fs, key=lambda f: f.addr))]):
            n, b, pn, pb = totals(gfs)
            w(f"{src:<18} {pn:>3}/{n:<3} fns  {pb:>6}/{b:<6} bytes {pct(pb, b):>5.1f}%")
            for f in gfs:
                if not verbose and f.status in (PROVEN, NONE):
                    continue
                w(f"  {STATUS_MARK[f.status]} {f.display:<24} 0x{f.addr:08x} {f.size:>5}B  {f.status}")
                for e in f.evidence if verbose or f.status != PROVEN else []:
                    w(f"        {e['kind']}: {e['what']}  {e['how']}")
    w("")
    if rep["errors"]:
        w("COVERAGE CHECK FAILED")
        w("-" * 64)
        for e in rep["errors"]:
            w(f"  {e}")
        w("")
    for n in rep["notes"]:
        w(f"note: {n}")
    return "\n".join(L)


def render_json(rep, verbose):
    images = rep["images"]
    return json.dumps({
        "roots": rep["facts"].roots,
        "summary": [dict(image=img, functions=n, bytes=b, proven=pn, proven_bytes=pb, by_status=c)
                    for img, n, b, pn, pb, c in summarize(images)],
        "images": {img: [dict(name=f.name, aliases=f.aliases, addr=f"0x{f.addr:x}", bytes=f.size,
                              instructions=f.ninstr, source=f.source, status=f.status,
                              evidence=f.evidence) for f in sorted(fs, key=lambda f: f.addr)]
                   for img, fs in images.items()},
        "errors": rep["errors"], "notes": rep["notes"]}, indent=1)


# --------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--facts", default=None,
                    help="envfacts.tsv from tools/ci/envfacts.sh (default: .lake/ci/envfacts.tsv)")
    ap.add_argument("--format", default="text", choices=("text", "md", "json"))
    ap.add_argument("--out")
    ap.add_argument("--xv6", help="an xv6-riscv checkout for source-file attribution "
                                  "(default: <repo>/xv6-riscv; optional)")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="list every function, with its evidence")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 unless every kernel function is proven and linked (minus "
                         "tools/ci/coverage_allow.txt) and no baselined user function regressed")
    ap.add_argument("--update-baseline", action="store_true",
                    help="rewrite tools/ci/coverage_user_baseline.txt from the current state")
    a = ap.parse_args(argv)

    repo = os.path.abspath(a.repo)
    facts_path = a.facts or os.path.join(repo, ".lake", "ci", "envfacts.tsv")
    if not os.path.exists(facts_path):
        sys.exit(f"proof_coverage: {facts_path} does not exist; produce it with "
                 "tools/ci/envfacts.sh on a built tree")
    images = load_images(repo)
    facts = load_facts(facts_path)
    notes = attribute_sources(repo, images, a.xv6)
    manifest = read_manifest(os.path.join(repo, "tools", "ci", "coverage_manifest.txt"))
    unresolved, manifest_errors = classify(images, facts, manifest)
    if unresolved:
        notes.append(f"{unresolved} user contract(s) pin an address that names no single program "
                     "(generic library contracts); they are credited to no function")
    allow_path = os.path.join(repo, "tools", "ci", "coverage_allow.txt")
    base_path = os.path.join(repo, "tools", "ci", "coverage_user_baseline.txt")
    allow = read_rows(allow_path)
    if a.update_baseline:
        keys = sorted(f.key for img, fs in images.items() if img != "kernel"
                      for f in fs if f.status == PROVEN)
        with open(base_path, "w", encoding="utf-8") as fh:
            fh.write("# The user functions that are proven and linked (tools/proof_coverage.py).\n"
                     "# `--check` fails if one of them stops being so: coverage may grow, never\n"
                     "# shrink.  Regenerate with `tools/proof_coverage.py --update-baseline`\n"
                     "# and review the diff -- a removed row is a lost proof.\n")
            fh.write("\n".join(keys) + "\n")
        print(f"wrote {base_path} ({len(keys)} functions)", file=sys.stderr)
    baseline = read_rows(base_path)
    errors = manifest_errors + check_floor(images, facts, allow, baseline)
    rep = dict(images=images, facts=facts, notes=notes, errors=errors if a.check else [],
               allow=allow)
    text = {"text": render_text, "md": render_md, "json": render_json}[a.format](rep, a.verbose)
    if a.out:
        with open(a.out, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
        print(f"wrote {a.out}", file=sys.stderr)
    else:
        print(text)
    kn, kb, kpn, kpb = totals(images["kernel"])
    users = [f for img, fs in images.items() if img != "kernel" for f in fs]
    un, ub, upn, upb = totals(users)
    print(f"coverage: kernel {kpn}/{kn} functions, {kpb}/{kb} bytes proven, linked and reached; "
          f"user programs {upn}/{un} functions, {upb}/{ub} bytes", file=sys.stderr)
    if a.check and errors:
        for e in errors:
            print(f"proof_coverage: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
