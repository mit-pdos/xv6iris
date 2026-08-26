#!/usr/bin/env python3
"""ctx_convert.py -- the TSO-port context-conversion sweeps (tso-port.md leg M).

Modes:
  caps [--apply]      M2 fallout: the CAPABILITY-DESTRUCT repair class.
                      `own_context` is a new conjunct of `IntrDefs.sie_cap`,
                      so an opener whose trailing name absorbed the
                      remainder now fails with "iIntuitionistic: not
                      persistent" -- bind the token instead, and re-frame
                      it at the matching rebuild.  Both halves, because a
                      destruct alone silently drops the thread's identity
                      (the leak the compiler does NOT find).

  NOTE: `binders` reaches a FIXPOINT IN TWO PASSES, and you must run it
  until a dry run reports 0 -- whether a file already has a section-level
  context is decided before the section binders are added, so a file that
  gains one in pass 1 only has its now-shadowing inline binders stripped in
  pass 2.  A dry run printing nothing is the signal that the tree is stable.

  binders [--apply]   M1: add the ambient `{XI : CurCtx}` binder beside every
                      CpuId binder (section Context lines and inline
                      definition binders) in files that mention the
                      sie_cap_gpr/context vocabulary, and add the TsoCtx
                      import.  Idempotent.  Default is a dry-run report.

  ambient [--apply]   M1 NOTATION FLIP: give every Section an ambient
                      `{XI : CurCtx}` if (a) the file imports TsoCtx (so its
                      ↦ₘ/↦₈ notations are the flipped, cur_ctx-relative
                      ones), (b) the section's own span uses the flipped
                      vocabulary (↦ₘ/↦₈/↦c/cur_ctx/is_lock family), and
                      (c) no enclosing section already binds CurCtx.  This
                      is the pass `binders` cannot do: `binders` keys on
                      CpuId vocabulary, and the ~30 invariant-definition
                      files (KallocInv, LogInv, ConsoleInv, ...) are
                      hart-free -- after the flip their ↦-statements need a
                      context with no hart in sight.  SECTION binders only:
                      they self-clean (a definition captures XI only if it
                      uses it), which is what makes over-inclusion safe;
                      the SchedCtx/boot lesson says a TOP-LEVEL phantom
                      binder is what breaks adequacy, so top-level
                      declarations are left to fail loudly and be fixed by
                      hand.  Boot/adequacy files are blacklisted: their
                      statements deliberately stay on the raw/explicit-ξ
                      side of the seam.

The per-function spec conversion (`↦ₘ`→`↦c`) and call-site patch modes are
added as they stabilize; the reference diffs are SpecMemset.v (spec) and
ProofBalloc.v (call site).
"""
import argparse, re, sys, pathlib

IRIS = pathlib.Path(__file__).resolve().parent.parent / "iris"

# A file is in scope if it states or opens the bundle, or already talks the
# context vocabulary.  (Files that merely IMPORT such files but never state
# the bundle need no binder: instances are only needed where cur_ctx-mentioning
# terms are elaborated.)
VOCAB = re.compile(r"sie_cap_gpr|sie_cap_of|sie_cap |sie_arm|intr_res|ihs_"
                   r"|own_context|ctx_pointsto|cur_ctx|↦c")

# Files BELOW TsoCtx in the import order (importing it would cycle), plus
# files that are deliberately context-TRANSPARENT: [wp_next] quantifies the
# CPU and must NOT bind the context -- the design point is that ξ is fixed
# across it (tso-port.md).
BLACKLIST = {"RiscvLang.v", "RiscvPtsto.v", "Ktier.v", "TsoMem.v",
             "TsoLitmus.v", "TsoCtx.v", "TsoCtxShim.v", "TsoCtxTwin.v",
             "WpNext.v",
             # hart-indexed but MEMORY-FREE: the register file's tp slot has
             # nothing to do with owning memory, and [rget_hart_indep]
             # quantifies two harts explicitly, so it could not infer a
             # context even if one were meaningful.
             "HartTp.v",
             # register/instruction level: PC + GPR file.  Hart-indexed,
             # thread-INdependent -- a context binder here is a phantom that
             # propagates into every consumer.  (StackOwn LEFT this list at
             # the M1 flip: a stack FRAME is thread data, and keeping it raw
             # made every function proof's prologue/epilogue a shim seam.)
             "InstrBytes.v", "WpGpr.v",
             # [cpu_ctx_free] (top-level, above the section) is the raw 14
             # save-area words at [a_cpu_ctx cid_word] with NOBODY parked in
             # them -- per-cpu geometry, no thread of control; its phantom
             # binder was the one that dragged [BootChain.boot_hart_res] onto
             # the axis and broke adequacy's eight-hart unification.  (The
             # SECTION below it does need [XI] and keeps its binder.)
             "SchedCtx.v"}

def strip_comments(text):
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1; i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1; i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)

# Section-level: the four observed shapes (732+38+4+4), never in comments --
# anchored to lines that BEGIN with optional space then `Context`.
SECTION_RE = re.compile(
    r"^(\s*)Context (`\{GEN : GenId\} )?`\{(CID0?) : CpuId\}\.\s*$")

# Inline definition/parameter binders.  The hart binder is spelled with many
# NAMES (CID, CID0, CIDa/CIDb on a hart-SHIFT lemma, CIDx, CIDq, ...), and a
# declaration may carry SEVERAL of them -- a shift lemma names the hart it
# comes from and the one it goes to.  The context is bound ONCE, after the
# LAST of them: there is one thread of control however many harts the
# statement mentions, which is the whole point of the index.
ANYCID_RE = re.compile(r"`\{CID\w* : CpuId\}")

# A declaration may instead bind a RAW hart, `(CID0 : CPU)`, and rebind the
# class INSIDE a [wp_next] continuation (`fun CID : CpuId => ...`).  Those
# still need an ambient context, and the binder placement says the design out
# loud: the HART is rebound inside the continuation because a trap can move
# it; the CONTEXT binds OUTSIDE, because it does not change.
RAWCPU_RE = re.compile(r"(?<!CurCtx\} )\(CID0 : CPU\)")

def convert_file(path: pathlib.Path, apply: bool):
    if path.name in BLACKLIST:
        return None
    text = path.read_text()
    orig = text
    # SECTION-AWARE, not file-aware: "this file has a section that binds the
    # context" does NOT mean "this declaration is inside it".  A top-level
    # declaration in such a file still needs its own binder, and an inline
    # one INSIDE the section would shadow.  Track the nesting.
    depth_ctx = []          # per open Section: does it (or an outer) bind XI?
    nsec = nin = 0
    out_lines = []
    for line in text.splitlines(keepends=True):
        st = line.lstrip()
        if st.startswith("Section "):
            depth_ctx.append(depth_ctx[-1] if depth_ctx else False)
        elif st.startswith("End ") and depth_ctx:
            depth_ctx.pop()
        elif st.startswith("Context ") and "CurCtx" in line and depth_ctx:
            depth_ctx[-1] = True
        has_section_ctx = bool(depth_ctx) and depth_ctx[-1]
        m = SECTION_RE.match(line)
        if m and "CurCtx" not in line:
            indent, gen, cid = m.group(1), m.group(2) or "", m.group(3)
            line = (f"{indent}Context {gen}`{{{cid} : CpuId}} "
                    f"`{{XI : CurCtx}}.\n")
            nsec += 1
        elif (not has_section_ctx) and "Context" not in line \
                and ("CpuId" in line or "(CID0 : CPU)" in line) \
                and not line.lstrip().startswith("(*"):
            k = 0
            if "CurCtx" not in line:
                ms = list(ANYCID_RE.finditer(line))
                if ms:
                    e = ms[-1].end()
                    line = line[:e] + " `{XI : CurCtx}" + line[e:]
                    k = 1
            nin += k
            if not k and "CurCtx" not in line and re.match(
                    r"\s*(Definition|Lemma|Theorem|Parameter|Fixpoint)\s", line):
                line, k2 = RAWCPU_RE.subn(r"`{XI : CurCtx} (CID0 : CPU)", line)
                nin += k2
        out_lines.append(line)
    text = "".join(out_lines)
    if has_section_ctx:
        keep, nstrip = [], 0
        for line in text.splitlines(keepends=True):
            if not line.lstrip().startswith("Context "):
                line, k = re.subn(r"(`\{CID0? : CpuId\}) `\{XI : CurCtx\}",
                                  r"\1", line)
                nstrip += k
            keep.append(line)
        text = "".join(keep)
        nin -= nstrip

    added_import = False
    if (nsec or nin) and "Require Import TsoCtx" not in text:
        # after the last Require line of the header block
        lines = text.splitlines(keepends=True)
        # the last line that TERMINATES a Require/From statement -- a
        # multi-line Require continues onto following lines, and inserting
        # between them yields "Cannot find a physical path bound to logical
        # path Require", which reads like a missing library and is not.
        last_req, in_req = None, False
        for i, l in enumerate(lines):
            if l.startswith(("Require ", "From ")):
                in_req = True
            if in_req and l.rstrip().endswith("."):
                last_req, in_req = i, False
        if last_req is not None:
            lines.insert(last_req + 1, "Require Import TsoCtx.\n")
            text = "".join(lines)
            added_import = True

    if text == orig:
        return None
    if apply:
        path.write_text(text)
    return (nsec, nin, added_import)

# The capability opener, and the rebuild that must give the token back.
# Deliberately ANCHORED on the full 5-slot shape: a shorter opener is a
# DIFFERENT resource and must not be touched.
CAP_OPEN = '(Hstk & Htr & Harm & #Htc & #Hwit)'
CAP_OPEN_FIXED = '(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)'
CAP_FRAME = '"Hstk Htr Harm Htc Hwit"'
CAP_FRAME_FIXED = '"Hstk Htr Harm Hctx Htc Hwit"'

def convert_caps(path: pathlib.Path, apply: bool):
    text = path.read_text()
    if CAP_OPEN not in text:
        return None
    n_open = text.count(CAP_OPEN)
    text2 = text.replace(CAP_OPEN, CAP_OPEN_FIXED)
    n_frame = text2.count(CAP_FRAME)
    text2 = text2.replace(CAP_FRAME, CAP_FRAME_FIXED)
    # an iSplitL feeding such a rebuild has to hand the token over too
    n_split = text2.count('iSplitL "Hstk Htr Harm".')
    text2 = text2.replace('iSplitL "Hstk Htr Harm".', 'iSplitL "Hstk Htr Harm Hctx".')
    if text2 == text:
        return None
    if apply:
        path.write_text(text2)
    return (n_open, n_frame, n_split)

# ------------------------------------------------------------- ambient

# the flipped vocabulary: any of these inside a section means its
# definitions/statements elaborate cur_ctx (directly, or through is_lock's
# implicit XI, or through a ctx-parametric definition) and the section needs
# the ambient binder.  The definition names are HARVESTED as conversions
# land -- vocabulary scanning cannot see ctx-ness that arrives through a
# converted definition, so each new ctx-parametric family gets its heads
# added here (the build's "?XI : CurCtx" existential errors are the signal).
FLIPPED = re.compile(r"↦ₘ|↦₈|↦c|cur_ctx|is_lock|lock_openable|lock_inv|<\{"
                     r"|byte_any|word_at|page_own|page_rest|page_head8"
                     r"|run_page|freelist_chain|kmem_res|buf_own|bb_bytes"
                     r"|bb_word|wordw_pointsto|kernel_data_window"
                     r"|kernel_data_bytes|bytes_own|stat_at|fentry_raw"
                     r"|ftable_res|free_slot_res|free_cell_res|uw_saved"
                     r"|uw_slot|console_caps|is_conslock|is_txlock"
                     r"|disk_res_at|lw_res|lw_close|file_core|file_fields"
                     r"|fd_slot|proc_priv|is_pipe|pipe_ref|fentry|disk_res"
                     r"|park_cap|park_chan|park_token|park_pkg|park_env|park_child")

# boot/adequacy: statements stay raw or explicit-ξ; a phantom ambient here is
# the boot_hart_res/eight-hart lesson.  (BootCarve talks to the flipped world
# through qualified TsoCtxShim names, no ambient.)
AMBIENT_BLACKLIST = {"RiscvAdequacy.v", "SystemAdequacy.v", "BootChain.v",
                     "BootShared.v", "BootBridge.v", "BootCarve.v",
                     "BootCarveMain.v", "DiskBoot.v", "FsCfgBoot.v",
                     "TsoCtx.v", "TsoCtxShim.v", "TsoCtxTwin.v",
                     "TsoCtxTwin2.v", "TsoCtxRehearsal.v"}

def convert_ambient(path: pathlib.Path, apply: bool):
    if path.name in AMBIENT_BLACKLIST or path.name in BLACKLIST:
        return None
    text = path.read_text()
    if "Require Import TsoCtx" not in text:
        return None            # notations not flipped in this file
    # a file that binds XI INLINE on declarations manages its own axis --
    # a section binder would clash ("XI is already used"), and stripping
    # the inline binder breaks module-signature argument order (the
    # ProofProcMapstacks lesson).  Skip; its uncovered sections surface as
    # build errors and are fixed by hand.
    if re.search(r"^(?!\s*Context).*`\{XI : CurCtx\}", text, re.M):
        return "skip-inline"
    lines = text.splitlines(keepends=True)
    stripped = [strip_comments(l) for l in lines]

    # section spans, nesting-aware
    stack, sections = [], []   # sections: (start, end, name)
    for i, l in enumerate(stripped):
        st = l.strip()
        m = re.match(r"Section (\w+)\.", st)
        if m:
            stack.append((i, m.group(1)))
        elif st.startswith("End ") and stack:
            j, name = stack.pop()
            if st == f"End {name}.":
                sections.append((j, i, name))

    def span_has(rx, a, b):
        return any(rx.search(stripped[k]) for k in range(a, b + 1))

    inserts = []               # line index to insert AFTER
    for (a, b, _name) in sorted(sections):
        if not span_has(FLIPPED, a, b):
            continue
        if any(oa < a and b < ob and any(
                   "Context" in stripped[k] and "CurCtx" in stripped[k]
                   for k in range(oa, ob))
               for (oa, ob, _n) in sections):
            pass               # an outer binder covers inner sections too --
                               # but only if it precedes; checked below
        # own or enclosing binder already present?
        covered = False
        for (oa, ob, _n) in sections:
            if oa <= a and b <= ob:
                for k in range(oa, min(b, ob) + 1):
                    s = stripped[k].strip()
                    if s.startswith("Context") and "CurCtx" in s:
                        covered = True
        if covered:
            continue
        # insertion point: after the section's leading Context/blank prologue
        ins = a
        k = a + 1
        while k <= b:
            s = stripped[k].strip()
            if s == "" or s.startswith("Context ") or s.startswith("Import ") \
               or s.startswith("Local Open Scope") or s.startswith("Implicit Types"):
                if s.startswith("Context "):
                    ins = k
                k += 1
                continue
            break
        if ins == a:
            ins = a            # no Context prologue: right after Section line
        inserts.append(ins)

    if not inserts:
        return None
    indent_of = lambda i: re.match(r"\s*", lines[i]).group(0) if \
        lines[i].strip().startswith("Context") else "  "
    for i in sorted(set(inserts), reverse=True):
        lines.insert(i + 1, f"{indent_of(i)}Context `{{XI : CurCtx}}.\n")
    if apply:
        path.write_text("".join(lines))
    return len(set(inserts))

# ------------------------------------------------------------- inline

DECL_RE = re.compile(
    r"^(\s*)((?:Local |Global )?(?:Lemma|Definition|Instance|Corollary|Theorem))"
    r"\s+([\w']+)", re.M)

def convert_inline(path: pathlib.Path, apply: bool):
    """For files that manage the context axis with INLINE binders (the
    ambient pass skips them): give every declaration whose span uses the
    flipped vocabulary -- and which binds neither CurCtx nor CpuId (the
    CpuId ones were handled by `binders`) -- its own `{XI : CurCtx}`,
    right after the name.  The vocabulary gate is what keeps the binder
    from being a phantom (the SchedCtx lesson)."""
    if path.name in AMBIENT_BLACKLIST or path.name in BLACKLIST:
        return None
    text = path.read_text()
    if "Require Import TsoCtx" not in text:
        return None
    decls = list(DECL_RE.finditer(text))
    if not decls:
        return None
    # a decl inside a section whose Context (possibly a COMBINED
    # `{GEN}`{CID}`{XI} line) already binds CurCtx must not re-bind it
    covered_at = []            # (offset, covered?) events
    depth = []
    off = 0
    for line in text.splitlines(keepends=True):
        st = line.lstrip()
        if st.startswith("Section "):
            depth.append(depth[-1] if depth else False)
        elif st.startswith("End ") and depth:
            depth.pop()
        elif st.startswith("Context ") and "CurCtx" in line and depth:
            depth[-1] = True
        covered_at.append((off, bool(depth) and depth[-1]))
        off += len(line)
    def covered(o):
        c = False
        for (start, v) in covered_at:
            if start > o: break
            c = v
        return c
    out, pos, count = [], 0, 0
    for i, m in enumerate(decls):
        span_end = decls[i + 1].start() if i + 1 < len(decls) else len(text)
        span = strip_comments(text[m.start():span_end])
        header_end = span.find("Proof.")
        header = span if header_end < 0 else span[:header_end]
        if "CurCtx" in header or "CpuId" in header or covered(m.start()):
            continue
        if not FLIPPED.search(span):
            continue
        out.append(text[pos:m.end()])
        out.append(" `{XI : CurCtx}")
        pos = m.end()
        count += 1
    if not count:
        return None
    out.append(text[pos:])
    if apply:
        path.write_text("".join(out))
    return count

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["binders", "caps", "ambient", "inline"])
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--files", nargs="*", help="restrict to these files")
    args = ap.parse_args()

    files = ([IRIS / f for f in args.files] if args.files
             else sorted(IRIS.glob("*.v")))
    if args.mode == "inline":
        tot = nf = 0
        for p in files:
            r = convert_inline(p, args.apply)
            if r:
                nf += 1; tot += r
                print(f"{p.name}: {r} inline binder(s)")
        print(f"-- inline: {nf} files, {tot} binders"
              f"{' (APPLIED)' if args.apply else ' (dry run)'}")
        return
    if args.mode == "ambient":
        tot = nf = nskip = 0
        for p in files:
            r = convert_ambient(p, args.apply)
            if r == "skip-inline":
                nskip += 1
                print(f"{p.name}: SKIP (manages its own inline XI binders)")
            elif r:
                nf += 1; tot += r
                print(f"{p.name}: {r} section binder(s)")
        print(f"-- ambient: {nf} files, {tot} binders, {nskip} inline-skips"
              f"{' (APPLIED)' if args.apply else ' (dry run)'}")
        return
    if args.mode == "caps":
        tot_o = tot_f = tot_s = nf = 0
        for p in files:
            r = convert_caps(p, args.apply)
            if r:
                o, fr, sp = r
                nf += 1; tot_o += o; tot_f += fr; tot_s += sp
                print(f"{p.name}: {o} opener(s), {fr} rebuild(s), {sp} split(s)")
        print(f"-- {nf} files, {tot_o} openers, {tot_f} rebuilds, {tot_s} splits"
              f"{' (APPLIED)' if args.apply else ' (dry run)'}")
        return

    tot_sec = tot_in = nfiles = 0
    for p in files:
        r = convert_file(p, args.apply)
        if r:
            nsec, nin, imp = r
            nfiles += 1
            tot_sec += nsec
            tot_in += nin
            print(f"{p.name}: {nsec} section, {nin} inline"
                  f"{', +import' if imp else ''}")
    print(f"-- {nfiles} files, {tot_sec} section binders, "
          f"{tot_in} inline binders{' (APPLIED)' if args.apply else ' (dry run)'}")

if __name__ == "__main__":
    main()
