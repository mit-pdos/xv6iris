#!/usr/bin/env python3
"""vtest.py -- the QEMU side of a device-semantics test.

Builds a test image, runs it on QEMU, captures what it left in the RESULT
region and what it did to the disk, and writes both out as a Rocq file that
vtest-rocq/ checks the model against.  See tools/vtest/README.md and abi.h.

  vtest.py list                 the tests it can see
  vtest.py build  <name>...     assemble/link only
  vtest.py run    <name>...     build + run on QEMU, print what came back
  vtest.py gen    <name>...     build + run + write vtest-rocq/<Name>Gen.v
  vtest.py gen --all
"""
import argparse, json, os, re, socket, subprocess, sys, tempfile, time

HERE     = os.path.dirname(os.path.abspath(__file__))
ROOT     = os.path.abspath(os.path.join(HERE, "..", ".."))
TESTDIR  = os.path.join(HERE, "tests")
ROCQDIR  = os.path.join(ROOT, "vtest-rocq")
BUILDDIR = os.path.join(HERE, "build")

CC      = os.environ.get("VTEST_CC", "riscv64-linux-gnu-gcc")
OBJCOPY = os.environ.get("VTEST_OBJCOPY", "riscv64-linux-gnu-objcopy")
QEMU    = os.environ.get("VTEST_QEMU", "qemu-system-riscv64")

def abi():
    """the ABI constants, read from abi.h so there is ONE definition."""
    d = {}
    for line in open(os.path.join(HERE, "abi.h")):
        m = re.match(r"#define\s+(\w+)\s+([^/\s].*?)\s*(?:/\*.*)?$", line)
        if m:
            try: d[m.group(1)] = eval(m.group(2), {}, dict(d))
            except Exception: pass
    return d
ABI = abi()

# ---------------------------------------------------------------- build ----

def config(name):
    """Per-test knobs, read from a `vtest:` directive in the .S itself so the
    configuration sits next to the test.  e.g.

        /* vtest: repeat=40 drive=cache=none,aio=threads */

    [repeat] > 1 is for a test whose QEMU-side result is NOT deterministic:
    the model must admit EVERY execution the hardware has, so such a test is
    captured as a SET of observations rather than one."""
    src = os.path.join(TESTDIR, name + ".S")
    cfg = {"repeat": 1, "drives": "cache=writeback", "smp": 1, "serial_in": "",
           # WHICH PLATFORMS THIS CASE IS MEANINGFUL ON.  There is ONE set of
           # test cases; executing a case on a platform produces a test RUN,
           # so a case yields zero, one or two runs.  The default is both.
           #
           #   platforms=qemu,jh7110   (the default -- may be omitted)
           #   platforms=qemu          QEMU only
           #   platforms=jh7110        board only
           #   platforms=none          runs nowhere, and the directive says why
           #
           # A case is marked down to one platform when it cannot produce a
           # MEANINGFUL run on the other -- not when it merely fails there.
           # A failure is a finding and belongs in the table; an exclusion
           # is a statement that the question cannot be asked.
           "platforms": "qemu,jh7110",
           # THE MODEL-SIDE CONFIGURATION, which is also a property of the
           # case and so also lives here.  vtest-rocq/VRun.v consumes these.
           #   budget=N    steps the model is given.  Too small reads as a
           #               failure (MBudget); too large only costs time, and
           #               only for a case that does not finish.
           #   tick=1      step the CLOCK-TICKING branch of the boundary's
           #               [exists tick : bool].  For a case whose subject is
           #               elapsed time; see VTest section 3a.
           #   proj=whole                compare the entire result region
           #   proj=fields:o1,o2,...     compare only these 4-byte words, for
           #               a case some of whose fields legitimately differ
           #               between two runs of the SAME machine (counters, a
           #               raw mtime, an image-dependent mtvec, the hart id)
           #   builder=single   the model side is one hart from [start_hart]
           #                    (the default, and most cases)
           #   builder=sched    the case needs a SCHEDULE PREFIX before it
           #                    runs -- a serial byte ARRIVING is a schedule
           #                    choice, not something run_until performs.
           #                    The `serial_in=` bytes are the prefix.
           #   builder=picks    the case's several outcomes come from the
           #                    DEVICE rather than from two harts: the disk
           #                    may answer two in-flight requests in either
           #                    order.  `picks=lowest_head,highest_head`
           #                    names one run per order.
           #   builder=multi    the case races two harts, so its model side
           #                    needs a VConc SCHEDULE.  VRun has no builder
           #                    for that yet, so no run module is emitted and
           #                    the table says so -- which is honest, where
           #                    running such a case through the single-hart
           #                    builder would compute an outcome in which the
           #                    second hart never ran at all.
           "budget": 2000, "tick": 0, "proj": "whole", "builder": "single"}
    for line in open(src):
        m = re.search(r"vtest:\s*(.*?)\s*\*/", line)
        if m:
            for kv in m.group(1).split():
                k, _, v = kv.partition("=")
                cfg[k] = int(v) if k in ("repeat", "smp", "budget", "tick") else v
    return cfg

def build(name, defines=(), march="rv64imafd", tag=""):
    """[defines]/[march]/[tag] are for a BOARD PROFILE (tools/vtest/board.py)
    and default to exactly what the QEMU suite has always built: no -D, the
    same -march, and the same output filenames.  A profile passes its own
    -D list and a [tag] so the two machines' images sit side by side in
    build/ instead of overwriting each other."""
    src = os.path.join(TESTDIR, name + ".S")
    if not os.path.exists(src): sys.exit(f"no such test: {src}")
    os.makedirs(BUILDDIR, exist_ok=True)
    elf = os.path.join(BUILDDIR, name + tag + ".elf")
    binf = os.path.join(BUILDDIR, name + tag + ".bin")
    subprocess.run([CC, f"-march={march}", "-mabi=lp64d", "-nostdlib",
                    "-nostartfiles", "-static", f"-I{HERE}",
                    *[f"-D{d}" for d in defines],
                    f"-Wl,-Ttext=0x{ABI['TEXT_BASE']:x}",
                    "-o", elf, os.path.join(HERE, "vtest.S"), src], check=True)
    # -j .text, never plain -O binary: that pads from address 0 and produces a
    # 2 GB file for an image linked at 0x80000000.
    subprocess.run([OBJCOPY, "-O", "binary", "-j", ".text", elf, binf], check=True)
    return elf, open(binf, "rb").read()

# ------------------------------------------------------------------ qemu ----

class Qmp:
    def __init__(self, path, deadline):
        while time.time() < deadline:
            try:
                self.s = socket.socket(socket.AF_UNIX); self.s.connect(path); break
            except OSError: time.sleep(0.01)
        else: raise RuntimeError("QEMU never opened its QMP socket")
        self.f = self.s.makefile("rw"); self.f.readline(); self.cmd("qmp_capabilities")
    def cmd(self, ex, **a):
        self.f.write(json.dumps({"execute": ex, "arguments": a}) + "\n"); self.f.flush()
        while True:
            r = json.loads(self.f.readline())
            if "event" not in r: return r
    def hmp(self, line):
        return self.cmd("human-monitor-command", **{"command-line": line})["return"]
    def read(self, addr, nbytes):
        """guest physical memory -> bytes.  `xp` rather than `pmemsave`: the
        latter mis-parses its filename argument in QEMU 10.2, and `xp` needs
        no temp file (4 KB in ~2 ms)."""
        out = b""
        for off in range(0, nbytes, 4096):
            n = min(4096, nbytes - off) // 4
            txt = self.hmp(f"xp/{n}xw 0x{addr + off:x}")
            for w in re.findall(r"0x([0-9a-f]{8})", txt):
                out += int(w, 16).to_bytes(4, "little")
        return out[:nbytes]

def run(name, disk_sectors=128, timeout=15.0, drive_opts="cache=writeback",
        smp=None, serial_in=None, hart=0):
    # smp and serial_in default to the test's own `vtest:` directive, so a
    # direct vtest.run("conc_foo") behaves the same as the command line.
    cfg = config(name)
    if smp is None: smp = cfg["smp"]
    if serial_in is None:
        serial_in = bytes(int(x, 0) for x in cfg["serial_in"].split(",")) \
                    if cfg["serial_in"] else b""
    # THE HART VARIANT.  hart 0 builds and runs exactly as this suite always
    # has (no -D, no tag, the test's own smp); anything else needs BOTH a
    # different image -- the prologue's primary/AP branch and its stack slot
    # are keyed on PRIMARY_HART -- and enough harts for that one to exist.
    if hart:
        smp = max(smp, hart + 1)
    elf, text = build(name,
                      defines=() if not hart else ("PRIMARY_HART=%d" % hart,),
                      tag="" if not hart else "_hart%d" % hart)
    d = tempfile.mkdtemp(prefix="vtest-")
    qmp  = os.path.join(d, "qmp")
    disk = os.path.join(d, "disk.img")
    ser  = os.path.join(d, "serial.out")
    sock = os.path.join(d, "serial.sock")
    with open(disk, "wb") as fh: fh.write(b"\0" * (512 * disk_sectors))
    pre = open(disk, "rb").read()
    q = subprocess.Popen([QEMU, "-machine", "virt", "-bios", "none",
        "-kernel", elf, "-display", "none",
        # THE SERIAL CHANNEL IS CAPTURED, not discarded: it is how a `uart`
        # test observes what the 16550 actually transmitted.  It is NOT the
        # channel other tests report through -- printing a result costs ~10
        # instructions per character and the model executes every one.
        #
        # A test that needs the UART to RECEIVE declares `serial_in=` and gets
        # a socket instead of an output file, so the runner can push bytes in.
        # Receiving is the only externally-driven event in the whole suite:
        # on the model side those same bytes are a SCHEDULE choice, the
        # [SUartRx] arm of VSched, delivered where the test says.
        *(["-chardev", f"socket,id=s0,path={sock},server=on,wait=off",
           "-serial", "chardev:s0"] if serial_in else
          ["-serial", f"file:{ser}"]),
        "-smp", str(smp), "-m", "128M",
        # without this QEMU is a LEGACY virtio-mmio device (Version = 1)
        "-global", "virtio-mmio.force-legacy=false",
        "-drive", f"file={disk},if=none,format=raw,id=x0,{drive_opts}",
        "-device", "virtio-blk-device,drive=x0,bus=virtio-mmio-bus.0",
        "-qmp", f"unix:{qmp},server,nowait"],
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    deadline = time.time() + timeout
    sc, sout = None, b""
    try:
        m = Qmp(qmp, deadline)
        if serial_in:
            while time.time() < deadline:
                try:
                    sc = socket.socket(socket.AF_UNIX); sc.connect(sock); break
                except OSError: time.sleep(0.01)
            else: raise RuntimeError("QEMU never opened its serial socket")
            sc.setblocking(False)
            sc.sendall(serial_in)
        t0, done = time.time(), False
        while time.time() < deadline:
            if sc is not None:
                try: sout += sc.recv(4096)
                except BlockingIOError: pass
                except OSError: pass
            if int.from_bytes(m.read(ABI["RESULT_BASE"], 4), "little") == ABI["DONE_MAGIC"]:
                done = True; break
            time.sleep(0.005)
        if sc is not None:
            for _ in range(20):
                try: sout += sc.recv(4096)
                except BlockingIOError: time.sleep(0.005)
                except OSError: break
        result = m.read(ABI["RESULT_BASE"], ABI["RESULT_SIZE"])
        ms = (time.time() - t0) * 1000
    finally:
        # ALWAYS reap it: a survivor holds the disk image's write lock and the
        # next run dies with "Failed to get write lock".
        try: m.hmp("quit")
        except Exception: pass
        try: q.wait(timeout=5)
        except subprocess.TimeoutExpired: q.kill(); q.wait()
    post = open(disk, "rb").read()
    serial = sout if serial_in else (open(ser, "rb").read()
                                     if os.path.exists(ser) else b"")
    changed = [(i, post[i*512:(i+1)*512]) for i in range(len(pre)//512)
               if pre[i*512:(i+1)*512] != post[i*512:(i+1)*512]]
    if not done:
        sys.exit(f"{name}: guest never set the DONE flag within {timeout}s "
                 f"(status word = 0x{int.from_bytes(result[4:8],'little'):08x})")
    return dict(name=name, text=text, result=result, disk=changed, ms=ms,
                serial=serial)

# ------------------------------------------------------------------- gen ----

def modname(name):
    return "".join(p.capitalize() for p in name.split("_"))


def regions_of(name):
    """The declared regions this case needs, read off its source.  Every
    declared byte is a gmap insert on the model side, so a case declares
    what it uses and no more."""
    src = open(os.path.join(TESTDIR, name + ".S")).read()
    if "PT_BASE" in src:
        return "pt_regions"
    if "DMA_BASE" in src:
        return "dma_regions"
    return "std_regions"


def proj_of(name):
    """The Rocq projection term for this case's `proj=` directive."""
    v = config(name).get("proj", "whole")
    if v == "whole":
        return "whole"
    if v.startswith("fields:"):
        offs = [o for o in v[len("fields:"):].split(",") if o]
        return "(fields [%s]%%nat)" % "; ".join(offs)
    sys.exit("%s: unknown proj=%s" % (name, v))


FORCE = [False]      # set from --force in main()

GEN_MARK = "GENERATED by tools/vtest"


def merge_observations(path, defn, text_defn, text, alts, force=False):
    """Union a fresh capture's observations with the ones already on disk.

    A CAPTURE IS AN ASSET, NOT A CACHE.  A racy case's value is the SET of
    distinct outcomes the platform has ever shown, and the rare one -- the
    (0,0) that makes conc_sb a finding at all -- may take many runs to see.
    Overwriting the file with whatever this run happened to produce silently
    throws that away, and nothing downstream can tell: the run still builds,
    still passes, and quietly asserts less than it used to.  So a re-capture
    ADDS, and re-running a case you are not working on cannot cost you
    anything.

    KEYED ON THE IMAGE, because that is what makes the union sound.  Old
    observations describe the program that produced them; if [text] differs
    the .S changed and every stored observation is about a DIFFERENT program,
    so they are dropped and the file is replaced.  [force] drops them anyway,
    for when a capture is known bad (a wedged board, a misconfigured run).

    Returns (alts, note) with alts in a stable sorted order."""
    if force or not os.path.exists(path):
        return sorted(set(map(tuple, alts))), "fresh"
    txt = open(path).read()
    m = re.search(r"Definition %s : list Z :=\s*\[(.*?)\]\." % text_defn, txt, re.S)
    old_text = [int(x) for x in re.findall(r"-?\d+", m.group(1))] if m else None
    if old_text != list(text):
        return sorted(set(map(tuple, alts))), "image changed -- old observations dropped"
    m = re.search(r"Definition %s : list \(list Z\) :=\s*\[(.*?)\]\.\s*$" % defn,
                  txt, re.S | re.M)
    old = []
    if m:
        old = [tuple(int(x) for x in re.findall(r"-?\d+", b))
               for b in re.findall(r"\[([^\[\]]*)\]", m.group(1))]
    else:
        m1 = re.search(r"Definition %s : list Z :=\s*\[(.*?)\]\."
                       % defn.replace("_results", "_result"), txt, re.S)
        if m1:
            old = [tuple(int(x) for x in re.findall(r"-?\d+", m1.group(1)))]
    merged = sorted(set(old) | set(map(tuple, alts)))
    added = len(merged) - len(set(old))
    return merged, ("kept %d, added %d" % (len(set(old)), added) if added
                    else "kept %d, nothing new" % len(set(old)))


def hand_written(fname):
    """True when this file is a HAND-WRITTEN module the generator must leave
    alone.

    A builder computes [outcome] for the shapes it knows.  Some runs it does
    not: a race whose interleavings nobody has worked out, or one whose model
    side is not an evaluation at all.  Rather than emit something wrong, the
    generator emits NOTHING for those and a hand-written file supplies the
    run or its proof -- still a [VRun.TEST_RUN] and a [VRun.TEST_PASSES], so
    the table judges it exactly like any other and nothing about the theorem
    changes.

    The marker is the generator's own header, so this cannot drift: a file
    the generator wrote says so, and anything else is somebody's work."""
    path = os.path.join(ROCQDIR, fname)
    if not os.path.exists(path):
        return False
    return GEN_MARK not in open(path).read(400)


def emit_passes():
    """One [TEST_PASSES] instantiation per RUN, in its own file.

    Per RUN and not per case: a case with two runs whose file failed to
    compile would not say WHICH platform failed, and that is exactly the
    column the table exists to show.

    THE PROOF IS THE SAME TWO TACTICS EVERY TIME, which is the point of
    stating the theorem once and parametrically: the pass condition is
    decidable, [run_passes_b_sound] says deciding it suffices, and
    [vm_cast_no_check] evaluates once rather than twice.  A file that does
    NOT compile is a run that does not pass -- the table's "no proof"
    column, which is a finding and not a build error to paper over.

    A HAND-WRITTEN Pass module is left alone.  See [hand_written]."""
    made, kept = [], []
    for n in all_tests():
        mod = modname(n)
        for pl in PLATFORMS:
            if pl not in platforms_of(n):
                continue
            m = mod + pl.capitalize()
            if not os.path.exists(os.path.join(ROCQDIR, m + "Run.v")):
                continue
            if hand_written(m + "Pass.v"):
                kept.append(m); continue
            open(os.path.join(ROCQDIR, m + "Pass.v"), "w").write(
f"""(* {m}Pass.v -- GENERATED by tools/vtest.  Do not edit.

   The passing proof for the run of case [{n}] on platform [{pl}].
   The theorem is [VRun.TEST_PASSES], stated once and parametric in the
   run; this is its instantiation. *)
From Stdlib Require Import List ZArith.
Require Import VRun {m}Run.

Module {m}Pass <: TEST_PASSES {m}.
  Lemma passes : run_passes {m}.observed {m}.outcome.
  Proof. apply run_passes_b_sound. vm_cast_no_check (eq_refl true). Qed.
End {m}Pass.
""")
            made.append(m)
    if kept:
        print("kept %d hand-written proof(s): %s" % (len(kept), " ".join(kept)))
    return made


# The model side that is not per-case: the harness, the run framework, and
# VModelFacts -- the universally quantified statements about the model that
# no capture comparison can express, which is why they outlived the per-case
# files they came from.
HARNESS = ["VSched.v", "VExecStuck.v", "VTest.v", "VBoot.v", "VConc.v",
           "VNode.v", "VRun.v", "VRunConc.v", "VModelFacts.v"]

PROJECT_HEAD = """-R . VTest
-R ../iris xv6iris
-R ../model-xv6iris Riscv
-R ../kernel-rocq Kernel
-arg -w
-arg -notation-overridden
"""



def write_project(from_build=False):
    """Regenerate vtest-rocq/_CoqProject.

    THE PROJECT IS THE GREEN SET, and it is also the RECORD of which runs
    pass: `make vtest-check` requires everything listed to compile, so a run
    whose proof does not hold is simply not listed.  There is no second file
    saying the same thing.

    Which Pass modules to list comes from one of two places:

      * by default, the ones ALREADY listed -- so regenerating after adding
        a case, or after taking a new capture, is idempotent and cannot
        silently drop a proof that still holds;
      * with [from_build], the ones with a .vo on disk, which is what
        `make vtest-try` leaves behind.  That is how a newly-passing run
        gets ADDED, and how one that stopped passing gets removed.

    Everything else -- which runs exist at all -- is read off the tree.

    THERE IS NO LEGACY TIER.  Every case is expressed as a run through a
    VRun builder; what a per-case <Name>.v used to say about a capture, its
    Run and Pass modules now say uniformly, and what it said about the MODEL
    ITSELF (the universally quantified lemmas, the ones a capture
    comparison cannot express) lives in VModelFacts.v."""
    gens = []
    for n in all_tests():
        mod = modname(n)
        for suffix in ("Gen.v", "HwGen.v", "Hart1Gen.v"):
            f = mod + suffix
            if os.path.exists(os.path.join(ROCQDIR, f)):
                gens.append(f)
    # the hand-written interleavings are always needed: a multi-hart run
    # module Requires its <Case>Sched.v
    scheds = sorted(f for f in os.listdir(ROCQDIR)
                    if f.endswith("Sched.v") and f != "VSched.v")
    runs = sorted(f for f in os.listdir(ROCQDIR)
                  if f.endswith("Run.v") and not f.startswith("V"))
    runs = scheds + runs
    if from_build:
        ok = {f[:-len("Pass.vo")] for f in os.listdir(ROCQDIR)
              if f.endswith("Pass.vo")}
    else:
        ok = _passing()
    passes = sorted(f for f in os.listdir(ROCQDIR)
                    if f.endswith("Pass.v") and f[:-len("Pass.v")] in ok)
    files = ([h for h in HARNESS if os.path.exists(os.path.join(ROCQDIR, h))]
             + sorted(set(gens)) + runs + passes)
    open(os.path.join(ROCQDIR, "_CoqProject"), "w").write(
        PROJECT_HEAD + "\n".join(files) + "\n")
    # ...and the ATTEMPT project: everything, including the Pass modules the
    # green set leaves out.  coq_makefile only emits rules for files it is
    # given, so a proof that is not listed anywhere cannot even be TRIED --
    # which is how "is this still failing?" would become unanswerable.
    every = ([h for h in HARNESS if os.path.exists(os.path.join(ROCQDIR, h))]
             + sorted(f for f in os.listdir(ROCQDIR)
                      if f.endswith(".v") and f not in HARNESS))
    open(os.path.join(ROCQDIR, "_CoqProject.all"), "w").write(
        PROJECT_HEAD + "\n".join(every) + "\n")
    return files, [], passes


def _built_at_all():
    """Has anything been compiled here?  With no build there are no .vo to
    read, and the table would call every run a failure; say "unbuilt"
    instead of lying in either direction."""
    return any(f.endswith("Pass.vo") for f in os.listdir(ROCQDIR))


def _passing():
    """The runs whose [TEST_PASSES] instantiation compiles.

    THE PROJECT IS THE RECORD.  A Pass module is listed in _CoqProject
    exactly when it holds, and `make vtest-check` -- which CI runs -- fails
    if anything listed does not compile.  So membership already IS the
    passing set, and a second file saying the same thing could only drift
    from it."""
    p = os.path.join(ROCQDIR, "_CoqProject")
    if not os.path.exists(p):
        return set()
    return {l.strip()[:-len("Pass.v")] for l in open(p)
            if l.strip().endswith("Pass.v")}


def _run_state(n, pl):
    """The ONE state of (case, platform).  They are mutually exclusive, so a
    single column says everything.

    THE ORDER MATTERS, and it is the order in which the answers are actually
    determined.  A RUN THAT EXISTS is judged, whatever produced it -- a
    builder or a hand-written module -- so that question comes first.  Only
    then is it worth asking why one does not: nothing was captured, or the
    capture is there but no builder knows how to run the model on it.
    Asking "no builder" first mislabelled a case that had never been
    captured at all."""
    if pl not in platforms_of(n):
        return "excluded"
    mod = modname(n) + pl.capitalize()
    if not os.path.exists(os.path.join(ROCQDIR, mod + "Run.v")):
        gen = modname(n) + ("Gen.v" if pl == "qemu" else "HwGen.v")
        if not os.path.exists(os.path.join(ROCQDIR, gen)):
            return "uncaptured"
        return "no-builder"
    # THE .vo IS THE EVIDENCE.  Membership in _CoqProject is only an
    # ASSERTION that the proof holds -- a Pass.v listed there that does not
    # actually compile would read as "pass" until a build caught it, i.e.
    # the table would be reporting its own bookkeeping back.  Only a .vo
    # says coqc accepted the proof, so CI generates the table AFTER the
    # build and this reads the artefact.
    if os.path.exists(os.path.join(ROCQDIR, mod + "Pass.vo")):
        return "pass"
    if not _built_at_all():
        return "unbuilt" if mod in _passing() else "no-proof"
    return "no-proof"


_MD = {"pass":       "**pass**",
       "unbuilt":    "*not built*",
       "no-proof":   "no proof",
       "uncaptured": "*not captured*",
       "no-builder": "*no builder*",
       "excluded":   "—"}
_TXT = {"pass": "PASS", "unbuilt": "not built",
        "no-proof": "no proof", "uncaptured": "not captured",
        "no-builder": "no builder", "excluded": "--"}


def print_table(fmt="text"):
    """THE SINGLE TABLE: every case, its run on each platform, and whether
    that run has a passing proof.

    Everything is read off the tree -- the case's own directive, whether a
    run module exists, whether its [TEST_PASSES] instantiation compiles --
    so it cannot drift."""
    rows = [(n, _run_state(n, "qemu"), _run_state(n, "jh7110"))
            for n in all_tests()]
    if fmt == "md":
        print("## Device conformance: every case, every run\n")
        print("| case | QEMU | JH7110 |")
        print("|---|---|---|")
        for n, q, b in rows:
            print("| `%s` | %s | %s |" % (n, _MD[q], _MD[b]))
    else:
        w = max(len(r[0]) for r in rows)
        print("%-*s | %-13s | %-13s" % (w, "case", "qemu", "jh7110"))
        print("-" * (w + 32))
        for n, q, b in rows:
            print("%-*s | %-13s | %-13s" % (w, n, _TXT[q], _TXT[b]))
        print("-" * (w + 32))
    def c(i, v): return sum(1 for r in rows if r[i] == v)
    if any(r[1] == "unbuilt" or r[2] == "unbuilt" for r in rows):
        print("\nNOTE: nothing is built here, so `not built` means the proof "
              "is listed in _CoqProject but has not been checked in this "
              "tree.  CI generates this table AFTER the build, where every "
              "verdict is a .vo.")
    line = ("%d cases.  QEMU: %d pass, %d no proof, %d not captured, "
            "%d no builder, %d excluded.  "
            "JH7110: %d pass, %d no proof, %d not captured, %d no builder, "
            "%d excluded."
            % (len(rows),
               c(1, "pass"), c(1, "no-proof"), c(1, "uncaptured"),
               c(1, "no-builder"), c(1, "excluded"),
               c(2, "pass"), c(2, "no-proof"), c(2, "uncaptured"),
               c(2, "no-builder"), c(2, "excluded")))
    if fmt == "md":
        print("\n" + line)
        print("""
| state | meaning |
|---|---|
| **pass** | the run exists and its `VRun.TEST_PASSES` instantiation compiles: the model exhibits every outcome this platform observed, or has no transition at all (also a pass — a state the model cannot leave is one no proof can reach) |
| no proof | the run exists, but its `TEST_PASSES` instantiation does not compile: the model does not exhibit what the platform observed |
| *not captured* | the case declares this platform, but nothing has been run there yet, so there is no run to judge |
| *no builder* | the case is captured, but its model side needs something `VRun` cannot yet compute — a race whose interleavings are not written |
| — | the case excludes this platform: the question cannot be asked there (no disk on the board, a QEMU-only device) |""")
    else:
        print(line)


def runs_from_captures():
    """Build every RUN MODULE from the captures already checked in.

    A run module is a re-presentation of a capture, not a new measurement,
    so this needs neither QEMU nor the board: it reads <Name>Gen.v (qemu)
    and <Name>HwGen.v (jh7110) and writes <Name><Platform>Run.v.  That
    keeps the captures authoritative and makes the port mechanical."""
    import re as _re
    # STALE FILES ARE DELETED, not left lying: a run module for a (case,
    # platform) pair that should no longer exist -- the case narrowed its
    # `platforms=`, or moved to a builder this has no support for -- would
    # otherwise keep building, keep appearing in the table, and keep
    # asserting an outcome nobody meant.
    wanted = set()
    for n in all_tests():
        b = config(n).get("builder", "single")
        if b == "multi" and not os.path.exists(
                os.path.join(ROCQDIR, modname(n) + "Sched.v")):
            continue
        for pl in platforms_of(n):
            wanted.add(modname(n) + pl.capitalize())
    for n in all_tests():          # a hand-written run exists regardless of
        for pl in platforms_of(n):  # whether a builder could have made it
            if hand_written(modname(n) + pl.capitalize() + "Run.v"):
                wanted.add(modname(n) + pl.capitalize())
    stale = 0
    for f in os.listdir(ROCQDIR):
        # MATCH ONLY GENERATED MODULE NAMES, never a harness file.  The
        # obvious pattern `(\w+?)(Run|Pass)\.v$` matches VRun.v with
        # group(1) = "V", and "V" is never in [wanted] -- so it DELETED the
        # harness module this whole framework is built on, and the deletion
        # went unnoticed because the file had not been committed yet.
        # A generated name is always <Case><Platform>, so require the suffix
        # to be one of the known platforms.
        m = _re.match(r"(\w+(?:%s))(Run|Pass)\.v$"
                      % "|".join(pl.capitalize() for pl in PLATFORMS), f)
        if m and m.group(1) not in wanted and not hand_written(f):
            os.remove(os.path.join(ROCQDIR, f))
            for ext in (".vo", ".vos", ".vok", ".glob"):
                q = os.path.join(ROCQDIR, f[:-2] + ext)
                if os.path.exists(q):
                    os.remove(q)
            stale += 1
    if stale:
        print("removed %d stale run/pass file(s)" % stale)
    made, missing = [], []
    for n in all_tests():
        mod = modname(n)
        for platform, gen_suffix, pfx, hart_def in [
                ("qemu",   "Gen.v",   n,            None),
                ("jh7110", "HwGen.v", n + "_hw",    n + "_hw_primary_hart")]:
            if platform not in platforms_of(n):
                continue
            builder = config(n).get("builder", "single")
            if builder == "multi" and not os.path.exists(
                    os.path.join(ROCQDIR, mod + "Sched.v")):
                continue                       # no interleavings written yet
            src = os.path.join(ROCQDIR, mod + gen_suffix)
            if not os.path.exists(src):
                missing.append((n, platform)); continue
            txt = open(src).read()
            def grab(defn):
                m = _re.search(r"Definition %s : list Z :=\s*\[(.*?)\]\." % defn,
                               txt, _re.S)
                return [int(x) for x in _re.findall(r"-?\d+", m.group(1))] if m else None
            text = grab(pfx + "_text")
            m = _re.search(r"Definition %s_%s : list \(list Z\) :=\s*\[(.*?)\]\.\s*$"
                           % (pfx, "qemu_results" if platform == "qemu" else "results"),
                           txt, _re.S | _re.M)
            if m:
                observed = [[int(x) for x in _re.findall(r"-?\d+", blk)]
                            for blk in _re.findall(r"\[([^\[\]]*)\]", m.group(1))]
            else:
                one = grab(pfx + ("_qemu_result" if platform == "qemu" else "_result"))
                observed = [one] if one else None
            if text is None or not observed:
                missing.append((n, platform)); continue
            hart = 0
            if hart_def:
                hm = _re.search(r"Definition %s : Z := (\d+)" % hart_def, txt)
                hart = int(hm.group(1)) if hm else 0
            out = os.path.join(ROCQDIR, mod + platform.capitalize() + "Run.v")
            if emit_run_for(n, platform, text, observed, hart, out):
                made.append((n, platform))
    return made, missing


def emit_run_for(name, platform, text, observed, hart, path):
    """Write the run module for one (case, platform), CHOOSING THE BUILDER
    from the case's own `builder=` directive.

    THERE IS EXACTLY ONE OF THESE, and that is the point.  `gen` used to call
    [emit_run] directly, so a freshly captured multi-hart case got a
    SINGLE-HART run module -- the shape in which the second hart never
    executes at all, which is the specific error VRunConc exists to prevent
    and which is invisible in the generated file unless you read the module
    type.  Both callers now come through here.

    Returns False when nothing was written: a hand-written module is in the
    way (leave it alone), or the case's builder needs something that does not
    exist yet, in which case emitting the WRONG builder would be worse than
    emitting nothing and letting the table say so."""
    if hand_written(os.path.basename(path)):
        return True                     # a run exists; it is just not ours
    b = config(name).get("builder", "single")
    if b == "multi":
        if not os.path.exists(os.path.join(ROCQDIR,
                                           modname(name) + "Sched.v")):
            return False                # no interleavings written yet
        emit_run_conc(name, platform, text, observed, path, hart)
    elif b == "sched":
        emit_run_sched(name, platform, text, observed, hart, path)
    elif b == "picks":
        emit_run_picks(name, platform, text, observed, hart, path)
    else:
        emit_run(name, platform, text, observed, hart, path)
    return True


def emit_run_sched(name, platform, text, observed, hart, path):
    """The RUN MODULE for a case that needs a schedule PREFIX.  Same
    [TEST_RUN]; [VRun.SchedHart] runs [srun] first and steps from there."""
    cfg = config(name)
    mod = modname(name) + platform.capitalize()
    rx = [b for b in cfg.get("serial_in", "").split(",") if b]
    prefix = "; ".join("SUartRx %s" % b for b in rx)
    results = ";\n     ".join("[%s]" % lit(o) for o in observed)
    open(path, "w").write(f"""(* {os.path.basename(path)} -- GENERATED by tools/vtest.  Do not edit.

   The test RUN produced by executing case [{name}] on platform
   [{platform}].  The bytes the serial line DELIVERS are a schedule, not
   something the program performs, so this run's model side is
   [VRun.SchedHart]: deliver [prefix], then step. *)
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VRun.
Local Open Scope Z_scope.

Module {mod}Case <: SCHED_CASE.
  Definition case     := "{name}"%string.
  Definition platform := "{platform}"%string.
  Definition hart     : Z := {hart}.
  Definition regions  : list region := {regions_of(name)}.
  Definition budget   : nat := {cfg['budget']}%nat.
  Definition prefix   : list sitem := [{prefix}].
  Definition proj     := {proj_of(name)}.

  Definition text : list Z :=
    [{lit(text)}].

  Definition observed_raw : list (list Z) :=
    [{results}].
End {mod}Case.

Module {mod} := SchedHart {mod}Case.
""")
    return path


def emit_run_picks(name, platform, text, observed, hart, path):
    """The RUN MODULE for a case whose several outcomes are the DEVICE's
    choice.  One model run per completion order; [VRun.PicksHart]."""
    cfg = config(name)
    mod = modname(name) + platform.capitalize()
    picks = [x for x in cfg.get("picks", "lowest_head").split(",") if x]
    results = ";\n     ".join("[%s]" % lit(o) for o in observed)
    open(path, "w").write(f"""(* {os.path.basename(path)} -- GENERATED by tools/vtest.  Do not edit.

   The test RUN produced by executing case [{name}] on platform
   [{platform}].  The disk may answer its in-flight requests in more than
   one order, so this run exhibits one model execution per order --
   [VRun.PicksHart] over [picks]. *)
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VRun.
Local Open Scope Z_scope.

Module {mod}Case <: PICKS_CASE.
  Definition case     := "{name}"%string.
  Definition platform := "{platform}"%string.
  Definition hart     : Z := {hart}.
  Definition regions  : list region := {regions_of(name)}.
  Definition budget   : nat := {cfg['budget']}%nat.
  Definition picks    : list (virtio_state -> option Z) := [{"; ".join(picks)}].
  Definition proj     := {proj_of(name)}.

  Definition text : list Z :=
    [{lit(text)}].

  Definition observed_raw : list (list Z) :=
    [{results}].
End {mod}Case.

Module {mod} := PicksHart {mod}Case.
""")
    return path


def emit_run_conc(name, platform, text, observed, path, hart=0):
    """The RUN MODULE for a multi-hart case.  Same [TEST_RUN] as any other
    run; only the way [outcome] is computed differs, and that lives in
    VRunConc's [ConcRun] functor.  The interleavings come from the
    hand-written <Case>Sched.v -- which schedule reproduces which observed
    outcome is the one thing about a race that cannot be generated."""
    cfg = config(name)
    mod = modname(name) + platform.capitalize()
    sched = modname(name) + "Sched"
    results = ";\n     ".join("[%s]" % lit(o) for o in observed)
    open(path, "w").write(f"""(* {os.path.basename(path)} -- GENERATED by tools/vtest.  Do not edit.

   The test RUN produced by executing the multi-hart case [{name}] on
   platform [{platform}].  The interleavings are {sched}.schedules. *)
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VConc VRun VRunConc {sched}.
Local Open Scope Z_scope.

Module {mod}Case <: CONC_CASE.
  Definition case      := "{name}"%string.
  Definition platform  := "{platform}"%string.
  Definition regions   : list region := {regions_of(name)}.
  Definition budget    : nat := {cfg['budget']}%nat.
  Definition hart_base : Z := {hart}.
  Definition schedules := {sched}.schedules.
  Definition proj      := {proj_of(name)}.

  Definition text : list Z :=
    [{lit(text)}].

  Definition observed_raw : list (list Z) :=
    [{results}].
End {mod}Case.

Module {mod} := ConcRun {mod}Case.
""")
    return path


def emit_run(name, platform, text, observed, hart, path):
    """Write the Rocq RUN MODULE for one (case, platform) pair.

    One shape for both platforms: the case's own parameters, then the
    [SingleHart] functor, which COMPUTES what the model did rather than
    letting the generator assert it.  See vtest-rocq/VRun.v."""
    cfg = config(name)
    mod = modname(name) + platform.capitalize()
    results = ";\n     ".join("[%s]" % lit(o) for o in observed)
    open(path, "w").write(f"""(* {os.path.basename(path)} -- GENERATED by tools/vtest.  Do not edit.

   The test RUN produced by executing case [{name}] on platform
   [{platform}].  [{mod}Case] is what was run and what came back;
   [{mod}] is the [VRun.TEST_RUN] built from it, whose [outcome] is
   COMPUTED from the model rather than asserted here. *)
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VRun.
Local Open Scope Z_scope.

Module {mod}Case <: SINGLE_HART_CASE.
  Definition case     := "{name}"%string.
  Definition platform := "{platform}"%string.
  Definition hart     : Z := {hart}.
  Definition regions  : list region := {regions_of(name)}.
  Definition budget   : nat := {cfg['budget']}%nat.
  Definition tick     : bool := {'true' if cfg['tick'] else 'false'}.
  Definition proj     := {proj_of(name)}.

  Definition text : list Z :=
    [{lit(text)}].

  (* every DISTINCT result region this platform produced *)
  Definition observed_raw : list (list Z) :=
    [{results}].
End {mod}Case.

Module {mod} := SingleHart {mod}Case.
""")
    return path

def lit(bs, per=20):
    xs = [str(b) for b in bs]
    rows = ["; ".join(xs[i:i+per]) for i in range(0, len(xs), per)]
    return ";\n   ".join(rows)

def gen(r, alts=None, hart=0):
    """alts: every DISTINCT result region observed, sorted, when the test is
    nondeterministic on the QEMU side.

    [hart] is the HART VARIANT.  0 is the plain capture this suite has always
    written; anything else is the same source built with PRIMARY_HART=<hart>
    and run under -smp <hart+1>, captured as <Name>Hart<N>Gen.v with its own
    <name>_hartN_ definitions.  See "Running a test on a hart that is not 0"
    in README.md for why that is a different program and not just a different
    schedule."""
    os.makedirs(ROCQDIR, exist_ok=True)
    mod, low = modname(r["name"]), r["name"]
    # A RE-CAPTURE ADDS.  See merge_observations: a racy case's value is the
    # SET of outcomes ever seen, and overwriting can silently throw away the
    # rare one that made the case a finding.
    if alts:
        pfx = low if hart == 0 else "%s_hart%d" % (low, hart)
        _path = os.path.join(ROCQDIR, mod + ("Gen.v" if hart == 0
                                             else "Hart%dGen.v" % hart))
        alts, _note = merge_observations(_path, pfx + "_qemu_results",
                                         pfx + "_text", r["text"], alts,
                                         force=FORCE[0])
        alts = [list(a) for a in alts]
        print("  captures: %s" % _note)
    vmod = mod if hart == 0 else "%sHart%d" % (mod, hart)
    low  = low if hart == 0 else "%s_hart%d" % (low, hart)
    path = os.path.join(ROCQDIR, vmod + "Gen.v")
    disk = ";\n   ".join("(%d, [%s])" % (i, lit(b)) for i, b in r["disk"]) or ""
    alts = alts or [bytes(r["result"])]
    ser = lit(r["serial"])
    results = ";\n   ".join("[%s]" % lit(a) for a in alts)
    open(path, "w").write(f"""(* {vmod}Gen.v -- GENERATED by tools/vtest/vtest.py from
   tools/vtest/tests/{r['name']}.S and one QEMU run.  Do not edit: run
   `make vtest` to regenerate.

   [{low}_text] is the image both machines execute.  [{low}_qemu_result] is
   the whole {len(r['result'])}-byte RESULT region as QEMU left it (nothing
   trimmed, so a difference cannot hide in the tail), and [{low}_qemu_disk]
   is every 512-byte sector of the disk image the run changed.

   THE HART: {hart}.  {"The plain capture -- the boot hart, -smp 1." if hart == 0 else
   f"Built with PRIMARY_HART={hart} and run under -smp {hart+1}, so _vtest_body ran on hart {hart} and hart 0 took the AP path.  The model must be started on the SAME hart -- [start_hart {low}_primary_hart {low}_text] -- because the program reads mhartid."} *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition {low}_text_base : Z := 0x{ABI['TEXT_BASE']:x}.

(* which hart ran [_vtest_body] *)
Definition {low}_primary_hart : Z := {hart}.

Definition {low}_text : list Z :=
  [{lit(r['text'])}].

Definition {low}_qemu_result : list Z :=
  [{lit(r['result'])}].

Definition {low}_qemu_disk : list (Z * list Z) :=
  [{disk}].

(* what the 16550 actually transmitted, as the host saw it *)
Definition {low}_qemu_serial : list Z :=
  [{ser}].

(* Every DISTINCT result region observed over {len(alts)} distinct
   observation(s) of this test.  More than one means QEMU itself has more
   than one legal execution here, and the model must admit each of them. *)
Definition {low}_qemu_results : list (list Z) :=
  [{results}].
""")
    return path

# ------------------------------------------------------------------ main ----

def repeat(name, n, drive_opts, smp=1):
    """Run a test n times and report the DISTINCT observations.

    The model must admit every execution the hardware has, so a test whose
    QEMU-side result varies between runs is not one capture but several, and
    each needs a model schedule that reproduces it.  This is how the suite
    looks for that -- notably for completion ORDER, which the model fixes to
    publication order and a real device does not have to."""
    seen = {}
    for _ in range(n):
        r = run(name, drive_opts=drive_opts, smp=smp)
        key = (bytes(r["result"]), tuple((i, bytes(b)) for i, b in r["disk"]),
               bytes(r["serial"]))
        seen.setdefault(key, 0)
        seen[key] += 1
    return seen

PLATFORMS = ["qemu", "jh7110"]


def platforms_of(name):
    """The platforms this CASE declares itself meaningful on."""
    v = config(name).get("platforms", "qemu,jh7110").strip()
    if v in ("none", ""):
        return []
    return [p for p in v.split(",") if p in PLATFORMS]


def all_tests():
    return sorted(f[:-2] for f in os.listdir(TESTDIR) if f.endswith(".S"))


def cases_for(platform):
    """The cases that declare themselves meaningful on [platform]."""
    return [t for t in all_tests() if platform in platforms_of(t)]

def main():
    p = argparse.ArgumentParser()
    p.add_argument("cmd", choices=["list", "build", "run", "gen", "runs",
                                   "table", "passes", "project"])
    p.add_argument("names", nargs="*")
    p.add_argument("--all", action="store_true")
    p.add_argument("--repeat", type=int, default=0,
                   help="run N times and report distinct observations")
    p.add_argument("--drive-opts", default="cache=writeback",
                   help="extra -drive options, e.g. aio=threads,cache=none")
    p.add_argument("--from-build", action="store_true",
                   help="take the passing set from the .vo on disk (what "
                        "`make vtest-try` leaves) rather than from the "
                        "project's current membership")
    p.add_argument("--force", action="store_true",
                   help="REPLACE the stored observations instead of adding "
                        "to them.  A re-capture normally UNIONS with what is "
                        "already on disk, so re-running a case cannot lose a "
                        "rare outcome somebody spent many runs catching; pass "
                        "this only when the stored capture is known bad.")
    p.add_argument("--check", action="store_true",
                   help="exit nonzero if anything listed in _CoqProject has "
                        "no .vo, i.e. did not compile")
    p.add_argument("--format", choices=["text", "md"], default="text",
                   help="md emits a GitHub-flavoured markdown table")
    p.add_argument("--hart", type=int, default=0,
                   help="run _vtest_body on this hart instead of 0.  Builds a "
                        "SEPARATE image (PRIMARY_HART=N) and runs it under "
                        "-smp N+1; the capture is <Name>Hart<N>Gen.v.")
    a = p.parse_args()
    FORCE[0] = a.force
    if a.cmd == "list":
        print("\n".join(all_tests())); return
    if a.cmd == "runs":
        made, missing = runs_from_captures()
        print("wrote %d run module(s)" % len(made))
        for n, pl in missing:
            print("  no capture yet: %-18s %s" % (n, pl))
        return
    if a.cmd == "table":
        print_table(a.format)
        if not a.check:
            return
        # THE VERDICT, from the same artefacts the table just read.  Every
        # file in _CoqProject is asserted to compile -- that is what listing
        # it means -- so a listed .v with no .vo is a failure, and there is
        # no second pass over the build log to disagree with the table.
        proj = os.path.join(ROCQDIR, "_CoqProject")
        red = [l.strip() for l in open(proj)
               if l.strip().endswith(".v")
               and not os.path.exists(os.path.join(ROCQDIR, l.strip() + "o"))]
        if red:
            print("\n**%d file(s) in _CoqProject did not compile:** %s"
                  % (len(red), ", ".join(red)))
            sys.exit(1)
        return
    if a.cmd == "project":
        files, _, passes = write_project(a.from_build)
        print("_CoqProject: %d files (%d run proofs)" % (len(files), len(passes)))
        return
    if a.cmd == "passes":
        made = emit_passes()
        print("wrote %d per-run Pass file(s)" % len(made))
        return
    names = all_tests() if a.all else a.names
    if not names: sys.exit("name a test, or pass --all")
    for n in names:
        if a.cmd == "build":
            _, t = build(n); print(f"{n}: {len(t)} text bytes")
        elif a.cmd == "gen":
            cfg = config(n)
            reps = a.repeat or cfg["repeat"]
            # SEVERAL BACKEND CONFIGURATIONS, not just one.  Whether QEMU
            # reorders two in-flight requests depends on the backend, and no
            # single configuration reliably shows BOTH orders -- so a test
            # that is about nondeterminism names the configurations that
            # between them exhibit its executions, and the capture is their
            # union.  Without this, `make vtest-gen` is itself flaky.
            drives = (cfg["drives"] if a.drive_opts == "cache=writeback"
                      else a.drive_opts).split(";")
            seen = {}
            for opts in drives:
                for _ in range(reps):
                    rr = run(n, drive_opts=opts, smp=cfg["smp"], hart=a.hart)
                    seen.setdefault(bytes(rr["result"]), rr)
            disks = {tuple((i, bytes(b)) for i, b in rr["disk"]) for rr in seen.values()}
            if len(disks) != 1:
                sys.exit(f"{n}: the runs disagree on the DISK too ({len(disks)} "
                         f"variants); <name>_qemu_disk cannot represent that yet")
            alts = sorted(seen.keys())
            r = seen[alts[0]]
            print(f"{n}: {reps}x{len(drives)} runs {drives} -> "
                  f"{len(alts)} distinct result(s), "
                  f"sectors changed: {[i for i,_ in r['disk']] or 'none'}")
            print("  ->", os.path.relpath(gen(r, alts, hart=a.hart), ROOT))
            # ...and the uniform RUN MODULE, which is what VRun's theorem is
            # stated over.  <Name>Gen.v above is the raw capture; the run
            # module is the capture in the form the theorem is about.
            # THE RUN MODULE IS DERIVED FROM THE CAPTURE ON DISK, never from
            # this run's own [alts].  gen() UNIONS with the stored
            # observations, so the two differ exactly when a re-capture saw
            # fewer outcomes than are on record -- and building the run from
            # [alts] there silently drops the rare ones the capture kept.
            # Measured: one `gen conc_sb --repeat 1` left the capture with
            # all four outcomes and the run module with one, losing the (0,0)
            # that IS finding 24.  runs_from_captures reads the file.
            made, _ = runs_from_captures()
            if (n, "qemu") in made:
                print("  ->", os.path.relpath(
                    os.path.join(ROCQDIR, modname(n) + "QemuRun.v"), ROOT))
            else:
                print("  -> no run module: builder=%s has nothing to run the "
                      "model with yet (see the table)"
                      % config(n).get("builder", "single"))
        elif a.repeat:
            seen = repeat(n, a.repeat, a.drive_opts, config(n)["smp"])
            print(f"{n}: {a.repeat} runs [{a.drive_opts}] -> "
                  f"{len(seen)} distinct observation(s)")
            for k, (key, cnt) in enumerate(sorted(seen.items(), key=lambda kv: -kv[1])):
                res = key[0]
                words = " ".join(f"{int.from_bytes(res[o:o+4],'little'):#010x}"
                                 for o in range(4, 68, 4))
                print(f"  [{k}] x{cnt}  sectors={[i for i,_ in key[1]]}")
                print(f"        +4..+64: {words}")
        else:
            r = run(n, drive_opts=a.drive_opts, smp=config(n)["smp"], hart=a.hart)
            print(f"{n}: DONE in {r['ms']:.0f} ms, serial={len(r['serial'])}B, status="
                  f"0x{int.from_bytes(r['result'][4:8],'little'):08x}, "
                  f"sectors changed: {[i for i,_ in r['disk']] or 'none'}")


if __name__ == "__main__":
    main()
