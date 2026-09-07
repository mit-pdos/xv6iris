#!/usr/bin/env python3
"""vtest.py -- the QEMU side of a device-semantics test.

Builds a test image, runs it on QEMU, captures what it left in the RESULT
region and what it did to the disk, and writes both out as a Rocq file that
vtest-rocq/ checks the model against.  See tools/vtest/README.md and abi.h.

  vtest.py list                 the tests it can see
  vtest.py build  <name>...     assemble/link only
  vtest.py run    <name>...     build + run on QEMU, print what came back
  vtest.py gen    <name>...     build + run + write <Plat>/<Name>{Test,Run}.v
  vtest.py gen --all
"""
import argparse, json, os, re, socket, subprocess, sys, tempfile, time

HERE     = os.path.dirname(os.path.abspath(__file__))
ROOT     = os.path.abspath(os.path.join(HERE, "..", ".."))
TESTDIR  = os.path.join(HERE, "tests")
ROCQDIR  = os.path.join(ROOT, "vtest-rocq")
BUILDDIR = os.path.join(HERE, "build")

# ---------------------------------------------------------------------------
# WHERE A vtest-rocq FILE LIVES.  One directory per platform: a capture, the
# run module built from it and that run's proof are all ABOUT one platform,
# so they go under that platform's directory.  What is SHARED stays at the
# top -- the harness (V*.v) and the hand-written interleavings (<Case>Sched.v,
# which both platforms' run modules Require).  Otherwise the top level is
# three hundred generated files and the eleven that matter cannot be found.
#
# THE PLATFORM IS THE DIRECTORY AND NOT THE NAME.  QEMU/CoreSmokeRun.v, not
# CoreSmokeQemuRun.v: saying it twice is what made the listing unreadable.
# So every path helper takes the platform as an ARGUMENT -- it can no longer
# be recovered from a file name, and nothing should try.
#
# Rocq needs only that a Require be qualified where the same name exists on
# both platforms: [-R . VTest] maps the directories to [VTest.QEMU.*] and
# [VTest.JH7110.*], and the generated files say [From VTest.QEMU Require
# Import CoreSmokeRun].  The capture's own DEFINITIONS keep their _hw_
# infix on the board side, so the two platforms' globals stay distinct even
# though their files are now both <Case>Test.v.
# ---------------------------------------------------------------------------
PLATDIR = {"qemu": "QEMU", "jh7110": "JH7110"}


def rp(fname, platform=None):
    """The absolute path of a vtest-rocq file.  [platform] names the
    directory it belongs to; None is the shared top level."""
    return os.path.join(ROCQDIR, PLATDIR.get(platform, ""), fname)


def rrel(fname, platform=None):
    """...and the path _CoqProject lists, relative to vtest-rocq/."""
    d = PLATDIR.get(platform, "")
    return "%s/%s" % (d, fname) if d else fname


def rocq_listdir(platform=None):
    """The basenames in one vtest-rocq directory ([platform] None = the top)."""
    d = os.path.join(ROCQDIR, PLATDIR.get(platform, ""))
    return sorted(os.listdir(d)) if os.path.isdir(d) else []


def rocq_mkdirs():
    """vtest-rocq/ and both platform directories."""
    for d in [ROCQDIR] + [os.path.join(ROCQDIR, x) for x in PLATDIR.values()]:
        os.makedirs(d, exist_ok=True)


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
           # A SEPARATE REPEAT COUNT FOR THE BOARD, because a board run costs
           # ~4 s of JTAG round trips where a QEMU run costs milliseconds.
           # conc_sb wants repeat=700 on QEMU to hunt the rare (0,0); on the
           # board that is 48 MINUTES to sample a test that performs ONE race
           # per run, and it silently blew past two sweep timeouts.  The
           # sensitive instrument for that question is conc_sbx, which does
           # 200000 races in a single run.  Defaults to `repeat` when unset.
           "board_repeat": "",
           # THE PROGRAM WRITES ITS OWN TEXT.  A board repeat reloads the
           # image only when it changes (board.py); a self-modifying program
           # must have it reloaded EVERY run or the repeat observes the
           # previous run's patched code.  QEMU starts afresh each run.
           "selfmod": 0,
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
           #   builder=icache   the case stores over its OWN code, so its
           #                    outcomes are the FETCH VIEW's choice (the
           #                    icache is not coherent: icache.md).  One
           #                    model run per fetch schedule of the
           #                    hand-written <Case>Sched.v; VIcache.v.
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
                cfg[k] = int(v) if k in ("repeat", "smp", "budget", "tick",
                                                 "board_repeat", "selfmod") else v
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


def hand_written(fname, platform=None):
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
    path = rp(fname, platform)
    if not os.path.exists(path):
        return False
    return GEN_MARK not in open(path).read(400)


VERDICTS = ("agree", "stuck")


def verdict_of_file(mod, pl):
    """Which way a generated proof claims the run passes, read off the file.

    BOTH ARE PASSES.  They say different things, though: "agree" is that
    the model exhibits what the platform produced, "stuck" that this test's
    execution reaches a thread the RELATION cannot step from -- which is
    sound (a state the model cannot leave is one no proof can reach) but
    mentions the observation nowhere.  A table that calls both just "pass"
    is hiding the difference, which is the whole reason this is recorded."""
    p = rp(mod + "Pass.v", pl)
    if not os.path.exists(p):
        return None
    head = open(p).read(600)
    for v in VERDICTS:
        if "VERDICT: %s" % v in head:
            return v
    return None


def emit_passes(flip_unbuilt=False):
    """One proof per RUN, in ONE of the two forms.

    NOT [first [agree | stuck]]: that pays for the agree branch and then the
    stuck branch on every stuck test, and a run of twenty thousand steps is
    minutes either way.  Each file does ONE computation, and which one is
    recorded in its header.

    [flip_unbuilt] switches a proof that did not compile to the other form,
    which is how the build classifies them: emit [agree] for everything,
    build, flip what failed, build again.  What still fails after that is a
    run that does not pass at all -- the table's "no proof"."""
    made, kept = [], []
    for n in all_tests():
        mod = modname(n)
        cfg = config(n)
        tick = "true" if str(cfg.get("tick", 0)) == "1" else "false"
        budget = cfg["budget"]
        for pl in PLATFORMS:
            if pl not in platforms_of(n):
                continue
            if not os.path.exists(rp(mod + "Run.v", pl)):
                continue
            if hand_written(mod + "Pass.v", pl):
                kept.append(rrel(mod, pl)); continue
            was = verdict_of_file(mod, pl)
            v = was or "agree"
            if flip_unbuilt and was is not None \
               and not os.path.exists(rp(mod + "Pass.vo", pl)):
                v = "stuck" if was == "agree" else "agree"
            if v == "agree":
                body = f"""    left. intros o Ho.
    cbn [{mod}Run.observed {mod}Run.results fmap list_fmap] in Ho.
    repeat (destruct Ho as [<-|Ho];
            [ apply (run_shows {tick} lowest_head {budget});
              vm_compute; repeat split |]).
    destruct Ho."""
                what = ("the model EXHIBITS every observation the platform\n"
                        "   produced, from this test's own configuration")
            else:
                body = f"""    right. apply (run_no_step {tick} lowest_head {budget}).
    vm_cast_no_check (eq_refl true)."""
                what = ("this test's execution reaches a thread the RELATION\n"
                        "   cannot step from -- a pass, and a real one, but it says\n"
                        "   nothing about what the platform observed")
            rocq_mkdirs()
            open(rp(mod + "Pass.v", pl), "w").write(
f"""(* {PLATDIR[pl]}/{mod}Pass.v -- GENERATED by tools/vtest.  Do not edit.
   VERDICT: {v}

   The proof for the run of case [{n}] on platform [{pl}].  The theorem is
   [VRun.run_passes], a statement about [RiscvLang.prim_step]; [VExecStep]
   is what carries a computation of the interpreter to it.

   THIS RUN PASSES BECAUSE {what}. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list.
Import ListNotations.
From VTest Require Import VTest VRun VExecStep.
From VTest.{PLATDIR[pl]} Require Import {mod}Test {mod}Run.

Module {mod}Pass <: TEST_PASSES {mod} {mod}Run.
  Lemma passes :
    run_passes {mod}.hart {mod}.text {mod}.regions
               {mod}.uart_input {mod}.disk_init {mod}Run.observed.
  Proof.
{body}
  Qed.
End {mod}Pass.
""")
            made.append("%s (%s)" % (rrel(mod, pl), v))
    if kept:
        print("kept %d hand-written proof(s): %s" % (len(kept), " ".join(kept)))
    return made


# The model side that is not per-case: the harness, the run framework, and
# VModelFacts -- the universally quantified statements about the model that
# no capture comparison can express, which is why they outlived the per-case
# files they came from.
HARNESS = ["VSched.v", "VExecStuck.v", "VTest.v", "VTso.v", "VBoot.v", "VConc.v",
           "VNode.v", "VExecStep.v", "VRun.v", "VRunConc.v", "VIcache.v",
           "VModelFacts.v"]

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
    # EVERY PATH LISTED IS RELATIVE TO vtest-rocq/ and carries its platform
    # directory; coq_makefile takes the subdirectories as they come.  ORDER:
    # the shared harness and interleavings first, then each platform's
    # captures, runs and proofs -- which is also how they are read.
    top = rocq_listdir()
    shared = ([h for h in HARNESS if os.path.exists(rp(h))]
              + sorted(f for f in top
                       if f.endswith("Sched.v") and f != "VSched.v"))
    files, passes = [rrel(f) for f in shared], []
    for pl in PLATFORMS:
        here = rocq_listdir(pl)
        gens = sorted(f for f in here if f.endswith("Test.v"))
        runs = sorted(f for f in here if f.endswith("Run.v"))
        if from_build:
            ok = {f[:-len("Pass.vo")] for f in here if f.endswith("Pass.vo")}
        else:
            ok = _passing(pl)
        mine = sorted(f for f in here
                      if f.endswith("Pass.v") and f[:-len("Pass.v")] in ok)
        files += [rrel(f, pl) for f in gens + runs + mine]
        passes += [rrel(f, pl) for f in mine]
    open(os.path.join(ROCQDIR, "_CoqProject"), "w").write(
        PROJECT_HEAD + "\n".join(files) + "\n")
    # ...and the ATTEMPT project: everything, including the Pass modules the
    # green set leaves out.  coq_makefile only emits rules for files it is
    # given, so a proof that is not listed anywhere cannot even be TRIED --
    # which is how "is this still failing?" would become unanswerable.
    every = [rrel(f) for f in shared]
    for pl in PLATFORMS:
        every += [rrel(f, pl) for f in rocq_listdir(pl) if f.endswith(".v")]
    open(os.path.join(ROCQDIR, "_CoqProject.all"), "w").write(
        PROJECT_HEAD + "\n".join(every) + "\n")
    return files, [], passes


def _built_at_all():
    """Has anything been compiled here?  With no build there are no .vo to
    read, and the table would call every run a failure; say "unbuilt"
    instead of lying in either direction."""
    return any(f.endswith("Pass.vo")
               for pl in PLATFORMS for f in rocq_listdir(pl))


def _passing(platform):
    """The runs whose [TEST_PASSES] instantiation compiles.

    THE PROJECT IS THE RECORD.  A Pass module is listed in _CoqProject
    exactly when it holds, and `make vtest-check` -- which CI runs -- fails
    if anything listed does not compile.  So membership already IS the
    passing set, and a second file saying the same thing could only drift
    from it."""
    p = os.path.join(ROCQDIR, "_CoqProject")
    if not os.path.exists(p):
        return set()
    pfx = PLATDIR[platform] + "/"
    return {l.strip()[len(pfx):-len("Pass.v")] for l in open(p)
            if l.strip().endswith("Pass.v") and l.strip().startswith(pfx)}


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
    mod = modname(n)
    if not os.path.exists(rp(mod + "Run.v", pl)):
        if not os.path.exists(rp(mod + "Test.v", pl)):
            return "uncaptured"
        return "no-builder"
    # THE .vo IS THE EVIDENCE.  Membership in _CoqProject is only an
    # ASSERTION that the proof holds -- a Pass.v listed there that does not
    # actually compile would read as "pass" until a build caught it, i.e.
    # the table would be reporting its own bookkeeping back.  Only a .vo
    # says coqc accepted the proof, so CI generates the table AFTER the
    # build and this reads the artefact.
    if os.path.exists(rp(mod + "Pass.vo", pl)):
        return verdict_of_file(mod, pl) or "pass"
    if not _built_at_all():
        return "unbuilt" if mod in _passing(pl) else "no-proof"
    return "no-proof"


_MD = {"pass":       "**pass**",
       "agree":      "**pass** (agrees)",
       "stuck":      "**pass** (stuck)",
       "unbuilt":    "*not built*",
       "no-proof":   "no proof",
       "uncaptured": "*not captured*",
       "no-builder": "*no builder*",
       "excluded":   "—"}
_TXT = {"pass": "PASS", "agree": "PASS agrees", "stuck": "PASS stuck", "unbuilt": "not built",
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
    # BOTH VERDICTS ARE PASSES; the split says what each one claims.
    def npass(i): return c(i, "pass") + c(i, "agree") + c(i, "stuck")
    line = ("%d cases.  QEMU: %d pass (%d agree, %d stuck), %d no proof, "
            "%d not captured, %d no builder, %d excluded.  "
            "JH7110: %d pass (%d agree, %d stuck), %d no proof, "
            "%d not captured, %d no builder, %d excluded."
            % (len(rows),
               npass(1), c(1, "agree"), c(1, "stuck"),
               c(1, "no-proof"), c(1, "uncaptured"),
               c(1, "no-builder"), c(1, "excluded"),
               npass(2), c(2, "agree"), c(2, "stuck"),
               c(2, "no-proof"), c(2, "uncaptured"),
               c(2, "no-builder"), c(2, "excluded")))
    if fmt == "md":
        print("\n" + line)
        print("""
| state | meaning |
|---|---|
| **pass** (agrees) | the model EXHIBITS every observation this platform produced, from the test's own configuration |
| **pass** (stuck) | this test's execution reaches a thread the RELATION cannot step from.  Also a pass, and a real one — a state the model cannot leave is one no proof can reach, so it costs REACH and not soundness — but it says nothing about what the platform observed |
| no proof | the run exists, but its `TEST_PASSES` instantiation does not compile: the model does not exhibit what the platform observed |
| *not captured* | the case declares this platform, but nothing has been run there yet, so there is no run to judge |
| *no builder* | the case is captured, but its model side needs something `VRun` cannot yet compute — a race whose interleavings are not written |
| — | the case excludes this platform: the question cannot be asked there (no disk on the board, a QEMU-only device) |""")
    else:
        print(line)


def gen(r, alts=None, hart=0):
    """alts: every DISTINCT result region observed, sorted, when the test is
    nondeterministic on the QEMU side.

    [hart] is the HART VARIANT.  0 is the plain capture this suite has always
    written; anything else is the same source built with PRIMARY_HART=<hart>
    and run under -smp <hart+1>, captured as <Name>Hart<N>Gen.v with its own
    <name>_hartN_ definitions.  See "Running a test on a hart that is not 0"
    in README.md for why that is a different program and not just a different
    schedule."""
    rocq_mkdirs()
    mod, low = modname(r["name"]), r["name"]
    # A RE-CAPTURE ADDS.  See merge_observations: a racy case's value is the
    # SET of outcomes ever seen, and overwriting can silently throw away the
    # rare one that made the case a finding.
    if alts:
        pfx = low if hart == 0 else "%s_hart%d" % (low, hart)
        _path = rp(mod + ("Gen.v" if hart == 0 else "Hart%dGen.v" % hart),
                   "qemu")
        alts, _note = merge_observations(_path, pfx + "_qemu_results",
                                         pfx + "_text", r["text"], alts,
                                         force=FORCE[0])
        alts = [list(a) for a in alts]
        print("  captures: %s" % _note)
    vmod = mod if hart == 0 else "%sHart%d" % (mod, hart)
    low  = low if hart == 0 else "%s_hart%d" % (low, hart)
    disk = ";\n   ".join("(%d, [%s])" % (i, lit(b)) for i, b in r["disk"]) or ""
    alts = alts or [bytes(r["result"])]
    ser = lit(r["serial"])
    results = ";\n     ".join("[%s]" % lit(a) for a in alts)
    return emit_capture("qemu", vmod, r["name"], hart, lit(r["text"]),
                        results, ser, disk)


def emit_capture(platform, vmod, case, hart, text, results, serial, disk):
    """Write a capture as the TWO files it is: the TEST (the experiment --
    the image, the hart, the mapped memory, the input) and the RUN (the
    measurement -- what came back, on all three channels).

    THERE IS NO THIRD FILE.  A capture used to be written as <Name>Gen.v and
    then re-presented as a run module, which duplicated the image and left
    the capture itself required by nothing.  The test and the run ARE the
    capture, split where the meaning splits.

    A Test and a Run are written for EVERY captured run.  Whether a Pass
    proof exists for one is a separate question, and the table answers it."""
    PL = PLATDIR[platform]
    rocq_mkdirs()
    try:
        regions, cfg = regions_of(case), config(case)
        uin = "[" + "; ".join(
            "Z_to_bv 8 %s" % b.strip()
            for b in cfg.get("serial_in", "").split(",") if b.strip()) + "]"
    except Exception:
        regions, uin = "std_regions", "[]"
    open(rp(vmod + "Test.v", platform), "w").write(
f"""(* {PL}/{vmod}Test.v -- GENERATED by tools/vtest.  Do not edit: run
   `make vtest` to regenerate.

   THE TEST: the image tools/vtest/tests/{case}.S was built to, the hart it
   ran on, the memory that was mapped, and what it was given.  This is the
   EXPERIMENT; what came back is in {vmod}Run.v.

   THE HART IS {hart}, and it is not a label: [ColdBoot.cold_regs] is
   parametric in it and the program reads [mhartid], so a model started on
   a different one computes a different stack slot and goes stuck. *)
From Stdlib Require Import List ZArith String.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From VTest Require Import VTest VRun.
Local Open Scope Z_scope.

Module {vmod} <: TEST.
  Definition name       := "{case}"%string.
  Definition platform   := "{platform}"%string.
  Definition hart       : Z := {hart}.
  Definition regions    : list region := {regions}.
  Definition uart_input : list (bv 8) := {uin}.
  Definition disk_init  : list (Z * list Z) := [].

  Definition text : list Z :=
    [{text}].
End {vmod}.
""")
    open(rp(vmod + "Run.v", platform), "w").write(
f"""(* {PL}/{vmod}Run.v -- GENERATED by tools/vtest.  Do not edit: run
   `make vtest` to regenerate.

   THE RUN: what the platform produced, on all three channels -- the whole
   result region untrimmed, the bytes that left the UART, and the disk it
   ended with.  More than one observation means the hardware itself has
   more than one legal execution here, and the model must have each. *)
From Stdlib Require Import List ZArith.
From stdpp Require Import base list gmap bitvector.definitions.
Import ListNotations.
From VTest Require Import VTest VRun.
From VTest.{PL} Require Import {vmod}Test.
Local Open Scope Z_scope.

Module {vmod}Run <: TEST_RUN {vmod}.
  Definition o_serial  : list Z := [{serial}].
  Definition o_sectors : list (Z * list Z) := [{disk}].

  Definition results : list (list Z) :=
    [{results}].

  Definition observed : list observation :=
    (fun r => Obs r o_serial o_sectors) <$> results.
End {vmod}Run.
""")
    return rp(vmod + "Test.v", platform)


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
        # A CAPTURE IS ALREADY ITS TEST AND ITS RUN.  There used to be a
        # third file to re-present, and this command wrote the run module
        # from it; now [gen] writes both directly and there is nothing to
        # derive.  The proofs are still worth regenerating.
        made = emit_passes()
        print("captures are self-contained; wrote %d proof(s)" % len(made))
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
            # [gen] wrote the Test and the Run; the observations it merged
            # are already in the Run, so nothing re-derives them.  (This is
            # what the old two-step got wrong: one `gen conc_sb --repeat 1`
            # left the capture with all four outcomes and the run module
            # with one, losing the (0,0) that IS finding 24.)
            print("  ->", os.path.relpath(
                rp(modname(n) + "Run.v", "qemu"), ROOT))
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
