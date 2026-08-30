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
           #   builder=sched    the case needs an explicit VSched item list
           #                    -- a serial byte ARRIVING is a schedule
           #                    choice, not something run_until performs.
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
    column, which is a finding and not a build error to paper over."""
    made = []
    for n in all_tests():
        mod = modname(n)
        for pl in PLATFORMS:
            if pl not in platforms_of(n):
                continue
            m = mod + pl.capitalize()
            if not os.path.exists(os.path.join(ROCQDIR, m + "Run.v")):
                continue
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
    return made


def _passing():
    """The runs whose [TEST_PASSES] instantiation compiles.  Read from the
    checked-in PASSING.txt so the table needs no build; `make vtest-passes`
    rewrites it."""
    p = os.path.join(ROCQDIR, "PASSING.txt")
    if not os.path.exists(p):
        return set()
    return {l.strip() for l in open(p) if l.strip() and not l.startswith("#")}


def print_table():
    """THE SINGLE TABLE: every case, the runs it produces on each platform,
    and whether that run has a passing proof.

    Everything here is read off the tree -- the case's own `platforms=`
    directive, whether a run module exists, whether a [TEST_PASSES]
    instantiation exists for it, and whether that instantiation has been
    COMPILED.  Nothing is maintained by hand, so it cannot drift."""
    passes = set()
    for f in os.listdir(ROCQDIR):
        if f.endswith(".v"):
            for m in re.finditer(r"Module\s+(\w+)Pass\s*<:\s*TEST_PASSES",
                                 open(os.path.join(ROCQDIR, f)).read()):
                passes.add(m.group(1))
    def cell(n, pl):
        if pl not in platforms_of(n):
            return "--", "--"                      # the case excludes it
        if config(n).get("builder", "single") != "single":
            return "no builder", ""                # needs the multi-hart one
        mod = modname(n) + pl.capitalize()
        if not os.path.exists(os.path.join(ROCQDIR, mod + "Run.v")):
            return "no run", ""
        if mod not in passes:
            return "run", "no proof"
        built = os.path.exists(os.path.join(ROCQDIR, mod + "Pass.vo")) or \
                mod in _passing()
        return "run", ("PASS" if built else "no proof")
    rows = []
    for n in all_tests():
        qr, qp = cell(n, "qemu")
        br, bp = cell(n, "jh7110")
        rows.append((n, qr, qp, br, bp))
    w = max(len(r[0]) for r in rows)
    print("%-*s | %-7s %-14s | %-7s %-14s" % (w, "case", "qemu", "", "jh7110", ""))
    print("-" * (w + 50))
    for n, qr, qp, br, bp in rows:
        print("%-*s | %-7s %-14s | %-7s %-14s" % (w, n, qr, qp, br, bp))
    tot = len(rows)
    def count(i, v): return sum(1 for r in rows if r[i] == v)
    print("-" * (w + 50))
    print("%d cases; qemu: %d runs, %d passing.  jh7110: %d runs, %d passing."
          % (tot, count(1, "run"), count(2, "PASS"),
             count(3, "run"), count(4, "PASS")))


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
        if config(n).get("builder", "single") != "single":
            continue
        for pl in platforms_of(n):
            wanted.add(modname(n) + pl.capitalize())
    stale = 0
    for f in os.listdir(ROCQDIR):
        m = _re.match(r"(\w+?)(Run|Pass)\.v$", f)
        if m and m.group(1) not in wanted:
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
            if config(n).get("builder", "single") != "single":
                continue
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
            emit_run(n, platform, text, observed, hart, out)
            made.append((n, platform))
    return made, missing


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
                                   "table", "passes"])
    p.add_argument("names", nargs="*")
    p.add_argument("--all", action="store_true")
    p.add_argument("--repeat", type=int, default=0,
                   help="run N times and report distinct observations")
    p.add_argument("--drive-opts", default="cache=writeback",
                   help="extra -drive options, e.g. aio=threads,cache=none")
    p.add_argument("--hart", type=int, default=0,
                   help="run _vtest_body on this hart instead of 0.  Builds a "
                        "SEPARATE image (PRIMARY_HART=N) and runs it under "
                        "-smp N+1; the capture is <Name>Hart<N>Gen.v.")
    a = p.parse_args()
    if a.cmd == "list":
        print("\n".join(all_tests())); return
    if a.cmd == "runs":
        made, missing = runs_from_captures()
        print("wrote %d run module(s)" % len(made))
        for n, pl in missing:
            print("  no capture yet: %-18s %s" % (n, pl))
        return
    if a.cmd == "table":
        print_table(); return
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
            # stated over.  The legacy <Name>Gen.v above stays for the tests
            # that have not been ported to the module form yet.
            runp = os.path.join(ROCQDIR, modname(n) + "QemuRun.v")
            emit_run(n, "qemu", r["text"], [list(a) for a in alts], a.hart, runp)
            print("  ->", os.path.relpath(runp, ROOT))
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
