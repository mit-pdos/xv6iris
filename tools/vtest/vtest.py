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
    cfg = {"repeat": 1, "drives": "cache=writeback", "smp": 1, "serial_in": ""}
    for line in open(src):
        m = re.search(r"vtest:\s*(.*?)\s*\*/", line)
        if m:
            for kv in m.group(1).split():
                k, _, v = kv.partition("=")
                cfg[k] = int(v) if k in ("repeat", "smp") else v
    return cfg

def build(name):
    src = os.path.join(TESTDIR, name + ".S")
    if not os.path.exists(src): sys.exit(f"no such test: {src}")
    os.makedirs(BUILDDIR, exist_ok=True)
    elf = os.path.join(BUILDDIR, name + ".elf")
    binf = os.path.join(BUILDDIR, name + ".bin")
    subprocess.run([CC, "-march=rv64imafd", "-mabi=lp64d", "-nostdlib",
                    "-nostartfiles", "-static", f"-I{HERE}",
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
        smp=None, serial_in=None):
    # smp and serial_in default to the test's own `vtest:` directive, so a
    # direct vtest.run("conc_foo") behaves the same as the command line.
    cfg = config(name)
    if smp is None: smp = cfg["smp"]
    if serial_in is None:
        serial_in = bytes(int(x, 0) for x in cfg["serial_in"].split(",")) \
                    if cfg["serial_in"] else b""
    elf, text = build(name)
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

def lit(bs, per=20):
    xs = [str(b) for b in bs]
    rows = ["; ".join(xs[i:i+per]) for i in range(0, len(xs), per)]
    return ";\n   ".join(rows)

def gen(r, alts=None):
    """alts: every DISTINCT result region observed, sorted, when the test is
    nondeterministic on the QEMU side."""
    os.makedirs(ROCQDIR, exist_ok=True)
    mod, low = modname(r["name"]), r["name"]
    path = os.path.join(ROCQDIR, mod + "Gen.v")
    disk = ";\n   ".join("(%d, [%s])" % (i, lit(b)) for i, b in r["disk"]) or ""
    alts = alts or [bytes(r["result"])]
    ser = lit(r["serial"])
    results = ";\n   ".join("[%s]" % lit(a) for a in alts)
    open(path, "w").write(f"""(* {mod}Gen.v -- GENERATED by tools/vtest/vtest.py from
   tools/vtest/tests/{r['name']}.S and one QEMU run.  Do not edit: run
   `make vtest` to regenerate.

   [{low}_text] is the image both machines execute.  [{low}_qemu_result] is
   the whole {len(r['result'])}-byte RESULT region as QEMU left it (nothing
   trimmed, so a difference cannot hide in the tail), and [{low}_qemu_disk]
   is every 512-byte sector of the disk image the run changed. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition {low}_text_base : Z := 0x{ABI['TEXT_BASE']:x}.

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

def all_tests():
    return sorted(f[:-2] for f in os.listdir(TESTDIR) if f.endswith(".S"))

def main():
    p = argparse.ArgumentParser()
    p.add_argument("cmd", choices=["list", "build", "run", "gen"])
    p.add_argument("names", nargs="*")
    p.add_argument("--all", action="store_true")
    p.add_argument("--repeat", type=int, default=0,
                   help="run N times and report distinct observations")
    p.add_argument("--drive-opts", default="cache=writeback",
                   help="extra -drive options, e.g. aio=threads,cache=none")
    a = p.parse_args()
    if a.cmd == "list":
        print("\n".join(all_tests())); return
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
                    rr = run(n, drive_opts=opts, smp=cfg["smp"])
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
            print("  ->", os.path.relpath(gen(r, alts), ROOT))
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
            r = run(n, drive_opts=a.drive_opts, smp=config(n)["smp"])
            print(f"{n}: DONE in {r['ms']:.0f} ms, serial={len(r['serial'])}B, status="
                  f"0x{int.from_bytes(r['result'][4:8],'little'):08x}, "
                  f"sectors changed: {[i for i,_ in r['disk']] or 'none'}")


if __name__ == "__main__":
    main()
