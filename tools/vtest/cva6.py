#!/usr/bin/env python3
"""cva6.py -- the CVA6 RTL side of a device-semantics test.

The third platform, beside vtest.py (QEMU) and board.py (the VisionFive 2).
Same question, a different machine:

    is what the hardware did an execution our model ALLOWS?

-- asked of the RTL of the OpenHW CVA6 core (cv64a6_imafdc_sv39, pinned in
tools/vtest/cva6/build.py), simulated cycle by cycle by Verilator inside
CVA6's own corev_apu testharness.  The platform is the directory: a run
writes vtest-rocq/CVA6/<Name>{Test,Run}.v, checked by the same theorem as
every other capture.  See claude-notes/projects/hw-refinement.md for why this
machine is in the suite.

  cva6.py runnable              the cases meaningful on cva6 (their platforms=)
  cva6.py build <name>...       assemble/link only
  cva6.py run   <name>...       build + simulate, print the result
  cva6.py gen   <name>...       build + simulate + write CVA6/<Name>{Test,Run}.v
  cva6.py gen --all             every runnable case

RUNS ON THE BUILD VM, where the simulator is built
(`./gcp-rocq/run-on-gcp tools/vtest/cva6/build.py`, then
`./gcp-rocq/run-on-gcp tools/vtest/cva6.py gen --all -k` and pull
vtest-rocq/CVA6 back).


WHAT A CVA6 RUN CLAIMS, next to the other two
---------------------------------------------

THE SAME IMAGE AS QEMU.  No -D and the same -march, so every capture's
[text] is byte-for-byte QEMU's -- unlike a board run -- and a difference
between the two columns is a difference between the machines.

A REAL POWER-ON.  The simulator starts from reset, runs CVA6's boot ROM at
0x10000 (a0 := mhartid, a1 := its DTB, s0 := 0x80000000, jump), and enters
the image at TEXT_BASE -- the same shape as QEMU's reset vector, so a
core_regs_* case measures the core's reset values, which a board run cannot
(README-hw.md section 2).  The boot ROM leaves s0 set; the model's cold state
has it 0.

DETERMINISTIC.  Same image, same cycles, same result, so a case's `repeat=`
buys nothing here and one run is taken.  A racy case (conc_*) is not
runnable anyway: the testharness has ONE hart.

ALL OF DRAM IS ZERO at the start (vtest_tb.cpp says why), so the declared
regions are zero as the ABI requires.

THE SERIAL CHANNEL IS THE WIRE.  vtest_tb.cpp decodes the 16550's SOUT pin
back into bytes, which is the model's [u_wire] -- not a tap on THR.

CVA6 IS IN THE DEFAULT `platforms=`, so a case runs here unless it says
otherwise.  WHAT THIS MACHINE DOES NOT HAVE, and so which cases narrow
themselves away from it:
  * a second hart (conc_*, which say platforms=qemu,jh7110),
  * virtio (disk_*),
  * a second UART (uart1_*),
  * a 16550 at the model's byte stride.  CVA6's UART is the PULP apb_uart
    with 32-bit registers 4 bytes apart (reg-shift 2, like the JH7110's --
    finding 30), and its interrupt is PLIC source 1, not 10.  So the uart_
    cases and the plic_ cases that raise an interrupt through the UART are
    not asked here yet.
"""
import argparse, os, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import vtest

ROOT, ABI = vtest.ROOT, vtest.ABI
FORCE = [False]

PLATFORM = "cva6"
HW_WORK = os.environ.get("HW_WORK", os.path.expanduser("~/hw/work"))
SIM = os.environ.get("CVA6_SIM",
                     os.path.join(HW_WORK, "cva6-vtest/obj/Variane_testharness"))
# At 512 cycles for core_smoke, a generous cap: a run that has not published
# by then is in a trap loop (mtvec = 0 sends a fault to the debug module's
# window at 0, not to an access fault as on QEMU) or waiting on a device.
MAX_CYCLES = int(os.environ.get("CVA6_MAX_CYCLES", "2000000"))
TRACEDIR = os.path.join(vtest.BUILDDIR, "cva6")


class RunFailed(Exception):
    def __init__(self, name, msg):
        super().__init__(msg)
        self.name, self.msg = name, msg


def runnable():
    return vtest.cases_for(PLATFORM)


def regions_for(name):
    """The declared regions, as board.py computes them (the ABI's currency).
    The testbench zeroes ALL of DRAM, so these are checked, not filled."""
    src = open(os.path.join(vtest.TESTDIR, name + ".S")).read()
    rs = [(ABI["STACK_BASE"], ABI["STACK_SIZE"]),
          (ABI["RESULT_BASE"], ABI["RESULT_SIZE"])]
    if "PT_BASE" in src:
        rs.append((ABI["PT_BASE"], ABI["PT_SIZE"]))
    if "DMA_BASE" in src:
        rs.append((ABI["DMA_BASE"], ABI["DMA_SIZE"]))
    return rs


def run(name):
    _, text = vtest.build(name)          # QEMU's image, exactly
    if not os.path.exists(SIM):
        sys.exit("no simulator at %s: run tools/vtest/cva6/build.py" % SIM)
    os.makedirs(TRACEDIR, exist_ok=True)
    with tempfile.TemporaryDirectory() as d:
        img, res, uart = (os.path.join(d, f) for f in ("img.bin", "res.bin", "uart.bin"))
        open(img, "wb").write(text)
        t = time.time()
        # the simulator's cwd is the temp dir: rvfi_tracer writes its
        # per-instruction trace there, which is kept below for diagnosis
        p = subprocess.run([SIM, img, res, uart, str(MAX_CYCLES)] +
                           ["%x:%x" % r for r in regions_for(name)],
                           cwd=d, capture_output=True, text=True)
        ms = 1000 * (time.time() - t)
        tr = os.path.join(d, "trace_rvfi_hart_00.dasm")
        if os.path.exists(tr):
            shutil.copy(tr, os.path.join(TRACEDIR, name + ".dasm"))
        if p.returncode not in (0, 2) or not (os.path.exists(res) and os.path.exists(uart)):
            raise RunFailed(name, "%s: simulator error (exit %d): %s"
                            % (name, p.returncode, p.stderr.strip()[-2000:]))
        result, serial = open(res, "rb").read(), open(uart, "rb").read()
    cycles = p.stderr.strip().split()[-2] if p.stderr.strip() else "?"
    if p.returncode == 2:
        raise RunFailed(name, "%s: no DONE within %d cycles (trace: %s)"
                        % (name, MAX_CYCLES,
                           os.path.relpath(os.path.join(TRACEDIR, name + ".dasm"), ROOT)))
    st = int.from_bytes(result[4:8], "little")
    if st == ABI["STATUS_MTRAP"]:
        w8 = lambda o: int.from_bytes(result[o:o+8], "little")
        raise RunFailed(name,
            "%s: the M-mode BACKSTOP fired -- the test gave up and set DONE "
            "itself, so this is a failure report and not an observation.\n"
            "  mcause=%#x mepc=%#x mtval=%#x" % (name, w8(56), w8(64), w8(72)))
    return dict(name=name, text=text, result=result, serial=serial,
                ms=ms, cycles=cycles)


def gen(r):
    """Write CVA6/<Name>Test.v and CVA6/<Name>Run.v through vtest's one
    emitter, so this platform's captures cannot drift into another shape.
    A re-capture UNIONS with what is on disk, as on the other platforms --
    here it can only ever find the same result, the simulator being
    deterministic, unless the RTL pin moved."""
    vtest.rocq_mkdirs()
    mod = vtest.modname(r["name"])
    alts, note = vtest.merge_observations(
        vtest.rp(mod + "Run.v", PLATFORM), vtest.rp(mod + "Test.v", PLATFORM),
        r["text"], [list(r["result"])], force=FORCE[0])
    print("  captures: %s" % note)
    results = ";\n     ".join("[%s]" % vtest.lit(list(a)) for a in alts)
    return vtest.emit_capture(PLATFORM, mod, r["name"], 0, vtest.lit(r["text"]),
                              results, vtest.lit(r["serial"]), "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["runnable", "build", "run", "gen"])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--all", action="store_true",
                    help="every case meaningful on cva6")
    ap.add_argument("-k", "--keep-going", action="store_true")
    ap.add_argument("--force", action="store_true",
                    help="REPLACE stored observations instead of adding")
    a = ap.parse_args()
    FORCE[0] = a.force
    if a.cmd == "runnable":
        print(" ".join(runnable())); return
    names = runnable() if a.all else a.names
    if not names:
        sys.exit("name a case, or pass --all")
    if a.cmd == "build":
        for n in names:
            _, t = vtest.build(n)
            print("%s: %d text bytes" % (n, len(t)))
        return
    failed = []
    for n in names:
        if PLATFORM not in vtest.platforms_of(n):
            print("%-20s not meaningful on cva6 (platforms=%s); running anyway"
                  % (n, vtest.config(n)["platforms"]))
        try:
            r = run(n)
        except RunFailed as e:
            if not a.keep_going:
                sys.exit(e.msg)
            failed.append(e)
            print("%-20s DID NOT FINISH" % n)
            continue
        st = int.from_bytes(r["result"][4:8], "little")
        print("%-20s DONE  %s cycles  %.0f ms  status=%#x  serial=%dB"
              % (n, r["cycles"], r["ms"], st, len(r["serial"])))
        if a.cmd == "gen":
            if PLATFORM not in vtest.platforms_of(n):
                print("  not written: the case excludes cva6")
                continue
            print("  ->", os.path.relpath(gen(r), ROOT))
    if failed:
        print("\n%d of %d did not finish:" % (len(failed), len(names)))
        for e in failed:
            print(e.msg)


if __name__ == "__main__":
    main()
