#!/usr/bin/env python3
"""build.py -- build the CVA6 vtest simulator (Verilator).

    tools/vtest/cva6/build.py            # on the build VM
    ./gcp-rocq/run-on-gcp tools/vtest/cva6/build.py

Produces $HW_WORK/cva6-vtest/Variane_testharness: CVA6's own corev_apu
testharness (the cv64a6_imafdc_sv39 core, DRAM at 0x80000000, the CLINT at
0x02000000, the PLIC at 0x0c000000, a 16550 at 0x10000000, the boot ROM at
0x10000), driven by tools/vtest/cva6/vtest_tb.cpp instead of CVA6's
fesvr-based testbench.

THE FILE LIST IS CVA6'S OWN.  It is taken from `make -n verilate` in the
pinned CVA6 tree and then edited, rather than copied here, so it follows the
pin.  The edits, each for a reason:

  * the testbench: vtest_tb.cpp + dpi_stubs.cc (the debug transport and
    rvfi_tracer's ELF reader, answered idle) replace ariane_tb.cpp and the
    fesvr-based DPI sources, and the Spike libraries leave the link line;
  * THE UART: the testharness turns the 16550 OFF under Verilator
    (`InclUART = 1'b0` in an `ifdef VERILATOR`) and puts a mock in its place.
    A vtest run observes the serial wire, so the build uses a copy of
    ariane_testharness.sv with the real apb_uart switched back on, and adds
    the apb_uart sources the stock Verilator list leaves out.

Needs Verilator v5.008 (see VERILATOR below).
"""
import os, shlex, subprocess, sys

CVA6_REV   = os.environ.get("CVA6_REV", "81245a47f")   # as tools/hw/cva6-netlist.sh
TARGET_CFG = os.environ.get("TARGET_CFG", "cv64a6_imafdc_sv39")
HOME       = os.path.expanduser("~")
# CVA6's CI pins Verilator v5.008 plus its own patch
# (verif/regress/install-verilator.sh); newer Verilators reject a streaming
# concatenation in the vendored axi_riscv_amos.sv under IEEE 1800-2023's
# stricter rule.  Built into ~/hw/verilator-5.008 on the VM.
VERILATOR  = os.environ.get("VERILATOR_BIN", os.path.join(HOME, "hw/verilator-5.008/bin"))
HW_WORK    = os.environ.get("HW_WORK", os.path.join(HOME, "hw/work"))
HERE       = os.path.dirname(os.path.abspath(__file__))
CVA6       = os.path.join(HW_WORK, "cva6")
OUT        = os.path.join(HW_WORK, "cva6-vtest")


def sh(cmd, **kw):
    return subprocess.run(cmd, check=True, **kw)


def main():
    env = dict(os.environ, PATH=VERILATOR + ":" + os.environ["PATH"],
               CVA6_REPO_DIR=CVA6, TARGET_CFG=TARGET_CFG,
               HPDCACHE_DIR=os.path.join(CVA6, "core/cache_subsystem/hpdcache"),
               RISCV="/nonexistent")   # the Makefile insists; nothing uses it
    if not os.path.isdir(os.path.join(CVA6, ".git")):
        sh(["git", "clone", "-q", "https://github.com/openhwgroup/cva6.git", CVA6])
    sh(["git", "-C", CVA6, "fetch", "-q", "origin"])
    sh(["git", "-C", CVA6, "checkout", "-q", CVA6_REV])
    sh(["git", "-C", CVA6, "submodule", "update", "-q", "--init", "--recursive"])
    os.makedirs(OUT, exist_ok=True)

    # the harness with the real UART
    th = os.path.join(CVA6, "corev_apu/tb/ariane_testharness.sv")
    src = open(th).read()
    stock = ("`ifndef VERILATOR\n    .InclUART     ( 1'b1                     ),\n"
             "`else\n    .InclUART     ( 1'b0                     ),\n`endif\n")
    if src.count(stock) != 1:
        sys.exit("ariane_testharness.sv: the InclUART block changed shape; "
                 "re-check the UART override")
    th2 = os.path.join(OUT, "ariane_testharness.sv")
    open(th2, "w").write(src.replace(stock, "    .InclUART     ( 1'b1 ),\n"))

    out = subprocess.run(["make", "-n", "verilate", "target=" + TARGET_CFG],
                         cwd=CVA6, env=env, capture_output=True, text=True).stdout
    cmd = next(l for l in out.splitlines() if l.startswith("verilator "))
    argv = shlex.split(cmd)

    drop_exact = {"corev_apu/tb/ariane_tb.cpp", "corev_apu/tb/dpi/SimDTM.cc",
                  "corev_apu/tb/dpi/SimJTAG.cc", "corev_apu/tb/dpi/remote_bitbang.cc",
                  "corev_apu/tb/dpi/msim_helper.cc"}
    new, i, n_th = [], 0, 0
    while i < len(argv):
        a = argv[i]
        if a in drop_exact:
            i += 1; continue
        if a == "-LDFLAGS":            # Spike's libraries: not linked
            new += ["-LDFLAGS", "-lpthread"]; i += 2; continue
        if a == "--Mdir":
            new += ["--Mdir", os.path.join(OUT, "obj")]; i += 2; continue
        if a.endswith("corev_apu/tb/ariane_testharness.sv"):
            new.append(th2); n_th += 1; i += 1; continue
        new.append(a); i += 1
    if n_th != 1:
        sys.exit("expected ariane_testharness.sv once in the verilate command")
    uart = os.path.join(CVA6, "corev_apu/fpga/src/apb_uart/src")
    new += sorted(os.path.join(uart, f) for f in os.listdir(uart)
                  if f.endswith(".sv") and not f.endswith("_wrap.sv"))
    new += [os.path.join(HERE, "vtest_tb.cpp"), os.path.join(HERE, "dpi_stubs.cc")]
    # the few signals the testbench reads (vtest.vlt), and nothing else public
    new.insert(1, os.path.join(HERE, "vtest.vlt"))

    open(os.path.join(OUT, "verilate.cmd"), "w").write(shlex.join(new) + "\n")
    sh(new, cwd=CVA6, env=env)
    sh(["make", "-j%d" % os.cpu_count(), "-f", "Variane_testharness.mk"],
       cwd=os.path.join(OUT, "obj"), env=env)
    exe = os.path.join(OUT, "obj", "Variane_testharness")
    print("built", exe)


if __name__ == "__main__":
    main()
