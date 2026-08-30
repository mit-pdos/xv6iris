#!/usr/bin/env python3
"""board.py -- the REAL HARDWARE side of a device-semantics test.

The sibling of vtest.py.  Same question, different machine:

    is what the real hardware did an execution our model ALLOWS?

vtest.py asks it of QEMU; this asks it of a development board over JTAG.
Everything downstream is unchanged -- the test sources in tests/, the ABI in
abi.h, the model side in vtest-rocq/ -- because the only thing that differs
is how an image is loaded, started and read back.  A run produces
vtest-rocq/<Name>HwGen.v beside vtest.py's <Name>Gen.v, and the SAME
vtest-rocq/<Name>.v checks the model against both.

  board.py profiles                 the board profiles it knows
  board.py probe                    talk to the board, print what is there
  board.py build  <name>...         assemble/link for the board only
  board.py run    <name>...         build + run on the board, print the result
  board.py gen    <name>...         build + run + write vtest-rocq/<Name>HwGen.v
  board.py gen --all

READ tools/vtest/README-hw.md FIRST.  It carries what a board run does and
does not claim, which is a narrower thing than what a QEMU run claims, and
the reasons are not obvious.


HOW A RUN WORKS, and why it is shaped like this
-----------------------------------------------

There is no `-kernel` and no QMP.  What there is:

  1. a GDB server (OpenOCD, port 3333) that can write memory in bulk and set
     registers, and
  2. an OpenOCD command server (telnet, port 4444) that can halt and resume.

so a run is: halt, write the image and the zero-filled regions, establish a
DEFINED register state on the harts the test uses, resume, poll the DONE
flag, halt, read the result region back.

Three things about that are worth knowing before changing any of it.

BULK, ALWAYS.  Every memory access over JTAG is a round trip.  gdb's
`restore <file> binary <addr>` writes a whole region in one go (measured: a
140-byte image plus two zeroed 4 KB regions in 1.6 s); a gdb `while` loop
writing the same 8 KB one doubleword at a time did not finish in two
minutes.  Nothing here may write memory a word at a time.

OPENOCD IS NOT IN OUR FILESYSTEM.  It may be a different container or a
different host, so `load_image` and `dump_image` -- which open files on
OpenOCD's side -- cannot be used at all.  Every byte moves over the GDB
remote protocol, which is why loading and reading back both go through gdb
and only run control goes over telnet.

HALT AND RESUME ARE SMP-WIDE.  On the VisionFive 2 the five harts are one
OpenOCD SMP group: `halt` halts all five and `resume` resumes all five, no
matter which target is selected.  So "run the test on one hart and leave the
rest alone" is not available; what IS available is to leave the harts we do
not use pointing where firmware left them, so they resume into their own
park loops.  See PROFILE["spare_harts"] and the --takeover flag.
"""
import argparse, json, os, re, select, signal, socket, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import vtest                      # the ABI, the build, the Rocq-literal helpers

FORCE    = [False]      # set from --force in main()
ROOT     = vtest.ROOT
ROCQDIR  = vtest.ROCQDIR
BUILDDIR = vtest.BUILDDIR
ABI      = vtest.ABI

GDB = os.environ.get("VTEST_GDB", "gdb-multiarch")

# ---------------------------------------------------------------- profiles --

# A BOARD PROFILE IS THE WHOLE DIFFERENCE between one machine and another,
# and it is deliberately small: every entry is a place a divergence could
# hide behind the scaffolding instead of showing up as a finding, so a new
# entry should have to justify itself.
#
# The three that are not just addresses:
#
#   primary_hart  which mhartid runs _vtest_body.  NOT 0 on the JH7110: hart
#                 0 is the E24, a 32-bit monitor core that cannot execute a
#                 64-bit image.  Also not 1 -- see spare_harts.
#   spare_harts   the harts this runner is allowed to take over.  On a board
#                 that boots firmware, the hart firmware is RUNNING ON is not
#                 one of them: hijacking it kills the firmware, and if the
#                 firmware was petting a watchdog the board resets a few
#                 seconds later.  (Measured, the hard way, on 2026-08-29.)
#   uart_shift    the 16550 register stride as a shift.  This one is a real
#                 device difference and NOT a scaffolding detail -- it is
#                 finding HW-1, and README-hw.md says why remapping it is
#                 legitimate and what it costs.
PROFILES = {
    "visionfive2": dict(
        desc         = "StarFive VisionFive 2 (JH7110: 4x SiFive U74 + 1x E24)",
        gdb_port     = 3333,
        ocd_port     = 4444,
        # mhartid 1..4 are the U74s; 0 is the E24 and is never touched.
        primary_hart = 2,
        spare_harts  = [2, 3, 4],
        firmware_hart= 1,        # U-Boot/OpenSBI live here; leave it alone
        # HART 0 IS THE E24 AND MUST NEVER BE TOUCHED.  It is a 32-bit core on
        # the same OpenOCD SMP group; reading a 64-bit CSR on it (`$misa`,
        # `$satp`) does not merely fail, it DROPS THE GDB CONNECTION -- twice
        # measured, 2026-08-29.  Nothing here may put it in a thread list.
        ignore_harts = [0],
        uart_shift   = 2,        # Synopsys DW-APB, reg-shift 2
        march        = "rv64gc", # what xv6 itself is built with
        # the name a case's `platforms=` directive uses for this machine
        platform_id  = "jh7110",
        # What the runner writes before resuming.  See establish_state().
        # mstatus is the model's own power-on obligation (ArchReset.board_regs:
        # SXL = UXL = 2, everything else clear), which core_regs_mcsr confirmed
        # of QEMU; writing it here makes the board start from the same place.
        cold_mstatus = 0xA00000000,
    ),
}
DEFAULT_PROFILE = "visionfive2"


class BoardRunFailed(Exception):
    """A test that did not reach [_vtest_done].  An EXCEPTION rather than a
    [sys.exit] so that a sweep can record it and carry on -- one test that
    hangs should not cost the other thirty."""
    def __init__(self, name, msg):
        super().__init__(msg)
        self.name, self.msg = name, msg


def runnable_tests(p):
    """The cases this platform is meant to execute, in suite order.

    ONE DECLARATION, AT THE CASE.  Which platforms a case is meaningful on
    is a property of the CASE, so it lives in the case's own `vtest:`
    directive (`platforms=`) and both runners read the same thing.  There is
    no runner-side skip list any more: a board profile that excluded an area
    would be hiding a fact about a case inside a fact about a machine, and
    the two drifted apart the moment a case was added."""
    return vtest.cases_for(p["platform_id"])


def profile(name):
    if name not in PROFILES:
        sys.exit("no such board profile: %s (have: %s)"
                 % (name, ", ".join(sorted(PROFILES))))
    return PROFILES[name]


def defines_for(p):
    """The -D list that turns a test source into an image for this board."""
    return ["VTEST_BOARD=1",
            "PRIMARY_HART=%d"   % p["primary_hart"],
            "UART_REG_SHIFT=%d" % p["uart_shift"]]


# ------------------------------------------------------------ openocd/telnet --

class Ocd:
    """OpenOCD's command server.  Used ONLY for run control (halt/resume) and
    for the cheap single-word poll of the DONE flag; everything bulk goes
    through gdb.

    EVERY COMMAND IS FRAMED BY A SENTINEL, and that is not belt-and-braces.
    OpenOCD writes ASYNCHRONOUS messages to this console -- "Disabling
    abstract command writes to CSRs", target-halted events, and every error
    a background poll hits -- so a reader that just waits for the next `> `
    prompt reads someone else's output and is off by one from then on.  It
    also emits stray NUL bytes mid-line.  So: send the command, send
    `echo <marker>`, and treat everything up to the marker as the reply.
    Measured the failure this prevents: an `mdw` that returned nothing and a
    `targets` that returned the previous command's answer."""

    def __init__(self, port, host="localhost", timeout=60):
        self.s = socket.create_connection((host, port), timeout=10)
        self.s.settimeout(timeout)
        self.buf = b""
        self.n = 0
        self.cmd("version")          # resynchronise, whatever was in flight

    def _read_until(self, marker, timeout):
        end = time.time() + timeout
        while marker not in self.buf:
            if time.time() > end:
                raise TimeoutError("openocd: no reply to %r within %.0fs"
                                   % (marker, timeout))
            self.s.settimeout(max(0.1, end - time.time()))
            try:
                d = self.s.recv(65536)
            except socket.timeout:
                continue
            if not d:
                raise RuntimeError("openocd closed the connection")
            # NULs are stripped ON ARRIVAL, not at the end: OpenOCD injects
            # them mid-line and they would otherwise break the marker match.
            self.buf += d.replace(b"\x00", b"")
        i = self.buf.index(marker)
        out, self.buf = self.buf[:i], self.buf[i + len(marker):]
        return out.replace(b"\x00", b"").decode(errors="replace").replace("\r", "")

    def cmd(self, c, timeout=60):
        self.n += 1
        mark = "__OCD%d__" % self.n
        self.s.sendall(("%s\necho %s\n" % (c, mark)).encode())
        # MATCH THE MARKER AT THE START OF A LINE, not anywhere.  The telnet
        # console echoes what we type, so the string also appears in the
        # echoed `echo __OCDn__` line -- cutting at the first occurrence
        # truncates the reply to nothing.  A leading newline distinguishes
        # the echo's OUTPUT (marker alone on its line) from that echo.
        txt = self._read_until(b"\n" + mark.encode(), timeout)
        keep = []
        for line in txt.split("\n"):
            t = line.strip().lstrip("> ").strip()
            if t in (c, "echo " + mark, ""):
                continue
            keep.append(line.strip().lstrip("> "))
        return "\n".join(keep).strip()

    def mdw(self, addr, n=1):
        """n words at addr.  OpenOCD prints `0xADDR: w0 w1 ...` per line."""
        txt = self.cmd("mdw 0x%x %d" % (addr, n))
        words = []
        for line in txt.split("\n"):
            m = re.search(r"0x[0-9a-fA-F]+:\s*((?:[0-9a-fA-F]{8}\s*)+)", line)
            if m:
                words += [int(w, 16) for w in m.group(1).split()]
        return words

    def close(self):
        try:
            self.s.sendall(b"exit\n")
            self.s.close()
        except Exception:
            pass


# --------------------------------------------------------------------- gdb --

class Gdb:
    """A PERSISTENT gdb session, and it is the whole performance story.

    THE BOTTLENECK IS NOT THE GUEST.  A vtest image runs on the board in
    about 70 ms.  The first version of this runner took ~25 SECONDS per
    test, i.e. the measurement was 0.3% of the cost, and all of the rest was
    scaffolding:

      - THREE gdb PROCESS SPAWNS per run (discover the hart map, load and
        set up, read the result back).  Each is a process start plus a fresh
        connection to OpenOCD and a detach.
      - ~50 register writes PER HART, each one a separate JTAG transaction
        over the GDB remote protocol.
      - a POLLING LOOP on the DONE word over the OpenOCD telnet port, one
        round trip per poll, which also cannot tell "not finished yet" from
        "hung".

    This class removes the first and the third.  One gdb process is started
    per Board and lives for the whole batch, so a `gen --all` pays the
    startup once instead of three times per test; and instead of polling,
    the runner puts a HARDWARE BREAKPOINT on `_vtest_done` -- the instruction
    the primary parks at, which vtest.S exports as a symbol for exactly this
    -- and just continues.  That is one round trip for the whole run and it
    is exact: the breakpoint hits when the program has finished, and a
    timeout means it genuinely did not.

    Commands are framed by an `echo` sentinel, for the same reason the
    OpenOCD side is: output arrives asynchronously and a reader that guesses
    where a reply ends goes out of sync."""

    def __init__(self, port, timeout=120):
        self.port, self.timeout, self.n = port, timeout, 0
        self.p = subprocess.Popen(
            [GDB, "-q", "-nx"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.buf = ""
        for c in ("set confirm off", "set pagination off", "set height 0",
                  "set width 0", "set debuginfod enabled off",
                  "set architecture riscv:rv64",
                  "set breakpoint pending off"):
            self.cmd(c)
        self.attach()

    # -- plumbing ---------------------------------------------------------

    def _read_until(self, mark, timeout):
        end = time.time() + timeout
        while mark not in self.buf:
            if time.time() > end:
                raise TimeoutError("gdb: no reply to %r in %.0fs" % (mark, timeout))
            r, _, _ = select.select([self.p.stdout], [], [], 0.2)
            if r:
                ch = os.read(self.p.stdout.fileno(), 65536).decode(errors="replace")
                if not ch:
                    raise RuntimeError("gdb exited")
                self.buf += ch
        i = self.buf.index(mark)
        out, self.buf = self.buf[:i], self.buf[i + len(mark):]
        return out

    def cmd(self, c, timeout=None):
        self.n += 1
        mark = "__GDB%d__" % self.n
        self.p.stdin.write("%s\necho %s\\n\n" % (c, mark))
        self.p.stdin.flush()
        return self._read_until(mark, timeout or self.timeout)

    def attach(self):
        return self.cmd("target extended-remote localhost:%d" % self.port)

    def close(self):
        try:
            self.p.stdin.write("detach\nquit\n")
            self.p.stdin.flush()
            self.p.wait(timeout=5)
        except Exception:
            try: self.p.kill()
            except Exception: pass

    # -- the one operation that can hang ----------------------------------

    def cont(self, timeout):
        """`continue`, with a deadline.  On timeout the inferior is
        interrupted with SIGINT so the session stays usable and the caller
        can read out where the harts actually are -- which is the diagnostic
        that matters when a test does not finish."""
        self.n += 1
        mark = "__GDB%d__" % self.n
        self.p.stdin.write("continue\necho %s\\n\n" % mark)
        self.p.stdin.flush()
        try:
            return self._read_until(mark, timeout), True
        except TimeoutError:
            self.p.send_signal(signal.SIGINT)
            try:
                return self._read_until(mark, 30), False
            except TimeoutError:
                return "", False


def zero_file(nbytes):
    """A file of [nbytes] zeros, for gdb `restore`.  Cached in build/."""
    os.makedirs(BUILDDIR, exist_ok=True)
    path = os.path.join(BUILDDIR, "zeros_%d.bin" % nbytes)
    if not os.path.exists(path) or os.path.getsize(path) != nbytes:
        with open(path, "wb") as fh:
            fh.write(b"\0" * nbytes)
    return path


def pad_image(text):
    """Pad the image so the model can FETCH its LAST instruction.

    THIS IS A HARNESS ARTIFACT, NOT A FINDING, and it is worth knowing about
    because it looks exactly like one.  COMPRESSED INSTRUCTIONS ARE NOT THE
    PROBLEM -- the model decodes them perfectly well, and a board image is
    full of them.  The problem is the FETCH WINDOW: the model sometimes
    fetches FOUR bytes for what turns out to be a two-byte instruction, and
    its memory is a finite gmap holding precisely the image bytes.  So a
    compressed instruction in the LAST two bytes of an image has its fetch
    reach two bytes past the end, find nothing there, and the machine is
    STUCK at an address that disassembles to something perfectly ordinary.

    The QEMU images never hit this because they are built -march=rv64imafd
    and contain no compressed instructions at all, so every image ends on a
    4-byte instruction whose own fetch exactly covers it.  A board image is
    built -march=rv64gc (what xv6 itself is built with), the assembler
    compresses freely, and core_smoke's final `ret` came out as a two-byte
    `c.jr ra`: measured 2026-08-29, VStuck at 0x8000008c.

    On the machine the bytes after the image are simply more DRAM, so the
    padding does not change what the hardware does; it only gives the model
    the same slack.  It is part of [_hw_text], so both sides run the same
    program, and it costs four declared bytes."""
    b = bytearray(text)
    while len(b) % 4:
        b.append(0)
    return bytes(b + b"\x00\x00\x00\x00")


# ------------------------------------------------------------------- board --

# The regions a test declares, in the same currency VTest.v declares them.
# THE RUNNER MUST ZERO EVERY ONE OF THEM, and this is not bookkeeping: the
# model's memory is the image plus these regions filled with ZEROS, so a
# board run that left a previous test's bytes lying in the result region
# would be comparing the model against a machine that started somewhere the
# model never starts.  QEMU gets this for free (fresh machine every run); a
# board does not.
def regions_for(name):
    src = open(os.path.join(vtest.TESTDIR, name + ".S")).read()
    rs = [(ABI["STACK_BASE"], ABI["STACK_SIZE"]),
          (ABI["RESULT_BASE"], ABI["RESULT_SIZE"])]
    if "PT_BASE" in src:
        rs.append((ABI["PT_BASE"], ABI["PT_SIZE"]))
    if "DMA_BASE" in src:
        rs.append((ABI["DMA_BASE"], ABI["DMA_SIZE"]))
    return rs


class Board:
    def __init__(self, p):
        self.p = p
        self.ocd = Ocd(p["ocd_port"])
        self.gdb = Gdb(p["gdb_port"])
        self._threads = None
        self._loaded = None      # the image currently in DRAM, for fast repeat

    # -- discovery ---------------------------------------------------------

    def thread_map(self):
        """gdb thread number -> mhartid.  DISCOVERED, not hardcoded: the
        order OpenOCD declares its targets in is a property of the board's
        config file, and getting it wrong means setting up the wrong hart
        and watching the test time out with no other symptom."""
        if self._threads is not None:
            return self._threads
        # CACHED ON DISK across invocations: the map is a property of the
        # board's OpenOCD config, not of a run, and discovering it costs a
        # round trip per hart.
        cache = os.path.join(BUILDDIR, "hartmap.json")
        if os.path.exists(cache):
            try:
                self._threads = {int(k): v for k, v in
                                 json.load(open(cache)).items()}
                return self._threads
            except Exception:
                pass
        out = ""
        for t in range(1, 16):
            out += self.gdb.cmd('thread %d' % t)
            out += self.gdb.cmd('printf "HART %d = %%d\\n", $mhartid' % t)
        m = {}
        for th, hid in re.findall(r"HART (\d+) = (-?\d+)", out):
            m[int(hid)] = int(th)
        if not m:
            sys.exit("board: could not read any hart's mhartid over gdb.\n" + out)
        self._threads = m
        os.makedirs(BUILDDIR, exist_ok=True)
        json.dump({str(k): v for k, v in m.items()}, open(cache, "w"))
        return m

    def probe(self):
        tm = self.thread_map()
        print("board: %s" % self.p["desc"])
        print("  gdb %d / openocd %d" % (self.p["gdb_port"], self.p["ocd_port"]))
        print("  mhartid -> gdb thread: %s" % dict(sorted(tm.items())))
        print("  primary hart %d, spares %s, firmware hart %d"
              % (self.p["primary_hart"], self.p["spare_harts"],
                 self.p["firmware_hart"]))
        for hid in sorted(tm):
            if hid in self.p.get("ignore_harts", []):
                print("  hart %d: SKIPPED (E24, 32-bit)" % hid)
                continue
            self.gdb.cmd("thread %d" % tm[hid])
            print(self.gdb.cmd('printf "  hart %d: pc=%%#lx misa=%%#lx '
                               'mstatus=%%#lx satp=%%#lx mtvec=%%#lx\\n", '
                               '$pc, $misa, $mstatus, $satp, $mtvec'
                               % hid).strip())
        print("  CLINT mtime = %#x" % self.read_u64(ABI_CLINT_MTIME))
        print("  targets:\n" + self.ocd.cmd("targets"))

    def read_u64(self, addr):
        w = self.ocd.mdw(addr, 2)
        return (w[1] << 32 | w[0]) if len(w) == 2 else -1

    # -- one run -----------------------------------------------------------

    def run(self, name, image, regions, harts, timeout=15.0, takeover=False,
            elf=None):
        """Load [image], start it on [harts], wait for DONE, read the result.

        ONE gdb SESSION, ONE `continue`.  The breakpoint is on `_vtest_done`
        -- the instruction vtest.S parks the primary at, right after the DONE
        store -- so this neither polls nor guesses: the stop IS the program
        finishing, and a timeout genuinely means it did not.  See the Gdb
        class for what this replaced and what it cost."""
        p, tm, g = self.p, self.thread_map(), self.gdb

        img = os.path.join(BUILDDIR, name + "_hw.bin")
        with open(img, "wb") as fh:
            fh.write(bytes(image))

        # ---- 1. memory.  Bulk only; every access here is a round trip. ----
        # THE IMAGE IS RELOADED ONLY WHEN IT CHANGES, which is what makes a
        # repeat=700 litmus test affordable: a repeat re-zeroes the regions
        # and re-establishes the registers, and that is all it needs to.
        g.cmd("\n".join("restore %s binary 0x%x" % (zero_file(size), base)
                        for base, size in regions))
        if self._loaded != (name, bytes(image)):
            g.cmd("restore %s binary 0x%x" % (img, ABI["TEXT_BASE"]))
            if elf:
                g.cmd("file %s" % elf)          # symbols only, for _vtest_done
            self._loaded = (name, bytes(image))

        # ---- 1b. the CLINT word this hart owns.  FIRMWARE LEAVES IT SET:
        #      OpenSBI parks a secondary hart waiting for an IPI, so its MSIP
        #      is 1 when we take the hart over, where the model's power-on
        #      CLINT has 0. ----
        g.cmd("\n".join("set *(unsigned int *)0x%x = 0" % (CLINT0 + 4 * hid)
                        for hid in harts))

        # ---- 2. registers: a DEFINED start state on every hart we use ----
        for hid in harts:
            if hid not in tm:
                sys.exit("board: hart %d is not on this board (have %s)"
                         % (hid, sorted(tm)))
            # ONE round trip for the whole register file, not fifty.  Each
            # `set` is still its own JTAG transaction, but the Python<->gdb
            # sentinel exchange around each one is what dominated: batching
            # them took a run from ~4 s to well under one.
            g.cmd("thread %d\n" % tm[hid] + establish_state(p, hid).strip())

        # ---- 3. go.  One breakpoint, one continue. ----
        t0 = time.time()
        g.cmd("delete breakpoints")
        bp = g.cmd("hbreak _vtest_done")
        if "Hardware assisted breakpoint" not in bp:
            # no symbols (or no trigger left): fall back to the poll
            return self._run_polled(name, harts, timeout, t0)
        _, hit = g.cont(timeout)
        ms = (time.time() - t0) * 1000
        g.cmd("delete breakpoints")

        # ---- 4. read the result region back, in one bulk transfer ----
        dump = os.path.join(BUILDDIR, name + "_hw_result.bin")
        g.cmd("dump binary memory %s 0x%x 0x%x"
              % (dump, ABI["RESULT_BASE"], ABI["RESULT_BASE"] + ABI["RESULT_SIZE"]))
        result = open(dump, "rb").read() if os.path.exists(dump) else b""

        # THE DONE FLAG IS THE CONTRACT, NOT THE BREAKPOINT.  abi.h: the flag
        # is written last, after a fence, so a reader that sees it sees a
        # complete result.  The breakpoint on [_vtest_done] is only an
        # ACCELERATOR for the common shape -- a test whose body returns
        # normally, so vtest.S writes the flag and parks there.
        #
        # A TEST MAY PUBLISH AND PARK SOMEWHERE ELSE, and several do: every
        # pt_ program has its own M-mode backstop that records the trap,
        # writes DONE, and loops inside the HANDLER.  Trusting the breakpoint
        # alone reported all nine of them as "never finished" when they had
        # finished -- measured 2026-08-30, and it is why the flag is checked
        # here regardless of whether the breakpoint fired.
        ok = (len(result) >= 4 and
              int.from_bytes(result[0:4], "little") == ABI["DONE_MAGIC"])

        if not ok:
            status = int.from_bytes(result[4:8], "little") if len(result) >= 8 else -1
            pcs = ""
            for h in harts:
                g.cmd("thread %d" % tm[h])
                pcs += g.cmd('printf "  hart %d pc=%%#lx mcause=%%#lx mepc=%%#lx '
                             'mtval=%%#lx\\n", $pc, $mcause, $mepc, $mtval' % h)
            raise BoardRunFailed(name,
                     "%s: the board never reached _vtest_done within %.1fs\n"
                     "  status word = 0x%08x\n%s\n"
                     "  (a pc parked at 0 means the program TRAPPED: mtvec is "
                     "0, so a fault is a trap loop at 0 -- exactly what the "
                     "model does.  Check mcause/mepc above.)"
                     % (name, timeout, status & 0xffffffff, pcs))

        return dict(name=name, text=bytes(image), result=result, ms=ms,
                    serial=b"", disk=[], board=self.p)

    def _run_polled(self, name, harts, timeout, t0, image=b""):
        """The old path: resume over the OpenOCD command server and poll the
        DONE word.  Kept because a board with no spare hardware trigger, or
        an image built without symbols, cannot use the breakpoint."""
        self.gdb.cmd("detach")
        self.ocd.cmd("resume", timeout=30)
        done, deadline = False, time.time() + timeout
        while time.time() < deadline:
            w = self.ocd.mdw(ABI["RESULT_BASE"], 1)
            if w and w[0] == ABI["DONE_MAGIC"]:
                done = True
                break
            time.sleep(0.02)
        ms = (time.time() - t0) * 1000
        self.ocd.cmd("halt", timeout=30)
        self.gdb.attach()
        dump = os.path.join(BUILDDIR, name + "_hw_result.bin")
        self.gdb.cmd("dump binary memory %s 0x%x 0x%x"
                     % (dump, ABI["RESULT_BASE"],
                        ABI["RESULT_BASE"] + ABI["RESULT_SIZE"]))
        result = open(dump, "rb").read() if os.path.exists(dump) else b""
        if not done:
            status = (int.from_bytes(result[4:8], "little")
                      if len(result) >= 8 else -1)
            raise BoardRunFailed(name,
                "%s: the board never set DONE within %.1fs (polled path)\n"
                "  status word = 0x%08x" % (name, timeout, status & 0xffffffff))
        # [image], not b"": gen() needs the text it ran, and returning empty
        # here wrote a capture with no program in it.
        return dict(name=name, text=bytes(image), result=result,
                    ms=ms, serial=b"", disk=[], board=self.p)

    def close(self):
        try:
            self.s.sendall(b"exit\n")
            self.s.close()
        except Exception:
            pass



CLINT0          = 0x02000000
ABI_CLINT_MTIME = 0x0200bff8


def establish_state(p, hid=0):
    """The gdb commands that put ONE hart into a defined start state.

    WHAT THIS IS AND IS NOT.  On QEMU every run starts from a machine that
    has just been reset, and vtest-rocq/VTest.v starts the model from
    [ColdBoot.cold_regs] -- the model's OWN reset chain.  The two agree
    because both are power-on states, and core_regs_* is the evidence.

    A BOARD DOES NOT GIVE US THAT.  OpenOCD's `reset halt` on this rig
    re-initialises the JTAG TAP and halts, but does not reset the cores:
    measured 2026-08-29, mtvec still held OpenSBI's 0x40000410 and mepc /
    mcause still held firmware's values afterwards (reset_config is
    trst_only -- there is no SRST line, and ndmreset did not reach the
    harts).  So the harts start wherever firmware left them.

    What this function does is therefore an HONEST SECOND BEST: it writes
    the architectural state a test program can actually observe, so a run
    starts from a defined place rather than from a firmware-dependent one.
    What it does NOT do is make that place power-on.

    THE CONSEQUENCE, and it is the one real limitation of this rig: a
    core_regs_* test on this board measures the CSRs THIS FUNCTION WROTE,
    not the CSRs the hardware powers up with, so for the registers listed
    below such a test is vacuous.  README-hw.md says which those are.  It is
    NOT vacuous for anything else -- misa, the counters, the PMP file, and
    every register a test writes itself are all still real observations."""
    p_ = p
    # PRIVILEGE FIRST, and it is not optional: a pt_ test switches to S-MODE
    # to exercise paging and FINISHES THERE, so the next run starts in S-mode
    # and takes an illegal-instruction trap on the very first `csrr mhartid`
    # -- into the mtvec=0 trap loop, which is why the symptom is pc=0 with
    # mcause=0x1 (the loop's own instruction access fault) rather than
    # mcause=0x2.  That trap lands in M-mode, so the run AFTER it succeeds.
    #
    # THE SIGNATURE IS STRICT ALTERNATION, not intermittency: pt_ad ran
    # PASS/FAIL/PASS/FAIL/PASS/FAIL, with $priv = 1 after every pass and 3
    # after every fail.  It read as a flaky JTAG link and cost two wrong
    # diagnoses (a stale TLB, then the hardware breakpoint), because a
    # SINGLE-RUN A/B on an alternating fault measures the phase, not the
    # change.
    cmds = ["set $priv = 3", "set $pc = 0x%x" % ABI["TEXT_BASE"]]
    # every GPR zeroed: the model's cold state has x1..x31 = 0, and leaving
    # firmware's values in place is how a test picks up a dependence on
    # something that is not in its own image.
    for r in ("ra sp gp tp t0 t1 t2 fp s1 a0 a1 a2 a3 a4 a5 a6 a7 "
              "s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6").split():
        cmds.append("set $%s = 0" % r)
    # ...EXCEPT a0, WHICH THE BOOT CONTRACT DEFINES.  ColdBoot's firmware
    # step is `a0 := mhartid, a1 := DTB`, so a0 = 0 is not "cleared", it is
    # the WRONG cold state on any hart but 0 -- and this runner's primary is
    # hart 2.  core_hart caught it: mhartid read 2 while a0 read 0, so the
    # test's own `a0 == mhartid` check failed and the run was red against a
    # model that had done nothing wrong.
    #
    # IT COULD ONLY EVER SHOW UP HERE.  On QEMU the capture is hart 0, where
    # a0 and mhartid are both 0 and the check passes for free; core_hart.S
    # says as much ("on hart 0 both are 0 and the test is nearly vacuous").
    #
    # a1 is deliberately NOT set: the model puts a hardcoded 0x1000 there
    # where real firmware passes the DTB pointer, which is finding 18 -- a
    # model defect, and replicating it in the harness would hide it.  The
    # case projects a1 away for exactly that reason.
    cmds.append("set $a0 = %d" % hid)
    # the CSRs a test can see and did not write itself
    cmds += [
        "set $mstatus = 0x%x" % p_["cold_mstatus"],
        "set $satp = 0",        # translation off; a pt_ test turns it on
        "set $mtvec = 0",       # so a fault is a trap loop at 0, as on QEMU
        "set $mie = 0", "set $mip = 0",
        "set $medeleg = 0", "set $mideleg = 0",
        "set $mcounteren = 0", "set $scounteren = 0",
        "set $mscratch = 0", "set $sscratch = 0",
        "set $mepc = 0", "set $mcause = 0", "set $mtval = 0",
        "set $sepc = 0", "set $scause = 0", "set $stval = 0",
        "set $stvec = 0",
    ]
    # Each on its own line, and each tolerated individually: a board may
    # refuse a CSR OpenOCD does not know, and that must not abort the run.
    return "".join("%s\n" % c for c in cmds)


# --------------------------------------------------------------------- gen --

def gen(r, alts=None):
    """Write vtest-rocq/<Name>HwGen.v -- the board's capture, beside the
    QEMU one.  Same shape as vtest.py's gen() so the test .v can compare
    them with the same combinators; the names carry _hw_ so one file can
    Require both."""
    os.makedirs(ROCQDIR, exist_ok=True)
    mod, low = vtest.modname(r["name"]), r["name"]
    path = os.path.join(ROCQDIR, mod + "HwGen.v")
    alts = alts or [bytes(r["result"])]
    # A RE-CAPTURE ADDS -- same rule as the QEMU side, and it matters MORE
    # here: a board run is seconds of wall clock on hardware somebody has to
    # physically own, and a racy outcome may take many sweeps to see again.
    alts, _note = vtest.merge_observations(
        path, low + "_hw_results", low + "_hw_text", r["text"],
        [list(a) for a in alts], force=FORCE[0])
    alts = [list(a) for a in alts]
    print("  captures: %s" % _note)
    results = ";\n   ".join("[%s]" % vtest.lit(a) for a in alts)
    p = r["board"]
    open(path, "w").write(f"""(* {mod}HwGen.v -- GENERATED by tools/vtest/board.py from
   tools/vtest/tests/{low}.S and one run on REAL HARDWARE.  Do not edit: run
   `make hwtest-gen` to regenerate.

   THE BOARD: {p['desc']}
   The image is NOT the one QEMU ran.  It is built from the same source with
   the board profile's -D list (PRIMARY_HART={p['primary_hart']},
   UART_REG_SHIFT={p['uart_shift']}, VTEST_BOARD), so [{low}_hw_text] below is
   its own program and the model must be run on IT, not on [{low}_text].
   tools/vtest/README-hw.md says what that costs and why it is still a
   one-directional claim.

   [{low}_hw_result] is the whole {len(r['result'])}-byte RESULT region as the
   board left it, read back over JTAG. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition {low}_hw_text_base : Z := 0x{ABI['TEXT_BASE']:x}.

(* which hart ran [_vtest_body]; the model must be scheduled on the same one,
   because the program reads [mhartid] and the prologue's stack slot is
   biased by it *)
Definition {low}_hw_primary_hart : Z := {p['primary_hart']}.

Definition {low}_hw_text : list Z :=
  [{vtest.lit(r['text'])}].

Definition {low}_hw_result : list Z :=
  [{vtest.lit(r['result'])}].

(* what the UART actually transmitted, as the host saw it.  EMPTY unless the
   board's serial line is exposed to the runner -- an empty list here means
   "not observed", NOT "nothing was sent". *)
Definition {low}_hw_serial : list Z :=
  [{vtest.lit(r['serial'])}].

(* Every DISTINCT result region observed over {len(alts)} observation(s). *)
Definition {low}_hw_results : list (list Z) :=
  [{results}].
""")
    return path


# -------------------------------------------------------------------- main --

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["profiles", "probe", "runnable",
                                    "build", "run", "gen"])
    ap.add_argument("names", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--board", default=DEFAULT_PROFILE)
    ap.add_argument("--repeat", type=int, default=0)
    ap.add_argument("--timeout", type=float, default=15.0)
    ap.add_argument("--force", action="store_true",
                   help="REPLACE the stored observations instead of adding "
                        "to them.  A re-capture normally UNIONS with what is "
                        "already on disk, so re-running a case cannot lose a "
                        "rare outcome somebody spent many runs catching; pass "
                        "this only when the stored capture is known bad.")
    ap.add_argument("-k", "--keep-going", action="store_true",
                    help="a test that does not finish is reported and the "
                         "sweep continues.  What `run --all` wants.")
    ap.add_argument("--takeover", action="store_true",
                    help="also take over the firmware hart.  Gives a quiescent "
                         "machine (nothing else polling the UART), at the cost "
                         "of losing firmware -- and of a watchdog reset if the "
                         "firmware was petting one.")
    a = ap.parse_args()
    FORCE[0] = a.force

    if a.cmd == "profiles":
        for k, v in sorted(PROFILES.items()):
            print("%-14s %s" % (k, v["desc"]))
        return
    p = profile(a.board)

    if a.cmd == "probe":
        b = Board(p); b.probe(); b.close(); return

    if a.cmd == "runnable":
        # what `make hwtest-gen-all` feeds to `gen`.  Whitespace-separated on
        # one line, because that is what a make $(shell ...) wants.
        print(" ".join(runnable_tests(p)))
        return

    names = vtest.all_tests() if a.all else a.names
    if not names:
        sys.exit("name a test, or pass --all")

    if a.cmd == "build":
        for n in names:
            _, t = vtest.build(n, defines_for(p), p["march"], "_hw")
            print("%s: %d text bytes (board image, %d padded)"
                  % (n, len(t), len(pad_image(t))))
        return

    b, failed = Board(p), []
    try:
        for n in names:
            cfg = vtest.config(n)
            elf, text = vtest.build(n, defines_for(p), p["march"], "_hw")
            text = pad_image(text)
            harts = [p["primary_hart"]]
            for k in range(1, cfg["smp"]):
                harts.append(p["primary_hart"] + k)
            if a.takeover:
                harts = sorted(set(harts) | {p["firmware_hart"]})
            reps = a.repeat or cfg.get("board_repeat") or cfg["repeat"]
            seen, counts = {}, {}
            try:
                for _ in range(reps):
                    r = b.run(n, text, regions_for(n), harts,
                              timeout=a.timeout, takeover=a.takeover, elf=elf)
                    st = int.from_bytes(r["result"][4:8], "little")
                    if st == ABI["STATUS_MTRAP"]:
                        w8 = lambda o: int.from_bytes(
                            r["result"][o:o+8], "little")
                        raise BoardRunFailed(n,
                            "%s: the M-mode BACKSTOP fired -- the test gave "
                            "up and set DONE itself, so this is a failure "
                            "report and not an observation.\n"
                            "  mcause=%#x mepc=%#x mtval=%#x"
                            % (n, w8(56), w8(64), w8(72)))
                    key = bytes(r["result"])
                    seen.setdefault(key, r)
                    counts[key] = counts.get(key, 0) + 1
            except BoardRunFailed as e:
                if not a.keep_going:
                    sys.exit(e.msg)
                failed.append(e)
                print("%-16s DID NOT FINISH" % n)
                continue
            alts = sorted(seen.keys())
            r = seen[alts[0]]
            print("%s: %d run(s) on harts %s -> %d distinct result(s), %.0f ms"
                  % (n, reps, harts, len(alts), r["ms"]))
            if a.cmd == "gen":
                print("  ->", os.path.relpath(gen(r, alts), ROOT))
                runp = os.path.join(ROCQDIR,
                                    vtest.modname(n) + "Jh7110Run.v")
                # emit_run_for, NOT emit_run: the builder comes from the
                # case's own `builder=` directive.  Calling emit_run direct
                # gave a multi-hart case a SINGLE-HART run module, in which
                # the second hart never executes -- the error VRunConc
                # exists to prevent, and invisible unless you read the
                # module type.  vtest.py's own gen had the same bug.
                # from the CAPTURE ON DISK, not from this run's alts --
                # gen() unions with the stored observations, and building
                # from alts drops whatever this run did not happen to see.
                made, _ = vtest.runs_from_captures()
                if (n, "jh7110") in made:
                    print("  ->", os.path.relpath(runp, ROOT))
                else:
                    print("  -> no run module: builder=%s has nothing to run "
                          "the model with yet"
                          % vtest.config(n).get("builder", "single"))
            else:
                st = int.from_bytes(r["result"][4:8], "little")
                words = " ".join("%#010x" % int.from_bytes(r["result"][o:o+4], "little")
                                 for o in range(8, 40, 4))
                print("  status=0x%08x  +8..+40: %s" % (st, words))
                if reps > 1:
                    # A TALLY, which is what a litmus test wants: the same
                    # program run many times, grouped by what it observed.
                    # The repeat path does NOT reload the image (see
                    # Board.run), so runs after the first cost only the
                    # region zeroing, the register set-up and one continue.
                    for k, (res, cnt) in enumerate(
                            sorted(counts.items(), key=lambda kv: -kv[1])):
                        ws = " ".join("%d" % int.from_bytes(res[o:o+4], "little")
                                      for o in (4, 8, 12, 16, 20, 24))
                        print("  [%d] x%-4d  +4/+8/+12/+16/+20/+24 = %s"
                              % (k, cnt, ws))
                    # ...and the SUM over all runs of each word, which is what
                    # a sticky litmus counter wants: one occurrence anywhere.
                    tot = {}
                    for res, cnt in counts.items():
                        for o in range(8, 40, 4):
                            tot[o] = tot.get(o, 0) + cnt * int.from_bytes(
                                res[o:o+4], "little")
                    print("  SUM over %d runs, +8..+36: %s"
                          % (reps, " ".join("%d" % tot[o]
                                            for o in range(8, 40, 4))))
        if failed:
            print("\n%d of %d did not finish:" % (len(failed), len(names)))
            for e in failed:
                print(e.msg)
    finally:
        b.close()


if __name__ == "__main__":
    main()
