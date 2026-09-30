#!/usr/bin/env python3
"""rocq2lean.py -- import the checked-in captures of the Rocq tree.

The captures (the image that ran, the whole result region, the bytes that
left each UART, the disk sectors the run changed) were measured ONCE, on
QEMU, the VisionFive 2 board and the CVA6 RTL, and are checked into the Rocq
tree as vtest-rocq/<PLAT>/<Case>{Test,Run}.v.  A capture is data; the .v
files are one rendering of it and the Lean files another.  This tool reads
each Test/Run pair back and re-emits it through vtest.py's one emitter, so
nothing is re-measured and nothing is re-typed.

  rocq2lean.py [--rocq <path to a rocq-branch checkout>] [--plat qemu,jh7110,cva6]

It also copies the case sources (tools/vtest/tests/*.S, abi.h, vtest.S,
trap.S), whose `vtest:` directives carry each case's configuration.
"""
import argparse, os, re, shutil, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def field(body, pat):
    m = re.search(pat + r"\s*:=\s*\[(.*?)\]\.", body, re.S)
    return m.group(1) if m else None


def ints(txt):
    return [int(x) for x in re.findall(r"-?\d+", txt)]


def parse_capture(tb, rb):
    """One Rocq Test/Run pair -> the capture it renders."""
    case = re.search(r'Definition name\s*:=\s*"(.*?)"', tb).group(1)
    hart = int(re.search(r"Definition hart\s*: Z\s*:=\s*(-?\d+)", tb).group(1))
    regions = re.search(r"Definition regions\s*: list region\s*:=\s*(\w+)", tb).group(1)
    uin = re.search(r"Definition uart_input[^\n]*:=\s*\[(.*?)\]\.", tb, re.S).group(1)
    uart_input = [(0 if p == "Uart0" else 1, int(b, 0))
                  for p, b in re.findall(r"\((Uart\d),\s*Z_to_bv 8 (\w+)\)", uin)]
    text = ints(field(tb, r"Definition text\s*: list Z"))
    ser = ints(field(rb, r"Definition o_serial\s*: list Z") or "")
    ser1 = ints(field(rb, r"Definition o_serial1\s*: list Z") or "")
    dtxt = field(rb, r"Definition o_sectors\s*: list \(Z \* list Z\)") or ""
    disk = [(int(i), ints(b)) for i, b in re.findall(r"\((\d+),\s*\[([^\]]*)\]\)", dtxt)]
    rtxt = re.search(r"Definition results : list \(list Z\) :=\s*\[(.*?)\]\.", rb, re.S).group(1)
    results = [ints(b) for b in re.findall(r"\[([^\[\]]*)\]", rtxt)]
    return dict(case=case, hart=hart, regions=regions, uart_input=uart_input, text=text,
                serials=[ser, ser1], disk=disk, results=results)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rocq", required=True,
                    help="a checkout of the Rocq tree (its vtest-rocq/ and tools/vtest/)")
    ap.add_argument("--plat", default="qemu,jh7110,cva6")
    a = ap.parse_args()
    # THE CASE SOURCES FIRST: vtest.py reads abi.h when it is imported, and a
    # case's `vtest:` directive is where its configuration lives.
    src_tests = os.path.join(a.rocq, "tools", "vtest")
    testdir = os.path.join(HERE, "tests")
    os.makedirs(testdir, exist_ok=True)
    for f in sorted(os.listdir(os.path.join(src_tests, "tests"))):
        if f.endswith(".S"):
            shutil.copyfile(os.path.join(src_tests, "tests", f), os.path.join(testdir, f))
    for f in ("abi.h", "vtest.S", "trap.S"):
        shutil.copyfile(os.path.join(src_tests, f), os.path.join(HERE, f))
    import vtest
    n = 0
    for pl in a.plat.split(","):
        d = os.path.join(a.rocq, "vtest-rocq", vtest.PLATDIR[pl])
        for f in sorted(os.listdir(d)):
            if not f.endswith("Test.v"):
                continue
            vmod = f[:-len("Test.v")]
            rf = os.path.join(d, vmod + "Run.v")
            if not os.path.exists(rf):
                continue
            cap = parse_capture(open(os.path.join(d, f)).read(), open(rf).read())
            if vtest.emit_capture(pl, vmod, cap["case"], cap["hart"], cap["text"],
                                  cap["results"], cap["serials"], cap["disk"],
                                  regions=cap["regions"], uart_input=cap["uart_input"]):
                # READ IT BACK: the Lean rendering must carry exactly the
                # bytes the Rocq one did.
                back = vtest.read_capture(vtest.rp(vmod + "Test.lean", pl),
                                          vtest.rp(vmod + "Run.lean", pl))
                cap["regions"] = vtest.REGIONS[cap["regions"]]
                for k in cap:
                    if back[k] != cap[k]:
                        sys.exit("%s/%s: field %s did not survive the import" % (pl, vmod, k))
                n += 1
    print("imported %d capture(s) from %s" % (n, a.rocq))


if __name__ == "__main__":
    main()
