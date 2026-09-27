#!/usr/bin/env python3
"""netlist_summary.py -- what a hierarchical Yosys JSON netlist contains.

    netlist_summary.py design.json top

Reports the facts the Rocq netlist semantics depends on
(claude-notes/projects/hw-refinement.md section 7), over the modules
reachable from the top (unreachable leftovers are listed as orphans):

  * the module tree: modules, instance cells, the distinct SOURCE modules, and
    the distinct module SHAPES.  yosys-slang --keep-hierarchy names a module
    per instance path (`pmp_entry$cva6.ex_stage_i...`), so identical instances
    arrive as copies; a shape is a module's body with nets renumbered, which
    is what lets one set of lemmas serve every copy.
  * the cells by type, flop bits, and memories (writable vs read-only tables).
  * clocking: every flop's and memory port's clock, traced to the top through
    instance ports and through pass-through modules.  A single top-level clock
    is what a one-edge semantics needs.
  * modules with undriven outputs and no cells: almost always a front-end
    loss (e.g. a macro wrapper hidden behind `synthesis translate_off`), and
    yosys reports success regardless.
"""
import collections
import hashlib
import json
import sys


def base(name):
    return name.split("$")[0] if not name.startswith("$") else name


def shape(md):
    ren = {}

    def r(b):
        return b if isinstance(b, str) else ren.setdefault(b, len(ren))

    ports = [(p, d["direction"], [r(b) for b in d["bits"]])
             for p, d in sorted(md["ports"].items())]
    cells = sorted(
        (c["type"] if c["type"].startswith("$") else base(c["type"]),
         json.dumps(c.get("parameters", {}), sort_keys=True),
         json.dumps({k: [r(b) for b in v]
                     for k, v in sorted(c["connections"].items())}))
        for c in md["cells"].values())
    return hashlib.sha1(json.dumps([ports, cells]).encode()).hexdigest()


def width(c):
    return int(c["parameters"]["WIDTH"], 2)


def main():
    path, top = sys.argv[1], sys.argv[2]
    mods = json.load(open(path))["modules"]

    # --- reachability: yosys can leave a module behind after opt_clean drops
    # its only instance (CVA6: the shared TLB's lfsr when UseSharedTlb = 0)
    def children(m):
        return [c["type"] for c in mods[m]["cells"].values()
                if c["type"] in mods]

    order, seen = [], set()  # post-order: children before parents

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for ch in children(m):
            visit(ch)
        order.append(m)

    visit(top)
    orphans = sorted({base(m) for m in mods if m not in seen})
    live = {m: mods[m] for m in order}

    # --- module tree
    shapes = collections.defaultdict(set)
    insts = 0
    for m, md in live.items():
        shapes[base(m)].add(shape(md))
        insts += len(children(m))
    print(f"modules {len(live)}, instance cells {insts}, "
          f"source modules {len(shapes)}, "
          f"distinct shapes {sum(len(s) for s in shapes.values())}")
    if orphans:
        print("orphan modules (unreachable from the top, ignored):", orphans)

    # --- cells, flops, memories
    types = collections.Counter(c["type"] for md in live.values()
                                for c in md["cells"].values()
                                if c["type"].startswith("$"))
    flop_bits = sum(width(c) for md in live.values()
                    for c in md["cells"].values()
                    if c["type"] in ("$dff", "$dffe", "$sdff", "$adff"))
    mems = [c for md in live.values() for c in md["cells"].values()
            if c["type"] == "$mem_v2"]
    rw = [c for c in mems if int(c["parameters"]["WR_PORTS"], 2) > 0]
    print(f"cells {sum(types.values())}, flop bits {flop_bits}")
    print(f"memories {len(mems)}: {len(rw)} writable "
          f"({sum(width(c) * int(c['parameters']['SIZE'], 2) for c in rw)} bits), "
          f"{len(mems) - len(rw)} read-only tables")
    print("cell types:", ", ".join(f"{t} {n}" for t, n in types.most_common()))
    odd = [t for t in types if t in ("$dlatch", "$adlatch", "$sr", "$dffsr",
                                     "$aldff", "$adff", "$print", "$check")]
    if odd:
        print("WARNING: cells a one-clock semantics must handle:", odd)

    # --- clocks, traced to the top through instance ports and through
    # PASS-THROUGH modules, transitively (an output that is, possibly via
    # nested pass-throughs, just one of the module's inputs: CVA6's stubbed
    # gated_clk_cell is `clk_out = clk_in`, used inside ct_vfdsu_ctrl)
    in_bits = {m: {b for d in md["ports"].values() if d["direction"] == "input"
                   for b in d["bits"]} for m, md in live.items()}
    parent = {}   # (module, input-port bit) -> (parent module, parent bit)
    through = {}  # (module, net bit) -> (module, net bit) across a pass-through
    passes = {}   # module -> {output-port bit: input-port bit}

    def local(m, b):
        hops = set()
        while (m, b) in through and (m, b) not in hops:
            hops.add((m, b))
            _, b = through[(m, b)]
        return b

    for m in order:  # children first, so passes[child] is ready
        md = live[m]
        for c in md["cells"].values():
            sub = live.get(c["type"])
            if sub is None:
                continue
            conn = {}  # child input bit -> parent bit
            for p, bits in c["connections"].items():
                if sub["ports"][p]["direction"] == "input":
                    for i, b in enumerate(bits):
                        cb = sub["ports"][p]["bits"][i]
                        conn[cb] = b
                        parent[(c["type"], cb)] = (m, b)
            for p, bits in c["connections"].items():
                if sub["ports"][p]["direction"] == "output":
                    for i, b in enumerate(bits):
                        src = passes[c["type"]].get(sub["ports"][p]["bits"][i])
                        if src in conn and conn[src] != b:
                            through[(m, b)] = (m, conn[src])
        passes[m] = {}
        for d in md["ports"].values():
            if d["direction"] == "output":
                for b in d["bits"]:
                    r = local(m, b)
                    if r in in_bits[m]:
                        passes[m][b] = r

    def top_name(m, b):
        hops = set()
        while (m, b) not in hops:
            hops.add((m, b))
            b = local(m, b)
            if b in in_bits[m] and (m, b) in parent:
                m, b = parent[(m, b)]
            else:
                break
        if isinstance(b, str):
            return f"const {b}"
        for n, d in live[m]["netnames"].items():
            if b in d["bits"]:
                return f"{base(m)}.{n}"
        return f"{base(m)}.?"

    clocks = collections.Counter()
    for m, md in live.items():
        for c in md["cells"].values():
            ps = c["parameters"]
            if c["type"] in ("$dff", "$dffe", "$sdff"):
                clocks[(top_name(m, c["connections"]["CLK"][0]),
                        int(ps["CLK_POLARITY"], 2))] += 1
            elif c["type"] == "$mem_v2":
                for en, pol, clk in (("RD_CLK_ENABLE", "RD_CLK_POLARITY", "RD_CLK"),
                                     ("WR_CLK_ENABLE", "WR_CLK_POLARITY", "WR_CLK")):
                    for i, e in enumerate(reversed(ps[en])):
                        if e == "1":
                            clocks[(top_name(m, c["connections"][clk][i]),
                                     int(ps[pol][::-1][i]))] += 1
    print("clocks (net at top, posedge?): " +
          ", ".join(f"{k[0]}/{k[1]} x{v}" for k, v in clocks.most_common()))

    # --- empty modules whose outputs nothing drives
    empty = sorted({base(m) for m, md in live.items()
                    if not md["cells"]
                    and any(isinstance(b, int) and b not in in_bits[m]
                            for d in md["ports"].values()
                            if d["direction"] == "output" for b in d["bits"])})
    if empty:
        print("WARNING: modules with undriven outputs and no cells:", empty)

    tp = mods[top]["ports"]
    print("top ports:", ", ".join(f"{p}:{d['direction'][0]}{len(d['bits'])}"
                                  for p, d in tp.items()))


if __name__ == "__main__":
    main()
