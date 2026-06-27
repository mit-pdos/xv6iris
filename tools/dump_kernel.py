#!/usr/bin/env python3
"""Dump the RISC-V instructions of a built xv6 kernel into a Rocq (.v) file.

The xv6 kernel is an ELF executable (``kernel/kernel``).  We disassemble its
executable sections with ``objdump`` and emit a self-contained Rocq file that
lists every instruction as a record:

    Record kinstr := MkKInstr {
      ki_addr  : Z;     (* virtual address of the instruction          *)
      ki_width : nat;   (* instruction width in bits: 16 (RVC) or 32   *)
      ki_enc   : Z;     (* the instruction word, exactly as Sail fetches it
                           from memory (little-endian bytes -> integer) *)
      ki_asm   : string (* objdump disassembly, kept only for humans    *)
    }.

The ``ki_enc`` value is precisely the integer that the Sail RISC-V model
obtains when it fetches the instruction from memory and assembles the bytes
little-endian.  It is therefore the value to feed into Sail's instruction
decoder (e.g. ``encdec_backwards`` / ``encdec_compressed_backwards``) once the
Sail RISC-V Rocq semantics are imported.

Usage:
    dump_kernel.py [--kernel PATH] [--out PATH] [--objdump PROG] [--name N]

Defaults assume the layout of this project:
    kernel  = <repo>/xv6-riscv/kernel/kernel
    out     = <repo>/rocq/KernelInstrs.v
    objdump = $OBJDUMP or riscv64-linux-gnu-objdump (then a few fallbacks)
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass

# A disassembly line, e.g.:
#     80000004:\t1d813103          \tld\tsp,472(sp) # 8000a1d8 <...>
INSN_RE = re.compile(r"^\s*([0-9a-fA-F]+):\t([0-9a-fA-F ]+?)\t(.*)$")
# A symbol/label header, e.g.:  000000008000001a <spin>:
LABEL_RE = re.compile(r"^[0-9a-fA-F]+\s+<([^>]+)>:\s*$")

OBJDUMP_CANDIDATES = [
    "riscv64-linux-gnu-objdump",
    "riscv64-unknown-elf-objdump",
    "riscv64-elf-objdump",
    "riscv64-none-elf-objdump",
    "riscv64-unknown-linux-gnu-objdump",
    "objdump",
]

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)


@dataclass
class Insn:
    addr: int
    width: int  # 16 or 32 (bits)
    enc: int    # instruction word value (little-endian bytes assembled)
    asm: str    # human-readable disassembly


@dataclass
class Label:
    addr: int
    name: str


def find_objdump(explicit: str | None) -> str:
    if explicit:
        if shutil.which(explicit):
            return explicit
        sys.exit(f"objdump not found: {explicit}")
    env = os.environ.get("OBJDUMP")
    if env and shutil.which(env):
        return env
    for cand in OBJDUMP_CANDIDATES:
        if shutil.which(cand):
            return cand
    sys.exit(
        "Could not find a RISC-V objdump. Tried: "
        + ", ".join(OBJDUMP_CANDIDATES)
        + "\nSet $OBJDUMP or pass --objdump."
    )


def disassemble(objdump: str, kernel: str) -> list[object]:
    """Return an interleaved list of Label and Insn in program order."""
    proc = subprocess.run(
        [objdump, "-d", kernel],
        check=True,
        capture_output=True,
        text=True,
    )
    items: list[object] = []
    for line in proc.stdout.splitlines():
        m = INSN_RE.match(line)
        if m:
            addr = int(m.group(1), 16)
            raw = m.group(2).strip().replace(" ", "")
            # raw is the instruction word printed as a hex value; its length in
            # hex digits gives the width: 4 -> 16 bits (RVC), 8 -> 32 bits.
            nbits = len(raw) * 4
            if nbits not in (16, 32):
                # Skip anything that is not a normal RV32/RVC encoding (objdump
                # may also print >32-bit forms; xv6 does not use them).
                continue
            enc = int(raw, 16)
            asm = re.sub(r"\s+", " ", m.group(3).strip())
            items.append(Insn(addr=addr, width=nbits, enc=enc, asm=asm))
            continue
        m = LABEL_RE.match(line)
        if m:
            # group(1) is "addr <name>"? No: LABEL_RE captures name only.
            # Re-extract the address from the start of the line.
            addr_hex = line.split()[0]
            items.append(Label(addr=int(addr_hex, 16), name=m.group(1)))
    return items


def coq_string(s: str) -> str:
    # In Rocq string literals only the double-quote needs escaping (by doubling).
    # Drop any stray non-printable characters defensively.
    s = "".join(ch for ch in s if 0x20 <= ord(ch) < 0x7F)
    return '"' + s.replace('"', '""') + '"'


def lean_string(s: str) -> str:
    # Lean string literals escape backslash and double-quote with a backslash.
    s = "".join(ch for ch in s if 0x20 <= ord(ch) < 0x7F)
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_lean(items: list[object], out_path: str, kernel: str, objdump: str,
              name: str) -> tuple[int, int]:
    insns = [it for it in items if isinstance(it, Insn)]
    n = len(insns)
    lo = min((it.addr for it in insns), default=0)
    hi = max((it.addr + it.width // 8 for it in insns), default=0)

    lines: list[str] = []
    w = lines.append
    w("/- ------------------------------------------------------------------")
    w("   AUTO-GENERATED by tools/dump_kernel.py -- DO NOT EDIT BY HAND.")
    w(f"   Source kernel : {os.path.relpath(kernel, REPO)}")
    w(f"   Disassembler  : {objdump}")
    w(f"   Instructions  : {n}")
    w(f"   Address range : 0x{lo:x} .. 0x{hi:x}")
    w("   ------------------------------------------------------------------ -/")
    w("")
    w("/-- One instruction of the kernel image.  `enc` is exactly the integer the")
    w("    Sail RISC-V decoder consumes: the instruction word assembled from the")
    w("    little-endian memory bytes.  Feed it to `encdec_backwards`")
    w("    (32-bit) or `encdec_compressed_backwards` (16-bit) as a `BitVec`.")
    w("    `asm` is the objdump disassembly, kept for humans. -/")
    w("structure KInstr where")
    w("  addr  : Nat")
    w("  width : Nat   -- 16 (RVC) or 32 bits")
    w("  enc   : Nat")
    w("  asm   : String")
    w("deriving Repr, Inhabited, DecidableEq")
    w("")
    w("/- Lean elaborates a single huge `List` literal in time super-linear in its")
    w("   length (deeply-nested `cons`), so we emit fixed-size chunks and join")
    w(f"   them.  `{name}` is the full list in program order. -/")
    w("")

    # Emit the instructions in bounded-size chunks to keep `List` literal nesting
    # shallow enough for Lean to elaborate quickly.
    CHUNK = 128
    chunk_idx = 0
    count_in_chunk = 0
    chunk_names: list[str] = []

    def open_chunk(idx: int) -> None:
        chunk_names.append(f"{name}_chunk{idx}")
        w(f"def {name}_chunk{idx} : List KInstr := [")

    open_chunk(chunk_idx)
    cur_label = None
    first_in_chunk = True
    for it in items:
        if isinstance(it, Label):
            cur_label = it
            continue
        if count_in_chunk == CHUNK:
            w("]")
            w("")
            chunk_idx += 1
            count_in_chunk = 0
            first_in_chunk = True
            open_chunk(chunk_idx)
        sep = "  " if first_in_chunk else ", "
        first_in_chunk = False
        if cur_label is not None:
            w(f"  -- <{cur_label.name}> @ 0x{cur_label.addr:x}")
            cur_label = None
        w(
            f"{sep}{{ addr := 0x{it.addr:x}, width := {it.width}, "
            f"enc := 0x{it.enc:x}, asm := {lean_string(it.asm)} }}"
        )
        count_in_chunk += 1
    w("]")
    w("")
    # Join the chunks. `List.flatten` over a small outer list keeps nesting shallow.
    w(f"def {name} : List KInstr := List.flatten [")
    for i, cn in enumerate(chunk_names):
        sep = "  " if i == 0 else ", "
        w(f"{sep}{cn}")
    w("]")
    w("")
    w(f"/- Total instructions = {n} (in {len(chunk_names)} chunks of <= {CHUNK}). -/")
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def load_segments(kernel: str) -> list[tuple[int, bytes]]:
    """Return the ELF's PT_LOAD segments as (vaddr, file_bytes) — the loadable
    on-disk image (code + data; excludes zero-initialised .bss tail)."""
    import struct
    f = open(kernel, "rb").read()
    if f[:4] != b"\x7fELF" or f[4] != 2:
        sys.exit("expected a 64-bit ELF kernel")
    e_phoff = struct.unpack_from("<Q", f, 0x20)[0]
    e_phentsize = struct.unpack_from("<H", f, 0x36)[0]
    e_phnum = struct.unpack_from("<H", f, 0x38)[0]
    segs: list[tuple[int, bytes]] = []
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        p_type = struct.unpack_from("<I", f, off)[0]
        p_offset = struct.unpack_from("<Q", f, off + 8)[0]
        p_vaddr = struct.unpack_from("<Q", f, off + 16)[0]
        p_filesz = struct.unpack_from("<Q", f, off + 32)[0]
        if p_type == 1 and p_filesz:  # PT_LOAD
            segs.append((p_vaddr, f[p_offset:p_offset + p_filesz]))
    return segs


def image_extent(kernel: str) -> tuple[int, int]:
    """Return (base, end) of the loadable image *including* zero-init .bss:
    base = lowest PT_LOAD vaddr, end = highest vaddr + memsz."""
    import struct
    f = open(kernel, "rb").read()
    e_phoff = struct.unpack_from("<Q", f, 0x20)[0]
    e_phentsize = struct.unpack_from("<H", f, 0x36)[0]
    e_phnum = struct.unpack_from("<H", f, 0x38)[0]
    base, end = None, 0
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        if struct.unpack_from("<I", f, off)[0] != 1:  # PT_LOAD
            continue
        p_vaddr = struct.unpack_from("<Q", f, off + 16)[0]
        p_memsz = struct.unpack_from("<Q", f, off + 40)[0]
        base = p_vaddr if base is None else min(base, p_vaddr)
        end = max(end, p_vaddr + p_memsz)
    return (base or 0, end)


def emit_lean_syms(items: list[object], out_path: str, kernel: str,
                   objdump: str, name: str) -> tuple[int, int]:
    """Emit the ELF symbol table as `kernelSymbols : List (String × Nat)` plus a
    `sym : String -> Nat` lookup, so Lean code can name addresses (`sym "main"`)
    instead of hard-coding them."""
    # Derive the matching `nm` from the objdump program (same tool prefix).
    base = os.path.basename(objdump)
    nm = objdump[: -len("objdump")] + "nm" if base.endswith("objdump") else "nm"
    if not shutil.which(nm):
        nm = "nm"
    proc = subprocess.run([nm, kernel], check=True, capture_output=True, text=True)
    # nm lines: "<16-hex-addr> <type> <name>"; undefined symbols have no address.
    rx = re.compile(r"^([0-9a-fA-F]{8,16})\s+\S\s+(\S+)$")
    syms: list[tuple[str, int]] = []
    seen: set[str] = set()
    for line in proc.stdout.splitlines():
        m = rx.match(line)
        if not m:
            continue
        nm_name = m.group(2)
        if nm_name in seen:
            continue
        seen.add(nm_name)
        syms.append((nm_name, int(m.group(1), 16)))
    syms.sort(key=lambda s: s[1])
    n = len(syms)

    lines: list[str] = []
    w = lines.append
    w("/- AUTO-GENERATED by tools/dump_kernel.py (--format lean-syms).")
    w(f"   Symbol table of {os.path.relpath(kernel, REPO)}: {n} symbols.")
    w("   `sym \"name\"` returns the symbol's address (0 if unknown). -/")
    w("")
    CHUNK = 200
    chunk_names: list[str] = []
    for ci in range(0, n, CHUNK):
        cn = f"{name}_chunk{ci // CHUNK}"
        chunk_names.append(cn)
        body = ", ".join(f"({lean_string(s)}, 0x{a:x})" for s, a in syms[ci:ci + CHUNK])
        w(f"def {cn} : List (String × Nat) := [{body}]")
    w("")
    if chunk_names:
        w(f"def {name} : List (String × Nat) := List.flatten [{', '.join(chunk_names)}]")
    else:
        w(f"def {name} : List (String × Nat) := []")
    w("")
    w("/-- Address of a kernel symbol by name (0 if not found). -/")
    w(f"def sym (n : String) : Nat := (({name}.find? (fun p => p.1 == n)).map (·.2)).getD 0")
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def emit_lean_data(items: list[object], out_path: str, kernel: str,
                   objdump: str, name: str) -> tuple[int, int]:
    """Emit the loadable *data* of the kernel image as a `List KInstr` of 64-bit
    words (reusing the KInstr shape; width is in bits).  "Data" = every byte of
    the PT_LOAD image not covered by a dumped instruction, so code (from
    `kernelInstrs`) + this together reconstruct the full on-disk image.  Zero
    bytes inside the image are kept (the model faults on reads of unmapped
    memory, so the data sections must be present in full)."""
    insns = [it for it in items if isinstance(it, Insn)]
    covered = set()
    for it in insns:
        for k in range(it.width // 8):
            covered.add(it.addr + k)

    image: dict[int, int] = {}
    for vaddr, data in load_segments(kernel):
        for k, b in enumerate(data):
            image[vaddr + k] = b

    data_addrs = sorted(a for a in image if a not in covered)
    aset = set(data_addrs)
    # Group into 8-byte aligned words where possible; stray bytes go solo.
    entries: list[tuple[int, int, int]] = []  # (addr, width_bits, value)
    idx = 0
    while idx < len(data_addrs):
        a = data_addrs[idx]
        if a % 8 == 0 and all((a + j) in aset for j in range(8)):
            val = 0
            for j in range(8):
                val |= image[a + j] << (8 * j)
            entries.append((a, 64, val))
            idx += 8
        else:
            entries.append((a, 8, image[a]))
            idx += 1

    n = len(entries)
    lo = min((a for a, _, _ in entries), default=0)
    hi = max((a + w // 8 for a, w, _ in entries), default=0)

    lines: list[str] = []
    w = lines.append
    w("/- AUTO-GENERATED by tools/dump_kernel.py (--format lean-data).")
    w(f"   Loadable data of {os.path.relpath(kernel, REPO)} not covered by")
    w(f"   instructions: {n} words, address range 0x{lo:x}..0x{hi:x}.")
    w("   Reuses `KInstr` (width in bits); load it the same way as the code. -/")
    w("import KernelInstrs")
    w("")
    base, end = image_extent(kernel)
    w(f"/-- Lowest loadable address. -/\ndef kernelMemBase : Nat := 0x{base:x}")
    w(f"/-- End of the loadable image including zero-init .bss (vaddr+memsz). -/")
    w(f"def kernelMemEnd : Nat := 0x{end:x}")
    w("")
    CHUNK = 200
    chunk_names: list[str] = []
    for ci in range(0, n, CHUNK):
        cn = f"{name}_chunk{ci // CHUNK}"
        chunk_names.append(cn)
        body = ", ".join(
            f"{{ addr := 0x{a:x}, width := {wd}, enc := 0x{v:x}, asm := \"\" }}"
            for a, wd, v in entries[ci:ci + CHUNK])
        w(f"def {cn} : List KInstr := [{body}]")
    w("")
    if chunk_names:
        w(f"def {name} : List KInstr := List.flatten [{', '.join(chunk_names)}]")
    else:
        w(f"def {name} : List KInstr := []")
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def emit_lean_decode(items: list[object], out_path: str, kernel: str,
                     objdump: str, name: str) -> tuple[int, int]:
    """Emit a Lean harness that decodes every kernel instruction through the
    (reduced, executable) Sail model and reports coverage.

    Drop the file into the generated model package directory
    (build/model/Lean_RV64D_executable) and run with `lake env lean`.
    """
    insns = [it for it in items if isinstance(it, Insn)]
    # Distinct (enc, width); decode is a pure function of the word.
    pairs = sorted({(it.enc, it.width) for it in insns})
    n_all = len(insns)
    n = len(pairs)

    lines: list[str] = []
    w = lines.append
    w("/- AUTO-GENERATED by tools/dump_kernel.py (--format lean-decode).")
    w("   Place in the generated model package (Lean_RV64D_executable) and run:")
    w("     lake build LeanRV64DExecutable.ZcbInsts   -- compressed decoder (orphan module)")
    w("     lake env lean KernelDecode.lean")
    w(f"   Source kernel: {os.path.relpath(kernel, REPO)}  ({n_all} instrs, {n} distinct). -/")
    w("import LeanRV64DExecutable")
    w("import LeanRV64DExecutable.ZcbInsts   -- encdec_compressed_backwards lives here")
    w("open LeanRV64DExecutable.Functions")
    w("open Sail")
    w("")
    # Distinct encodings, chunked (Lean elaborates big List literals super-linearly).
    CHUNK = 200
    chunk_names: list[str] = []
    for ci in range(0, len(pairs), CHUNK):
        cn = f"{name}_chunk{ci // CHUNK}"
        chunk_names.append(cn)
        body = ", ".join(f"(0x{enc:x}, {wd})" for enc, wd in pairs[ci:ci + CHUNK])
        w(f"def {cn} : List (Nat × Nat) := [{body}]")
    w("")
    w(f"def {name} : List (Nat × Nat) := List.flatten [{', '.join(chunk_names)}]")
    w("")
    w("def isIllegal : instruction → Bool")
    w("  | .ILLEGAL _ => true")
    w("  | .C_ILLEGAL _ => true")
    w("  | _ => false")
    w("")
    w("/-- Decode one word at a freshly-seeded machine state (the reduced model has")
    w("    no `init_model`, so we set the CSRs the decoder reads). -/")
    w("def decodeOne (enc width : Nat) : SailM instruction := do")
    w("  Sail.writeReg Register.misa (0x8000000000141105 : BitVec 64) -- RV64 IMACSU")
    w("  Sail.writeReg Register.cur_privilege Privilege.Machine")
    w("  Sail.writeReg Register.mstatus (0 : BitVec 64)")
    w("  Sail.writeReg Register.menvcfg (0 : BitVec 64)")
    w("  Sail.writeReg Register.senvcfg (0 : BitVec 64)")
    w("  Sail.writeReg Register.mseccfg (0 : BitVec 64)")
    w("  if width == 32 then encdec_backwards (BitVec.ofNat 32 enc)")
    w("  else encdec_compressed_backwards (BitVec.ofNat 16 enc)")
    w("")
    w("/-- Decode the whole kernel; count OK vs ILLEGAL. -/")
    w(f"def coverage : SailM (Nat × Nat) := do")
    w("  let mut ok := 0")
    w("  let mut bad := 0")
    w(f"  for p in {name} do")
    w("    let inst ← decodeOne p.1 p.2")
    w("    if isIllegal inst then bad := bad + 1 else ok := ok + 1")
    w("  pure (ok, bad)")
    w("")
    w("#eval! match coverage.run default with")
    w(f'  | .ok r _ => s!"decoded ok={{r.1}}  illegal={{r.2}}  (of {{{name}.length}} distinct, {n_all} total)"')
    w('  | .error .Unreachable _ => "ABORT: Unreachable (an unset register was read)"')
    w('  | .error _ _ => "ABORT: monadic error"')
    w("")
    w("-- Inspect a single instruction's AST, e.g. the first one:")
    w(f"#eval! match (decodeOne ({name}.head!).1 ({name}.head!).2).run default with")
    w('  | .ok i _ => s!"{repr i}"')
    w('  | .error _ _ => "error"')
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def emit_rocq(items: list[object], out_path: str, kernel: str, objdump: str,
              name: str) -> tuple[int, int]:
    insns = [it for it in items if isinstance(it, Insn)]
    n = len(insns)
    lo = min((it.addr for it in insns), default=0)
    hi = max((it.addr + it.width // 8 for it in insns), default=0)

    # Per-BYTE image: expand each instruction into its little-endian bytes so the
    # map is keyed by individual byte ADDRESS -> byte VALUE.  This makes fetching
    # uniform: a 2- or 4-byte instruction at any alignment is just that many
    # consecutive byte lookups, with no special handling of instruction
    # boundaries or adjacent-instruction windows.  We also keep a per-instruction
    # asm/label comment trail for human readers.
    byte_map: dict[int, int] = {}
    comments: dict[int, str] = {}  # byte addr -> comment to print just before it
    cur_label = None
    for it in items:
        if isinstance(it, Label):
            cur_label = it
            continue
        nb = it.width // 8
        if cur_label is not None:
            comments[it.addr] = f"  (* <{cur_label.name}> @ 0x{cur_label.addr:x} *)"
            cur_label = None
        else:
            comments.setdefault(
                it.addr, f"  (* 0x{it.addr:x}: {it.asm} *)")
        for j in range(nb):
            byte_map[it.addr + j] = (it.enc >> (8 * j)) & 0xff
    addrs = sorted(byte_map)
    nbytes = len(addrs)

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w("(* AUTO-GENERATED by tools/dump_kernel.py -- DO NOT EDIT BY HAND.      *)")
    w(f"(* Source kernel : {os.path.relpath(kernel, REPO)}")
    w(f"   Disassembler : {objdump}")
    w(f"   Instructions : {n}   Bytes : {nbytes}")
    w(f"   Address range: 0x{lo:x} .. 0x{hi:x}                              *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import List ZArith.")
    w("From stdpp Require Import gmap.")
    w("From stdpp.bitvector Require Import definitions.")
    w("Import ListNotations.")
    w("")
    w("(* The kernel text image, exposed as a [gmap] keyed by individual byte")
    w("   ADDRESS mapping to that byte's VALUE (a [bv 8]).  Fetching an")
    w("   instruction at [pc] of width [W] bytes is just [W] consecutive byte")
    w("   lookups ([kernel_bytes !! pc], [!! (pc+1)], ...), so the 2- vs 4-byte")
    w("   encodings and adjacent-byte windows need no special handling.  The map")
    w("   is built from a single flat (address, byte) list with [list_to_map];")
    w("   no chunking is needed because each entry is tiny (two numbers). *)")
    w("")
    w(f"Definition {name} : gmap Z (bv 8) := list_to_map [")
    for i, a in enumerate(addrs):
        if a in comments:
            w(comments[a])
        sep = "  " if i == 0 else "; "
        w(f"{sep}((0x{a:x})%Z, Z_to_bv 8 (0x{byte_map[a]:x})%Z)")
    w("].")
    w("")
    w(f"(* Total bytes = {nbytes} (from {n} instructions); keys are byte")
    w(f"   addresses, so [{name} !! addr] yields that byte. *)")
    w("")
    # CRITICAL for build speed: keep typeclass resolution from ever unfolding this
    # giant map.  Without this, resolving e.g. [Persistent ([∗ map] .. kernel_bytes ..)]
    # forces the 20k-entry [list_to_map] and takes ~2 MINUTES per resolution; with it,
    # ~0ms.  [vm_compute]/[reflexivity] still unfold it (they ignore this), so byte
    # lookups are unaffected.
    w(f"Global Typeclasses Opaque {name}.")
    w("")

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def emit_rocq_data(items: list[object], out_path: str, kernel: str,
                   objdump: str, name: str) -> tuple[int, int]:
    """The loadable DATA of the kernel image (every PT_LOAD byte NOT covered by a
    dumped instruction), as a PER-BYTE `gmap Z (bv 8)` keyed by byte ADDRESS ->
    byte VALUE -- exactly like [kernel_bytes] for the code.  Plus [kernelMemBase]
    and [kernelMemEnd] (= vaddr+memsz, INCLUDING zero-init .bss).  [kernel_bytes]
    (code) + this map = the full on-disk image; the BSS zero-init region is
    [kernelMemBase, kernelMemEnd) minus the loaded bytes.  ONE flat [list_to_map]
    (no chunking; each entry is tiny), and [Typeclasses Opaque] so resolution
    never forces the map (cf. kernel_bytes)."""
    insns = [it for it in items if isinstance(it, Insn)]
    covered: set[int] = set()
    for it in insns:
        for k in range(it.width // 8):
            covered.add(it.addr + k)

    image: dict[int, int] = {}
    for vaddr, data in load_segments(kernel):
        for k, b in enumerate(data):
            image[vaddr + k] = b

    data_addrs = sorted(a for a in image if a not in covered)
    n = len(data_addrs)
    lo = data_addrs[0] if data_addrs else 0
    hi = (data_addrs[-1] + 1) if data_addrs else 0
    base, end = image_extent(kernel)

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w("(* AUTO-GENERATED by tools/dump_kernel.py (--format rocq-data).        *)")
    w(f"(* Loadable data of {os.path.relpath(kernel, REPO)} not covered by")
    w(f"   instructions: {n} bytes, address range 0x{lo:x} .. 0x{hi:x}.")
    w("   Per-byte [gmap], same shape as [kernel_bytes] for the code.        *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import List ZArith.")
    w("From stdpp Require Import gmap.")
    w("From stdpp.bitvector Require Import definitions.")
    w("Import ListNotations.")
    w("")
    w("(* Lowest loadable address. *)")
    w(f"Definition kernelMemBase : Z := 0x{base:x}%Z.")
    w("(* End of the loadable image INCLUDING zero-init .bss (vaddr + memsz). *)")
    w(f"Definition kernelMemEnd : Z := 0x{end:x}%Z.")
    w("")
    w(f"Definition {name} : gmap Z (bv 8) := list_to_map [")
    for i, a in enumerate(data_addrs):
        sep = "  " if i == 0 else "; "
        w(f"{sep}((0x{a:x})%Z, Z_to_bv 8 (0x{image[a]:x})%Z)")
    w("].")
    w("")
    # Keep typeclass resolution from ever forcing this giant map (cf. kernel_bytes).
    w(f"Global Typeclasses Opaque {name}.")
    w("")
    w(f"(* Total data bytes = {n}; keys are byte addresses, [{name} !! addr]. *)")
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def emit_rocq_syms(items: list[object], out_path: str, kernel: str,
                   objdump: str, name: str) -> tuple[int, int]:
    """Rocq mirror of emit_lean_syms: the ELF symbol table as
    `kernel_symbols : list (string * Z)` (chunked) plus a `sym : string -> Z`
    lookup (0 if unknown), so proofs can name addresses (`sym "main"`)."""
    base = os.path.basename(objdump)
    nm = objdump[: -len("objdump")] + "nm" if base.endswith("objdump") else "nm"
    if not shutil.which(nm):
        nm = "nm"
    proc = subprocess.run([nm, kernel], check=True, capture_output=True, text=True)
    rx = re.compile(r"^([0-9a-fA-F]{8,16})\s+\S\s+(\S+)$")
    syms: list[tuple[str, int]] = []
    seen: set[str] = set()
    for line in proc.stdout.splitlines():
        m = rx.match(line)
        if not m:
            continue
        nm_name = m.group(2)
        if nm_name in seen:
            continue
        seen.add(nm_name)
        syms.append((nm_name, int(m.group(1), 16)))
    syms.sort(key=lambda s: s[1])
    n = len(syms)

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w("(* AUTO-GENERATED by tools/dump_kernel.py (--format rocq-syms).        *)")
    w(f"(* Symbol table of {os.path.relpath(kernel, REPO)}: {n} symbols.")
    w("   A [gmap string Z] keyed by symbol NAME -> address; [sym \"name\"]")
    w("   returns the address (0 if unknown).                                *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import ZArith String.")
    w("From stdpp Require Import gmap strings.")
    w("")
    w("(* Symbol table as a name-keyed [gmap].  ONE flat [list_to_map] (no chunking;")
    w("   each entry is tiny), and [Typeclasses Opaque] so resolution never forces")
    w("   the map (cf. kernel_bytes). *)")
    w(f"Definition {name} : gmap string Z := list_to_map [")
    for i, (s, a) in enumerate(syms):
        sep = "  " if i == 0 else "; "
        w(f"{sep}({coq_string(s)}%string, (0x{a:x})%Z)")
    w("].")
    w("")
    w(f"Global Typeclasses Opaque {name}.")
    w("")
    w("(* Address of a kernel symbol by name (0 if not found). *)")
    w("Definition sym (q : string) : Z :=")
    w(f"  match {name} !! q with")
    w("  | Some a => a")
    w("  | None => 0%Z")
    w("  end.")
    w("")
    w(f"(* Total symbols = {n}; [{name} !! \"name\"] / [sym \"name\"]. *)")
    w("")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    return n, len(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--kernel", default=os.path.join(REPO, "xv6-riscv", "kernel", "kernel"))
    ap.add_argument("--format",
                    choices=["lean", "lean-data", "lean-syms", "lean-decode",
                             "rocq", "rocq-data", "rocq-syms"],
                    default="lean",
                    help="output: 'lean' (instruction data), 'lean-data' "
                         "(loadable data words), 'lean-syms' (symbol table), "
                         "'lean-decode' (decode/coverage harness), or 'rocq'. "
                         "Default: lean")
    ap.add_argument("--out", default=None,
                    help="output file (default depends on --format)")
    ap.add_argument("--objdump", default=None)
    ap.add_argument("--name", default=None,
                    help="name of the generated instruction-list definition")
    args = ap.parse_args()

    if not os.path.exists(args.kernel):
        sys.exit(f"kernel not found: {args.kernel}\n"
                 "Build it first (cd xv6-riscv && make kernel/kernel).")

    if args.format == "lean":
        out = args.out or os.path.join(REPO, "lean", "KernelInstrs.lean")
        name = args.name or "kernelInstrs"
        emit_fn = emit_lean
    elif args.format == "lean-data":
        out = args.out or os.path.join(REPO, "lean", "KernelData.lean")
        name = args.name or "kernelData"
        emit_fn = emit_lean_data
    elif args.format == "lean-syms":
        out = args.out or os.path.join(REPO, "lean", "KernelSyms.lean")
        name = args.name or "kernelSymbols"
        emit_fn = emit_lean_syms
    elif args.format == "lean-decode":
        out = args.out or os.path.join(REPO, "lean", "KernelDecode.lean")
        name = args.name or "kernelEncs"
        emit_fn = emit_lean_decode
    elif args.format == "rocq-data":
        out = args.out or os.path.join(REPO, "kernel-rocq", "KernelData.v")
        name = args.name or "kernel_data"
        emit_fn = emit_rocq_data
    elif args.format == "rocq-syms":
        out = args.out or os.path.join(REPO, "kernel-rocq", "KernelSyms.v")
        name = args.name or "kernel_symbols"
        emit_fn = emit_rocq_syms
    else:
        out = args.out or os.path.join(REPO, "rocq", "KernelInstrs.v")
        name = args.name or "kernel_bytes"
        emit_fn = emit_rocq

    objdump = find_objdump(args.objdump)
    items = disassemble(objdump, args.kernel)
    n, nlines = emit_fn(items, out, args.kernel, objdump, name)
    print(f"Wrote {n} instructions ({nlines} lines) to {out}")


if __name__ == "__main__":
    main()
