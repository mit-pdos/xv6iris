#!/usr/bin/env python3
"""Dump a RISC-V ELF image into Rocq (.v) / Lean definitions.

Works for any statically-linked rv64 ELF built by the xv6 tree: the KERNEL
(``xv6-riscv/kernel/kernel``, loaded at 0x80000000 in S/M-mode) and the
USER-SPACE programs (``xv6-riscv/user/_sync`` & friends, linked at virtual
address 0 by ``user/user.ld`` and loaded by ``exec()`` into a per-process page
table).  Nothing here is kernel-specific: every generated name is derived from
``--prefix``, so a kernel dump and a user-program dump can be `Require`d into
the same proof without clashing.

We disassemble the executable sections with ``objdump`` and emit:

  ``--format rocq``       the TEXT image as ``<prefix>_bytes : gmap Z (bv 8)``,
                          keyed by byte address, plus ``<prefix>_instrs``, a
                          decode index (instruction number -> addr/width/enc).
  ``--format rocq-data``  every loadable byte NOT covered by an instruction, as
                          ``<prefix>_data : gmap Z (bv 8)``, plus the image
                          geometry the loader needs: ``<prefix>MemBase``,
                          ``<prefix>MemEnd``, ``<prefix>Entry`` (the ELF entry
                          pc) and ``<prefix>_segments`` (the PT_LOAD table).
  ``--format rocq-syms``  the symbol table, one ``Definition <sym> : Z`` each.

  (``lean``, ``lean-data``, ``lean-syms``, ``lean-decode`` are the Lean mirrors
  from the previous iteration of this development.)

The byte VALUES are exactly what the Sail RISC-V model fetches from memory: an
instruction word is its little-endian bytes assembled into an integer, i.e. the
value to feed ``encdec_backwards`` / ``encdec_compressed_backwards``.

Usage:
    dump_elf.py [--elf PATH] [--prefix P] [--format F] [--out PATH]
                [--objdump PROG] [--name N]

Defaults assume the layout of this project:
    elf     = <repo>/xv6-riscv/kernel/kernel
    prefix  = derived from the ELF basename ("_sync" -> "sync")
    objdump = $OBJDUMP or riscv64-linux-gnu-objdump (then a few fallbacks)

Outputs are only rewritten when their content actually changes, so re-running
the dumper (e.g. after an unrelated edit to this script) does not touch the
mtime of a generated .v and therefore does not trigger a Rocq rebuild.
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
GEN_BY = "tools/" + os.path.basename(__file__)


def write_if_changed(path: str, text: str) -> None:
    """Write `text` to `path`, but leave the file (and its mtime) alone when the
    content is already identical.  The generated .v files are prerequisites of a
    Rocq build; rewriting one with identical bytes would still invalidate every
    .vo that depends on it."""
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    try:
        with open(path) as f:
            if f.read() == text:
                return
    except FileNotFoundError:
        pass
    with open(path, "w") as f:
        f.write(text)


@dataclass
class Names:
    """Every generated Rocq/Lean identifier, derived from one `--prefix`.

    The kernel dump keeps the historical names (`kernel_bytes`, `kernel_data`,
    `kernelMemBase`, ...); a user program linked at address 0 gets `sync_bytes`,
    `syncMemBase`, ... so both can be `Require`d side by side."""
    prefix: str          # "kernel", "sync", ...

    @property
    def camel(self) -> str:      # "kernel" -> "Kernel";  "sync" -> "Sync"
        return "".join(p.capitalize() for p in self.prefix.split("_"))

    @property
    def bytes_(self) -> str:  return f"{self.prefix}_bytes"
    @property
    def instrs(self) -> str:  return f"{self.prefix}_instrs"
    @property
    def data(self) -> str:    return f"{self.prefix}_data"
    @property
    def syms(self) -> str:    return f"{self.prefix}_symbols"
    @property
    def base(self) -> str:    return f"{self.prefix}MemBase"
    @property
    def end(self) -> str:     return f"{self.prefix}MemEnd"
    @property
    def entry(self) -> str:   return f"{self.prefix}Entry"
    @property
    def segs(self) -> str:    return f"{self.prefix}_segments"
    @property
    def rodata_end(self) -> str: return f"{self.prefix}RodataEnd"
    # The decode-index RECORD keeps one fixed name across all images.  It holds
    # no image-specific data (addr/width/enc), and naming it per-prefix would
    # rewrite every one of the ~8500 entries of a kernel re-dump — burying a
    # real address change in thousands of lines of rename noise, in exactly the
    # diff you re-dump in order to read.  A file Requiring two dumps qualifies
    # (`Kernel.KernelInstrs.kinstr` vs `User.SyncInstrs.kinstr`); the maps
    # themselves, which is what proofs actually name, are prefixed.
    @property
    def record(self) -> str:  return "kinstr"
    @property
    def ctor(self) -> str:    return "MkKInstr"

    # Lean mirrors (camelCase, as in the previous iteration of this project).
    @property
    def lean_instrs(self) -> str: return f"{self.prefix}Instrs"
    @property
    def lean_data(self) -> str:   return f"{self.prefix}Data"
    @property
    def lean_syms(self) -> str:   return f"{self.prefix}Symbols"
    @property
    def lean_encs(self) -> str:   return f"{self.prefix}Encs"


def default_prefix(elf: str) -> str:
    """A dump prefix from the ELF's file name: `kernel/kernel` -> `kernel`,
    `user/_sync` -> `sync` (xv6 links user programs as `_<name>`)."""
    base = os.path.basename(elf).lstrip("_")
    base = re.sub(r"[^A-Za-z0-9_]", "_", base)
    if not re.match(r"^[A-Za-z_]", base):
        base = "_" + base
    return base


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


def emit_lean(items: list[object], out_path: str, elf: str, objdump: str,
              names: Names) -> tuple[int, int]:
    name = names.lean_instrs
    insns = [it for it in items if isinstance(it, Insn)]
    n = len(insns)
    lo = min((it.addr for it in insns), default=0)
    hi = max((it.addr + it.width // 8 for it in insns), default=0)

    lines: list[str] = []
    w = lines.append
    w("/- ------------------------------------------------------------------")
    w(f"   AUTO-GENERATED by {GEN_BY} -- DO NOT EDIT BY HAND.")
    w(f"   Source ELF    : {os.path.relpath(elf, REPO)}")
    w(f"   Disassembler  : {objdump}")
    w(f"   Instructions  : {n}")
    w(f"   Address range : 0x{lo:x} .. 0x{hi:x}")
    w("   ------------------------------------------------------------------ -/")
    w("")
    w("/-- One instruction of the image.  `enc` is exactly the integer the")
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

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


@dataclass
class Segment:
    """One PT_LOAD program header: what the loader must map, and from where."""
    vaddr: int
    filesz: int
    memsz: int
    flags: int          # PF_X=1, PF_W=2, PF_R=4
    data: bytes         # the `filesz` on-disk bytes

    def flag_str(self) -> str:
        return ("R" if self.flags & 4 else "-") + \
               ("W" if self.flags & 2 else "-") + \
               ("X" if self.flags & 1 else "-")


@dataclass
class Sect:
    """One ALLOCATED section header.  The program headers say only "one RWX
    PT_LOAD" (the linker merges everything into a single segment), so the
    read-only/writable split of the loaded image is visible ONLY here."""
    name: str
    addr: int
    size: int
    flags: int          # SHF_WRITE=1, SHF_ALLOC=2, SHF_EXECINSTR=4
    has_bits: bool      # SHT_NOBITS (.bss) has no file contents

    @property
    def writable(self) -> bool: return bool(self.flags & 1)

    def flag_str(self) -> str:
        return ("r" if self.flags & 2 else "-") + \
               ("w" if self.flags & 1 else "-") + \
               ("x" if self.flags & 4 else "-")


@dataclass
class Elf:
    """The bits of a 64-bit little-endian ELF this dumper needs: the entry pc
    and the PT_LOAD segments.  A user program (`user/_sync`) has a low, often
    ZERO, base vaddr and an entry that is *not* the first byte of .text (xv6
    links `start` ahead of `main`), so neither may be assumed."""
    path: str
    entry: int
    segments: list[Segment]     # PT_LOAD only, in program-header order
    sections: list[Sect]        # SHF_ALLOC only, in address order


def read_elf(path: str) -> Elf:
    import struct
    f = open(path, "rb").read()
    if f[:4] != b"\x7fELF" or f[4] != 2 or f[5] != 1:
        sys.exit(f"{path}: expected a 64-bit little-endian ELF")
    e_entry = struct.unpack_from("<Q", f, 0x18)[0]
    e_phoff = struct.unpack_from("<Q", f, 0x20)[0]
    e_phentsize = struct.unpack_from("<H", f, 0x36)[0]
    e_phnum = struct.unpack_from("<H", f, 0x38)[0]
    segs: list[Segment] = []
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        p_type = struct.unpack_from("<I", f, off)[0]
        if p_type != 1:  # PT_LOAD
            continue
        p_flags = struct.unpack_from("<I", f, off + 4)[0]
        p_offset = struct.unpack_from("<Q", f, off + 8)[0]
        p_vaddr = struct.unpack_from("<Q", f, off + 16)[0]
        p_filesz = struct.unpack_from("<Q", f, off + 32)[0]
        p_memsz = struct.unpack_from("<Q", f, off + 40)[0]
        segs.append(Segment(vaddr=p_vaddr, filesz=p_filesz, memsz=p_memsz,
                            flags=p_flags,
                            data=f[p_offset:p_offset + p_filesz]))
    if not segs:
        sys.exit(f"{path}: no PT_LOAD segments")
    # --- the section headers, ALLOC only (what the loader actually maps) ---
    e_shoff = struct.unpack_from("<Q", f, 0x28)[0]
    e_shentsize = struct.unpack_from("<H", f, 0x3A)[0]
    e_shnum = struct.unpack_from("<H", f, 0x3C)[0]
    e_shstrndx = struct.unpack_from("<H", f, 0x3E)[0]
    raw = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        raw.append((struct.unpack_from("<I", f, off)[0],       # sh_name
                    struct.unpack_from("<I", f, off + 4)[0],   # sh_type
                    struct.unpack_from("<Q", f, off + 8)[0],   # sh_flags
                    struct.unpack_from("<Q", f, off + 16)[0],  # sh_addr
                    struct.unpack_from("<Q", f, off + 24)[0],  # sh_offset
                    struct.unpack_from("<Q", f, off + 32)[0])) # sh_size
    strtab_off = raw[e_shstrndx][4] if e_shnum else 0

    def shname(n: int) -> str:
        end = f.index(b"\0", strtab_off + n)
        return f[strtab_off + n:end].decode()

    sects = [Sect(name=shname(nm), addr=addr, size=size, flags=flags,
                  has_bits=(typ != 8))                          # 8 = SHT_NOBITS
             for (nm, typ, flags, addr, _o, size) in raw if flags & 2]
    sects.sort(key=lambda s: (s.addr, s.size))
    return Elf(path=path, entry=e_entry, segments=segs, sections=sects)


def rodata_end(elf_info: Elf) -> int:
    """The lowest address of a WRITABLE allocated section -- i.e. one past the
    last byte of read-only image material (.text/.rodata/.eh_frame).  Every
    loadable byte BELOW it is immutable for the life of the image; a byte at
    or above it may be stored to at run time, so a proof may never reside one
    at a discarded (permanently read-only) fraction.  An image with no
    writable allocated section has nothing above the read-only material, so
    the answer is the end of the image."""
    w = [s.addr for s in elf_info.sections if s.writable]
    return min(w) if w else image_extent(elf_info.path)[1]


def load_segments(elf_path: str) -> list[tuple[int, bytes]]:
    """The loadable on-disk image as (vaddr, file_bytes) per PT_LOAD segment
    (code + data; excludes the zero-initialised .bss tail).  A segment with
    `filesz = 0` (xv6 user programs have one: .data is empty, .bss is not)
    contributes no bytes."""
    return [(s.vaddr, s.data) for s in read_elf(elf_path).segments if s.filesz]


def image_extent(elf_path: str) -> tuple[int, int]:
    """Return (base, end) of the loadable image *including* zero-init .bss:
    base = lowest PT_LOAD vaddr, end = highest vaddr + memsz."""
    segs = read_elf(elf_path).segments
    return (min(s.vaddr for s in segs), max(s.vaddr + s.memsz for s in segs))


def emit_lean_syms(items: list[object], out_path: str, elf: str,
                   objdump: str, names: Names) -> tuple[int, int]:
    """Emit the ELF symbol table as `<prefix>Symbols : List (String × Nat)` plus
    a `sym : String -> Nat` lookup, so Lean code can name addresses
    (`sym "main"`) instead of hard-coding them."""
    name = names.lean_syms
    kernel = elf
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
    w(f"/- AUTO-GENERATED by {GEN_BY} (--format lean-syms).")
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

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


def emit_lean_data(items: list[object], out_path: str, elf: str,
                   objdump: str, names: Names) -> tuple[int, int]:
    """Emit the loadable *data* of the image as a `List KInstr` of 64-bit
    words (reusing the KInstr shape; width is in bits).  "Data" = every byte of
    the PT_LOAD image not covered by a dumped instruction, so code (from
    the instruction dump) + this together reconstruct the full on-disk image.
    Zero bytes inside the image are kept (the model faults on reads of unmapped
    memory, so the data sections must be present in full)."""
    name, kernel = names.lean_data, elf
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
    w(f"/- AUTO-GENERATED by {GEN_BY} (--format lean-data).")
    w(f"   Loadable data of {os.path.relpath(kernel, REPO)} not covered by")
    w(f"   instructions: {n} words, address range 0x{lo:x}..0x{hi:x}.")
    w("   Reuses `KInstr` (width in bits); load it the same way as the code. -/")
    w(f"import {names.camel}Instrs")
    w("")
    elf_info = read_elf(kernel)
    base, end = image_extent(kernel)
    w(f"/-- Lowest loadable address. -/\ndef {names.base} : Nat := 0x{base:x}")
    w(f"/-- End of the loadable image including zero-init .bss (vaddr+memsz). -/")
    w(f"def {names.end} : Nat := 0x{end:x}")
    w(f"/-- ELF entry point (the initial pc). -/")
    w(f"def {names.entry} : Nat := 0x{elf_info.entry:x}")
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

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


def emit_lean_decode(items: list[object], out_path: str, elf: str,
                     objdump: str, names: Names) -> tuple[int, int]:
    """Emit a Lean harness that decodes every instruction of the image through
    the (reduced, executable) Sail model and reports coverage.

    Drop the file into the generated model package directory
    (build/model/Lean_RV64D_executable) and run with `lake env lean`.
    """
    name, kernel = names.lean_encs, elf
    insns = [it for it in items if isinstance(it, Insn)]
    # Distinct (enc, width); decode is a pure function of the word.
    pairs = sorted({(it.enc, it.width) for it in insns})
    n_all = len(insns)
    n = len(pairs)

    lines: list[str] = []
    w = lines.append
    w(f"/- AUTO-GENERATED by {GEN_BY} (--format lean-decode).")
    w("   Place in the generated model package (Lean_RV64D_executable) and run:")
    w("     lake build LeanRV64DExecutable.ZcbInsts   -- compressed decoder (orphan module)")
    w(f"     lake env lean {names.camel}Decode.lean")
    w(f"   Source ELF: {os.path.relpath(kernel, REPO)}  ({n_all} instrs, {n} distinct). -/")
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
    w("/-- Decode the whole image; count OK vs ILLEGAL. -/")
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

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


def rocq_range_lemmas(w, name: str, addrs: list[int]) -> None:
    """Emit the KEY-RANGE facts for a per-byte `gmap Z (bv 8)`.

    A consumer that has to turn the map into a per-address resource needs
    "every key is in [lo, hi)", and the direction it needs is the one that
    is FATAL to prove by hand: going back through `list_to_map` (stdpp's
    `elem_of_list_to_map_2`) puts the whole 20k-entry list into the proof
    term and the `Qed` never returns.  So the fact is generated here as a
    DECIDABLE check closed by one `vm_compute`: the proof term is `eq_refl`,
    no list, and it elaborates in about a second.

    The bounds are emitted as LITERALS -- kernel-rocq/ sits below iris/ and
    cannot name `ram_lo`/`text_end`/`img_end`; the iris side bridges the
    literals by `lia`.
    """
    lo = addrs[0]
    hi = addrs[-1] + 1
    w("(* KEY RANGE.  [%s_lo <= a < %s_hi] for every key [a]: the decidable" % (name, name))
    w("   [map_Forall] check, closed by one [vm_compute], so the proof term is")
    w("   [eq_refl] and no list ever enters it.  Bounds are LITERALS (this file")
    w("   is below iris/ and cannot name [ram_lo]/[text_end]/[img_end]); the")
    w("   consumer bridges them arithmetically. *)")
    w(f"Definition {name}_lo : Z := 0x{lo:x}%Z.")
    w(f"Definition {name}_hi : Z := 0x{hi:x}%Z.")
    w("")
    w(f"Lemma {name}_range_bool :")
    w(f"  bool_decide (map_Forall (fun (a : Z) (_ : bv 8) =>")
    w(f"                 ({name}_lo <= a < {name}_hi)%Z) {name}) = true.")
    w("Proof. vm_compute. reflexivity. Qed.")
    w("")
    w(f"Lemma {name}_range (a : Z) (b : bv 8) :")
    w(f"  {name} !! a = Some b -> ({name}_lo <= a < {name}_hi)%Z.")
    w("Proof.")
    w(f"  pose proof {name}_range_bool as H.")
    w("  apply bool_decide_eq_true_1 in H. exact (H a b).")
    w("Qed.")
    w("")


def text_byte_map(items: list[object], elf_path: str) -> tuple[dict[int, int], int]:
    """The TEXT image as byte address -> byte value, plus the padding a FETCH
    can actually reach.

    objdump disassembles instructions, so the alignment bytes gas leaves
    between functions appear nowhere in its output and an instruction-only map
    has HOLES.  That is not cosmetic: a fetch reads a fixed 4-byte window, so
    the last (compressed) instruction of a function whose successor starts 2
    bytes later cannot discharge its byte obligation.  Found at [sys_pipe +
    0xe0], where a c.ret sits 2 bytes before <kernelvec>.

    Only the WINDOW is filled -- for each instruction, bytes [addr, addr+4) --
    not every gap.  Filling all of them added 1524 entries and pushed
    `list_to_map` over a STACK OVERFLOW at ~24.8k; the window needs a few
    hundred and no proof can fetch further than that anyway.

    Returns (map, number of padding bytes filled)."""
    insns = [it for it in items if isinstance(it, Insn)]
    bm: dict[int, int] = {}
    for it in insns:
        for j in range(it.width // 8):
            bm[it.addr + j] = (it.enc >> (8 * j)) & 0xff
    if not bm:
        return bm, 0
    image: dict[int, int] = {}
    for vaddr, data in load_segments(elf_path):
        for k, b in enumerate(data):
            image[vaddr + k] = b
    pad = 0
    for it in insns:
        for a in range(it.addr, it.addr + 4):
            if a not in bm and a in image:
                bm[a] = image[a]
                pad += 1
    return bm, pad


def emit_rocq(items: list[object], out_path: str, elf: str, objdump: str,
              names: Names) -> tuple[int, int]:
    name, kernel = names.bytes_, elf
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
    byte_map, n_pad = text_byte_map(items, elf)
    comments: dict[int, str] = {}  # byte addr -> comment to print just before it
    cur_label = None
    for it in items:
        if isinstance(it, Label):
            cur_label = it
            continue
        if cur_label is not None:
            comments[it.addr] = f"  (* <{cur_label.name}> @ 0x{cur_label.addr:x} *)"
            cur_label = None
        else:
            comments.setdefault(
                it.addr, f"  (* 0x{it.addr:x}: {it.asm} *)")
    addrs = sorted(byte_map)
    nbytes = len(addrs)

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w(f"(* AUTO-GENERATED by {GEN_BY} -- DO NOT EDIT BY HAND.         *)")
    w(f"(* Source ELF    : {os.path.relpath(kernel, REPO)}")
    w(f"   Disassembler : {objdump}")
    w(f"   Instructions : {n}   Bytes : {nbytes}   (of which padding: {n_pad})")
    w(f"   Address range: 0x{lo:x} .. 0x{hi:x}                              *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import List ZArith.")
    w("From stdpp Require Import gmap.")
    w("From stdpp.bitvector Require Import definitions.")
    w("Import ListNotations.")
    w("")
    w("(* The text image, exposed as a [gmap] keyed by individual byte")
    w("   ADDRESS mapping to that byte's VALUE (a [bv 8]).  Fetching an")
    w("   instruction at [pc] of width [W] bytes is just [W] consecutive byte")
    w(f"   lookups ([{name} !! pc], [!! (pc+1)], ...), so the 2- vs 4-byte")
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
    # giant map.  Without this, resolving e.g. [Persistent ([∗ map] .. <prefix>_bytes ..)]
    # forces the 20k-entry [list_to_map] and takes ~2 MINUTES per resolution; with it,
    # ~0ms.  [vm_compute]/[reflexivity] still unfold it (they ignore this), so byte
    # lookups are unaffected.
    w(f"Global Typeclasses Opaque {name}.")
    w("")
    rocq_range_lemmas(w, name, addrs)
    # Auxiliary per-instruction DECODE-INDEX metadata: just (address, width-bits,
    # encoding) per instruction, NO asm, so the flat list elaborates without
    # chunking.  This is NOT the byte-storage format (that is the per-byte
    # [<prefix>_bytes] above, which owns every byte); it only lets a proof name
    # the i-th instruction so it can pick the right decode lemma + fetch window.
    # The window bytes themselves are still extracted per-byte from the map.
    w(f"Record {names.record} := {names.ctor} "
      "{ ki_addr : Z; ki_width : nat; ki_enc : Z }.")
    w("")
    w("(* Keyed by instruction INDEX (program order, 0-based) for O(log n) lookup")
    w("   of the i-th instruction.  [Typeclasses Opaque] so resolution never forces")
    w(f"   the map (cf. {name}). *)")
    cur_label2 = None
    w(f"Definition {names.instrs} : gmap Z {names.record} := list_to_map [")
    first2 = True
    insn_idx = 0
    for it in items:
        if isinstance(it, Label):
            cur_label2 = it
            continue
        if cur_label2 is not None:
            w(f"  (* <{cur_label2.name}> @ 0x{cur_label2.addr:x} *)")
            cur_label2 = None
        sep = "  " if first2 else "; "
        first2 = False
        w(f"{sep}(({insn_idx})%Z, {names.ctor} (0x{it.addr:x})%Z {it.width}%nat (0x{it.enc:x})%Z)")
        insn_idx += 1
    w("].")
    w("")
    w(f"Global Typeclasses Opaque {names.instrs}.")
    w("")

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


def emit_rocq_data(items: list[object], out_path: str, elf: str,
                   objdump: str, names: Names) -> tuple[int, int]:
    """The loadable DATA of the image (every PT_LOAD byte NOT covered by a
    dumped instruction), as a PER-BYTE `gmap Z (bv 8)` keyed by byte ADDRESS ->
    byte VALUE -- exactly like [<prefix>_bytes] for the code.  Plus the geometry
    a loader needs: [<prefix>MemBase], [<prefix>MemEnd] (= vaddr+memsz,
    INCLUDING zero-init .bss), [<prefix>Entry] (the initial pc) and
    [<prefix>_segments] (the PT_LOAD table: what to map, and with what
    permissions).  [<prefix>_bytes] (code) + this map = the full on-disk image;
    the BSS zero-init region is [MemBase, MemEnd) minus the loaded bytes.  ONE
    flat [list_to_map] (no chunking; each entry is tiny), and [Typeclasses
    Opaque] so resolution never forces the map."""
    name, kernel = names.data, elf
    insns = [it for it in items if isinstance(it, Insn)]
    # exactly what <prefix>_bytes covers -- instructions AND the inter-function
    # padding it now fills -- so no byte lands in both maps
    covered = set(text_byte_map(items, kernel)[0])

    image: dict[int, int] = {}
    for vaddr, data in load_segments(kernel):
        for k, b in enumerate(data):
            image[vaddr + k] = b

    data_addrs = sorted(a for a in image if a not in covered)
    n = len(data_addrs)
    lo = data_addrs[0] if data_addrs else 0
    hi = (data_addrs[-1] + 1) if data_addrs else 0
    base, end = image_extent(kernel)
    elf_info = read_elf(kernel)

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w(f"(* AUTO-GENERATED by {GEN_BY} (--format rocq-data).           *)")
    w(f"(* Loadable data of {os.path.relpath(kernel, REPO)} not covered by")
    w(f"   instructions: {n} bytes, address range 0x{lo:x} .. 0x{hi:x}.")
    w(f"   Per-byte [gmap], same shape as [{names.bytes_}] for the code.")
    w("                                                                       *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import List ZArith.")
    w("From stdpp Require Import gmap.")
    w("From stdpp.bitvector Require Import definitions.")
    w("Import ListNotations.")
    w("")
    w("(* Lowest loadable address. *)")
    w(f"Definition {names.base} : Z := 0x{base:x}%Z.")
    w("(* End of the loadable image INCLUDING zero-init .bss (vaddr + memsz). *)")
    w(f"Definition {names.end} : Z := 0x{end:x}%Z.")
    w("(* ELF entry point: the pc the image starts executing at.  For a user")
    w("   program this is what [exec] puts in the trapframe's epc -- NOT the")
    w("   lowest text address (xv6 links `start` ahead of `main`). *)")
    w(f"Definition {names.entry} : Z := 0x{elf_info.entry:x}%Z.")
    w("")
    w("(* The PT_LOAD program headers, in program-header order:")
    w("     (vaddr, filesz, memsz, flags)   with flags = PF_X 1 | PF_W 2 | PF_R 4.")
    w("   [filesz] bytes come from the image maps above (code + data); the")
    w("   remaining [memsz - filesz] bytes are zero-filled (.bss).  This is what")
    w("   a loader walks: for a user program, one entry per [exec] segment. *)")
    segs = ";\n".join(
        f"    ((0x{s.vaddr:x})%Z, (0x{s.filesz:x})%Z, (0x{s.memsz:x})%Z, ({s.flags})%Z)"
        f"   (* {s.flag_str()} *)"
        for s in elf_info.segments)
    w(f"Definition {names.segs} : list (Z * Z * Z * Z) := [")
    w(segs)
    w("  ].")
    w("")
    # --- the read-only/writable boundary, off the SECTION table ---------
    # The program headers above are ONE RWX PT_LOAD, so they cannot say which
    # loaded bytes are read-only; only the section flags can.  A proof that
    # resides image bytes as permanently read-only (Iris `DfracDiscarded`)
    # must stop here, or it claims read-only status for cells the kernel
    # writes -- an inconsistent premise, not a failed proof.
    w("(* THE ALLOCATED SECTIONS, in address order.  The program headers above")
    w("   are a SINGLE RWX PT_LOAD, so the read-only/writable split of the")
    w("   loaded image is visible only here:")
    for s in elf_info.sections:
        w(f"     {s.name:<18}0x{s.addr:x} .. 0x{s.addr + s.size:x}  {s.flag_str()}"
          + ("" if s.has_bits else "  (no file contents)"))
    w(f"   [{names.rodata_end}] is the LOWEST WRITABLE one's address: every")
    w("   loadable byte below it is read-only image material and is immutable")
    w("   for the life of the image, while a byte at or above it may be stored")
    w("   to at run time -- so no proof may reside one permanently read-only.")
    w("   (An image with no writable allocated section gets")
    w(f"   [{names.end}], i.e. the whole image is read-only.) *)")
    w(f"Definition {names.rodata_end} : Z := 0x{rodata_end(elf_info):x}%Z.")
    w("")
    w(f"Definition {name} : gmap Z (bv 8) := list_to_map [")
    for i, a in enumerate(data_addrs):
        sep = "  " if i == 0 else "; "
        w(f"{sep}((0x{a:x})%Z, Z_to_bv 8 (0x{image[a]:x})%Z)")
    w("].")
    w("")
    # Keep typeclass resolution from ever forcing this giant map (cf. the code map).
    w(f"Global Typeclasses Opaque {name}.")
    w("")
    w(f"(* Total data bytes = {n}; keys are byte addresses, [{name} !! addr]. *)")
    w("")
    rocq_range_lemmas(w, name, data_addrs)

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


ROCQ_KEYWORDS = {
    "as", "at", "cofix", "else", "end", "exists", "exists2", "fix", "for",
    "forall", "fun", "if", "IF", "in", "let", "match", "mod", "Prop",
    "return", "Set", "then", "Type", "using", "where", "with",
}


def rocq_ident(nm_name: str) -> str:
    """Sanitize an ELF symbol name into a valid Rocq identifier.  `nm` can
    emit names with characters Rocq identifiers don't allow (e.g. the
    `.0`/`.1` GCC appends to disambiguate colliding `static` locals across
    translation units); replace any run of such characters with `_`.  A
    symbol that happens to BE a Rocq keyword (e.g. the linker symbol `end`,
    xv6's end-of-kernel-image marker) gets a trailing `_`."""
    ident = re.sub(r"[^A-Za-z0-9_']", "_", nm_name)
    if not re.match(r"^[A-Za-z_]", ident):
        ident = "_" + ident
    if ident in ROCQ_KEYWORDS:
        ident = ident + "_"
    return ident


def emit_rocq_syms(items: list[object], out_path: str, elf: str,
                   objdump: str, names: Names) -> tuple[int, int]:
    """Rocq mirror of emit_lean_syms: the ELF symbol table as one
    `Definition <name> : Z := 0x...%Z.` per symbol, so proofs can name
    addresses directly (`KernelSyms._entry`, `KernelSyms.kernelvec`,
    `SyncSyms.main`, ...) instead of going through a map lookup.  Each dump
    lives in its own module, so the same symbol name (`main`) in the kernel and
    in a user program does not clash."""
    kernel = elf
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

    # Sanitize to valid Rocq identifiers and check the sanitization didn't
    # introduce any collisions (it hasn't, as of the current images,
    # but a future symbol set might: fail loudly rather than silently
    # shadowing one Definition with another).
    idents: dict[str, str] = {}
    for nm_name, _ in syms:
        ident = rocq_ident(nm_name)
        if ident in idents.values():
            clash = next(o for o, i in idents.items() if i == ident)
            sys.exit(f"rocq-syms: symbols {clash!r} and {nm_name!r} both "
                     f"sanitize to Rocq identifier {ident!r}; adjust rocq_ident().")
        idents[nm_name] = ident

    lines: list[str] = []
    w = lines.append
    w("(* ------------------------------------------------------------------ *)")
    w(f"(* AUTO-GENERATED by {GEN_BY} (--format rocq-syms).           *)")
    w(f"(* Symbol table of {os.path.relpath(kernel, REPO)}: {n} symbols.")
    w("   One [Definition <name> : Z] per symbol -- refer to a symbol's")
    w(f"   address directly as `{names.camel}Syms.<name>` (e.g.")
    w(f"   `{names.camel}Syms.main`). A handful of ELF names aren't valid Rocq")
    w("   identifiers as-is (e.g. GCC's `.0`/`.1` static-local disambiguation")
    w("   suffixes); those are sanitized (non-ident chars -> `_`), noted below.")
    w("                                                                       *)")
    w("(* ------------------------------------------------------------------ *)")
    w("")
    w("From Stdlib Require Import ZArith.")
    w("")
    renamed = [(o, i) for o, i in idents.items() if o != i]
    if renamed:
        w("(* Sanitized (original ELF name -> Rocq identifier): *)")
        for o, i in renamed:
            w(f"(*   {o!r} -> {i} *)")
        w("")
    for nm_name, addr in syms:
        w(f"Definition {idents[nm_name]} : Z := 0x{addr:x}%Z.")
    w("")
    w(f"(* Total symbols = {n}. *)")
    w("")

    write_if_changed(out_path, "\n".join(lines))
    return n, len(lines)


# format -> (emitter, default output directory, default file suffix).  The
# default file name is <Module><suffix>, e.g. KernelInstrs.v / SyncInstrs.v.
FORMATS = {
    "lean":        (emit_lean,        "lean",        "Instrs.lean"),
    "lean-data":   (emit_lean_data,   "lean",        "Data.lean"),
    "lean-syms":   (emit_lean_syms,   "lean",        "Syms.lean"),
    "lean-decode": (emit_lean_decode, "lean",        "Decode.lean"),
    "rocq":        (emit_rocq,        "kernel-rocq", "Instrs.v"),
    "rocq-data":   (emit_rocq_data,   "kernel-rocq", "Data.v"),
    "rocq-syms":   (emit_rocq_syms,   "kernel-rocq", "Syms.v"),
}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--elf", "--kernel", dest="elf",
                    default=os.path.join(REPO, "xv6-riscv", "kernel", "kernel"),
                    help="the ELF to dump: the xv6 kernel (default) or a user "
                         "program, e.g. xv6-riscv/user/_sync")
    ap.add_argument("--prefix", default=None,
                    help="prefix for every generated name (<prefix>_bytes, "
                         "<prefix>MemBase, ...).  Default: from the ELF's file "
                         "name ('kernel', '_sync' -> 'sync')")
    ap.add_argument("--format", choices=list(FORMATS), default="lean",
                    help="output: 'rocq' (text image + decode index), "
                         "'rocq-data' (loadable data + image geometry), "
                         "'rocq-syms' (symbol table), or their 'lean' mirrors "
                         "('lean', 'lean-data', 'lean-syms', 'lean-decode'). "
                         "Default: lean")
    ap.add_argument("--out", default=None,
                    help="output file (default depends on --format and --prefix)")
    ap.add_argument("--objdump", default=None)
    args = ap.parse_args()

    if not os.path.exists(args.elf):
        sys.exit(f"ELF not found: {args.elf}\n"
                 "Build it first: `make -C xv6-riscv kernel/kernel` for the "
                 "kernel, `make -C xv6-riscv fs.img` for the user programs.")

    names = Names(prefix=args.prefix or default_prefix(args.elf))
    emit_fn, out_dir, suffix = FORMATS[args.format]
    out = args.out or os.path.join(REPO, out_dir, names.camel + suffix)

    objdump = find_objdump(args.objdump)
    items = disassemble(objdump, args.elf)
    n, nlines = emit_fn(items, out, args.elf, objdump, names)
    print(f"Wrote {n} instructions ({nlines} lines) to {out}")


if __name__ == "__main__":
    main()
