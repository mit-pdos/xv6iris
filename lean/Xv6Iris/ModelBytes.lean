/-
Port of `../iris/RiscvModelBytes.v` — the iris-free byte / bitvector prelude
underpinning faithful multi-byte memory access (an n-byte read returns the
little-endian word whose every byte is the memory byte at `pa + j`).

Model-agnostic: stated over an abstract byte-lookup `BitVec 64 → Option (BitVec 8)`
so it works for whichever concrete memory map the Iris `gen_heap` layer ends up
using. Addresses are `BitVec 64` (the Rocq `Arch.pa = mword 64`).

Status: definitions ported and compiling. The spec lemmas (`readBytes_spec`,
`bv_eq_of_bytes`, …) are the next increment — they are the determinism enablers
on the Iris side and are tracked in lean/README.md.
-/
module

public import Std.Data.HashMap

@[expose] public section

namespace Xv6Iris.ModelBytes

/-- Byte address `a + j` (model's own bitvector wraparound arithmetic). -/
def paAdd (a : BitVec 64) (j : Nat) : BitVec 64 := a + BitVec.ofNat 64 j

/-- Byte `j` of a word, little-endian (`bv_extract (8*j) 8`). -/
def nthByte {w : Nat} (x : BitVec w) (j : Nat) : BitVec 8 := x.extractLsb' (8 * j) 8

/-- Little-endian assembly of a byte list into a natural number
(own fold, matching the Rocq `assemble_bytes`, for a controllable spec). -/
def assembleBytes : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * assembleBytes bs

/-- Gather `n` little-endian bytes from memory; `none` if any byte is absent. -/
def readBytes (m : BitVec 64 → Option (BitVec 8)) (pa : BitVec 64) (n : Nat) :
    Option (BitVec (8 * n)) :=
  match (List.range n).mapM (fun j => m (paAdd pa j)) with
  | some bs => some (BitVec.ofNat (8 * n) (assembleBytes bs))
  | none => none

/-- Store the `n` little-endian bytes of `v` at `pa..pa+n`, returned as the
updated lookup function (dual of `readBytes`). -/
def writeBytes {w : Nat} (m : BitVec 64 → Option (BitVec 8)) (pa : BitVec 64)
    (n : Nat) (v : BitVec w) : BitVec 64 → Option (BitVec 8) :=
  fun a =>
    match (List.range n).find? (fun j => a = paAdd pa j) with
    | some j => some (nthByte v j)
    | none => m a

end Xv6Iris.ModelBytes
