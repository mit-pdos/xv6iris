/-
The byte-buffer algebra the copy loops and the fs block code run on -- the
part of it this port does not already have.

A port of Rocq `ByteBuf.v` (`/shared/xv6rocq/iris/ByteBuf.v`).

## The one structural deviation, and why almost nothing is left to port

Rocq's buffer is a run of bytes NAMED BY A FUNCTION,

    [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j,

and most of `ByteBuf.v` is the bookkeeping that naming functions force:
re-anchoring a window (`bb_seq_shift`), rebranding a naming function
(`bb_ext`), joining two differently-named halves under one name
(`bb_join3`, `bb_join3_fn`), naming an anonymous region (`bb_choose`,
`bb_any_named`) and forgetting the names again (`bb_named_any`), plus the
list<->function bridge (`bb_list_id`, `bb_fmap_len`, `bb_bytes_of_list`,
`bb_bytes_to_list`).

THIS PORT'S BUFFER IS NAMED BY A LIST: `MachCSL.byteBuf a dq bs` is
`[∗list] j ↦ b ∈ bs, wordPointsTo (a + BitVec.ofNat 64 j) 1 dq b`
(`MachCSL/CallConv.lean`).  A list carries its own length, its windows are
`List.take` / `List.drop`, and re-anchoring, rebranding and joining are
all `List.append` -- so every one of the lemmas above is either
`MachCSL.byteBuf_append` or a `rfl`.  That is the deviation; it is the
port's pre-existing choice, not one made here, and the point of this
header is to record where each Rocq name went so nobody ports it twice.

## Rocq -> Lean name map

PORTED HERE (the three that have no Lean counterpart):

| Rocq (`ByteBuf.v`) | Lean | note |
| --- | --- | --- |
| `bb_split3` / `bb_join3` / `bb_join3_fn` / `bb_join` / `bb_split` | `Xv6.bbSplit3` | ONE `⊣⊢` in the `take`/`drop` spelling: the join is its `mpr`, and the naming functions of Rocq's four variants are the one list (deviation 1) |
| `bb_chunk` | `Xv6.bbChunk` | verbatim; `seq`-indexed records become `List.range`-indexed `take`/`drop` windows |
| `bb_cstr_uniq` | `Xv6.bbCstrUniq` | stated over `MachCSL.nonul` on `bs.take k`, since this port has no naming-function `bb_nonul` |

NOT PORTED, because this port already has them (do not duplicate):

| Rocq | existing Lean | where |
| --- | --- | --- |
| the window itself, `bb_bytes` | `MachCSL.byteBuf` | `MachCSL/CallConv.lean` |
| `bb_bytes_of_list`, `bb_bytes_to_list`, `bb_list_id`, `bb_fmap_len` | -- | vacuous: the window IS the list |
| `bb_seq_shift`, `bb_ext` | `MachCSL.byteBuf_append`, `MachCSL.byteBuf_list_cong` | `MachCSL/ByteWord.lean`, `MachCSL/WpStoreFree.lean` |
| `bb_cut`, `bb_split`, `bb_join` | `MachCSL.byteBuf_append` (a `⊣⊢`) | `MachCSL/ByteWord.lean` |
| `bb_byte_acc` | `MachCSL.byteBuf_acc` (read), `MachCSL.byteBuf_upd` (write) | `MachCSL/CallConv.lean` |
| `bb_nonul`, `bb_nonul_0`, `bb_nonul_step` | `MachCSL.nonul` (a predicate on the byte LIST) | `MachCSL/CallConv.lean` |
| `bb_cstr`, `bb_cstr_intro` | `MachCSL.cstr`, `MachCSL.cstr_intro`, `MachCSL.cstr_elim` | `MachCSL/CallConv.lean` |
| `bb_upd`, `bb_upd_eq`, `bb_upd_ne`, `bb_nonul_upd`, `bb_cstr_upd` | `List.set` and its `getElem` lemmas | core |
| `bb_set`, `bb_set_in`, `bb_set_out` | `List.take`/`List.drop` splicing, as `MachCSL.byteBuf_word4_at` produces it | `MachCSL/ByteWord4.lean` |
| `bb_mk`, `bb_mk_byte`, `bb_assemble_len4`, `bb_word_bytes` | `MachCSL.bytesToWord4`, `MachCSL.nthByte_bytesToWord4` | `MachCSL/ByteWord4.lean` |
| `bb_mk_set`, `bb_set_mk` | `MachCSL.bytesToWord4_wordToBytes4`, `MachCSL.wordToBytes4_bytesToWord4` | `MachCSL/ByteWord4.lean` |
| `bb_word4_acc` | `MachCSL.byteBuf_word4_acc`, `MachCSL.byteBuf_word4_at` | `MachCSL/ByteWord4.lean` |
| `bb_word_acc` | `MachCSL.byteBuf_word_acc` | `MachCSL/ByteWord.lean` |
| `bb_align_z` | `MachCSL.toNat_mod4_add` | `MachCSL/ByteWord4.lean` |
| `bb_uint32` | `BitVec.toNat` | core: this port has no `uint` |
| `bb_choose`, `bb_any_named`, `bb_named_any` | `Xv6.pageOwn` (`∃ bs, ⌜bs.length = 4096⌝ ∗ byteBuf p 1 bs`) | `Xv6/KallocDefs.lean`: the anonymous region is ALREADY an existential over a byte LIST, so there is nothing to choose |
| `page_filled_named`, `bb_page_of_named` | `Xv6.pageOwn` and `Xv6.pageOwn_pageFree` | `Xv6/KallocDefs.lean` |
| `ctx_word_pointsto_split4`, `ctx_word_pointsto_join4` | `Xv6.word8_split4`, `Xv6.word8_join4` | `Xv6/ArgLemmas.lean` |
| `ctx_buf_forget` | `MachCSL.byteBuf_bytesFree` | `MachCSL/WpStoreFree.lean` |

## Deviations

1. ONE `⊣⊢` FOR SPLIT AND JOIN.  Rocq needs `bb_split3` (an `⊣⊢` over
   naming functions), `bb_join3` (an existential join, because the three
   pieces need NOT be restrictions of one function) and `bb_join3_fn` (the
   join with the name supplied and three pointwise equations discharged),
   because the middle window comes back named by the SOURCE's naming
   function.  With list-named windows the join's name is literally the
   concatenation, so `bbSplit3.mpr` is `bb_join3_fn`, and `bb_join3`'s
   existential is `⟨_ ++ _ ++ _, _⟩`.  Nothing is lost: Rocq's
   `bb_join3_fn` exists precisely to keep the caller in control of the
   contents, which the list does by construction.

2. `bbChunk` IS ONE-DIRECTIONAL, as in Rocq ("nobody has needed the
   join").

3. `bbCstrUniq` TAKES THE PREFIX, NOT A `bb_nonul` INDEX.  Rocq's
   `bb_nonul f d` says "the first `d` bytes of the naming function are
   non-NUL"; here that is `MachCSL.nonul (bs.take d)`, the predicate the
   rest of the port already uses (`MachCSL.cstr`).
-/
import Xv6.ByteCursor

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-! ## Split / join -/

/-- PREFIX / CHUNK / SUFFIX, with every window and base spelled out and the
total length given as a premise.  This is what a page-at-a-time copy loop
and every fs record accessor calls, once per buffer per iteration.  The
`mpr` direction is Rocq's `bb_join3` / `bb_join3_fn`. -/
theorem bbSplit3 [CurCtx] (p : BitVec 64) (dq : DFrac) (bs : List (BitVec 8)) (a b c : Nat)
    (h : a + b + c = bs.length) :
    byteBuf (GF := GF) p dq bs ⊣⊢
      byteBuf p dq (bs.take a) ∗
      byteBuf (p + BitVec.ofNat 64 a) dq ((bs.drop a).take b) ∗
      byteBuf (p + BitVec.ofNat 64 (a + b)) dq (bs.drop (a + b)) := by
  have hla : (bs.take a).length = a := by rw [List.length_take]; omega
  have hlb : ((bs.drop a).take b).length = b := by rw [List.length_take, List.length_drop]; omega
  have hdd : (bs.drop a).drop b = bs.drop (a + b) := by
    rw [List.drop_drop]
  have h1 := byteBuf_append (GF := GF) p dq (bs.take a) (bs.drop a)
  rw [List.take_append_drop, hla] at h1
  have h2 := byteBuf_append (GF := GF) (p + BitVec.ofNat 64 a) dq
    ((bs.drop a).take b) ((bs.drop a).drop b)
  rw [List.take_append_drop, hlb, hdd, paAddBump] at h2
  exact Trans.trans h1 (sep_congr_right h2)

/-! ## Regrouping a buffer into equal-sized records -/

/-- A buffer of `k * n` bytes is `k` records of `n` bytes, each re-anchored
at its own base `p + i*n`.  This is what a caller wants when the region is an
ARRAY of structs (the inodes of a block, the dirents of a directory block,
the descriptors of a virtio queue) rather than one flat window: the
per-record work is then a single lemma applied under `bigSepL_mono`, with no
offset arithmetic in the caller.  One direction only -- nobody has needed the
join. -/
theorem bbChunk [CurCtx] (dq : DFrac) (n : Nat) :
    ∀ (k : Nat) (p : BitVec 64) (bs : List (BitVec 8)), bs.length = k * n →
      byteBuf (GF := GF) p dq bs ⊢
        [∗list] i ∈ List.range k,
          byteBuf (p + BitVec.ofNat 64 (i * n)) dq ((bs.drop (i * n)).take n) := by
  intro k
  induction k with
  | zero =>
    intro p bs hlen
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hb
    simp only [List.range_zero, byteBuf, Iris.Algebra.BigOpL.bigOpL_nil]
    iintro H; iexact H
  | succ k IH =>
    intro p bs hlen
    rw [Nat.succ_mul] at hlen
    have hln : (bs.take n).length = n := by rw [List.length_take]; omega
    have hlen' : (bs.drop n).length = k * n := by rw [List.length_drop]; omega
    have hsplit := byteBuf_append (GF := GF) p dq (bs.take n) (bs.drop n)
    rw [List.take_append_drop, hln] at hsplit
    have hre : ([∗list] i ∈ List.range k,
          byteBuf (GF := GF) (p + BitVec.ofNat 64 n + BitVec.ofNat 64 (i * n)) dq
            (((bs.drop n).drop (i * n)).take n)) ⊢
        [∗list] i ∈ List.range k,
          byteBuf (GF := GF) (p + BitVec.ofNat 64 ((i + 1) * n)) dq
            ((bs.drop ((i + 1) * n)).take n) := by
      refine BigSepL.bigSepL_mono_of_forall ?_
      intro _ i
      rw [paAddBump, List.drop_drop,
        show n + i * n = (i + 1) * n from by rw [Nat.succ_mul]; omega]
    iintro H
    icases hsplit.1 $$ H with ⟨H0, Hr⟩
    ihave Hr := IH (p + BitVec.ofNat 64 n) (bs.drop n) hlen' $$ Hr
    ihave Hr := hre $$ Hr
    rw [List.range_succ_eq_map]
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (i : Nat) =>
      byteBuf (GF := GF) (p + BitVec.ofNat 64 (i * n)) dq ((bs.drop (i * n)).take n))).2
    rw [BigSepL.bigSepL_map Nat.succ]
    isplitl [H0]
    · simp only [Nat.zero_mul, List.drop_zero, BitVec.add_zero]
      iexact H0
    · iexact Hr

/-! ## The NUL terminator pins the string's length -/

private theorem bbNulMemTake (bs : List (BitVec 8)) (k d : Nat) (hd : d < k)
    (h0 : bs[d]? = some 0#8) : (0#8 : BitVec 8) ∈ bs.take k := by
  have : (bs.take k)[d]? = some 0#8 := by
    rw [List.getElem?_take, if_pos hd]; exact h0
  exact List.mem_of_getElem? this

/-- A NUL-terminated reading of a buffer is UNIQUE: there is only one index
at which the string ends.  This is what lets `strlen`'s loop conclude that the
zero byte it stopped at is the `k` its precondition named, and what
`DirentEnc` uses to pin a directory entry's name length. -/
theorem bbCstrUniq (bs : List (BitVec 8)) (k d : Nat)
    (hk : nonul (bs.take k)) (hk0 : bs[k]? = some 0#8)
    (hd : nonul (bs.take d)) (hd0 : bs[d]? = some 0#8) : d = k := by
  rcases Nat.lt_trichotomy d k with hlt | heq | hgt
  · exact absurd rfl (hk _ (bbNulMemTake bs k d hlt hd0))
  · exact heq
  · exact absurd rfl (hd _ (bbNulMemTake bs d k hgt hk0))

end Xv6
