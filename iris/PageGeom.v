(* PageGeom.v -- the PURE geometry of a kalloc page, extracted out of
   KallocInv.v so that files BELOW the lock/kalloc layer can name it.

   Everything here is a statement about an address (or a physical page
   number), with no ghost state and no Iris resources; it was all sitting
   inside KallocInv's [Section Kalloc] using none of that section's
   context.  KallocInv.v [Require Export]s this file, so every existing
   consumer of [page_valid] / [nullp] / [page_in_range_addr_is_kdata] is
   unaffected.

   WHY IT HAD TO MOVE.  [PtTree.pt_node_claim] -- the persistent per-node
   identity claim carried inside [pt_page_own] -- now records that a page
   TABLE node's page is a kalloc page ([page_valid (page_base b)]), which
   is what makes a page-table node re-freeable by freewalk.  PtTree.v sits
   far below WpLock (KallocInv's only heavy dependency), so the predicate
   had to come down to it rather than the file going up.  This is step 1
   of claude-notes/projects/proc-pagetable-ownership.md; the [page_own]
   family itself stays in KallocInv.v for now (it needs nothing lower).

   [page_base] also lives here rather than in ProcPtOwn.v, for the same
   reason: [pt_node_claim] has to spell the node page's base address. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
(* for ssreflect's [rewrite ... in H |- *] semantics, which the two
   [uint]/[bv_unsigned] bridges below are written against (they came from
   KallocInv.v, which gets ssreflect through the proofmode) *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import RiscvExtras.
(* [kmem_lo] IS the dumped `end` symbol -- see below.  This is what stops it
   being a transcription that goes stale on every image bump. *)
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Definition nullp : mword 64 := mword_of_int 0.

(* A free page must be exactly what the real [kfree]/[kalloc] enforce: a
   4096-byte-aligned physical address within [end, PHYSTOP).  kfree PANICS
   otherwise (bounds + [pa % PGSIZE] checks), and kalloc only ever hands out
   pages it earlier took in, so the invariant must CARRY this validity to make
   kalloc's result re-freeable.  [PHYSTOP = 17 << 27].

   [kmem_lo] IS `end`, so it is DEFINED as the dumped symbol rather than
   transcribed from it.  As a literal it went stale on every image bump, and
   it failed NOT here but as a bare [lia] "Cannot find witness" in whichever
   consumer built first -- which reads as a broken proof and is not one.  The
   [ltac:(eval vm_compute)] is durable-notes.md's "compute the result ONCE
   into its own Definition" idiom: the body is a plain [Z] literal by the
   time anything downstream sees it, so every existing [unfold kmem_lo; lia]
   works unchanged -- which is the point.  Defining it as [KernelSyms.end_]
   directly does NOT work: [unfold kmem_lo] then leaves a constant [lia]
   cannot see through, and every one of the consumers has to learn to unfold
   a second name. *)
Definition PGSIZE  : Z := 4096.
Definition kmem_lo : Z :=
  ltac:(let x := eval vm_compute in KernelSyms.end_ in exact x).
Definition kmem_hi : Z := 0x88000000.   (* PHYSTOP = 17 << 27 *)
Definition page_aligned (p : mword 64) : Prop := (uint p) mod PGSIZE = 0.
Definition page_in_range (p : mword 64) : Prop := kmem_lo <= uint p < kmem_hi.
Definition page_valid (p : mword 64) : Prop := page_aligned p /\ page_in_range p.

(* the base address of a physical page.  This is simultaneously the page's
   physical base and its IDENTITY KERNEL VA -- i.e. the pointer value
   kalloc returned and the one [p->pagetable] / [p->trapframe] hold. *)
Definition page_base (ppn : mword 44) : mword 64 :=
  zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12)).

(* a valid page is never the null pointer (its address is >= [end] > 0) *)
Lemma page_valid_ne_null p : page_valid p -> p <> nullp.
Proof.
  intros [_ [Hlo _]] Heq. subst p. unfold nullp in Hlo.
  assert (uint (mword_of_int 0 : mword 64) = 0) as H0 by reflexivity.
  rewrite H0 in Hlo. unfold kmem_lo in Hlo. lia.
Qed.

(* ...which is what decides the [bnez a0] every caller of a page-returning
   routine (walkaddr, vmfault, kalloc) branches on: a page it handed back is
   never NULL, so the branch is not a case split. *)
Lemma page_valid_neq_zero (q : mword 64) : page_valid q -> neq_vec q zero_reg = true.
Proof.
  intro Hv. unfold neq_vec.
  assert (Hzr : (zero_reg : mword 64) = mword_of_int 0)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hzr.
  destruct (eq_vec q (mword_of_int 0)) eqn:E; [| reflexivity].
  apply eq_vec_true_iff in E.
  destruct (page_valid_ne_null q Hv E).
Qed.

(* PGSIZE(4096)-alignment implies doubleword(8)-alignment, in the exact
   [is_aligned_paddr] shape [word_pointsto]/[word_at] demand. *)
Lemma page_valid_aligned8 p : page_valid p -> is_aligned_paddr (Physaddr p) 8 = true.
Proof.
  intros [Hal _]. unfold page_aligned, PGSIZE in Hal.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  assert (Hnn : 0 <= uint p) by (unfold uint; pose proof (bv_unsigned_in_range 64 p); lia).
  assert (Hrem : Z.rem (uint p) 8 = (uint p) mod 8) by (apply Z.rem_mod_nonneg; lia).
  rewrite Hrem.
  apply Z.mod_divide in Hal; [| lia]. apply Z.mod_divide; [lia|].
  apply (Z.divide_trans 8 4096); [ exists 512; reflexivity | exact Hal ].
Qed.

(* --- bridge to the kernel data region (RiscvPtsto's [addr_is_kdata]) ---

   [uint]/[bv_unsigned] bridge and the additive-offset fact for [pa_add],
   re-derived here rather than pulled from SmodePte.v (which drags in the
   whole InstrBytes/WP stack) -- see [uint_unsigned]/[uint_pa_add] in
   SmodePte.v / WpSmodeGpr.v for the upstream originals; this is the same
   one-line proof, kept local so this file's Require chain stays light. *)

Local Lemma kalloc_uint_pa_add (a : mword 64) (j : nat) :
  (uint a + Z.of_nat j < 18446744073709551616)%Z ->
  uint (pa_add a j) = uint a + Z.of_nat j.
Proof.
  intro Hlt. rewrite !uint_unsigned in Hlt |- *.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (Z.of_nat j) : mword 64) = Z.of_nat j).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    split.
    - apply Nat2Z.is_nonneg.
    - apply Z.le_lt_trans with (bv_unsigned a + Z.of_nat j).
      + rewrite <- (Z.add_0_l (Z.of_nat j)) at 1. apply Z.add_le_mono_r. exact Har.
      + exact Hlt. }
  rewrite Hj.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split.
  - apply Z.add_nonneg_nonneg. exact Har. apply Nat2Z.is_nonneg.
  - exact Hlt.
Qed.

(* THE BRIDGE LEMMA: every byte of a kalloc page lies in the kernel data
   region [RiscvPtsto.addr_is_kdata] = [etext, PHYSTOP).  Pure arithmetic on
   the concrete literals: [kmem_lo] (= `end`) > [text_end]
   (0x80007000), and [kmem_hi] (0x88000000) = [ram_base]+[ram_size] =
   PHYSTOP.  Page-alignment of both [p] and [kmem_hi] is what keeps
   [uint p + j] strictly below [kmem_hi] for every in-page offset [j] --
   [page_in_range] alone (without [page_aligned]) is not enough. *)
Lemma page_in_range_addr_is_kdata (p : mword 64) (j : nat) :
  page_valid p -> (j < 4096)%nat -> addr_is_kdata (pa_add p j).
Proof.
  intros [Hal [Hlo Hhi]] Hj.
  assert (Hlit : text_end <= kmem_lo) by (unfold text_end, kmem_lo; lia).
  assert (Hhilit : kmem_hi = ram_base + ram_size)
    by (unfold kmem_hi, ram_base, ram_size; lia).
  assert (Hhimod : kmem_hi mod 4096 = 0) by (unfold kmem_hi; vm_compute; reflexivity).
  (* [uint p] is a multiple of 4096 (from [page_aligned]) strictly below
     [kmem_hi], itself a multiple of 4096, so [uint p <= kmem_hi - 4096]. *)
  assert (Hstep : uint p <= kmem_hi - 4096).
  { unfold page_aligned, PGSIZE in Hal.
    apply Z.mod_divide in Hal; [ | lia ]. apply Z.mod_divide in Hhimod; [ | lia ].
    destruct Hal as [ka Hka]. destruct Hhimod as [kb Hkb]. lia. }
  assert (Hno : (uint p + Z.of_nat j < 18446744073709551616)%Z)
    by (unfold kmem_hi in Hhi; lia).
  unfold addr_is_kdata. rewrite (kalloc_uint_pa_add p j Hno). lia.
Qed.

(* the width-8 instance of [RiscvModelBytes.nth_byte_assemble_len]. *)
Lemma nth_byte_assemble8 (bs : list (bv 8)) (j : nat) :
  length bs = 8%nat -> (j < 8)%nat ->
  nth_byte (Z_to_bv 64 (assemble_bytes bs) : mword 64) j = bs !!! j.
Proof. intros Hlen Hj. apply nth_byte_assemble_len; lia. Qed.
