(* PlicHart.v -- the per-hart PLIC context ADDRESSES, and what a hart's own
   accesses to them do.

   Every xv6 function that touches its own PLIC S-context ([plicinithart],
   [plic_claim], [plic_complete]) computes the same two base addresses the same
   way -- shift the hart id left, add a [lui] constant -- and then accesses a
   fixed offset off one of them.  The resulting addresses are SYMBOLIC in the
   hart id, which is only bounded ([bv_unsigned tp < dev_ncpu]), so every fact
   that needs one of them as a number is proved by an eight-way case split on
   the hart id ([hart_cases]) followed by [vm_compute].

   Those lemmas live here, at the altitude of what they say (a PLIC address and
   a hart id, nothing function-specific), so that each whole-function proof
   body stays single-copy and symbolic -- case-splitting inside a function
   proof would multiply the whole body by eight -- and so that no function
   proof has to import another function's proof to reuse them.

   Iris-free on purpose: these are pure address/geometry facts. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import KptPt.
Require Import DevModel PlicPlan.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* A closed [lo <= x < hi] bound over Z.  [lia] is unusable on these once a
   bitvector term is in scope: bitvector.tactics installs a zify hook that
   answers "Cannot find witness" even on ground literals.  So decide each side
   through the boolean reflection lemmas instead. *)
Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.

(* ...and for the same reason the pure Z case split is proved HERE, in a
   statement with nothing bitvector-shaped in it. *)
Lemma z_lt8_cases (z : Z) :
  0 <= z -> z < 8 ->
  z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7.
Proof. lia. Qed.

(* A legal hart id is one of the [dev_ncpu] = 8 concrete 64-bit words. *)
Lemma hart_cases (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  tp = (mword_of_int 0 : mword 64) \/ tp = (mword_of_int 1 : mword 64) \/
  tp = (mword_of_int 2 : mword 64) \/ tp = (mword_of_int 3 : mword 64) \/
  tp = (mword_of_int 4 : mword 64) \/ tp = (mword_of_int 5 : mword 64) \/
  tp = (mword_of_int 6 : mword 64) \/ tp = (mword_of_int 7 : mword 64).
Proof.
  intro Hh.
  change (Z.of_nat dev_ncpu) with 8%Z in Hh.
  remember (bv_unsigned tp) as z eqn:Hz.
  assert (Hu : bv_unsigned tp = z) by (symmetry; exact Hz).
  assert (Hlo : 0 <= z).
  { rewrite <- Hu. apply (proj1 (bv_unsigned_in_range _ tp)). }
  destruct (z_lt8_cases z Hlo Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E in Hu;
    [ left | right; left | right; right; left | right; right; right; left
    | right; right; right; right; left | right; right; right; right; right; left
    | right; right; right; right; right; right; left
    | right; right; right; right; right; right; right ];
    apply bv_eq; rewrite Hu; vm_compute; reflexivity.
Qed.

(* [cpuid] truncates its result to an [int] ([sext.w]); for a legal hart id the
   top bits are clear, so the truncation is the identity.  Stated on the raw
   sign-extension rather than on [cpuid_ret] so this file stays iris-free --
   [cpuid_ret] IS this term (SpecCpuid.v). *)
Lemma sext32_id_hart (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  sign_extend' 64 (subrange_vec_dec tp 31 0 : mword 32) = tp.
Proof.
  intro Hh.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]];
    rewrite E; apply bv_eq; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  The addresses.                                                        *)
(* ===================================================================== *)

(* the SLLIW every one of these functions applies to the hart id (shift the low
   32 bits, sign-extend the 32-bit result back) *)
Definition ph_shl (tp : mword 64) (k : Z) : mword 64 :=
  sign_extend' 64 (shift_bits_left (subrange_vec_dec tp 31 0 : mword 32) (mword_of_int k : mword 5)).

(* the two [lui]+[add] bases: the hart's S-context enable block, and its
   S-context block (threshold at +0, claim/complete at +4) *)
Definition ph_senb (tp : mword 64) : mword 64 :=
  add_vec (mword_of_int 0x0c002000 : mword 64) (ph_shl tp 8).
Definition ph_sthb (tp : mword 64) : mword 64 :=
  add_vec (mword_of_int 0x0c201000 : mword 64) (ph_shl tp 13).

(* the effective address of an access at [imm] off [base], in the exact shape
   the S-mode access WPs compute it *)
Definition ph_a8 (base : mword 64) (imm : mword 12) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec (add_vec base (sign_extend' 64 imm)) (xlen - 0 - 1) 0).

(* [add_vec] is commutative.  Needed because the three functions build the
   same context address with the [lui] constant and the shifted hart id in
   opposite operand order ([add a5,a5,a0] vs [add a5,a5,a4]), so one of them
   lands on the mirror image of [ph_senb]/[ph_sthb]. *)
Lemma ph_add_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned. rewrite Z.add_comm. reflexivity.
Qed.

(* the geometry every S-mode PLIC access WP asks for: the address is inside the
   PLIC window, 4-aligned, canonical, on a [kpt_dev_vpn] page, and identity-
   mapped by the kernel page table. *)
Definition ph_geom_ok (a8 : mword 64) : Prop :=
  (plic_base <= uint a8 < plic_base + plic_size)%Z
  /\ is_aligned_vaddr (Virtaddr a8) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of a8)
  /\ zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8.

(* named projections, so a call site can hand one conjunct to an access WP
   without a [proj1 (proj2 (proj2 ...))] chain *)
Lemma ph_geom_range (a8 : mword 64) :
  ph_geom_ok a8 -> (plic_base <= uint a8 < plic_base + plic_size)%Z.
Proof. intros (H & _ & _ & _ & _). exact H. Qed.
Lemma ph_geom_align (a8 : mword 64) :
  ph_geom_ok a8 -> is_aligned_vaddr (Virtaddr a8) 4 = true.
Proof. intros (_ & H & _ & _ & _). exact H. Qed.
Lemma ph_geom_canon (a8 : mword 64) :
  ph_geom_ok a8 ->
  neq_vec (bits_of_virtaddr (Virtaddr a8))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false.
Proof. intros (_ & _ & H & _ & _). exact H. Qed.
Lemma ph_geom_vpn (a8 : mword 64) : ph_geom_ok a8 -> kpt_dev_vpn (svpn_of a8).
Proof. intros (_ & _ & _ & H & _). exact H. Qed.
Lemma ph_geom_ident (a8 : mword 64) :
  ph_geom_ok a8 ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
    (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8.
Proof. intros (_ & _ & _ & _ & H). exact H. Qed.

Ltac ph_geom_split :=
  (split; [ zrange_vm | ]); (split; [ vm_compute; reflexivity | ]);
  (split; [ vm_compute; reflexivity | ]);
  (split; [ unfold kpt_dev_vpn; zrange_vm | ]);
  apply bv_eq; vm_compute; reflexivity.

(* PLIC_SENABLE(hart) = ph_senb + 128 *)
Lemma ph_senable_geom (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  ph_geom_ok (ph_a8 (ph_senb tp) (mword_of_int 128 : mword 12)).
Proof.
  intro Hh. unfold ph_geom_ok.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; ph_geom_split.
Qed.

(* PLIC_SPRIORITY(hart) (the context threshold) = ph_sthb + 0 *)
Lemma ph_sthresh_geom (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  ph_geom_ok (ph_a8 (ph_sthb tp) (mword_of_int 0 : mword 12)).
Proof.
  intro Hh. unfold ph_geom_ok.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; ph_geom_split.
Qed.

(* PLIC_SCLAIM(hart) (claim on read, complete on write) = ph_sthb + 4 *)
Lemma ph_sclaim_geom (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  ph_geom_ok (ph_a8 (ph_sthb tp) (mword_of_int 4 : mword 12)).
Proof.
  intro Hh. unfold ph_geom_ok.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; ph_geom_split.
Qed.

(* ===================================================================== *)
(*  What an access at each address does to the PLIC state.                *)
(* ===================================================================== *)

Lemma ph_senable_write (tp : mword 64) (p : plic_state) (v : bv 32) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_write p (uint (ph_a8 (ph_senb tp) (mword_of_int 128 : mword 12)) - plic_base) v
  = Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
            (hupd (p_enable p) (Z.to_nat (bv_unsigned tp)) v) (p_thresh p)).
Proof.
  intro Hh.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    vm_compute; reflexivity.
Qed.

Lemma ph_sthresh_write (tp : mword 64) (p : plic_state) (v : bv 32) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_write p (uint (ph_a8 (ph_sthb tp) (mword_of_int 0 : mword 12)) - plic_base) v
  = Some (PlicState (p_prio p) (p_pending p) (p_claimed p) (p_enable p)
            (hupd (p_thresh p) (Z.to_nat (bv_unsigned tp)) v)).
Proof.
  intro Hh.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    vm_compute; reflexivity.
Qed.

(* The claim/complete register is the one PLIC address whose access does real
   work in the model, so the two lemmas below take the decode apart by its
   GUARDS rather than by [vm_compute]ing the whole equation: [plic_claim] hides
   a 31-element fold ([plic_best]) over a SYMBOLIC state, and normalising that
   does not terminate in any useful time.  Reducing only the numeric guards
   leaves [plic_claim]/[plic_complete] untouched on both sides. *)
Lemma plic_read_sclaim (p : plic_state) (off : Z) (h : nat) :
  ((0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0))%Z = false ->
  (off =? 0x1000)%Z = false ->
  plic_senable_hart off = None ->
  plic_sthresh_hart off = None ->
  plic_sclaim_hart off = Some h ->
  plic_read p off = Some (plic_claim p h).
Proof.
  (* plain Stdlib [rewrite] here (no ssreflect in this iris-free file): commas. *)
  intros H1 H2 H3 H4 H5. unfold plic_read. rewrite H1, H2, H3, H4, H5. reflexivity.
Qed.

Lemma plic_write_sclaim (p : plic_state) (off : Z) (h : nat) (v : bv 32) :
  ((0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0))%Z = false ->
  plic_senable_hart off = None ->
  plic_sthresh_hart off = None ->
  plic_sclaim_hart off = Some h ->
  plic_write p off v = Some (plic_complete p (Z.to_N (bv_unsigned v))).
Proof.
  intros H1 H3 H4 H5. unfold plic_write. rewrite H1, H3, H4, H5. reflexivity.
Qed.

(* the claim/complete address decodes to THIS hart's context, and to none of
   the other register families *)
Lemma ph_sclaim_decode (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  let off := (uint (ph_a8 (ph_sthb tp) (mword_of_int 4 : mword 12)) - plic_base)%Z in
  ((0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0))%Z = false
  /\ (off =? 0x1000)%Z = false
  /\ plic_senable_hart off = None
  /\ plic_sthresh_hart off = None
  /\ plic_sclaim_hart off = Some (Z.to_nat (bv_unsigned tp)).
Proof.
  intro Hh. cbv zeta.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    repeat split; vm_compute; reflexivity.
Qed.

(* a write to the claim/complete register is a COMPLETION: it clears the
   claimed bit of the id written, and is total (an out-of-range id completes
   nothing). *)
Lemma ph_sclaim_write (tp : mword 64) (p : plic_state) (v : bv 32) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_write p (uint (ph_a8 (ph_sthb tp) (mword_of_int 4 : mword 12)) - plic_base) v
  = Some (plic_complete p (Z.to_N (bv_unsigned v))).
Proof.
  intro Hh. destruct (ph_sclaim_decode tp Hh) as (H1 & _ & H3 & H4 & H5).
  exact (plic_write_sclaim p _ _ v H1 H3 H4 H5).
Qed.

(* a READ of the claim/complete register is a CLAIM: it returns the id of the
   source taken and advances the PLIC state. *)
Lemma ph_sclaim_read (tp : mword 64) (p : plic_state) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_read p (uint (ph_a8 (ph_sthb tp) (mword_of_int 4 : mword 12)) - plic_base)
  = Some (plic_claim p (Z.to_nat (bv_unsigned tp))).
Proof.
  intro Hh. destruct (ph_sclaim_decode tp Hh) as (H1 & H2 & H3 & H4 & H5).
  exact (plic_read_sclaim p _ _ H1 H2 H3 H4 H5).
Qed.
