(* PtFree.v -- THE TEARDOWN LAYER of a page table: what freewalk needs to
   walk a table apart and hand every one of its node pages back to kfree,
   and the altitude at which uvmfree's caller holds a table that is SAFE to
   tear apart.

   Three pieces, in dependency order.

   §1  [pt_free_ok lvl t] -- the PURE precondition of freewalk at level
       [lvl]: every slot of every node is either the literal ZERO word (so
       the C's [pte & PTE_V] test falls through and the slot claims no
       child) or a valid POINTER to a node the description owns (so the C's
       [pte & (PTE_R|PTE_W|PTE_X)] test falls through too and the recursive
       call gets a node we own).  A LEAF anywhere would take freewalk's
       [panic("freewalk: leaf")] arm, so [pt_free_ok] is exactly "this
       table maps nothing" -- and it is exactly what [pt_rep0 t ∅] says
       ([pt_free_ok_rep0]).  The level indexing is what makes freewalk's
       recursion an induction: freewalk at [S l] recurses at [l], and
       [ptree_own] is indexed the same way.

   §2  The node page, as kfree's argument.  [ptree_own] holds a node as 512
       physical DOUBLEWORDS at [u_pte_addr]; kfree wants 4096 loose bytes
       at the VA tier.  [pt_slots_any_phys] is the regrouping (the inverse
       of [PtBuild.zero_page_to_node]'s, over the same
       [big_sepL_seq_chunk]) and [pt_page_kfree_pre] the whole move, from
       [pt_page_own] to [KallocInv.kfree_pre].  The [page_valid] it needs
       rides in the node's own [PtTree.pt_node_claim] -- that is what the
       claim was strengthened for.  [pt_kids_own_take] pulls one child out
       of an owned node for the recursive call and leaves the parent
       claiming no child there.

   The altitude at which a caller HOLDS such a table -- a process page
   table that has lost its trampoline and trapframe leaves -- is
   [BarePt.bare_pt], built on top of this file. *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvExec RiscvTryStep.
Require Import PageGeom.
Require Import SmodePte.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtAdBits.
Require Import PtTree.
Require Import PtBuild.
Require Import KMap.
Require Import UptTree.
Require Import UserPtTree.
Require Import KallocInv.
Require Import ProcPtOwn.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 [pt_free_ok] -- freewalk's pure precondition, level-indexed.        *)
(* ===================================================================== *)

Fixpoint pt_free_ok (lvl : nat) (t : ptree) {struct lvl} : Prop :=
  match lvl with
  | O => forall i : mword 9, pt_ents t i = mword_of_int 0
  | S l =>
      forall i : mword 9,
        (pt_kids t i = None /\ pt_ents t i = mword_of_int 0)
        \/ (exists c : ptree,
              pt_kids t i = Some c /\
              pte_valid (pt_ents t i) /\ pte_ptr (pt_ents t i) /\
              u_next_base (pt_ents t i) = pt_base c /\
              pt_free_ok l c)
  end.

(* the three 9-bit walk indices are INDEPENDENT: every triple is some
   vpn's.  Needed to read [ptree_blocks0]'s per-vpn statement as a
   per-slot statement about each node -- freewalk's loop is over SLOTS,
   not over vpns. *)
Definition vpn_mk (i2 i1 i0 : mword 9) : mword 27 :=
  mword_of_int (bv_unsigned i2 * 262144 + bv_unsigned i1 * 512 + bv_unsigned i0).

(* ---- the arithmetic, [mword]-FREE.  Any goal mentioning [bv_unsigned]
   defeats [lia] under this file's transitive [bitvector.tactics] import
   (durable-notes), so the three field extractions are proved over plain
   [Z] variables and fed the unsigned values below. *)
Local Lemma vmk_div (q r d : Z) : 0 < d -> 0 <= r < d -> (q * d + r) / d = q.
Proof.
  intros Hd Hr.
  rewrite Z.div_add_l; [| lia].
  rewrite (Z.div_small r d); [| lia].
  lia.
Qed.

Local Lemma vmk_mod (q r d : Z) : 0 < d -> 0 <= r < d -> (q * d + r) `mod` d = r.
Proof.
  intros Hd Hr.
  rewrite Z.add_comm. rewrite Z.mod_add; [| lia].
  apply Z.mod_small. lia.
Qed.

Local Lemma vmk_z_bound (a b c : Z) :
  0 <= a < 512 -> 0 <= b < 512 -> 0 <= c < 512 ->
  0 <= a * 262144 + b * 512 + c < 134217728.
Proof. lia. Qed.

Local Lemma vmk_z2 (a b c : Z) :
  0 <= a < 512 -> 0 <= b < 512 -> 0 <= c < 512 ->
  ((a * 262144 + b * 512 + c) ≫ 18) `mod` 2 ^ 9 = a.
Proof.
  intros Ha Hb Hc.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 18) with 262144. change (2 ^ 9) with 512.
  replace (a * 262144 + b * 512 + c) with (a * 262144 + (b * 512 + c)) by lia.
  rewrite (vmk_div a (b * 512 + c) 262144); [| lia | lia].
  apply Z.mod_small. lia.
Qed.

Local Lemma vmk_z1 (a b c : Z) :
  0 <= a < 512 -> 0 <= b < 512 -> 0 <= c < 512 ->
  ((a * 262144 + b * 512 + c) ≫ 9) `mod` 2 ^ 9 = b.
Proof.
  intros Ha Hb Hc.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 9) with 512.
  replace (a * 262144 + b * 512 + c) with ((a * 512 + b) * 512 + c) by lia.
  rewrite (vmk_div (a * 512 + b) c 512); [| lia | lia].
  apply (vmk_mod a b 512); lia.
Qed.

Local Lemma vmk_z0 (a b c : Z) :
  0 <= a < 512 -> 0 <= b < 512 -> 0 <= c < 512 ->
  (a * 262144 + b * 512 + c) `mod` 2 ^ 9 = c.
Proof.
  intros Ha Hb Hc.
  change (2 ^ 9) with 512.
  replace (a * 262144 + b * 512 + c) with ((a * 512 + b) * 512 + c) by lia.
  apply (vmk_mod (a * 512 + b) c 512); lia.
Qed.

(* the two bitvector bridges *)
Lemma pt_bv9_range (x : mword 9) : 0 <= bv_unsigned x < 512.
Proof.
  pose proof (bv_unsigned_in_range _ x) as H.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
    by (vm_compute; reflexivity).
  rewrite Hm in H. exact H.
Qed.

Lemma pt_mword27_unsigned (i : Z) :
  0 <= i < 134217728 -> bv_unsigned (mword_of_int i : mword 27) = i.
Proof.
  intros Hi.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  apply bv_wrap_small.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728)
    by (vm_compute; reflexivity).
  rewrite Hm. exact Hi.
Qed.

(* [vpn_mk] does not wrap: the three 9-bit fields fit in 27 bits. *)
Lemma vpn_mk_unsigned (i2 i1 i0 : mword 9) :
  bv_unsigned (vpn_mk i2 i1 i0)
  = bv_unsigned i2 * 262144 + bv_unsigned i1 * 512 + bv_unsigned i0.
Proof.
  unfold vpn_mk. apply pt_mword27_unsigned.
  apply vmk_z_bound; apply pt_bv9_range.
Qed.

Lemma vpn_mk_idx2 (i2 i1 i0 : mword 9) : vpn_idx 2 (vpn_mk i2 i1 i0) = i2.
Proof.
  cbn [vpn_idx]. apply bv_eq. rewrite pt_sub27_26_18 vpn_mk_unsigned.
  apply vmk_z2; apply pt_bv9_range.
Qed.

Lemma vpn_mk_idx1 (i2 i1 i0 : mword 9) : vpn_idx 1 (vpn_mk i2 i1 i0) = i1.
Proof.
  cbn [vpn_idx]. apply bv_eq. rewrite pt_sub27_17_9 vpn_mk_unsigned.
  apply vmk_z1; apply pt_bv9_range.
Qed.

Lemma vpn_mk_idx0 (i2 i1 i0 : mword 9) : vpn_idx 0 (vpn_mk i2 i1 i0) = i0.
Proof.
  cbn [vpn_idx]. apply bv_eq. rewrite pt_sub27_8_0 vpn_mk_unsigned.
  apply vmk_z0; apply pt_bv9_range.
Qed.

(* A TABLE THAT MAPS NOTHING IS FREEWALK-SAFE.  [pt_rep0 t ∅] says every
   vpn's walk stops at a literal zero word in the xv6 shape; read slot by
   slot (through [vpn_mk]) that is exactly [pt_free_ok 2]. *)
(* [ptree_blocks0] at [vpn_mk i2 i1 i0], with the three walk indices READ
   OFF as the independent slot indices they are.  This is the only thing
   the [vpn_mk_idx*] lemmas are for. *)
Lemma pt_blocks0_at (t : ptree) (i2 i1 i0 : mword 9) :
  (forall vpn, ptree_blocks0 t vpn) ->
  (pt_kids t i2 = None /\ pt_ents t i2 = mword_of_int 0)
  \/ (exists c1,
        pt_kids t i2 = Some c1 /\ pt_kids c1 i1 = None /\
        pte_valid (pt_ents t i2) /\ pte_ptr (pt_ents t i2) /\
        u_next_base (pt_ents t i2) = pt_base c1 /\
        pt_ents c1 i1 = mword_of_int 0)
  \/ (exists c1 c0,
        pt_kids t i2 = Some c1 /\ pt_kids c1 i1 = Some c0 /\
        pte_valid (pt_ents t i2) /\ pte_ptr (pt_ents t i2) /\
        pte_valid (pt_ents c1 i1) /\ pte_ptr (pt_ents c1 i1) /\
        u_next_base (pt_ents t i2) = pt_base c1 /\
        u_next_base (pt_ents c1 i1) = pt_base c0 /\
        pt_ents c0 i0 = mword_of_int 0).
Proof.
  intros Hb. pose proof (Hb (vpn_mk i2 i1 i0)) as H.
  unfold ptree_blocks0 in H.
  rewrite vpn_mk_idx2 vpn_mk_idx1 vpn_mk_idx0 in H.
  exact H.
Qed.

Lemma pt_free_ok_rep0 (t : ptree) :
  pt_rep0 t (∅ : gmap (mword 27) (mword 64)) -> pt_free_ok 2 t.
Proof.
  intros [_ Hb0].
  assert (Hb : forall vpn, ptree_blocks0 t vpn).
  { intros vpn. apply Hb0. apply lookup_empty. }
  (* the LEVEL-2 slot facts, at any index that claims a child *)
  assert (H2 : forall j2 c1, pt_kids t j2 = Some c1 ->
            pte_valid (pt_ents t j2) /\ pte_ptr (pt_ents t j2) /\
            u_next_base (pt_ents t j2) = pt_base c1).
  { intros j2 c1 Hk.
    destruct (pt_blocks0_at t j2 (mword_of_int 0) (mword_of_int 0) Hb) as
      [ (Hn & _)
      | [ (d & Hd & _ & Hv & Hp & Hnb & _)
        | (d & e & Hd & _ & Hv & Hp & _ & _ & Hnb & _ & _) ] ].
    - rewrite Hk in Hn. discriminate.
    - rewrite Hk in Hd. injection Hd as <-.
      split; [exact Hv | split; [exact Hp | exact Hnb]].
    - rewrite Hk in Hd. injection Hd as <-.
      split; [exact Hv | split; [exact Hp | exact Hnb]]. }
  (* ...and the level-2 slot's ZERO word where it claims none *)
  assert (Hz2 : forall j2, pt_kids t j2 = None -> pt_ents t j2 = mword_of_int 0).
  { intros j2 Hk.
    destruct (pt_blocks0_at t j2 (mword_of_int 0) (mword_of_int 0) Hb) as
      [ (_ & Hz)
      | [ (d & Hd & _)
        | (d & e & Hd & _) ] ].
    - exact Hz.
    - rewrite Hk in Hd. discriminate.
    - rewrite Hk in Hd. discriminate. }
  (* the LEVEL-1 facts, under a claimed level-2 child *)
  assert (H1 : forall j2 c1 j1 c0,
            pt_kids t j2 = Some c1 -> pt_kids c1 j1 = Some c0 ->
            pte_valid (pt_ents c1 j1) /\ pte_ptr (pt_ents c1 j1) /\
            u_next_base (pt_ents c1 j1) = pt_base c0).
  { intros j2 c1 j1 c0 Hk2 Hk1.
    destruct (pt_blocks0_at t j2 j1 (mword_of_int 0) Hb) as
      [ (Hn & _)
      | [ (d & Hd & Hn1 & _)
        | (d & e & Hd & He & _ & _ & Hv & Hp & _ & Hnb & _) ] ].
    - rewrite Hk2 in Hn. discriminate.
    - rewrite Hk2 in Hd. injection Hd as <-. rewrite Hk1 in Hn1. discriminate.
    - rewrite Hk2 in Hd. injection Hd as <-. rewrite Hk1 in He. injection He as <-.
      split; [exact Hv | split; [exact Hp | exact Hnb]]. }
  assert (Hz1 : forall j2 c1 j1,
            pt_kids t j2 = Some c1 -> pt_kids c1 j1 = None ->
            pt_ents c1 j1 = mword_of_int 0).
  { intros j2 c1 j1 Hk2 Hk1.
    destruct (pt_blocks0_at t j2 j1 (mword_of_int 0) Hb) as
      [ (Hn & _)
      | [ (d & Hd & _ & _ & _ & _ & Hz)
        | (d & e & Hd & He & _) ] ].
    - rewrite Hk2 in Hn. discriminate.
    - rewrite Hk2 in Hd. injection Hd as <-. exact Hz.
    - rewrite Hk2 in Hd. injection Hd as <-. rewrite Hk1 in He. discriminate. }
  (* the LEVEL-0 words: all zero, under two claimed children *)
  assert (Hz0 : forall j2 c1 j1 c0 j0,
            pt_kids t j2 = Some c1 -> pt_kids c1 j1 = Some c0 ->
            pt_ents c0 j0 = mword_of_int 0).
  { intros j2 c1 j1 c0 j0 Hk2 Hk1.
    destruct (pt_blocks0_at t j2 j1 j0 Hb) as
      [ (Hn & _)
      | [ (d & Hd & Hn1 & _)
        | (d & e & Hd & He & _ & _ & _ & _ & _ & _ & Hz) ] ].
    - rewrite Hk2 in Hn. discriminate.
    - rewrite Hk2 in Hd. injection Hd as <-. rewrite Hk1 in Hn1. discriminate.
    - rewrite Hk2 in Hd. injection Hd as <-. rewrite Hk1 in He. injection He as <-.
      exact Hz. }
  (* assemble *)
  cbn [pt_free_ok]. intros i2.
  destruct (pt_kids t i2) as [c1|] eqn:Hk2.
  - right. exists c1.
    destruct (H2 i2 c1 Hk2) as (Hv & Hp & Hnb).
    split; [reflexivity |]. split; [exact Hv |]. split; [exact Hp |].
    split; [exact Hnb |].
    intros i1.
    destruct (pt_kids c1 i1) as [c0|] eqn:Hk1.
    + right. exists c0.
      destruct (H1 i2 c1 i1 c0 Hk2 Hk1) as (Hv1 & Hp1 & Hnb1).
      split; [reflexivity |]. split; [exact Hv1 |]. split; [exact Hp1 |].
      split; [exact Hnb1 |].
      intros i0. exact (Hz0 i2 c1 i1 c0 i0 Hk2 Hk1).
    + left. split; [reflexivity | exact (Hz1 i2 c1 i1 Hk2 Hk1)].
  - left. split; [reflexivity | exact (Hz2 i2 Hk2)].
Qed.

(* ===================================================================== *)
(* §1b WHAT A VALID POINTER PTE PINS ABOVE THE PPN.                       *)
(*                                                                        *)
(*   freewalk computes the child's page base in SOFTWARE, [(pte >> 10) << *)
(*   12], and [ProcPtOwn.pte2pa] identifies that with [page_base (pte_ppn *)
(*   w)] only for [w < 2^54].  [PtTree.pte_hi_zero] gets that bound from  *)
(*   [pte_valid + pte_no_napot + pte_pbmt0], but [pt_free_ok]'s pointer   *)
(*   case carries only [pte_valid + pte_ptr] (exactly [ptree_blocks0]'s   *)
(*   pointer conjuncts), and strengthening it would break                 *)
(*   [pt_free_ok_rep0].  It does not have to be strengthened: the model's *)
(*   [pte_is_invalid] has a disjunct                                      *)
(*                                                                        *)
(*     pte_is_non_leaf(flags) && (A=1 || D=1 || U=1 || ext != 0)          *)
(*                                                                        *)
(*   so on a NON-LEAF word, validity forces the whole 10-bit extension    *)
(*   field (bits 63:54) to zero all by itself.                            *)
(* ===================================================================== *)

(* [pte_is_invalid] evaluated at a no-extension state, with the NON-LEAF
   disjunct exposed (the other six are irrelevant here, so they stay
   existential).  Mirrors [PtTree.pte_piv_split], which exposes the
   RSW/reserved disjuncts instead. *)
Local Lemma ptf_piv_nonleaf (f : mword 8) (e : mword 10) :
  exists b1 b2 b3 x y z b5 b6 b7,
    exec (pte_is_invalid f e) PtTree.pte_s0
    = Some (orb b1 (orb b2 (orb b3
              (orb (andb (pte_is_non_leaf f)
                      (orb x (orb y (orb z (neq_vec e (zeros' 10))))))
                   (orb b5 (orb b6 b7)))))
            , PtTree.pte_s0).
Proof.
  do 9 eexists.
  unfold pte_is_invalid.
  eapply exec_or_v; [ apply exec_returnM | ].
  eapply exec_or_v;
    [ eapply exec_and_v; [ apply exec_returnM |
        eapply exec_and_v; [ apply exec_returnM |
          eapply exec_and_v; [ apply exec_returnM | vm_compute; reflexivity ] ] ] | ].
  eapply exec_or_v; [ apply exec_returnM | ].
  eapply exec_or_v; [ apply exec_returnM | ].
  eapply exec_or_v;
    [ eapply exec_and_v; [ apply exec_returnM | vm_compute; reflexivity ] | ].
  eapply exec_or_v;
    [ eapply exec_and_v; [ apply exec_returnM |
        eapply exec_or_v; [ vm_compute; reflexivity | apply exec_returnM ] ] | ].
  eapply exec_or_v; [ | apply exec_returnM ].
  eapply exec_and_v; [ apply exec_returnM | vm_compute; reflexivity ].
Qed.

Lemma pte_ptr_ext_zero (w : mword 64) :
  pte_valid w -> pte_ptr w -> ext_bits_of_PTE w = (zeros' 10 : mword 10).
Proof.
  intros Hv Hp.
  destruct (ptf_piv_nonleaf (Mk_PTE_Flags (subrange_vec_dec w 7 0))
              (ext_bits_of_PTE w))
    as (b1 & b2 & b3 & x & y & z & b5 & b6 & b7 & Hex).
  specialize (Hv PtTree.pte_s0). rewrite Hex in Hv. injection Hv as Hb.
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  apply orb_false_iff in Hb; destruct Hb as [Hb _].
  unfold pte_ptr in Hp. rewrite Hp in Hb. rewrite andb_true_l in Hb.
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  apply orb_false_iff in Hb; destruct Hb as [_ Hb].
  unfold neq_vec in Hb. apply negb_false_iff in Hb.
  apply eq_vec_true_iff. exact Hb.
Qed.

Lemma pte_ptr_hi_zero (w : mword 64) :
  pte_valid w -> pte_ptr w -> (bv_unsigned w < 18014398509481984)%Z.
Proof.
  intros Hv Hp.
  pose proof (pte_ptr_ext_zero w Hv Hp) as He.
  assert (Hext : ext_bits_of_PTE w = (subrange_vec_dec w 63 54 : mword 10))
    by reflexivity.
  rewrite Hext in He.
  apply (f_equal bv_unsigned) in He.
  rewrite PtTree.pte_sub_63_54 in He.
  assert (Z0 : bv_unsigned (zeros' 10 : mword 10) = 0) by (vm_compute; reflexivity).
  rewrite Z0 in He.
  apply PtTree.pte_z_hi_zero; [| exact He].
  pose proof (bv_unsigned_in_range _ w) as Hr.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr. exact Hr.
Qed.

(* ===================================================================== *)
(* §2 A node page, on its way to kfree.                                   *)
(* ===================================================================== *)

(* byte [j] of slot [i] of a node page = byte [i*8+j] of the page, at
   [PageGeom.page_base]'s spelling of the page's base ([page_base] is
   definitionally the [zero_extend'/concat_vec] form [Pt4kWalk] states it
   with, so [exact] bridges).  The [PtBuild.pa_add_page_slot_u] of the
   inverse regrouping. *)
Lemma pa_add_page_slot_pb (b : mword 44) (i j : nat) :
  (i < 512)%nat -> (j < 8)%nat ->
  pa_add (page_base b) (i * 8 + j) = pa_add (u_pte_addr b (mword_of_int (Z.of_nat i))) j.
Proof. exact (pa_add_page_slot b i j). Qed.

Section PtFreeIris.
  Context `{!riscvGS Σ, !lockG Σ, !kallocG Σ}.

  (* the 512 slot doublewords of a node page, at ARBITRARY contents, are
     the page's 4096 loose physical bytes.  The inverse regrouping of
     [PtBuild.zero_page_to_node]'s, over the same [big_sepL_seq_chunk] and
     [pa_add_page_slot]; [phys_word_pointsto_bytes] replaces
     [phys_word_pointsto_intro]. *)
  Lemma pt_slots_any_phys (b : mword 44) :
    ([∗ list] i ∈ seqZ 0 512, ∃ w : mword 64, u_pte_addr b (mword_of_int i) ↦ₚ₈ w)
    ⊢ phys_page_own b.
  Proof.
    iIntros "Hs".
    iEval (rewrite /seqZ) in "Hs".
    iEval (rewrite big_sepL_fmap) in "Hs".
    iEval (change (Z.to_nat 512) with 512%nat) in "Hs".
    rewrite /phys_page_own.
    change 4096%nat with (512 * 8)%nat.
    rewrite (PtBuild.big_sepL_seq_chunk
               (fun j => phys_byte_any (pa_add (page_base b) j)) 512 8).
    iApply (big_sepL_mono with "Hs").
    intros k i Hki. apply lookup_seq in Hki. destruct Hki as [-> Hlt].
    cbn [Nat.add]. iIntros "H". iDestruct "H" as (w) "H".
    replace (Z.of_nat k + 0) with (Z.of_nat k) by lia.
    iDestruct (phys_word_pointsto_bytes with "H") as "H".
    iApply (big_sepL_mono with "H").
    intros k' j Hkj. apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
    cbn [Nat.add]. iIntros "Hb".
    rewrite /phys_byte_any.
    rewrite (pa_add_page_slot_pb b k k' Hlt Hjlt).
    iExists (nth_byte w k'). iExact "Hb".
  Qed.

  (* ...and a node whose slots still hold the description's words is that
     same page (the words are forgotten). *)
  Lemma pt_page_own_phys (t : ptree) :
    pt_page_own (DfracOwn 1) t ⊢
      ⌜page_valid (page_base (pt_base t))⌝ ∗ phys_page_own (pt_base t).
  Proof.
    iIntros "Hp".
    iEval (rewrite /pt_page_own /pt_node_claim) in "Hp".
    iDestruct "Hp" as "((%Hkd & %Hpv & #Hk) & Hs)".
    iSplitR; [done |].
    iApply pt_slots_any_phys.
    iApply (big_sepL_mono with "Hs").
    intros k i _. cbn beta. iIntros "H".
    iExists (pt_ents t (mword_of_int i)). iExact "H".
  Qed.

  (* THE HAND-OFF.  A node page, at kfree's precondition.  [page_valid]
     comes out of the node's own claim (PtTree.pt_node_claim), the tier
     move from [ProcPtOwn.phys_to_page_own]. *)
  Lemma pt_page_kfree_pre (t : ptree) :
    kmap_static_claims -∗ pt_page_own (DfracOwn 1) t -∗
      kfree_pre (page_base (pt_base t)).
  Proof.
    iIntros "#Hb Hp".
    iDestruct (pt_page_own_phys with "Hp") as "[%Hv Hph]".
    rewrite /kfree_pre. iSplitR; [done |].
    iApply (phys_to_page_own (pt_base t) Hv with "Hb Hph").
  Qed.

  (* the same, for a page held as loose slots (freewalk's loop has
     rewritten some of them, so the description's words are gone) *)
  Lemma pt_slots_kfree_pre (b : mword 44) :
    page_valid (page_base b) ->
    kmap_static_claims -∗
    ([∗ list] i ∈ seqZ 0 512, ∃ w : mword 64, u_pte_addr b (mword_of_int i) ↦ₚ₈ w) -∗
      kfree_pre (page_base b).
  Proof.
    intros Hv. iIntros "#Hb Hs".
    iDestruct (pt_slots_any_phys with "Hs") as "Hph".
    rewrite /kfree_pre. iSplitR; [done |].
    iApply (phys_to_page_own b Hv with "Hb Hph").
  Qed.

  (* TAKE ONE CHILD OUT.  freewalk frees the child and then zeroes the
     slot, so the parent must be left claiming NO child at [i] -- the
     destructive twin of [PtBuild.pt_kids_own_ins]. *)
  Lemma pt_kids_own_take (lvl : nat) (dq : dfrac) (t : ptree) (i : mword 9) (c : ptree) :
    pt_kids t i = Some c ->
    pt_kids_own lvl dq t ⊢
      ptree_own lvl dq c ∗ pt_kids_own lvl dq (pt_upd_kid t i None).
  Proof.
    intros Hk.
    pose proof (bv_unsigned_in_range _ i) as Hir.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
      by (vm_compute; reflexivity).
    rewrite Hm in Hir.
    assert (Hlk : seqZ 0 512 !! Z.to_nat (bv_unsigned i) = Some (bv_unsigned i)).
    { apply lookup_seqZ. split; lia. }
    iIntros "Hks".
    iEval (rewrite /pt_kids_own) in "Hks".
    iEval (rewrite (big_sepL_delete _ _ _ _ Hlk)) in "Hks".
    iDestruct "Hks" as "[Hc Hks]".
    iEval (rewrite pt_mword9_id Hk) in "Hc".
    iSplitL "Hc"; [iExact "Hc" |].
    rewrite /pt_kids_own.
    rewrite (big_sepL_delete
               (fun _ j => (match pt_kids (pt_upd_kid t i None) (mword_of_int j) with
                            | Some cc => ptree_own lvl dq cc
                            | None => emp end)%I)
               _ _ _ Hlk).
    iSplitR.
    { iEval (rewrite pt_mword9_id pt_upd_kid_same). done. }
    iApply (big_sepL_mono with "Hks").
    intros k j Hkj. cbn beta.
    case_decide as Hkk; [reflexivity |].
    rewrite pt_upd_kid_other; [reflexivity |].
    apply lookup_seqZ in Hkj. destruct Hkj as [-> Hjlt].
    intros Heq. apply Hkk.
    apply (f_equal bv_unsigned) in Heq.
    rewrite pt_mword9_unsigned in Heq; [| lia].
    lia.
  Qed.

End PtFreeIris.

