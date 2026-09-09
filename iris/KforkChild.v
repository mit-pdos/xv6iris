(* ===================================================================== *)
(* KforkChild.v -- THE RECORD A FORKED CHILD IS PARKED WITH, as a        *)
(* function of the parent's, and the three pure laws that make it the    *)
(* record kfork's proof actually reaches.                                 *)
(*                                                                       *)
(* WHY THIS FILE EXISTS.  [SpecKfork]'s slot premise is ONE slot at      *)
(* [uvis_of (kfork_child Up) stsP] -- kfork states the child's           *)
(* user-visible state from the parent's, so a caller with a continuation *)
(* for its child can pay for exactly that continuation and nothing else. *)
(* [SpecSysFork] names the same record one level up, so the definition   *)
(* lives below both of them rather than inside either.                    *)
(*                                                                       *)
(* WHAT THE PROOF NEEDS BESIDES THE DEFINITION.  The child's ACTUAL      *)
(* record is not [kfork_child Up] on the nose: it carries allocproc's    *)
(* page-table root and trapframe page, its own descriptor pointers,      *)
(* ghost names and name bytes, and the kernel words uvmcopy and          *)
(* prepare_return leave in its trapframe.  The slot reads none of those  *)
(* ([UexecApply.uslot_key_cong]), so the park re-keys by                 *)
(* [UexecRet.urun_eq] and the three laws below are what discharge it:    *)
(*                                                                       *)
(*   [umem_write_copy_id]        the IMAGE.  uvmcopy reports the child's *)
(*                               bytes as [umem_write Mnew 0 (4096 n)    *)
(*                               (Mold !!! .)], not as [Mold] -- but the *)
(*                               kernel's view is the LAZY one, whose    *)
(*                               domain is exactly [0, PGROUNDUP sz), so *)
(*                               the write covers it and the two maps    *)
(*                               are equal.                              *)
(*   [perm_of_uvmcopy_child]     the PERMISSION VIEW.  uvmcopy rebuilds  *)
(*                               each leaf as an A/D variant of          *)
(*                               [uvm_pte (pte_flags10 w) r]; that moves *)
(*                               the PPN and bits 0, 6 and 7, and        *)
(*                               [perm_leaf] reads bits 1..4.            *)
(*   [urun_eq_kfork_child]       the ASSEMBLY: those two, the trapframe  *)
(*                               with a0 := 0, [np->sz = p->sz] and the  *)
(*                               copied cwd inum ARE the run key.        *)
(*                                                                       *)
(* [umem_write_copy_id], [perm_of_ext] and [perm_leaf_bits_eq] are       *)
(* hypothesis-free laws of [UserPtTree.umem_write] and                   *)
(* [UserPerm.perm_leaf]; they are here rather than in those two files    *)
(* because a lemma added to [UserPtTree] rebuilds 659 files and one      *)
(* added to [UserPerm] rebuilds 153, and this leaf rebuilds none.  They  *)
(* are lift candidates for the next change that is in those files        *)
(* anyway, exactly as [ProofKforkParts]' bridges are for [ProcInv].      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap sets list bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExtras.  (* [svpn_of], [uint_unsigned] *)
Require Import PtAdBits Pt4kWalk PtBuild.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UserPerm.
Require Import FdSlots.      (* [fdstate] -- the descriptor view in the key *)
Require Import ProcDefs.     (* [ustate] / [pprivate] *)
Require Import ProcInv.      (* [us_tf] -- the trapframe-word updater *)
Require Import UexecSlot.    (* [uvis] / [uvis_of] *)
Require Import UexecRet.     (* [urun_eq] -- the run key the park re-keys by *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1 THE CHILD RECORD.                                                   *)
(* ===================================================================== *)

(* xv6's fork copies the parent's whole trapframe into the child and then
   writes [np->trapframe->a0 = 0] (word 14 = [ProcGeom.tf_arg_idx 0]); the
   address space is copied page for page and the size, the descriptor
   table and the working directory are the parent's.  Everything the slot
   reads of a process is therefore the parent's, with that one word
   replaced -- which is what this record says. *)
Definition kfork_child (Up : ustate) : ustate :=
  us_tf Up (<[14%nat := zero_reg]> (pv_tf (us_V Up))).

(* the four projections the record does NOT move, each by [reflexivity]
   ([us_tf] is a [MkUstate] of projections) *)
Lemma kfork_child_sz (Up : ustate) :
  pv_sz (us_V (kfork_child Up)) = pv_sz (us_V Up).
Proof. reflexivity. Qed.

Lemma kfork_child_upt (Up : ustate) :
  pv_upt (us_V (kfork_child Up)) = pv_upt (us_V Up).
Proof. reflexivity. Qed.

Lemma kfork_child_cwi (Up : ustate) :
  pv_cwi (us_V (kfork_child Up)) = pv_cwi (us_V Up).
Proof. reflexivity. Qed.

Lemma kfork_child_M (Up : ustate) : us_M (kfork_child Up) = us_M Up.
Proof. reflexivity. Qed.

Lemma kfork_child_tf (Up : ustate) :
  pv_tf (us_V (kfork_child Up)) = <[14%nat := zero_reg]> (pv_tf (us_V Up)).
Proof. reflexivity. Qed.

(* ...and the key it projects to, spelled out: this is the record
   [SpecKfork]'s premise hands kfork a slot at. *)
Lemma uvis_of_kfork_child (Up : ustate) (sts : list fdstate) :
  uvis_of (kfork_child Up) sts
  = MkUvis (<[14%nat := zero_reg]> (pv_tf (us_V Up)))
           (us_M Up)
           (perm_of (ud_um (pv_upt (us_V Up))) (uint (pv_sz (us_V Up))))
           (uint (pv_sz (us_V Up)))
           sts
           (pv_cwi (us_V Up)).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §2 THE IMAGE.  [SpecUvmcopy]'s post reports the child's bytes as the   *)
(* parent's bytes WRITTEN OVER whatever the freshly allocated child had;  *)
(* the two maps have the same domain -- the lazy view's, which is exactly *)
(* [0, PGROUNDUP sz) -- and the run covers it, so the write is the        *)
(* parent's map on the nose.                                              *)
(* ===================================================================== *)
Lemma umem_write_copy_id (Mold Mnew : gmap Z (bv 8)) (sz : Z) (n : nat) :
  (forall va : Z, is_Some (Mold !! va) <-> uva_live sz va) ->
  (forall va : Z, is_Some (Mnew !! va) <-> uva_live sz va) ->
  4096 * Z.of_nat n = UserPtTree.pgroundup sz ->
  umem_write Mnew 0 (4096 * n)%nat (fun a => Mold !!! Z.of_nat a) = Mold.
Proof.
  intros Hold Hnew Hn.
  assert (Hlen : Z.of_nat (4096 * n)%nat = 4096 * Z.of_nat n)
    by (rewrite Nat2Z.inj_mul; reflexivity).
  apply map_eq. intros va.
  destruct (decide (0 <= va < 4096 * Z.of_nat n)) as [Hin | Hout].
  - assert (Hj : (Z.to_nat va < 4096 * n)%nat) by lia.
    assert (Hva : (0 + Z.of_nat (Z.to_nat va)) = va) by lia.
    assert (Hz : Z.of_nat (Z.to_nat va) = va) by lia.
    rewrite <- Hva.
    rewrite (umem_write_lookup_in Mnew 0 (4096 * n)%nat
               (fun a => Mold !!! Z.of_nat a) (Z.to_nat va) Hj).
    cbv beta. rewrite Hva. rewrite Hz.
    assert (Hlive : uva_live sz va) by (unfold uva_live; lia).
    destruct (proj2 (Hold va) Hlive) as [x Hx].
    rewrite Hx. rewrite (lookup_total_correct _ _ _ Hx).
    reflexivity.
  - rewrite (umem_write_lookup_out Mnew 0 (4096 * n)%nat
               (fun a => Mold !!! Z.of_nat a) va ltac:(intros j Hj; lia)).
    assert (Hnl : ~ uva_live sz va) by (unfold uva_live; lia).
    destruct (Mnew !! va) as [x |] eqn:E1.
    { exfalso. apply Hnl. apply Hnew. rewrite E1. exact (mk_is_Some _ _ eq_refl). }
    destruct (Mold !! va) as [y |] eqn:E2.
    { exfalso. apply Hnl. apply Hold. rewrite E2. exact (mk_is_Some _ _ eq_refl). }
    reflexivity.
Qed.

(* ===================================================================== *)
(* §3 THE PERMISSION VIEW.                                                *)
(* ===================================================================== *)

(* [perm_leaf] reads bits 4 (U) and 1 (R) to decide presence and bits 3
   (X) and 2 (W) for the value: two words agreeing on 1..4 project the
   same, whatever else they differ in. *)
Lemma perm_leaf_bits_eq (w w' : mword 64) :
  (forall k : Z, 1 <= k <= 4 ->
     Z.testbit (bv_unsigned w') k = Z.testbit (bv_unsigned w) k) ->
  perm_leaf w' = perm_leaf w.
Proof.
  intros Hb. unfold perm_leaf, perm_bits, pte_bit.
  rewrite (Hb 1 ltac:(lia)), (Hb 2 ltac:(lia)), (Hb 3 ltac:(lia)),
          (Hb 4 ltac:(lia)).
  reflexivity.
Qed.

(* the A/D write-back moves bits 6 and 7 only *)
Lemma perm_leaf_pte_set_ad (w : mword 64) (a d : mword 1) :
  perm_leaf (pte_set_ad w a d) = perm_leaf w.
Proof.
  apply perm_leaf_bits_eq. intros k Hk.
  rewrite (pte_set_ad_testbit w a d k ltac:(lia)).
  destruct (Z.eqb_spec k 6) as [-> | _]; [lia |].
  destruct (Z.eqb_spec k 7) as [-> | _]; [lia |].
  reflexivity.
Qed.

(* ...and rebuilding a leaf at its own flag byte over a new page moves the
   PPN and bit 0 (mappages ors in PTE_V) and nothing between 1 and 9 *)
Lemma perm_leaf_uvm_pte_flags10 (w r : mword 64) :
  perm_leaf (uvm_pte (pte_flags10 w) r) = perm_leaf w.
Proof.
  pose proof (pte_flags10_range w) as Hf.
  pose proof (pb_lor1_range _ Hf) as Hm.
  apply perm_leaf_bits_eq. intros k Hk.
  unfold uvm_pte, mappages_pte.
  rewrite (mk_pte_unsigned _ (Z.lor (pte_flags10 w) 1) Hm).
  (* the low ten bits of [q * 1024 + m] are [m]'s *)
  assert (Hlow : forall q m : Z, 0 <= m < 1024 -> 0 <= k < 10 ->
                   Z.testbit (q * 1024 + m) k = Z.testbit m k).
  { intros q m Hmb Hkb.
    replace (q * 1024 + m) with (m + q * 1024) by lia.
    rewrite <- (Z.mod_pow2_bits_low (m + q * 1024) 10 k); [| lia].
    change (2 ^ 10) with 1024.
    rewrite Z_mod_plus_full, (Z.mod_small m 1024 Hmb). reflexivity. }
  rewrite (Hlow _ _ Hm ltac:(lia)).
  rewrite Z.lor_spec.
  assert (H1 : Z.testbit 1 k = false)
    by (apply Z.bits_above_log2; [lia | rewrite Z.log2_1; lia]).
  rewrite H1, orb_false_r.
  unfold pte_flags10.
  assert (Ho : (1023 = Z.ones 10)) by (vm_compute; reflexivity).
  rewrite Ho, Z.land_spec, (Z.ones_spec_low 10 k ltac:(lia)), andb_true_r.
  reflexivity.
Qed.

(* MAPPED IMPLIES LIVE.  [um_below] bounds a mapped page's BASE by [p->sz],
   so every byte of it is under PGROUNDUP -- which is what collapses
   [umem_lazy]'s two-armed domain law to the live region alone, and that
   collapse is what [umem_write_copy_id] above is stated against.  The
   [dom]/[live_pages] form is [UserPerm.um_below_dom_live]; this is the
   per-va one, which nothing had. *)
Lemma z_page_in_pgroundup (v s : Z) (j : nat) :
  0 <= v -> v * 4096 < s -> (j < 4096)%nat ->
  0 <= v * 4096 + Z.of_nat j < UserPtTree.pgroundup s.
Proof.
  intros Hv Hvs Hj. unfold UserPtTree.pgroundup.
  pose proof (Z_div_mod_eq_full (s + 4095) 4096) as Hd.
  pose proof (Z.mod_pos_bound (s + 4095) 4096 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma um_below_uva_live (szv : mword 64) (P : uptd) (va : Z) :
  um_below szv (ud_um P) -> uva_mapped P va -> uva_live (uint szv) va.
Proof.
  intros Hbel (vpn & w & j & Hl & Hj & ->).
  pose proof (Hbel _ _ Hl) as Hlt.
  pose proof (proj1 (bv_unsigned_in_range 27 vpn)) as Hv0.
  unfold uva_live. rewrite uint_unsigned.
  exact (z_page_in_pgroundup _ _ _ Hv0 Hlt Hj).
Qed.

(* ...and the collapse itself: [ProcPtOwn.proc_ptm_dom]'s law, cut down to
   the domain premise [umem_write_copy_id] takes. *)
Lemma umem_dom_live (P : uptd) (szv : mword 64) (M : gmap Z (bv 8)) :
  um_below szv (ud_um P) ->
  (forall va : Z, is_Some (M !! va) <-> (uva_mapped P va \/ uva_live (uint szv) va)) ->
  forall va : Z, is_Some (M !! va) <-> uva_live (uint szv) va.
Proof.
  intros Hbel Hdom va. rewrite Hdom. split.
  - intros [Hm | Hl]; [exact (um_below_uva_live szv P va Hbel Hm) | exact Hl].
  - intros Hl. right. exact Hl.
Qed.

(* uvmcopy's run starts at page 0 -- [SpecUvmcopy]'s [vpn0] is
   [svpn_of 0] -- which is the side condition the two lemmas below take. *)
Lemma svpn_of_zero : bv_unsigned (svpn_of (mword_of_int 0 : mword 64)) = 0.
Proof. vm_compute. reflexivity. Qed.

(* THE PROJECTION IS POINTWISE.  Two maps that are defined at the same
   pages and whose leaves project the same have the same permission view:
   [omap perm_leaf] agrees by the second premise and [perm_fill]'s "minus
   the mapped pages" by the first, which the match delivers. *)
Lemma perm_of_ext (um um' : gmap (mword 27) (mword 64)) (sz : Z) :
  (forall vpn : mword 27,
     match um !! vpn, um' !! vpn with
     | None, None => True
     | Some w, Some w' => perm_leaf w' = perm_leaf w
     | _, _ => False
     end) ->
  perm_of um' sz = perm_of um sz.
Proof.
  intros Hpt.
  assert (Hdom : dom um' = dom um).
  { apply set_eq. intros v. rewrite !elem_of_dom.
    pose proof (Hpt v) as Hv.
    destruct (um !! v) as [w |] eqn:E; destruct (um' !! v) as [w' |] eqn:E';
      try contradiction.
    - split; intros _; [exists w | exists w']; reflexivity.
    - reflexivity. }
  unfold perm_of, perm_fill. rewrite Hdom. f_equal.
  apply map_eq. intros v. rewrite !lookup_omap.
  pose proof (Hpt v) as Hv.
  destruct (um !! v) as [w |] eqn:E; destruct (um' !! v) as [w' |] eqn:E';
    try contradiction.
  - simpl. exact Hv.
  - reflexivity.
Qed.

(* ---- the arithmetic, over plain [Z]/[nat] --------------------------
   Stated away from the bitvectors on purpose: [lia] answers "Cannot find
   witness" on any of these while an [mword] is merely in context
   (durable-notes, Arithmetic). *)
Lemma z_page_index_lt (v s g : Z) (n : nat) :
  0 <= v -> v * 4096 < s -> s <= g -> 4096 * Z.of_nat n = g ->
  (Z.to_nat v < n)%nat.
Proof. lia. Qed.

Lemma z_vpn_nowrap (v z : Z) :
  0 <= v < 134217728 -> z = 0 -> z + Z.of_nat (Z.to_nat v) < 134217728.
Proof. lia. Qed.

Lemma z_vpn_id (v z : Z) : 0 <= v -> z = 0 -> v = z + Z.of_nat (Z.to_nat v).
Proof. lia. Qed.

(* every page the parent maps is inside the run uvmcopy walks: [um_below]
   puts its base under [p->sz] and the run is [PGROUNDUP(p->sz)/4096]
   pages from page 0 *)
Lemma um_below_in_run (szw : mword 64) (vpn0 : mword 27)
    (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  bv_unsigned vpn0 = 0 ->
  um_below szw um ->
  um !! vpn = Some w ->
  exists i : nat, (i < uvm_np szw)%nat /\ vpn = vpn_at vpn0 i.
Proof.
  intros Hv0 Hbel Hlk.
  pose proof (Hbel _ _ Hlk) as Hlt.
  pose proof (bv_unsigned_in_range 27 vpn) as [Hv_lo Hv_hi].
  pose proof (bv_unsigned_in_range 64 szw) as [Hs_lo _].
  assert (HM : bv_modulus 27 = 134217728) by (vm_compute; reflexivity).
  rewrite HM in Hv_hi.
  pose proof (uvm_np_live szw) as Hnp.
  rewrite uint_unsigned in Hnp.
  pose proof (pgroundup_ge (bv_unsigned szw) Hs_lo) as Hge.
  exists (Z.to_nat (bv_unsigned vpn)).
  split; [exact (z_page_index_lt _ _ _ _ Hv_lo Hlt Hge Hnp) |].
  apply bv_eq.
  rewrite (vpn_at_unsigned vpn0 (Z.to_nat (bv_unsigned vpn))
             (z_vpn_nowrap _ _ (conj Hv_lo Hv_hi) Hv0)).
  exact (z_vpn_id _ _ Hv_lo Hv0).
Qed.

(* THE LEMMA.  uvmcopy's three clauses, the child's empty starting map and
   the parent's [um_below] give the child the parent's permission view. *)
Lemma perm_of_uvmcopy_child (szw : mword 64) (vpn0 : mword 27)
    (Pold Pnew P' : uptd) :
  bv_unsigned vpn0 = 0 ->
  ud_um Pnew = ∅ ->
  um_below szw (ud_um Pold) ->
  (forall vpn : mword 27, vpn ∉ vpn_run vpn0 (uvm_np szw) ->
     ud_um P' !! vpn = ud_um Pnew !! vpn) ->
  (forall i : nat, (i < uvm_np szw)%nat ->
     match ud_um Pold !! vpn_at vpn0 i with
     | None => ud_um P' !! vpn_at vpn0 i = ud_um Pnew !! vpn_at vpn0 i
     | Some w => exists (r w' : mword 64) (a d : mword 1),
         ud_um P' !! vpn_at vpn0 i = Some w' /\
         w' = pte_set_ad (uvm_pte (pte_flags10 w) r) a d
     end) ->
  perm_of (ud_um P') (uint szw) = perm_of (ud_um Pold) (uint szw).
Proof.
  intros Hv0 Hempty Hbel Hout Hin.
  apply perm_of_ext. intros vpn.
  destruct (decide (vpn ∈ vpn_run vpn0 (uvm_np szw))) as [Hmem | Hnot].
  - apply elem_of_vpn_run in Hmem as (i & Hi & ->).
    specialize (Hin i Hi).
    destruct (ud_um Pold !! vpn_at vpn0 i) as [w |] eqn:Ep.
    + destruct Hin as (r & w' & a & d & Hp' & ->).
      rewrite Hp'. rewrite perm_leaf_pte_set_ad.
      apply perm_leaf_uvm_pte_flags10.
    + rewrite Hin, Hempty, lookup_empty. exact I.
  - rewrite (Hout vpn Hnot), Hempty, lookup_empty.
    destruct (ud_um Pold !! vpn) as [w |] eqn:Ep; [| exact I].
    exfalso. destruct (um_below_in_run szw vpn0 (ud_um Pold) vpn w Hv0 Hbel Ep)
      as (i & Hi & ->).
    apply Hnot. apply elem_of_vpn_run. exists i. split; [exact Hi | reflexivity].
Qed.

(* ===================================================================== *)
(* §4 THE ASSEMBLY: the child's actual record has the run key of the      *)
(* record [SpecKfork] states.                                             *)
(* ===================================================================== *)
Lemma urun_eq_kfork_child (Up Uc : ustate) (sts : list fdstate) :
  pv_tf (us_V Uc) = <[14%nat := zero_reg]> (pv_tf (us_V Up)) ->
  us_M Uc = us_M Up ->
  perm_of (ud_um (pv_upt (us_V Uc))) (uint (pv_sz (us_V Uc)))
    = perm_of (ud_um (pv_upt (us_V Up))) (uint (pv_sz (us_V Up))) ->
  pv_sz (us_V Uc) = pv_sz (us_V Up) ->
  pv_cwi (us_V Uc) = pv_cwi (us_V Up) ->
  urun_eq (uvis_of (kfork_child Up) sts) Uc.
Proof.
  intros Htf HM Hperm Hsz Hcw.
  unfold urun_eq. rewrite uvis_of_kfork_child.
  cbn [uvis_tf uvis_M uvis_perm uvis_sz uvis_cwd].
  rewrite Htf. rewrite HM. rewrite Hperm. rewrite Hsz. rewrite Hcw.
  repeat split.
Qed.
