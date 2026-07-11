(* UptInv.v -- the user page-table invariant.

   Ownership is organized PER PT SLOT (an address-indexed map of 8-byte
   words), NOT per vpn: upper-level slots are shared by many vpns, so a
   per-vpn big-op would duplicate ownership.  A pure spec [upt_spec] ties
   the slot map to per-vpn walk descriptions; the walk hypotheses of
   UmodeWalk are packaged as [uw_wf] (access-agnostic structure) plus a
   per-access permission fact [uw_check_ok].

   A/D bits are ARBITRARY: [uw_wf] says nothing about them.  Whether an
   access succeeds or page-faults is decided per access by
   [update_PTE_Bits ... = None] vs [= Some _] -- both arms proven
   (UmodeWalk success / UmodeFetchFault + translate_TLB_miss fault).

   The Iris half: [upt_slots] owns every slot word ([↦₈], full ownership:
   slots stay writable so a future ADUE=1 write-back arm can update them
   in place), and [upt_slot_read_pte] turns one owned slot into the
   [read_pte] exec fact the UmodeWalk lemmas consume -- alignment and
   RAM-ness come bundled with [↦₈], the PMP facts from the frame's TOR
   entry 0, PMA/CLINT/SIG/HTIF from [hw_config] (plus the separate
   [pma_allows_pte_read], pinned by the concrete boot PMA list exactly
   like WpSmodeGpr's Hpteregion).

   [upt_tlb_ok] closes the loop-invariant story for the TLB: every
   present entry is the [u_walk_entry] of some spec-mapped vpn, so the
   TLB state stays describable across walk-induced fills (the ONLY TLB
   writes user execution can cause).                                    *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import UmodeWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The pure walk description: one mapped vpn = three PTE words          *)
(* ===================================================================== *)

Record uwalk_info := UWalk {
  uw_pte2 : mword 64;   (* root level: valid non-leaf *)
  uw_pte1 : mword 64;   (* mid level:  valid non-leaf *)
  uw_pte0 : mword 64    (* leaf: arbitrary A/D, no NAPOT, not global *)
}.

(* the three slot addresses the walk for [vpn] reads *)
Definition uw_addr2 (root : mword 44) (vpn : mword 27) : mword 64 :=
  u_pte_addr root (subrange_vec_dec vpn 26 18).
Definition uw_addr1 (i : uwalk_info) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base (uw_pte2 i)) (subrange_vec_dec vpn 17 9).
Definition uw_addr0 (i : uwalk_info) (vpn : mword 27) : mword 64 :=
  u_pte_addr (u_next_base (uw_pte1 i)) (subrange_vec_dec vpn 8 0).

(* structural wf: exactly the access-agnostic UserWalk section hypotheses *)
Definition uw_wf (i : uwalk_info) : Prop :=
  (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (uw_pte2 i) 7 0))
                     (ext_bits_of_PTE (uw_pte2 i))) s = Some (false, s)) /\
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec (uw_pte2 i) 7 0)) = true /\
  (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (uw_pte1 i) 7 0))
                     (ext_bits_of_PTE (uw_pte1 i))) s = Some (false, s)) /\
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec (uw_pte1 i) 7 0)) = true /\
  (forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (uw_pte0 i) 7 0))
                     (ext_bits_of_PTE (uw_pte0 i))) s = Some (false, s)) /\
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec (uw_pte0 i) 7 0)) = false /\
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE (uw_pte0 i))) ('b"1") = false /\
  u_global (uw_pte2 i) (uw_pte1 i) (uw_pte0 i) = false /\
  (* leaf PBMT bits are zero (NOT an A/D bit -- those stay arbitrary): the
     TLB-hit path recomputes the page type from the STORED pte, so the
     spec must pin it (the walk path needs only menvcfg.PBMTE = 0) *)
  _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2).

(* per-access permission fact on the leaf, in U-mode (mxr/do_sum-generic,
   exactly the UserWalk Hchk0 shape) *)
Definition uw_check_ok (acc : MemoryAccessType mem_payload) (i : uwalk_info) : Prop :=
  forall (mxr do_sum : bool) s,
    exec (check_PTE_permission acc User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (uw_pte0 i) 7 0))
            (ext_bits_of_PTE (uw_pte0 i)) tt) s
      = Some (PTE_Check_Success tt, s).

(* the pure spec: the slot map describes every mapped vpn's walk *)
Definition upt_spec (root : mword 44)
    (slots : gmap (mword 64) (mword 64))
    (spec : gmap (mword 27) uwalk_info) : Prop :=
  forall vpn i, spec !! vpn = Some i ->
    slots !! uw_addr2 root vpn = Some (uw_pte2 i) /\
    slots !! uw_addr1 i vpn = Some (uw_pte1 i) /\
    slots !! uw_addr0 i vpn = Some (uw_pte0 i) /\
    uw_wf i.

(* ===================================================================== *)
(* §2 TLB consistency: user execution only ever installs walk entries      *)
(* ===================================================================== *)

(* the entry a completed walk for [vpn] installs (asid 0 throughout) *)
Definition upt_entry (vpn : mword 27) (i : uwalk_info) : TLB_Entry :=
  u_walk_entry vpn (uw_pte2 i) (uw_pte1 i) (uw_pte0 i) (mword_of_int 0).

(* every present TLB slot is the walk entry of some spec-mapped vpn
   (quantified through the hash so the fill lemma needs no injectivity) *)
Definition upt_tlb_ok (spec : gmap (mword 27) uwalk_info)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  forall (vpn' : mword 27) ent,
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = Some ent ->
    exists vpn i, spec !! vpn = Some i /\
      tlb_hash (__id 39) vpn = tlb_hash (__id 39) vpn' /\
      ent = upt_entry vpn i.

(* an all-empty TLB is consistent with any spec *)
Lemma upt_tlb_ok_empty (spec : gmap (mword 27) uwalk_info)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall vpn', vec_access_dec tlbvec (tlb_hash (__id 39) vpn') = None) ->
  upt_tlb_ok spec tlbvec.
Proof.
  intros Hnone vpn' ent Hget. rewrite Hnone in Hget. discriminate.
Qed.

(* consistency survives a walk-induced fill -- the ONLY TLB write user
   execution can cause (add_to_TLB at the end of a successful miss walk) *)
Lemma upt_tlb_ok_fill (spec : gmap (mword 27) uwalk_info)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (vpn : mword 27) (i : uwalk_info) :
  spec !! vpn = Some i ->
  upt_tlb_ok spec tlbvec ->
  upt_tlb_ok spec (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                     (Some (upt_entry vpn i))).
Proof.
  intros Hvpn Hok vpn' ent Hget.
  rewrite (vec64_access_update _ _ _ _ (tlb_hash_range vpn)) in Hget.
  destruct (Z.eqb (tlb_hash (__id 39) vpn') (tlb_hash (__id 39) vpn)) eqn:Hh.
  - apply Z.eqb_eq in Hh. injection Hget as <-.
    exists vpn, i. auto.
  - exact (Hok vpn' ent Hget).
Qed.

(* ===================================================================== *)
(* §2b Hit-path bridges: a stored [upt_entry] recovers the leaf facts      *)
(*     the TLB-hit translation lemmas consume (tlb_get_pte / match /       *)
(*     tlb_get_pbmt), so a hit at a spec-mapped entry replays the walk's   *)
(*     leaf.                                                               *)
(* ===================================================================== *)

(* the 63..0 subrange of a 64-bit word is the word *)
Lemma subrange64_id (w : mword 64) : subrange_vec_dec w 63 0 = w.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (63 - 0 + 1)) with 64%N.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply bool_decide_eq_true_2. reflexivity. Qed.

(* dropping a zero-width mask is a no-op, at the two widths the entry uses *)
Lemma and_ones45 (x : mword 45) :
  and_vec x (not_vec (zero_extend' (57 - 12) (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  (* uniformize the width forms (Z_idx 45 vs Z_idx (57-12)) so the closed
     mask converts in place *)
  change (Z.sub 57 12) with 45.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 45) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

Lemma and_ones27 (x : mword 27) :
  and_vec x (not_vec (zero_extend' 27 (ones 0 : mword 0))) = x.
Proof.
  apply bv_eq.
  unfold and_vec, word_binop, with_word', with_word, MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land _ (bv_unsigned ?m)] =>
    change (bv_unsigned m) with (Z.ones 27) end.
  rewrite Z.land_ones; [|lia].
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr. exact Hr.
Qed.

(* the stored 8-byte PTE is the walk's leaf *)
Lemma upt_entry_pte (vpn : mword 27) (i : uwalk_info) :
  tlb_get_pte 8 (upt_entry vpn i) = uw_pte0 i.
Proof.
  unfold tlb_get_pte, upt_entry, u_walk_entry. cbn [TLB_Entry_pte].
  rewrite autocast_id. rewrite zero_extend'_id.
  change (Z.sub (Z.mul 8 8) 1) with 63.
  rewrite subrange64_id. apply autocast_id.
Qed.

(* the stored entry matches its own vpn lookup (asid 0) *)
Lemma upt_entry_match (vpn : mword 27) (i : uwalk_info) :
  match_TLB_Entry (upt_entry vpn i) (mword_of_int 0) (sign_extend' (57 - 12) vpn) = true.
Proof.
  unfold match_TLB_Entry, upt_entry, u_walk_entry.
  cbn [TLB_Entry_global TLB_Entry_asid TLB_Entry_vpn TLB_Entry_levelMask].
  rewrite and_ones45. rewrite and_ones27. rewrite !eq_vec_refl.
  rewrite orb_true_r. reflexivity.
Qed.

(* the general match fact: a stored walk entry matches a lookup for vpn'
   iff the sign-extended vpns agree (asid is 0 on both sides) *)
Lemma upt_entry_match_gen (vpn vpn' : mword 27) (i : uwalk_info) :
  match_TLB_Entry (upt_entry vpn i) (mword_of_int 0) (sign_extend' (57 - 12) vpn')
  = eq_vec (sign_extend' (57 - 12) vpn) (sign_extend' (57 - 12) vpn').
Proof.
  unfold match_TLB_Entry, upt_entry, u_walk_entry.
  cbn [TLB_Entry_global TLB_Entry_asid TLB_Entry_vpn TLB_Entry_levelMask].
  rewrite and_ones45. rewrite and_ones27. rewrite eq_vec_refl.
  rewrite orb_true_r. reflexivity.
Qed.

(* sign-extension 27 -> 45 is injective: a hash-slot hit for vpn' at a
   stored entry for vpn forces vpn = vpn' *)
Lemma sext45_inj (x y : mword 27) :
  sign_extend' (57 - 12) x = sign_extend' (57 - 12) y -> x = y.
Proof.
  intros H.
  apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H; [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma upt_entry_match_inj (vpn vpn' : mword 27) (i : uwalk_info) :
  match_TLB_Entry (upt_entry vpn i) (mword_of_int 0) (sign_extend' (57 - 12) vpn')
    = true ->
  vpn = vpn'.
Proof.
  rewrite upt_entry_match_gen. intros He.
  apply sext45_inj. apply eq_vec_true_iff. exact He.
Qed.

(* the stored entry recomputes the walk's page type (leaf PBMT pinned 0) *)
Lemma upt_entry_pbmt (vpn : mword 27) (i : uwalk_info) (s : mstate) :
  _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) ->
  exec (tlb_get_pbmt (upt_entry vpn i)) s = Some (PBMT_PMA, s).
Proof.
  intros Hp.
  unfold tlb_get_pbmt, upt_entry, u_walk_entry. cbn [TLB_Entry_pte].
  rewrite autocast_id. rewrite zero_extend'_id.
  rewrite Hp.
  apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §3 The pte-read PMA fact (pinned by the concrete boot PMA list, the     *)
(*    same way WpSmodeGpr threads Hpteregion)                              *)
(* ===================================================================== *)
Definition pma_allows_pte_read (regions : list PMA_Region) : Prop :=
  forall (a : mword 64), exists r,
    matching_pma_region regions (Physaddr a) 8 = Some r /\
    (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_read) = true.

(* ===================================================================== *)
(* §4 The Iris half                                                        *)
(* ===================================================================== *)
Section UptInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the owned PT slots (full ownership: a future ADUE=1 write-back arm
     updates them in place) *)
  Definition upt_slots (slots : gmap (mword 64) (mword 64)) : iProp Σ :=
    ([∗ map] a ↦ w ∈ slots, a ↦₈ w)%I.

  (* the user page-table invariant body *)
  Definition upt_inv (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info) : iProp Σ :=
    (upt_slots slots ∗ ⌜upt_spec root slots spec⌝)%I.

  (* ONE owned slot word yields its [read_pte] exec fact at any machine
     state consistent with the frame: alignment + RAM-ness travel with
     [↦₈]; PMP entry 0 is the frame's all-of-RAM TOR entry; PMA / CLINT /
     SIG / HTIF come from [hw_config] + [pma_allows_pte_read].           *)
  Lemma upt_slot_read_pte (a : mword 64) (w : bv 64) (dq : dfrac) (σ : mstate) :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    (a ↦₈{dq} w) -∗
    ⌜exec (read_pte (Physaddr a) 8) σ = Some (Ok w, σ)⌝.
  Proof.
    iIntros (HA Hord HR Hcov Hpter) "Hhw [Hreg Hmem] Hw".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hbytes".
    (* the byte heap agrees with [w] on the 8-byte window *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add a j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    (* RAM-ness of both window ends, for the PMP range fact *)
    iAssert (⌜addr_is_ram a⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hram7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    iPureIntro.
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    destruct (Hpter pmar0 Hpma_all a) as (region & Hpmam & Hptep).
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr a) 8 = Some region) by (rewrite Lpma; exact Hpmam).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint a) (uint (to_bits 64 8)) = PMP_Match).
    { exact (ram_fetch_pmp a (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram7 Hcov). }
    exact (exec_read_pte_S a region w σ
             HA Hord Hrange HR Hpmam' Hal Hptep
             (within_clint_false a 8 σ Hnc ltac:(lia))
             (within_sig_false a 8 σ Hns ltac:(lia))
             (within_htif_false a 8 σ Lhtif)
             Hbf).
  Qed.

  (* the aggregated form: a spec-mapped vpn yields ALL THREE walk reads
     (the conclusion is pure, so the slots are only borrowed) *)
  Lemma upt_walk_read_ptes (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (i : uwalk_info) (σ : mstate) :
    spec !! vpn = Some i ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exec (read_pte (Physaddr (uw_addr2 root vpn)) 8) σ = Some (Ok (uw_pte2 i), σ) /\
     exec (read_pte (Physaddr (uw_addr1 i vpn)) 8) σ = Some (Ok (uw_pte1 i), σ) /\
     exec (read_pte (Physaddr (uw_addr0 i vpn)) 8) σ = Some (Ok (uw_pte0 i), σ) /\
     uw_wf i⌝.
  Proof.
    iIntros (Hvpn HA Hord HR Hcov Hpter) "#Hhw Hint [Hslots %Hspec]".
    destruct (Hspec vpn i Hvpn) as (Hs2 & Hs1 & Hs0 & Hwf).
    (* each application borrows [Hint]/[Hslots] inside a pure iAssert, so
       the spatial context survives all three *)
    iAssert (⌜exec (read_pte (Physaddr (uw_addr2 root vpn)) 8) σ
               = Some (Ok (uw_pte2 i), σ)⌝)%I as %Hr2.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw2 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw2"). }
    iAssert (⌜exec (read_pte (Physaddr (uw_addr1 i vpn)) 8) σ
               = Some (Ok (uw_pte1 i), σ)⌝)%I as %Hr1.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw1 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw1"). }
    iAssert (⌜exec (read_pte (Physaddr (uw_addr0 i vpn)) 8) σ
               = Some (Ok (uw_pte0 i), σ)⌝)%I as %Hr0.
    { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs0 with "Hslots") as "[Hw0 _]".
      iApply (upt_slot_read_pte _ _ _ _ HA Hord HR Hcov Hpter
                with "Hhw Hint Hw0"). }
    iPureIntro. auto.
  Qed.

End UptInv.
