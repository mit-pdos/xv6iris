(* WpUserMemStep.v -- the spatial-composed user-mode step (WORKLIST).

   Goal: a dispatcher [user_step_holds_full] that discharges
   [user_step_obligation] WITHOUT the pure premise [Hclass : ∀ frame,
   ustep_case] of [wp_user_exec_v1] -- because [ustep_case] (a pure-Prop
   44-way disjunction) has NO home for data-page loads, stores, or
   atomics (they need mutable-memory ownership).  The frame ALREADY owns
   [user_data] (WpUserBase.user_frame), so the dispatcher can, per step,
   unpack it and route a memory word to the frame-decomposed spatial arm
   ([ustep_ld_data]/[ustep_sw]/...) while non-memory words reuse the
   existing classification arms.  See iris/CLAUDE.md ("The FULL user-mode
   WP") for the full plan.

   BRICKS:
   (1) Value derivation ([nth_byte_assemble8], this file): the spatial load
       arms take the loaded value [v] plus [∀ j<N, dm !! pa_add paD j =
       Some (nth_byte v j)].  Since [v] must be READ from the frame's
       existential data map [dm], the dispatcher assembles it little-endian
       from the bytes of [dm] once the window lies in [dom dm].  (NB
       [RiscvModelBytes.read_bytes] cannot be used: it bakes [bv_countable]
       for [Arch.pa] keys while the memory arms' [dm] uses [Countable_mword]
       -- non-convertible instances -- so we gather over [dm]'s own instance
       and prove the byte roundtrip with the pure [assemble_bytes] lemmas.)
   (2) Window peel/restore ([data_window_acc_gen], WpUserMemPeel.v) for the
       store arms.
   (3) Dispatcher-facing memory steps (this file): consume [user_data]
       whole and derive the loaded value internally.  [wp_user_ld_data_frame]
       is the width-8 data-page load case. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions list list_monad.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecodeBridge.
Require Import SmodePte.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase WpUserMem WpUserMem4 WpUserMem2 WpUserMem1 WpUserAmo.
Require Import WpUserSplitMem.

(* ---------------------------------------------------------------------- *)
(* (1) Value derivation: assemble the loaded word from the owned bytes.     *)
(* ---------------------------------------------------------------------- *)

(* Roundtrip: byte [j] of the little-endian assembly of an 8-byte list is
   the [j]-th list element.  Pure (instance-agnostic); lets the dispatcher
   build the loaded [mword 64] from bytes read out of the arm's own data
   map (whose [Countable Arch.pa] instance differs from [read_bytes]'s, so
   [read_bytes] itself cannot be applied to it).  Cloned from
   [KallocInv.nth_byte_assemble8]. *)
Lemma nth_byte_assemble8 (bs : list (bv 8)) (j : nat) :
  length bs = 8%nat -> (j < 8)%nat ->
  nth_byte (Z_to_bv 64 (assemble_bytes bs) : mword 64) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 64 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

(* Width-4 companion of [nth_byte_assemble8] (for the SW/LW dispatchers). *)
Lemma nth_byte_assemble4 (bs : list (bv 8)) (j : nat) :
  length bs = 4%nat -> (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (assemble_bytes bs) : mword 32) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 32 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

(* Width-2 companion (for the LH/SH dispatchers). *)
Lemma nth_byte_assemble2 (bs : list (bv 8)) (j : nat) :
  length bs = 2%nat -> (j < 2)%nat ->
  nth_byte (Z_to_bv 16 (assemble_bytes bs) : mword 16) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 16 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

(* Width-1 companion (for the LB/SB dispatchers). *)
Lemma nth_byte_assemble1 (bs : list (bv 8)) (j : nat) :
  length bs = 1%nat -> (j < 1)%nat ->
  nth_byte (Z_to_bv 8 (assemble_bytes bs) : mword 8) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 8 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* (2) Window peel/restore for the STORE dispatcher.                        *)
(*                                                                          *)
(*     These are the [WpUserMemPeel.v] helpers RE-PROVEN here over the       *)
(*     frame's NATIVE [Countable_mword] instance (the one [user_data]'s     *)
(*     [dm : gmap Arch.pa (bv 8)] actually uses).  The [WpUserMemPeel.v]     *)
(*     copies bake [bv_countable] (that file avoids [SailStdpp.Base]) and    *)
(*     so DO NOT apply to a [dm] pulled from [user_data] here -- the two     *)
(*     [Countable Arch.pa] instances are non-convertible.  Two Base-context  *)
(*     tactic hazards worth recording: (a) bare [NoDup] resolves to          *)
(*     [List.NoDup], not stdpp's [base.NoDup] -- qualify both the statement  *)
(*     and the destructor ([list_relations.NoDup_cons]); (b) [simpl] over-    *)
(*     reduces [Arch.pa]/its instances into a form where the generic map      *)
(*     lemmas ([delete_insert_ne], [dom_insert_L]) can no longer synthesise   *)
(*     [FinMap Arch.pa (gmap Arch.pa)] -- expose the [foldr] cons step with   *)
(*     [cbn [foldr]] or an explicit [assert ... by reflexivity] instead, and  *)
(*     avoid [set_solver] (it chokes the same way). *)

(* window addresses are pairwise distinct when the window does not wrap *)
Lemma pa_add_inj_nowrap (paD : Arch.pa) (n : nat) (j j' : nat) :
  (uint paD + Z.of_nat n <= 18446744073709551616)%Z ->
  (j < n)%nat -> (j' < n)%nat -> pa_add paD j = pa_add paD j' -> j = j'.
Proof.
  intros Hnw Hj Hj' Heq.
  assert (Huj : uint (pa_add paD j) = uint paD + Z.of_nat j) by (apply uint_pa_add; lia).
  assert (Huj' : uint (pa_add paD j') = uint paD + Z.of_nat j') by (apply uint_pa_add; lia).
  rewrite Heq in Huj. rewrite Huj' in Huj. lia.
Qed.

Lemma NoDup_pa_window (paD : Arch.pa) (n : nat) :
  (uint paD + Z.of_nat n <= 18446744073709551616)%Z ->
  base.NoDup ((pa_add paD) <$> (seq 0 n)).
Proof.
  intro Hnw. apply NoDup_fmap_2_strong.
  - intros x y Hx Hy Heq. apply elem_of_seq in Hx; apply elem_of_seq in Hy.
    apply (pa_add_inj_nowrap paD n); [lia|lia|lia|exact Heq].
  - apply NoDup_seq.
Qed.

(* gmap: deleting a key commutes past inserts of OTHER keys *)
Lemma foldr_insert_delete_comm (paD : Arch.pa) (g : nat -> bv 8)
    (k : Arch.pa) (l : list nat) (m : gmap Arch.pa (bv 8)) :
  k ∉ ((pa_add paD) <$> l) ->
  foldr (fun j acc => <[pa_add paD j := g j]> acc) (delete k m) l
  = delete k (foldr (fun j acc => <[pa_add paD j := g j]> acc) m l).
Proof.
  induction l as [|x xs IH]; intro Hk.
  - reflexivity.
  - rewrite fmap_cons in Hk. apply not_elem_of_cons in Hk as [Hne Hk].
    cbn [foldr]. rewrite (IH Hk).
    symmetry. apply delete_insert_ne. exact Hne.
Qed.

(* inserting keys already present preserves the domain *)
Lemma dom_foldr_insert_indom (g : nat -> bv 8) (paD : Arch.pa)
    (l : list nat) (m : gmap Arch.pa (bv 8)) :
  (forall j, j ∈ l -> pa_add paD j ∈ dom m) ->
  dom (foldr (fun j acc => <[pa_add paD j := g j]> acc) m l) = dom m.
Proof.
  induction l as [|x xs IH]; intro Hin.
  - reflexivity.
  - assert (Hin' : forall j, j ∈ xs -> pa_add paD j ∈ dom m).
    { intros j Hj. apply Hin. apply elem_of_list_further. exact Hj. }
    assert (Hstep : foldr (fun j acc => <[pa_add paD j := g j]> acc) m (x :: xs)
             = <[pa_add paD x := g x]> (foldr (fun j acc => <[pa_add paD j := g j]> acc) m xs))
      by reflexivity.
    rewrite Hstep. rewrite dom_insert_L. rewrite (IH Hin').
    assert (Hx : pa_add paD x ∈ dom m) by (apply Hin; apply elem_of_list_here).
    apply subseteq_union_1_L. apply singleton_subseteq_l. exact Hx.
Qed.

Section peel.
  Context `{!riscvGS Σ}.

  (* Peel the [pa_add paD 0 .. paD (|l|-1)] cells out of a frame-owned byte
     map, keeping a restore wand.  [fold_new] is chosen by the caller at
     restore time (for a store: [fun j => nth_byte vNew j]). *)
  Lemma data_window_acc_gen (paD : Arch.pa) (l : list nat)
      (fold_old : nat -> bv 8) (m : gmap Arch.pa (bv 8)) :
    base.NoDup ((pa_add paD) <$> l) ->
    (forall j, j ∈ l -> m !! pa_add paD j = Some (fold_old j)) ->
    ⊢@{iPropI Σ}
      ([∗ map] a↦b ∈ m, a ↦ₘ b) -∗
      ([∗ list] j ∈ l, pa_add paD j ↦ₘ fold_old j) ∗
      (∀ fold_new : nat -> bv 8,
        ([∗ list] j ∈ l, pa_add paD j ↦ₘ fold_new j) -∗
        [∗ map] a↦b ∈ (foldr (fun j acc => <[pa_add paD j := fold_new j]> acc) m l), a↦ₘ b).
  Proof.
    revert m. induction l as [|x xs IH]; intros m Hnd Hcont.
    - iIntros "Hm". iSplitR "Hm".
      { done. }
      iIntros (fn) "_". cbn [foldr]. iFrame.
    - rewrite fmap_cons in Hnd. apply list_relations.NoDup_cons in Hnd as [Hxni Hnd].
      assert (Hmx : m !! pa_add paD x = Some (fold_old x))
        by (apply Hcont; apply elem_of_list_here).
      assert (Hcont' : forall j, j ∈ xs ->
                 delete (pa_add paD x) m !! pa_add paD j = Some (fold_old j)).
      { intros j Hj.
        assert (Hne : pa_add paD x ≠ pa_add paD j).
        { intro Hc. apply Hxni. rewrite Hc. apply elem_of_list_fmap.
          exists j. split; [reflexivity|exact Hj]. }
        rewrite (lookup_delete_ne _ _ _ Hne). apply Hcont.
        apply elem_of_list_further. exact Hj. }
      iIntros "Hm".
      iDestruct (big_sepM_delete _ _ _ _ Hmx with "Hm") as "[Hx Hrest]".
      iDestruct (IH (delete (pa_add paD x) m) Hnd Hcont' with "Hrest") as "[Hwin Hback]".
      iSplitL "Hx Hwin".
      { iFrame. }
      iIntros (fn) "[Hxn Hwn]".
      iDestruct ("Hback" $! fn with "Hwn") as "Hmap".
      cbn [foldr].
      iApply big_sepM_insert_delete.
      iFrame "Hxn".
      rewrite (foldr_insert_delete_comm paD fn (pa_add paD x) xs m Hxni).
      iFrame "Hmap".
  Qed.
End peel.

(* ---------------------------------------------------------------------- *)
(* (3) Dispatcher-facing memory steps: consume [user_data] whole and       *)
(*     derive the loaded/stored value internally, so the caller supplies    *)
(*     only the translation facts + a window-in-[data] premise.             *)
(* ---------------------------------------------------------------------- *)
Section WpUserMemStep.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation spec := (WpUserBase.spec U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation ustep_ld_data := (WpUserMem.ustep_ld_data U).
  Local Notation ustep_lw_data := (WpUserMem4.ustep_lw_data U).
  Local Notation ustep_lh_data := (WpUserMem2.ustep_lh_data U).
  Local Notation ustep_lb_data := (WpUserMem1.ustep_lb_data U).
  Local Notation ustep_sd := (WpUserMem.ustep_sd U).
  Local Notation ustep_sw := (WpUserMem4.ustep_sw U).
  Local Notation ustep_sh := (WpUserMem2.ustep_sh U).
  Local Notation ustep_sb := (WpUserMem1.ustep_sb U).
  Local Notation ustep_ld_u := (WpUserMem.ustep_ld_u U).
  Local Notation ustep_lw_u := (WpUserMem4.ustep_lw_u U).
  Local Notation ustep_lh_u := (WpUserMem2.ustep_lh_u U).
  Local Notation ustep_lb_u := (WpUserMem1.ustep_lb_u U).
  Local Notation ustep_sd_u := (WpUserMem.ustep_sd_u U).
  Local Notation ustep_sw_u := (WpUserMem4.ustep_sw_u U).
  Local Notation ustep_sh_u := (WpUserMem2.ustep_sh_u U).
  Local Notation ustep_sb_u := (WpUserMem1.ustep_sb_u U).
  Local Notation ustep_amoswap_w_u := (WpUserAmo.ustep_amoswap_w_u U).
  Local Notation ustep_u_split_ld_u := (WpUserSplitMem.ustep_u_split_ld_u U).
  Local Notation ustep_u_split_lw_u := (WpUserSplitMem.ustep_u_split_lw_u U).
  Local Notation ustep_u_split_lh_u := (WpUserSplitMem.ustep_u_split_lh_u U).
  Local Notation ustep_u_split_lb_u := (WpUserSplitMem.ustep_u_split_lb_u U).
  Local Notation ustep_u_split_sd_u := (WpUserSplitMem.ustep_u_split_sd_u U).
  Local Notation ustep_u_split_sw_u := (WpUserSplitMem.ustep_u_split_sw_u U).
  Local Notation ustep_u_split_sh_u := (WpUserSplitMem.ustep_u_split_sh_u U).
  Local Notation ustep_u_split_sb_u := (WpUserSplitMem.ustep_u_split_sb_u U).
  Local Notation ustep_u_split_amoswap_w_u := (WpUserSplitMem.ustep_u_split_amoswap_w_u U).

  (* Width-8 data-page load, dispatcher form: [user_data] whole in, value
     read from [dm] via [read_bytes] -- the caller only shows the target
     window lies in [data]. *)
  Lemma wp_user_ld_data_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    (* the loaded value, assembled from the owned data bytes (dm's own
       Countable instance, so [read_bytes] does not apply) *)
    assert (Hindom : forall j : nat, (j < 8)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 8).
    set (v := (Z_to_bv 64 (assemble_bytes bs)) : mword 64).
    assert (Hlen : length bs = 8%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 8)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 8))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 8 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 8 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble8 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_ld_data va vpn ie w vpnD ieD imm rs1 rd v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  (* Width-4 data-page LOAD, dispatcher form: like [wp_user_ld_data_frame]
     at 4 bytes -- [user_data] whole in, the loaded [mword 32] assembled
     from [dm] via [nth_byte_assemble4] and handed to [ustep_lw_data]
     (read-only, so no window peel).  [is_unsigned] rides the decode. *)
  Lemma wp_user_lw_data_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (v := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lw_data va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  (* Width-8 data-page STORE, dispatcher form: [user_data] whole in.  The
     dispatcher assembles the OLD value from [dm], peels the 8-cell target
     window with [data_window_acc_gen], and hands [ustep_sd] the window plus
     a restore wand that rebuilds [user_data] from the NEW bytes (the store
     leaves [dom dm = data] intact via [dom_foldr_insert_indom]).  The caller
     supplies the translation facts, a no-wrap bound on [paD] (from
     [addr_is_ram paD]), and [∀ j<8, pa_add paD j ∈ data]. *)
  Lemma wp_user_sd_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 8 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (g !!! Regidx rs2)).
    (* the OLD value, assembled from the owned data bytes (dm's own
       Countable instance, so [read_bytes] does not apply) *)
    assert (Hindom : forall j : nat, (j < 8)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 8).
    set (vold := (Z_to_bv 64 (assemble_bytes bs)) : mword 64).
    assert (Hlen : length bs = 8%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 8)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 8))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 8 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 8 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble8 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    (* peel the 8-cell window out of dm, keep the restore-to-map wand *)
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 8)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 8 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 8) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    (* lift the restore-to-map wand into a restore-to-[user_data] wand *)
    iAssert (([∗ list] j ∈ seq 0 8, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 8)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 8) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sd va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  (* Width-4 data-page STORE, dispatcher form: the width-8 [wp_user_sd_frame]
     recipe at 4 bytes -- assemble the OLD [mword 32] from [dm], peel the
     4-cell window, restore [user_data] from the NEW bytes, apply [ustep_sw].
     [vNew] is the low 32 bits of [g !!! rs2], matching [ustep_sw]. *)
  Lemma wp_user_sw_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 4 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
    (* the OLD value (mword 32), assembled from the owned data bytes *)
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (vold := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 4)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 4 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 4) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 4, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 4)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 4) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sw va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  (* Width-2 data-page LOAD (LH), dispatcher form.  (Fetch-side stays 4:
     [va]/fetch-PA alignment and the [code]/[w] instruction bytes are the
     32-bit instruction; only the DATA side is 2 bytes.) *)
  Lemma wp_user_lh_data_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 2)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 2).
    set (v := (Z_to_bv 16 (assemble_bytes bs)) : mword 16).
    assert (Hlen : length bs = 2%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 2)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 2))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 2 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 2 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble2 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lh_data va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  (* Width-1 data-page LOAD (LB), dispatcher form. *)
  Lemma wp_user_lb_data_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 1)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 1).
    set (v := (Z_to_bv 8 (assemble_bytes bs)) : mword 8).
    assert (Hlen : length bs = 1%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 1)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 1))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 1 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 1 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble1 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lb_data va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  (* Width-2 data-page STORE (SH), dispatcher form. *)
  Lemma wp_user_sh_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 2 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 2 8) 1) 0) : mword 16)).
    assert (Hindom : forall j : nat, (j < 2)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 2).
    set (vold := (Z_to_bv 16 (assemble_bytes bs)) : mword 16).
    assert (Hlen : length bs = 2%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 2)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 2))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 2 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 2 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble2 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 2)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 2 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 2) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 2, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 2)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 2) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sh va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  (* Width-1 data-page STORE (SB), dispatcher form. *)
  Lemma wp_user_sb_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 1 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8)).
    assert (Hindom : forall j : nat, (j < 1)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 1).
    set (vold := (Z_to_bv 8 (assemble_bytes bs)) : mword 8).
    assert (Hlen : length bs = 1%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 1)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 1))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 1 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 1 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble1 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 1)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 1 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 1) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 1, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 1)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 1) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sb va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HvecD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  Lemma wp_user_ld_data_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    (* the loaded value, assembled from the owned data bytes (dm's own
       Countable instance, so [read_bytes] does not apply) *)
    assert (Hindom : forall j : nat, (j < 8)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 8).
    set (v := (Z_to_bv 64 (assemble_bytes bs)) : mword 64).
    assert (Hlen : length bs = 8%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 8)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 8))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 8 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 8 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble8 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_ld_u va vpn ie w vpnD ieD imm rs1 rd v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  Lemma wp_user_lw_data_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (v := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lw_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  Lemma wp_user_lh_data_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 2)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 2).
    set (v := (Z_to_bv 16 (assemble_bytes bs)) : mword 16).
    assert (Hlen : length bs = 2%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 2)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 2))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 2 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 2 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble2 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lh_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  Lemma wp_user_lb_data_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 1)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 1).
    set (v := (Z_to_bv 8 (assemble_bytes bs)) : mword 8).
    assert (Hlen : length bs = 1%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 1)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 1))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 1 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 1 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble1 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_lb_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.

  Lemma wp_user_sd_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 8 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 8 = true ->
    (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (g !!! Regidx rs2)).
    (* the OLD value, assembled from the owned data bytes (dm's own
       Countable instance, so [read_bytes] does not apply) *)
    assert (Hindom : forall j : nat, (j < 8)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 8).
    set (vold := (Z_to_bv 64 (assemble_bytes bs)) : mword 64).
    assert (Hlen : length bs = 8%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 8)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 8))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 8 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 8 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble8 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    (* peel the 8-cell window out of dm, keep the restore-to-map wand *)
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 8)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 8 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 8) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    (* lift the restore-to-map wand into a restore-to-[user_data] wand *)
    iAssert (([∗ list] j ∈ seq 0 8, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 8)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 8) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sd_u va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  Lemma wp_user_sw_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 4 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32)).
    (* the OLD value (mword 32), assembled from the owned data bytes *)
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (vold := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 4)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 4 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 4) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 4, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 4)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 4) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sw_u va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  Lemma wp_user_sh_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 2 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 2 = true ->
    (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 2 8) 1) 0) : mword 16)).
    assert (Hindom : forall j : nat, (j < 2)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 2).
    set (vold := (Z_to_bv 16 (assemble_bytes bs)) : mword 16).
    assert (Hlen : length bs = 2%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 2)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 2))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 2 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 2 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble2 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 2)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 2 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 2) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 2, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 2)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 2) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sh_u va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  Lemma wp_user_sb_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 1 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Store Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Store Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 1 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 1 = true ->
    (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vNew := (autocast (T := mword)
                    (subrange_vec_dec (g !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8)).
    assert (Hindom : forall j : nat, (j < 1)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 1).
    set (vold := (Z_to_bv 8 (assemble_bytes bs)) : mword 8).
    assert (Hlen : length bs = 1%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 1)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 1))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 1 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 1 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble1 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 1)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 1 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 1) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 1, pa_add paD j ↦ₘ nth_byte vNew j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vNew j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vNew j]> acc) dm (seq 0 1)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vNew j) paD (seq 0 1) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_sb_u va vpn ie w vpnD ieD imm rs2 rs1 vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  (* AMOSWAP.W success, window-model dispatcher form: the fetch+data combined
     [ustep_amoswap_w_u] recipe wrapped over [user_data].  Mirrors
     [wp_user_sw_frame_u] (assemble the OLD [mword 32] from [dm], peel the
     4-cell window, restore [user_data] from the SWAPPED bytes, apply
     [ustep_amoswap_w_u]).  The stored value is the AMO swap value
     [vN := sign_extend' (8*4) (trunc (4*8) (g !!! rs2))], not the store's
     [vNew].  AMO has no immediate (eaF = g!!!rs1). *)
  Lemma wp_user_amoswap_frame_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (rs2 rs1 rd : mword 5)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    (uint paD + 4 <= 18446744073709551616)%Z ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Atomic (AMOSWAP, Data, Data)) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Atomic (AMOSWAP, Data, Data)) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
           Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin_in.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    set (vN := sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8)
                 (g !!! Regidx rs2)) : mword 32).
    (* the OLD value (mword 32), assembled from the owned data bytes *)
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin_in. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (vold := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst vold. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    assert (HND : base.NoDup ((pa_add paD) <$> (seq 0 4)))
      by (apply NoDup_pa_window; exact Hnowrap).
    assert (Hpeelcont : forall j, j ∈ seq 0 4 -> dm !! pa_add paD j = Some (nth_byte vold j)).
    { intros j Hj. apply elem_of_seq in Hj. apply Hcwd. lia. }
    iDestruct (data_window_acc_gen paD (seq 0 4) (fun j => nth_byte vold j) dm HND Hpeelcont
                 with "Hfmap") as "[Hwin Hback]".
    iAssert (([∗ list] j ∈ seq 0 4, pa_add paD j ↦ₘ nth_byte vN j) -∗ user_data)%I
      with "[Hback]" as "Hrestore".
    { iIntros "Hnew".
      iDestruct ("Hback" $! (fun j => nth_byte vN j) with "Hnew") as "Hmap".
      iExists (foldr (fun j acc => <[pa_add paD j := nth_byte vN j]> acc) dm (seq 0 4)).
      iSplitR.
      { iPureIntro.
        rewrite (dom_foldr_insert_indom (fun j => nth_byte vN j) paD (seq 0 4) dm).
        - exact Hdomdm.
        - intros j Hj. rewrite Hdomdm. apply elem_of_seq in Hj. apply Hwin_in. lia. }
      iExact "Hmap". }
    iApply (ustep_amoswap_w_u va vpn ie w vpnD ieD rs2 rs1 rd vold ms_v sc_v stval_v sepc_v
              g tlbvec E Φ HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval
              Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hwin Hrestore Hcfg Hcont").
  Qed.

  Lemma wp_user_split_lw_frame
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j
         = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)) ->
    (forall j : nat, (j < 2)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) j
         = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn)) 2 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) ->
    uint rd <> 0 ->
    spec !! vpnD = Some ieD ->
    uw_check_ok (Load Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (Load Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros eaF paD HN Hok Hsome Hchk0 HupdN HcwL HcwH HSXL HMPRV HMXR Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hrd
           HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt #Hcode Hdata Hcfg Hcont".
    iDestruct "Hdata" as (dm) "[%Hdomdm Hfmap]".
    assert (Hindom : forall j : nat, (j < 4)%nat -> is_Some (dm !! pa_add paD j)).
    { intros j Hj. apply elem_of_dom. rewrite Hdomdm. apply Hwin. exact Hj. }
    set (bs := (fun j => default (Z_to_bv 8 0) (dm !! pa_add paD j)) <$> seq 0 4).
    set (v := (Z_to_bv 32 (assemble_bytes bs)) : mword 32).
    assert (Hlen : length bs = 4%nat)
      by (subst bs; rewrite length_fmap length_seq; reflexivity).
    assert (Hcwd : forall j : nat, (j < 4)%nat -> dm !! pa_add paD j = Some (nth_byte v j)).
    { intros j Hj.
      destruct (Hindom j Hj) as [bj Hbj].
      assert (Hbsj : bs !!! j = bj).
      { subst bs.
        assert (Hjl : (j < length (seq 0 4))%nat) by (rewrite length_seq; exact Hj).
        rewrite (list_lookup_total_fmap _ _ j Hjl).
        assert (Hsj : seq 0 4 !!! j = j).
        { apply list_lookup_total_correct.
          pose proof (lookup_seq_lt 0 4 j Hj) as Hls. exact Hls. }
        rewrite Hsj. rewrite Hbj. reflexivity. }
      rewrite Hbj. f_equal. subst v. rewrite (nth_byte_assemble4 bs j Hlen Hj).
      symmetry. exact Hbsj. }
    iApply (ustep_u_split_lw_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
              g dm tlbvec E Φ HN Hok Hsome Hchk0 HupdN HcwL HcwH HSXL HMPRV HMXR Hbit0 Hbit1 Hvalign4
              HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD
              HalignD HcanonD Hvpn_defD HpaalD Hdomdm Hcwd
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hfmap Hcfg Hcont").
  Qed.


End WpUserMemStep.
