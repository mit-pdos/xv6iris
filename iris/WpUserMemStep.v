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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv UmodeData WpGprStore.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase WpUserMem.

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

(* ---------------------------------------------------------------------- *)
(* (3) Dispatcher-facing memory steps: consume [user_data] whole and       *)
(*     derive the loaded value internally, so the caller supplies only the  *)
(*     translation facts + a window-in-[data] premise (no value/bytes).     *)
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
End WpUserMemStep.
