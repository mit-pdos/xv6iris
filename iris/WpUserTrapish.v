(* WpUserTrapish.v -- trapish combined-fetch engine for U-mode sync-trap
   arms (option B).  [wp_exec_trapish_hit] does the fetch (TLB hit) + the
   generic U-mode sync-trap-delivery tower, and hands the fault body a
   callback: given the post-fetch state s_x (nextPC ticked, tlb = the
   fetch-filled tlbvec_f), provide the execute -> Trap fact + the trap
   cause/xtval + the delegation, and the engine delivers user_trap_frame.
   Mirrors the retiring [wp_instr_u_data] (WpUserComputeMiss.v).           *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
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
Require Import WpPushOffMem MemData4 UmodeData4 MemAmo4 UmodeAmo4.
Require Import RiscvTryStep UmodeLrsc UmodeLrscWalk.
Require Import WpLeafCommon UmodeTrap UmodeStep UmodeFetchFault.
Require Import UmodeWalk WpUserComputeMiss.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserTrapish.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation mie_v := (WpUserBase.mie_v U).
  Local Notation midl_v := (WpUserBase.midl_v U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation mip_v := (WpUserBase.mip_v U).
  Local Notation meip := (WpUserBase.meip U).
  Local Notation seip := (WpUserBase.seip U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation dqc := (WpUserBase.dqc U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation Htvd := (WpUserBase.Htvd U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).

  (* The trapish fetch-HIT engine.  Fetch is a TLB hit; the callback [K]
     supplies the execute->Trap fact at the post-fetch state, the trap
     cause [tc] + xtval [xv], and the medeleg delegation for [tc]. *)
  Lemma wp_exec_trapish_hit
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
    (* the fault-body callback K, at the post-fetch state s_x *)
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hnlp : is_lpad_instruction ii = false) by exact Hnlpad.
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* the fetch-hit collapses the fill back to tlbvec *)
    assert (Hfill_id : vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                         (Some (upt_entry vpn ie)) = tlbvec).
    { apply vec64_update_same; [ pose proof (tlb_hash_range vpn); lia | exact Hvec ]. }
    (* s_x register facts *)
    assert (LpcX : register_lookup PC s_x.(sregs) = va) by (unfold s_x; lk; exact Lpc).
    assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
      by (unfold s_x; lk; reflexivity).
    assert (LprivX : register_lookup cur_privilege s_x.(sregs) = User) by (unfold s_x; lk; exact Lpriv).
    assert (LmsX : register_lookup mstatus s_x.(sregs) = ms_v) by (unfold s_x; lk; exact Lms).
    assert (LsatpX : register_lookup satp s_x.(sregs) = satp0) by (unfold s_x; lk; exact Lsatp).
    assert (LpmpcX : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0) by (unfold s_x; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00) by (unfold s_x; lk; exact Lpmpa).
    assert (LtlbX : register_lookup tlb s_x.(sregs) = tlbvec) by (unfold s_x; lk; exact Ltlb).
    assert (HagX : agree_on D_u s_x dstateU).
    { unfold s_x.
      exact (agree_u_set_nextPC σ (add_vec_int va 4)
               (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')). }
    (* --- invoke the fault-body callback at s_x --- *)
    rewrite <- Hfill_id in LtlbX.
    iMod ("K" $! s_x LpcX LnpcX LprivX LmsX LsatpX LpmpcX LpmpaX HagX LtlbX
            with "[Htlbc] Hupt Hgpr [Hreg Hmem Hdev]")
      as (tc xv s' tlbvecD) "(%Hexec & %Hdel & %LpcS & %LtlbS & %HokD & Hσ' & Htlbc & Hupt & Hgpr)".
    { rewrite Hfill_id. iExact "Htlbc". }
    { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct "Hσ'" as "[Hreg [Hmem Hdev]]".
    (* --- run_hart_active: fetch (engine) + execute-Trap (callback) --- *)
    set (resf := rv64d_types.Trap (User, make_sync_exception tc xv, va)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (resf, zero_extend' 32 w), s')).
    { apply (exec_hart_active_progress_base_gen User σ σ s' w ii va resf
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlp Lpc).
      - unfold resf. exact Hexec.
      - exact I. }
    (* --- s' CSR facts via reg_valid against the returned interp --- *)
    iDestruct (reg_valid with "Hreg Hpriv") as %LprivX'.
    iDestruct (reg_valid with "Hreg Hms") as %LmsX'.
    iDestruct (reg_valid with "Hreg Hsc") as %LscX'.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %LstvecX'.
    iDestruct (reg_valid_dq with "Hreg Help") as %LelpX'.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %LmisaX'.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %LmedlX'.
    assert (LmisaSX' : eq_vec (_get_Misa_S (register_lookup misa s'.(sregs))) ('b"1") = true)
      by (rewrite LmisaX'; exact HmisaS).
    assert (LmedlX'' : bit_to_bool (access_vec_dec (register_lookup medeleg s'.(sregs))
                       (uint (exceptionType_bits_forwards tc))) = true)
      by (rewrite LmedlX'; exact Hdel).
    (* --- the Trap arm of try_step_dispatch, at s' --- *)
    pose proof (exec_exception_handler_ne_M s' (rv64d_types.Exception tc) User va
                  (xtval_exception_value tc xv)
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX' LmsX' LscX' LstvecX' LelpX' LmisaSX' Htvd
                  (make_sync_exception tc xv)
                  eq_refl eq_refl eq_refl LmedlX'') as Hehe.
    match type of Hehe with _ = Some (_, ?T) => set (s9x := T) in Hehe end.
    set (s_trap := set_reg s9x nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch (Step_Execute (resf, zero_extend' 32 w))) s'
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch, resf. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hehe).
      unfold s_trap. apply exec_set_next_pc. }
    (* --- ghost trap-CSR tower (tlb already filled by the callback) --- *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s'.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpX'. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception tc))))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception tc) sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value tc xv))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (resf, zero_extend' 32 w)), s', s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s9x. lk. exact LpcS. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. unfold s_trap, s9x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause (rv64d_types.Exception tc) sc_v),
            (tval (xtval_exception_value tc xv)),
            va, g, tlbvecD.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact HokD |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

  Lemma wp_exec_trapish_miss
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent', vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' /\
        match_TLB_Entry ent' (mword_of_int 0 : mword 16)
          (sign_extend' (57 - 12) vpn) = false)) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
    (* the fault-body callback K, at the post-fetch state s_x *)
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hmiss Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hnlpad.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    assert (Hnlp : is_lpad_instruction ii = false) by exact Hnlpad.
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid with "Hreg Htlbc") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    destruct (Hspec vpn ie Hsome) as (HFsl2 & HFsl1 & HFsl0 & HFwf).
    destruct HFwf as (HF2i & HF2nl & HF1i & HF1nl & HF0i & HF0nl & HF0N & HFglob & HFpbmt0).
    assert (HAf : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hordf : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HRf : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcovf : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    iDestruct (upt_walk_read_ptes root slots spec vpn ie σ Hsome
                 HAf Hordf HRf Hcovf Hpter with "Hhw [$Hreg $Hmem $Hdev] Hupt")
      as %(HFrd2 & HFrd1 & HFrd0 & _).
    set (pa := u_walk_pa (uw_pte0 ie) va) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    set (tlbvec' := vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    set (σ' := set_reg σ tlb tlbvec').
    assert (Htr : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
                    = Some (Ok (Physaddr (u_walk_pa (uw_pte0 ie) va), PBMT_PMA, init_ext_ptw), σ')).
    { destruct Hmiss as [Hvec | (ent' & Hvec & Hnm)].
      - exact (exec_translateAddr_fetch_walk_u vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 HF2i HF2nl HF1i HF1nl HF0i HF0nl (fun s0 => Hchk0 false false s0) HF0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec HupdN
                 HFrd2 HFrd1 HFrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def).
      - exact (exec_translateAddr_fetch_walk_u_nomatch ent' vpn root
                 (uw_pte2 ie) (uw_pte1 ie) (uw_pte0 ie) false false va satp0
                 MENVCFG_S tlbvec σ
                 HF2i HF2nl HF1i HF1nl HF0i HF0nl (fun s0 => Hchk0 false false s0) HF0N
                 Lmisa' Lpriv HSXL' Lsatp Hsatpmode Hasid Hroot Ltlb Hvec Hnm HupdN
                 HFrd2 HFrd1 HFrd0 Lmenv' ltac:(vm_compute; reflexivity)
                 Hcanon Hvpn_def). }
    assert (LpmpcS : register_lookup pmpcfg_n σ'.(sregs) = pmpcfg0) by (unfold σ'; lk; exact Lpmpc).
    assert (LpmpaS : register_lookup pmpaddr_n σ'.(sregs) = pmpaddr00) by (unfold σ'; lk; exact Lpmpa).
    assert (LpmaS : register_lookup pma_regions σ'.(sregs) = pmar0) by (unfold σ'; lk; exact Lpma).
    assert (LhtifS : register_lookup htif_tohost_base σ'.(sregs) = None) by (unfold σ'; lk; exact Lhtif).
    assert (LprivS : register_lookup cur_privilege σ'.(sregs) = User) by (unfold σ'; lk; exact Lpriv).
    assert (LelpS : register_lookup elp σ'.(sregs) = elp0) by (unfold σ'; lk; exact Lelp).
    assert (LpcSf : register_lookup PC σ'.(sregs) = va) by (unfold σ'; lk; exact Lpc).
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite LpmpaS.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ' region
                  Lpc Hval Htr
                  ltac:(rewrite LpmpcS; exact HpmpA)
                  ltac:(rewrite LpmpaS; exact Hpmp_ord)
                  Hrange'
                  ltac:(rewrite LpmpcS; exact HpmpX)
                  ltac:(rewrite LpmaS; exact Hpmam)
                  Hpaal Hpmax
                  (within_clint_false pa 4 σ' Hnc ltac:(lia))
                  (within_sig_false pa 4 σ' Hns ltac:(lia))
                  (within_htif_false pa 4 σ' LhtifS)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf LprivS HnotRVC) as Hfetch.
    pose proof (agree_u_set_tlb σ tlbvec'
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as HagXf.
    pose proof (Hdec σ' HagXf) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ'.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite LelpS; exact Help_np).
    set (s_x := set_reg σ' nextPC (add_vec_int va 4)).
    iMod (reg_update _ tlb _ tlbvec' with "Hreg Htlbc") as "[Hreg Htlbc]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    (* s_x register facts (s_x = set_reg σ' nextPC ...) *)
    assert (LpcX : register_lookup PC s_x.(sregs) = va) by (unfold s_x, σ'; lk; exact Lpc).
    assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
      by (unfold s_x; lk; reflexivity).
    assert (LprivX : register_lookup cur_privilege s_x.(sregs) = User) by (unfold s_x, σ'; lk; exact Lpriv).
    assert (LmsX : register_lookup mstatus s_x.(sregs) = ms_v) by (unfold s_x, σ'; lk; exact Lms).
    assert (LsatpX : register_lookup satp s_x.(sregs) = satp0) by (unfold s_x, σ'; lk; exact Lsatp).
    assert (LpmpcX : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0) by (unfold s_x, σ'; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00) by (unfold s_x, σ'; lk; exact Lpmpa).
    assert (LtlbX : register_lookup tlb s_x.(sregs)
                    = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))).
    { unfold s_x, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      unfold σ', set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (HagX : agree_on D_u s_x dstateU).
    { unfold s_x. exact (agree_u_set_nextPC σ' (add_vec_int va 4) HagXf). }
    (* --- invoke the fault-body callback at s_x --- *)
    iMod ("K" $! s_x LpcX LnpcX LprivX LmsX LsatpX LpmpcX LpmpaX HagX LtlbX
            with "Htlbc Hupt Hgpr [Hreg Hmem Hdev]")
      as (tc xv s' tlbvecD) "(%Hexec & %Hdel & %LpcS & %LtlbS & %HokD & Hσ' & Htlbc & Hupt & Hgpr)".
    { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
    iDestruct "Hσ'" as "[Hreg [Hmem Hdev]]".
    (* --- run_hart_active: fetch (engine) + execute-Trap (callback) --- *)
    set (resf := rv64d_types.Trap (User, make_sync_exception tc xv, va)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (resf, zero_extend' 32 w), s')).
    { apply (exec_hart_active_progress_base_gen User σ σ' s' w ii va resf
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlp LpcSf).
      - unfold resf. exact Hexec.
      - exact I. }
    (* --- s' CSR facts via reg_valid against the returned interp --- *)
    iDestruct (reg_valid with "Hreg Hpriv") as %LprivX'.
    iDestruct (reg_valid with "Hreg Hms") as %LmsX'.
    iDestruct (reg_valid with "Hreg Hsc") as %LscX'.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %LstvecX'.
    iDestruct (reg_valid_dq with "Hreg Help") as %LelpX'.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %LmisaX'.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %LmedlX'.
    assert (LmisaSX' : eq_vec (_get_Misa_S (register_lookup misa s'.(sregs))) ('b"1") = true)
      by (rewrite LmisaX'; exact HmisaS).
    assert (LmedlX'' : bit_to_bool (access_vec_dec (register_lookup medeleg s'.(sregs))
                       (uint (exceptionType_bits_forwards tc))) = true)
      by (rewrite LmedlX'; exact Hdel).
    (* --- the Trap arm of try_step_dispatch, at s' --- *)
    pose proof (exec_exception_handler_ne_M s' (rv64d_types.Exception tc) User va
                  (xtval_exception_value tc xv)
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX' LmsX' LscX' LstvecX' LelpX' LmisaSX' Htvd
                  (make_sync_exception tc xv)
                  eq_refl eq_refl eq_refl LmedlX'') as Hehe.
    match type of Hehe with _ = Some (_, ?T) => set (s9x := T) in Hehe end.
    set (s_trap := set_reg s9x nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch (Step_Execute (resf, zero_extend' 32 w))) s'
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch, resf. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hehe).
      unfold s_trap. apply exec_set_next_pc. }
    (* --- ghost trap-CSR tower (tlb already filled by the callback) --- *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s'.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpX'. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception tc))))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception tc) sc_v)
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
               (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0)))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _
            (update_subrange_vec_dec
               (update_subrange_vec_dec (update_subrange_vec_dec ms_v 23 23 elp0) 5 5
                  (_get_Mstatus_SIE (update_subrange_vec_dec ms_v 23 23 elp0))) 1 1 ('b"0"))
            with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _
            (tval (xtval_exception_value tc xv))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (resf, zero_extend' 32 w)), s', s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s9x. lk. exact LpcS. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { rewrite /mstate_interp. unfold s_trap, s9x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause (rv64d_types.Exception tc) sc_v),
            (tval (xtval_exception_value tc xv)),
            va, g, tlbvecD.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact HokD |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  (* Combined trapish fetch engine: dispatch on the TLB slot. *)
  Lemma wp_exec_trapish_u
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ii : instruction) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    spec !! vpn = Some ie ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (ii, s0)) ->
    is_lpad_instruction ii = false ->
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
    (* the fault-body callback K, at the post-fetch state s_x *)
    (∀ (s_x : mstate)
       (Hpc : register_lookup PC s_x.(sregs) = va)
       (Hnpc : register_lookup nextPC s_x.(sregs) = add_vec_int va 4)
       (Hpr : register_lookup cur_privilege s_x.(sregs) = User)
       (Hms : register_lookup mstatus s_x.(sregs) = ms_v)
       (Hsatp : register_lookup satp s_x.(sregs) = satp0)
       (Hpmpc : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
       (Hpmpa : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
       (Hag : agree_on D_u s_x dstateU)
       (Htl : register_lookup tlb s_x.(sregs)
              = vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))),
       tlb ↦ᵣ (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (upt_entry vpn ie))) -∗
       upt_inv root slots spec -∗
       gpr_file g -∗
       mstate_interp s_x ={E ∖ ↑minstretN}=∗
       ∃ (tc : ExceptionType) (xv : mword 64) (s' : mstate)
         (tlbvecD : vec (option TLB_Entry) (2 ^ 6)),
         ⌜ exec (execute ii) s_x
             = Some (rv64d_types.Trap (User, make_sync_exception tc xv, va), s') ⌝ ∗
         ⌜ bit_to_bool (access_vec_dec medl_v
              (uint (exceptionType_bits_forwards tc))) = true ⌝ ∗
         ⌜ register_lookup PC s'.(sregs) = va ⌝ ∗
         ⌜ register_lookup tlb s'.(sregs) = tlbvecD ⌝ ∗
         ⌜ upt_tlb_ok spec tlbvecD ⌝ ∗
         mstate_interp s' ∗
         tlb ↦ᵣ tlbvecD ∗
         upt_inv root slots spec ∗
         gpr_file g) -∗
    ▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec Hnlpad.
    assert (Hcw' : forall j : nat, (j < 4)%nat ->
              code !! pa_add (u_walk_pa (uw_pte0 ie) va) j = Some (nth_byte w j)).
    { intros j Hj. rewrite <- (u_pa_upt_entry_walk vpn ie va). exact (Hcw j Hj). }
    assert (Hpaal' : is_aligned_paddr (Physaddr (u_walk_pa (uw_pte0 ie) va)) 4 = true).
    { rewrite <- (u_pa_upt_entry_walk vpn ie va). exact Hpaal. }
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg K Hcont".
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hvacc.
    - destruct (match_TLB_Entry ent (mword_of_int 0 : mword 16)
                  (sign_extend' (57 - 12) vpn)) eqn:Hmatch.
      + destruct (Hok vpn ent Hvacc) as (vpn'' & i & Hspec'' & _ & Hent).
        subst ent.
        pose proof (upt_entry_match_inj vpn'' vpn i Hmatch) as Hvv. subst vpn''.
        rewrite Hsome in Hspec''. inversion Hspec''. subst i.
        iApply (wp_exec_trapish_hit va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hvacc Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
                  HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg K Hcont").
      + iApply (wp_exec_trapish_miss va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome (or_intror (ex_intro _ ent (conj Hvacc Hmatch)))
                  Hchk0 HupdN Hpbmt0 Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                        Hcode Hdata Hcfg K Hcont").
    - iApply (wp_exec_trapish_miss va vpn ie w ii ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hsome (or_introl Hvacc)
                Hchk0 HupdN Hpbmt0 Hcw' HSXL Hval Hcanon Hvpn_def Hpaal' HnotRVC Hdec Hnlpad
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg K Hcont").
  Qed.

End WpUserTrapish.

