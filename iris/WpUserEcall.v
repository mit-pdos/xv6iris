(* WpUserEcall.v -- THE FIRST USER-MODE INSTRUCTION, END TO END.

   [wp_user_ecall]: one whole machine step in USER mode executing ecall
   (0x73), fetched through the Sv39 TLB-hit path from a user page whose
   mapping is NOT the identity, trapping through the delegated
   trap_handler tower, and landing at stvec's direct-mode base -- the
   single kernel re-entry point of the user-execution theorem.

   The step composes every U-mode layer built so far:
     UmodeFetch  : dispatchInterrupt = None, translateAddr TLB hit at an
                   abstract user TLB entry, the 4-byte F_Base fetch;
     UmodeEcall  : the User decode bridge (0x73 -> ECALL) and
                   execute (ECALL) = Trap (User, E_U_EnvCall, pc);
     SmodeCore   : the privilege-generic run_hart_active progress lemma;
     UmodeTrap   : the delegated sync-exception tower (SPP := 0, sepc :=
                   pc, scause := 8, stval := 0, nextPC := stvec base);
     UmodeStep   : the non-retiring try_step engine (no minstret bump,
                   continuation under a later).

   The continuation receives the trapped machine: Supervisor privilege,
   the mstatus trap tower, scause = ecall-from-U, sepc = the user pc,
   pc_is (stvec base) -- plus every config cell handed back.           *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon.
Require Import SmodeCore.
Require Import WpIntrCore.
Require Import UmodeTrap UmodeFetch UmodeStep UmodeEcall.
Local Open Scope Z_scope.
Import Defs.

(* the ecall word *)
Definition ecall_w : mword 32 := mword_of_int 0x73.

(* the trap cause *)
Notation ecall_cause := (rv64d_types.Exception (E_U_EnvCall tt)).

(* the post-trap register values (UmodeTrap's tower, at cause ecall-from-U
   and trapping privilege User) *)
Definition u_ms_e (ms_v : mword 64) (elp_v : mword 1) : mword 64 :=
  update_subrange_vec_dec ms_v 23 23 elp_v.
Definition u_ms_a (ms_v : mword 64) (elp_v : mword 1) : mword 64 :=
  update_subrange_vec_dec (u_ms_e ms_v elp_v) 5 5 (_get_Mstatus_SIE (u_ms_e ms_v elp_v)).
Definition u_ms_b (ms_v : mword 64) (elp_v : mword 1) : mword 64 :=
  update_subrange_vec_dec (u_ms_a ms_v elp_v) 1 1 ('b"0").
Definition u_trap_ms (ms_v : mword 64) (elp_v : mword 1) : mword 64 :=
  update_subrange_vec_dec (u_ms_b ms_v elp_v) 8 8 (spp_bits User).
Definition u_c1 (sc_old : mword 64) : mword 64 :=
  update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
    (bool_to_bit (trapCause_is_interrupt ecall_cause)).
Definition u_trap_cause (sc_old : mword 64) : mword 64 :=
  update_subrange_vec_dec (u_c1 sc_old) (64 - 2) 0
    (zero_extend' (64 - 1) (trapCause_bits_forwards ecall_cause)).

Section WpUserEcall.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma wp_user_ecall
      (ent : TLB_Entry) (vpn : mword 27) (va satp0 : mword 64)
      (ms_v sc_old stval_old sepc_old stvec_v : mword 64)
      (mie_v midl_v mip_v medl_v menvcfg0 : mword 64) (meip seip : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      E (Φ : mval -> iProp Σ) {dq dqc dqt : dfrac} :
    ↑minstretN ⊆ E ->
    (* no interrupt can be pending *)
    and_vec mie_v (not_vec midl_v) = zeros' 64 ->
    and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v midl_v) = zeros' 64 ->
    (* mstatus / satp: Sv39, asid 0 *)
    _get_Mstatus_SXL ms_v = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    (* the user TLB entry: present, matching, U/X/A leaf, A/D preset, PMA *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    (forall (mxr do_sum : bool) s,
       exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
               (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
               (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
         = Some (PTE_Check_Success tt, s)) ->
    update_PTE_Bits (tlb_get_pte 8 ent) (InstructionFetch tt) = (None : option (mword 64)) ->
    (forall s, exec (tlb_get_pbmt ent) s = Some (PBMT_PMA, s)) ->
    match_TLB_Entry ent (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = true ->
    (* va / pa geometry *)
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa ent va vpn)) 4 = true ->
    (* PMP: entry 0 is an executable TOR entry covering all of RAM *)
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (* stvec: direct mode; ecall-from-U delegated *)
    trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct ->
    bit_to_bool (access_vec_dec medl_v
                   (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true ->
    (* decode config *)
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_old -∗
    stval ↦ᵣ stval_old -∗
    sepc ↦ᵣ sepc_old -∗
    stvec ↦ᵣ{ dqc } stvec_v -∗
    mie ↦ᵣ{ dqc } mie_v -∗
    mideleg ↦ᵣ{ dqc } midl_v -∗
    medeleg ↦ᵣ{ dqc } medl_v -∗
    mip ↦ᵣ{ dqc } mip_v -∗
    sig_meip ↦ᵣ{ dqc } meip -∗
    sig_seip ↦ᵣ{ dqc } seip -∗
    satp ↦ᵣ{ dqc } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    menvcfg ↦ᵣ{ dqc } menvcfg0 -∗
    senvcfg ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) -∗
    mstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) -∗
    sstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 32) -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqc } pmpaddr00 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (u_pa ent va vpn) j) ↦ₘ□ nth_byte ecall_w j) -∗
    pc_is va -∗
    ( cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ u_trap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED) -∗
      scause ↦ᵣ u_trap_cause sc_old -∗
      stval ↦ᵣ tval None -∗
      sepc ↦ᵣ va -∗
      stvec ↦ᵣ{ dqc } stvec_v -∗
      mie ↦ᵣ{ dqc } mie_v -∗
      mideleg ↦ᵣ{ dqc } midl_v -∗
      medeleg ↦ᵣ{ dqc } medl_v -∗
      mip ↦ᵣ{ dqc } mip_v -∗
      sig_meip ↦ᵣ{ dqc } meip -∗
      sig_seip ↦ᵣ{ dqc } seip -∗
      satp ↦ᵣ{ dqc } satp0 -∗
      tlb ↦ᵣ{ dqt } tlbvec -∗
      menvcfg ↦ᵣ{ dqc } menvcfg0 -∗
      senvcfg ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) -∗
      mstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) -∗
      sstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 32) -∗
      pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dqc } pmpaddr00 -∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      pc_is (stvec_base stvec_v) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hmm Hs0 HSXL Hsatpmode Hasid Hvec Hchk Hupd Hpbmt Hmatch
           Hval Hcanon Hvpn_def Hpaal HA Hord HX Hcov Htvd Hdel8 Hmenvval.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hscause Hstval Hsepc Hstvec Hmie Hmidl
             Hmedl Hmip Hmeip Hseip Hsatp Htlb Hmenv Hsenv Hmst0 Hsst0 Hpmpc
             Hpmpa #Hbytes Hpc Hcont".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    (* ---- register facts at σ ---- *)
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Hscause") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb") as %Ltlb.
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
    (* ---- the instruction bytes + RAM-ness of the user code page ---- *)
    set (pa := u_pa ent va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte ecall_w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* ---- pure facts: the whole user step at σ ---- *)
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u ent vpn Hchk Hupd Hpbmt Hmatch
                  va satp0 tlbvec σ Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec
                  Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hcov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    assert (HnotRVC : isRVC (subrange_vec_dec ecall_w 15 0) = false)
      by (vm_compute; reflexivity).
    pose proof (exec_fetch_F_Base_4_U_gen va pa ecall_w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; exact Hmenvval).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (decode_ecall_u σ
                  (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* the execute leaf, at σ with nextPC := va+4 *)
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (Lxpriv : register_lookup cur_privilege s_x.(sregs) = User).
    { unfold s_x. lk. exact Lpriv. }
    assert (Lxpc : register_lookup PC s_x.(sregs) = va).
    { unfold s_x. lk. exact Lpc. }
    pose proof (exec_execute_ECALL_U va s_x Lxpriv Lxpc) as Hexec.
    (* run_hart_active: the Trap execution result *)
    assert (Hha : exec (run_hart_active 0) σ
                  = Some (Step_Execute (rv64d_types.Trap (User, ecall_u_exc, va),
                                        zero_extend' 32 ecall_w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x ecall_w (ECALL tt) va
               _ Lpriv Hdisp Hfetch Hdec Hlpad
               ltac:(vm_compute; reflexivity) Lpc Hexec I). }
    (* the dispatch arm: exception_handler + set_next_pc, via the U trap tower *)
    assert (Lxms : register_lookup mstatus s_x.(sregs) = ms_v).
    { unfold s_x. lk. exact Lms. }
    assert (Lxsc : register_lookup scause s_x.(sregs) = sc_old).
    { unfold s_x. lk. exact Lsc. }
    assert (Lxstvec : register_lookup stvec s_x.(sregs) = stvec_v).
    { unfold s_x. lk. exact Lstvec. }
    assert (Lxelp : register_lookup elp s_x.(sregs) = elp0).
    { unfold s_x. lk. exact Lelp. }
    assert (LxmisaS : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true).
    { unfold s_x. lk. rewrite Lmisa. exact HmisaS. }
    assert (Lxmedl : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards
                                (ecall_u_exc.(sync_exception_trap))))) = true).
    { unfold s_x. lk. rewrite Lmedl. exact Hdel8. }
    pose proof (exec_exception_handler_ne_M s_x ecall_cause User va None
                  ms_v sc_old stvec_v elp0
                  (or_introl eq_refl) Lxpriv Lxms Lxsc Lxstvec Lxelp LxmisaS Htvd
                  ecall_u_exc eq_refl eq_refl eq_refl Lxmedl) as Hexch.
    match type of Hexch with _ = Some (_, ?T) => set (s9 := T) in Hexch end.
    assert (Hdispb : exec (try_step_dispatch
                             (Step_Execute (rv64d_types.Trap (User, ecall_u_exc, va),
                                            zero_extend' 32 ecall_w))) s_x
                     = Some (tt, set_reg s9 nextPC (stvec_base stvec_v))).
    { unfold try_step_dispatch. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hexch).
      apply exec_set_next_pc. }
    (* ---- ghost updates: thread the tower through the cells ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (u_ms_e ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (u_ms_e ms_v elp0)
                 (register_set nextPC (add_vec_int va 4) σ.(sregs)))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite Lelp. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _ (u_c1 sc_old) with "Hreg Hscause") as "[Hreg Hscause]".
    iMod (reg_update _ scause _ (u_trap_cause sc_old) with "Hreg Hscause") as "[Hreg Hscause]".
    iMod (reg_update _ mstatus _ (u_ms_a ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (u_ms_b ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (u_trap_ms ms_v elp0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval None) with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (rv64d_types.Trap (User, ecall_u_exc, va), zero_extend' 32 ecall_w)),
            s_x, (set_reg s9 nextPC (stvec_base stvec_v)).
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC (set_reg s9 nextPC (stvec_base stvec_v)).(sregs) = va).
    { unfold s9, s_x. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem".
    { unfold s9, s_x, set_reg; cbn [sregs mem].
      unfold u_trap_ms, u_ms_b, u_ms_a, u_ms_e, u_trap_cause, u_c1.
      iFrame "Hreg Hmem". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC (set_reg s9 nextPC (stvec_base stvec_v)).(sregs)
                  = stvec_base stvec_v).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    rewrite LnT.
    (* elp0 is pinned; fold it back into the tower value *)
    rewrite Help0.
    iApply ("Hcont" with "Hpriv Hms Hscause Hstval Hsepc Hstvec Hmie Hmidl Hmedl
                          Hmip Hmeip Hseip Hsatp Htlb Hmenv Hsenv Hmst0 Hsst0
                          Hpmpc Hpmpa Hhs [$Hpcr $Hnpc]").
  Qed.

End WpUserEcall.
