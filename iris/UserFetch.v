(* UserFetch.v -- the U-mode instruction-fetch layer: exec-level reductions
   of the model's [fetch] over the user page table.

   FAULT side (this file's first installment): a fetch whose pc is odd
   raises E_Fetch_Addr_Align before touching memory; a 4-aligned fetch
   whose translation errs surfaces the exception as [F_Error (e, pc)],
   which [run_hart_active] turns into [Step_Fetch_Failure] -- delivered by
   UserTrap.v's tower.  The 2-aligned (split) fetch variants land together
   with the 2-aligned success machinery.

   All lemmas are state-threading generic where translation can fill the
   TLB; the pure fault paths leave the state untouched.                   *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
From iris.program_logic Require Import language lifting.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 fetch_bytes on a FAILED translation: the exception surfaces.         *)
(* Generic over the chunk width and the translate's output state (a walk   *)
(* that faults leaves the state untouched, but a straddling second chunk   *)
(* runs after the first chunk's TLB fill).                                 *)
(* ===================================================================== *)
Lemma exec_fetch_bytes_fault (width : Z) (fs gs : mword 64) (ex : ExceptionType)
    (s s' : mstate) :
  exec (translateAddr (Virtaddr gs) (InstructionFetch tt)) s
    = Some (Err (ex, tt), s') ->
  exec (fetch_bytes fs gs width) s = Some (FetchBytes_Exception ex, s').
Proof.
  intros Htr.
  unfold fetch_bytes.
  rewrite exec_catch_early_return.
  change (ext_fetch_check_pc fs gs) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ _ _
    (_ : execR (Defs.bind0 (Defs.returnR _ tt)
            (Defs.liftR (translateAddr (Virtaddr gs) (InstructionFetch tt)))) s
         = Some (inr (Err (ex, tt)), s'))).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr.
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite execR_bind. rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The whole [fetch] on the fault paths.                                *)
(* ===================================================================== *)
Section UserFetchFault.
  Context (s : mstate) (pc : mword 64).
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.

  Let HrdPC : exec (Defs.read_reg PC) s = Some (pc, s).
  Proof. rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. Qed.

  (* an ODD pc: E_Fetch_Addr_Align before any translation or memory read
     (with Zca enabled, bit 1 never matters -- only bit 0) *)
  Lemma exec_fetch_align_fault :
    neq_vec (access_vec_dec pc 0) ('b"0") = true ->
    exec (fetch tt) s = Some (F_Error (E_Fetch_Addr_Align tt, pc), s).
  Proof using HpcPC.
    intros Hbit0.
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_returnR_fwd. }
        cbv iota beta. apply execR_returnR_fwd. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* a 4-ALIGNED pc whose translation faults *)
  Lemma exec_fetch_fault_4 (ex : ExceptionType) :
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    exec (translateAddr (Virtaddr pc) (InstructionFetch tt)) s
      = Some (Err (ex, tt), s) ->
    exec (fetch tt) s = Some (F_Error (ex, pc), s).
  Proof using HpcPC.
    intros Hvalign Htr.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
            apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
            apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif.
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_fetch_bytes_fault 4 pc pc ex s s Htr)).
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End UserFetchFault.

(* ===================================================================== *)
(* §3 run_hart_active on a failed fetch (privilege-generic): no decode,    *)
(* no execute; the step result is Step_Fetch_Failure, delivered by the     *)
(* trap tower via try_step's arm ([exec_riscv_step_fetch_failure]).        *)
(* ===================================================================== *)
Lemma exec_run_hart_active_fetch_failure
    (priv : Privilege) (s s_f : mstate) (vaddr : mword 64) (ex : ExceptionType) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Error (ex, vaddr), s_f) ->
  exec (run_hart_active 0) s = Some (Step_Fetch_Failure (Virtaddr vaddr, ex), s_f).
Proof.
  intros Hpriv Hdisp Hfetch.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §4 The Iris FETCH-FAULT arm: a fetch that faults (odd, non-canonical,   *)
(* unmapped, or fetch-denied pc) traps the ACTIVE user hart to stvec,      *)
(* producing [user_trap_frame].  ONE arm, generic over a per-flavor        *)
(* fault-derivation callback (the §2 / UserTranslate §3 facts plug in).    *)
(* ===================================================================== *)
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodePte KptPt SmodeCore.
Require Import UserPt UserExec UserStep UserTrap.

Section UserFetchFaultArm.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  Lemma wp_user_step_fetch_fault E Φ (ex : ExceptionType) (xv : mword 64)
      (ms_v sc_v stval_v sepc_v va : mword 64)
      (g : gmap regidx (mword 64))
      (meip seip : mword 1) {dqe1 dqe2 : dfrac} :
    ↑minstretN ⊆ E ->
    user_mstatus_ok ms_v ->
    user_exc ex = true ->
    u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C) = None ->
    hw_config -∗
    minstret_inv -∗
    sig_meip ↦ᵣ{ dqe1 } meip -∗
    sig_seip ↦ᵣ{ dqe2 } seip -∗
    user_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
    upt_inv pt -∗
    user_cfg C -∗
    (* the flavor plug: at any machine state satisfying the pins, the fetch
       faults with cause [ex] at faulting address [xv], state unchanged *)
    (∀ (σ : mstate) (usatp : mword 64) (tlbvec : type_of_register tlb),
       ⌜register_lookup cur_privilege σ.(sregs) = User⌝ -∗
       ⌜register_lookup mstatus σ.(sregs) = ms_v⌝ -∗
       ⌜register_lookup PC σ.(sregs) = va⌝ -∗
       ⌜register_lookup satp σ.(sregs) = usatp⌝ -∗
       ⌜upt_satp_ok pt usatp⌝ -∗
       ⌜register_lookup tlb σ.(sregs) = tlbvec⌝ -∗
       ⌜upt_tlb_ok pt.(u_map) tlbvec⌝ -∗
       ⌜pmpAddrMatchType_encdec_backwards
          (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR⌝ -∗
       ⌜zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false⌝ -∗
       ⌜eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true⌝ -∗
       ⌜(ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z⌝ -∗
       ⌜forall regions, pma_allows_all regions -> pma_allows_pte_read regions⌝ -∗
       hw_config -∗
       mstate_interp σ -∗
       upt_slots_own pt.(u_slots) -∗
       ⌜exec (fetch tt) σ = Some (F_Error (ex, xv), σ)⌝) -∗
    ▷ (sig_meip ↦ᵣ{ dqe1 } meip -∗ sig_seip ↦ᵣ{ dqe2 } seip -∗
       user_trap_frame C pt -∗
       WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmsok Hexc Hd) "#Hhw #Hminstret Hmeip Hseip Hregs Hupt Hcfg Hfd Hcont".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc &
                           Hpc & Hnpc & Hgpr)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iDestruct "Hupt" as (usatp tlbvec)
      "(Hsatp & %Hsatpok & Htlb & %Htlbok & Hslots & Hdata & Hpmp & %Hwf)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA & %Hord & %Hpter & %HpmpX & %HpmpW & %HpmpR & %Hcov)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ &
        %Help_ne & _)".
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hminstret").
    iIntros (σ) "[Hreg Hmd] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmedl") as %Lmedl.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    (* every pin transports σ -> s_a (minstret_increment is none of them) *)
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r σ.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r s_a.(sregs) = v).
    { intros r v Hv Hne. unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    (* the fetch fault at s_a, via the flavor plug *)
    assert (HA_a : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s_a.(sregs)) 0)) = TOR)
      by (rewrite (T _ _ Lpmpc eq_refl); exact HA).
    assert (Hord_a : zopz0zKzJ_u (zeros' 64)
              (vec_access_dec (register_lookup pmpaddr_n s_a.(sregs)) 0) = false)
      by (rewrite (T _ _ Lpmpa eq_refl); exact Hord).
    assert (HpmpR_a : eq_vec (_get_Pmpcfg_ent_R
              (vec_access_dec (register_lookup pmpcfg_n s_a.(sregs)) 0)) ('b"1") = true)
      by (rewrite (T _ _ Lpmpc eq_refl); exact HpmpR).
    assert (Hcov_a : (ram_base + ram_size
              <= uint (vec_access_dec (register_lookup pmpaddr_n s_a.(sregs)) 0) * 4)%Z)
      by (rewrite (T _ _ Lpmpa eq_refl); exact Hcov).
    iDestruct ("Hfd" $! s_a usatp tlbvec
                 (T _ _ Lpriv eq_refl) (T _ _ Lms eq_refl) (T _ _ Lpc eq_refl)
                 (T _ _ Lsatp eq_refl) Hsatpok (T _ _ Ltlb eq_refl) Htlbok
                 HA_a Hord_a HpmpR_a Hcov_a
                 Hpter
                 with "Hhw [Hreg Hmd] Hslots") as %Hfetch.
    { unfold s_a, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmd". }
    (* dispatch is None at s_a *)
    assert (HES_a : exec (currentlyEnabled Ext_S) s_a = Some (true, s_a)).
    { rewrite exec_currentlyEnabled_S.
      rewrite (T _ _ Lmisa eq_refl). rewrite HmisaS. reflexivity. }
    assert (HmisaS_a : eq_vec (_get_Misa_S (register_lookup misa s_a.(sregs))) ('b"1") = true)
      by (rewrite (T _ _ Lmisa eq_refl); exact HmisaS).
    assert (Hmedl_a : bit_to_bool (access_vec_dec (register_lookup medeleg s_a.(sregs))
              (uint (exceptionType_bits_forwards ex))) = true)
      by (rewrite (T _ _ Lmedl eq_refl); exact (uc_del C ex Hexc)).
    assert (Hdisp : exec (dispatchInterrupt User) s_a = Some (None, s_a)).
    { rewrite (exec_dispatchInterrupt_U_reduce s_a (uc_mip C) (uc_mie C)
                 (uc_mideleg C) meip seip
                 HES_a
                 (T _ _ Lmip eq_refl) (T _ _ Lmeip eq_refl) (T _ _ Lseip eq_refl)
                 (T _ _ Lmie eq_refl) (T _ _ Lmdl eq_refl) (uc_mm C)).
      rewrite Hd. reflexivity. }
    pose proof (exec_run_hart_active_fetch_failure User s_a s_a xv ex
                  (T _ _ Lpriv eq_refl) Hdisp Hfetch) as Hha.
    (* the delivered trap at s_a *)
    pose proof (exec_handle_exception_U s_a (rv64d_types.Exception ex)
                  (xtval_exception_value ex xv) va ms_v sc_v (uc_stvec C) elp0
                  (T _ _ Lpriv eq_refl) (T _ _ Lms eq_refl) (T _ _ Lsc eq_refl)
                  (T _ _ Lstvec eq_refl) (T _ _ Lelp eq_refl)
                  HmisaS_a (uc_tvd C)
                  (T _ _ Lpc eq_refl)
                  ex xv eq_refl eq_refl
                  Hmedl_a)
      as Hhe.
    set (s_trap := set_reg _ nextPC (stvec_base (uc_stvec C))) in Hhe.
    assert (Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt)
      by (exact (T _ _ Lhs eq_refl)).
    assert (Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt).
    { unfold s_trap, s_a, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact Lhs. }
    pose proof (exec_riscv_step_fetch_failure σ s_a s_trap xv ex b
                  Hsi Hhart_a Hha Hhe Hhart_trap) as Hstep.
    assert (Hnpc_trap : register_lookup nextPC s_trap.(sregs)
                          = stvec_base (uc_stvec C)).
    { unfold s_trap, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Hnpc_trap in Hstep.
    (* ghost updates, mirroring the physical writes *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp Help0. reflexivity. }
    iMod (reg_update _ scause _ _ with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ _ with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ _ with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ _ with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms elp0 ms_v) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval (xtval_exception_value ex xv))
            with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base (uc_stvec C)) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro.
    iExists _.
    iSplitR. { iPureIntro. exact Hstep. }
    iNext. iModIntro.
    unfold s_trap, s_a, set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
    iApply ("Hcont" with "Hmeip Hseip").
    (* re-assemble the trap frame *)
    iExists (utrap_ms elp0 ms_v), _, (tval (xtval_exception_value ex xv)), va, g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr".
    iSplitR.
    { iPureIntro.
      destruct Hmsok as (HSXL & HMPRV & HMXR).
      split; [ rewrite utrap_ms_SXL; exact HSXL | ].
      split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
      split; [ rewrite utrap_ms_MXR; exact HMXR | ].
      split; [ rewrite utrap_ms_SPP; reflexivity | ].
      rewrite utrap_ms_SIE; reflexivity. }
    iSplitL "Hpc Hnpc". { iFrame "Hpc Hnpc". }
    iSplitL "Hsatp Htlb Hslots Hdata Hpmpc Hpmpa".
    { iExists usatp, tlbvec.
      iFrame "Hsatp Htlb Hslots Hdata".
      iSplitR. { iPureIntro. exact Hsatpok. }
      iSplitR. { iPureIntro. exact Htlbok. }
      iSplitL. { iExists pmpcfg0, pmpaddr00. iFrame "Hpmpc Hpmpa". iPureIntro. tauto. }
      iPureIntro. exact Hwf. }
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

End UserFetchFaultArm.
