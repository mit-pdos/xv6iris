(* WpSmodeIntr.v -- the SIE=1 instruction step engine (stage 1 of the
   SIE-agnostic sweep) and the SIE-AGNOSTIC funnel engines over
   [sconf] + [sie_cap] (stages 3-4).

   LAYER 1 [wp_instr_s_intr]: the interrupts-ENABLED mirror of
   [wp_instr_s_tlbinv_pt] (SmodeCorePt.v) -- the same per-instruction
   σ-callback shape, rebased on the interrupt-absorbing step engine
   [wp_exec_step_intr] (WpIntrInv.v).  "No interrupt dispatched" is
   discharged from the PURE fact the absorbing engine hands its
   callback -- an arbitrary number of pending interrupts has already
   been taken and fully handled (trap + handler + sret round trips)
   before the callback runs -- NOT from SIE=0.  Differences forced by
   the absorbing step rule: the config travels as the ONE bundle
   [intr_config] (no ghost argument -- the SIE ghost is the hart's
   canonical [sie_gname]); the caller threads [gpr_file m] and the
   per-trap frame [intr_frame] (each interrupt consumes and
   re-establishes them); the interrupted pc must be a legal sret
   target; the callback receives the nextPC cell explicitly (the whole [pc_is pc] is
   threaded through the absorbing engine; the PC half stays here for
   the retire obligation); and this engine assembles the full
   [run_hart_active] retire witness itself (via
   [exec_hart_active_progress_base_gen]/[_RVC_gen] at Supervisor),
   driving the unified [tlb_inv_pt_fetch] with tlb_inv_pt / menvcfg
   borrowed from [intr_frame].

   LAYER 2 [wp_instr_s_sconf]: THE SIE-AGNOSTIC FUNNEL.  Takes the v2
   bundle [sconf] + the capability [sie_cap m n b] (IntrDefs.v) and
   cases on the capability's SIE INDEX [b] -- the arm is an index, not
   an internal disjunction, so a caller can say which one it is in; at
   the '0' arm ghost agreement between the bundle's tied half and the
   capability's eighth then pins the live SIE bit, replacing every pure
   SIE premise:
     - [b = false]: today's dispatch-None body -- delegates to
       [wp_instr_s_config_regime] with SIE=0 derived from the ghost;
     - [b = true]: delegates to [wp_instr_s_intr], assembling
       [intr_config]/[intr_frame] from the bundle + capability via
       [intr_config_of_v2] and disassembling them back around the
       σ-callback; the sret-target premise is DERIVED from
       [instr_bytes]' 2-alignment ([update_bit0_zero_of_aligned2]), so
       no call site carries it.
   Both arms present the SAME σf-callback, so everything above is
   SIE-blind; the perf-hot σ-level fetch drive is not duplicated (each
   arm reuses its engine's existing one).  The bundle owns
   [gpr_file (tp_pin m)] (HartTp.v), so the two engines below it are fed
   [tp_pin m] as THEIR map; [sie_cap] / [intr_frame] stay stated at [m]
   (they depend on it only through sp, which the pin does not move).

   On top: the agnostic gpr-write engines [wp_gpr_write_s_sconf]
   (premise [ops_ok b rd rsa rsb], which occupies the slot the old
   [rd <> csp_rs1] did: its [rd_ok] conjunct says [sie_cap] is keyed on sp
   and transported by [sie_cap_retarget] -- sp-moving instructions re-carve
   their stack explicitly -- and that tp is pinned to the hart; its two
   [src_ok] conjuncts guard the READS, see IntrDefs.v), and the pilot leaf
   [wp_cli_s_sconf] (which reads x0 only, so it keeps plain [rd_ok rd] and
   builds the engine's premise with [ops_ok_conc]).  All three hand their
   continuation back through [wp_next b] -- with interrupts enabled the
   instruction can be trapped and the thread resumed on a DIFFERENT hart,
   and the rebound [CID] binder makes every resource in the continuation
   about that hart.  That rebinding is also why the READ side of [ops_ok]
   exists: see §3.  *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpNext WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodeCore SmodeCorePt.
Require Import AlignBits.
Require Import IntrDefs WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSmodeIntr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* =================================================================== *)
  (* §1 THE STEP ENGINE at SIE=1, over the FOLDED BUNDLE.  Everything it   *)
  (* used to take piecewise ([intr_res], [intr_config], [gpr_file],        *)
  (* [intr_frame]) is inside [sie_cap_gpr] now, and the σ-callback it hands *)
  (* on is the funnel's own -- which is why §2's '1' arm is three lines.    *)
  (*                                                                      *)
  (* THE CALLBACK IS HART-GENERIC, inherited from                          *)
  (* [WpIntrInv.wp_exec_step_intr]: the absorbing loop can park the thread, *)
  (* so the instruction executes on the hart the last trap returned to.    *)
  (* The proof therefore does the standard rename -- the STATEMENT never    *)
  (* sees it, so callers that name this lemma's hart keep working -- and    *)
  (* everything after it means the REBOUND hart by instance resolution.     *)
  (* =================================================================== *)
  Lemma wp_instr_s_intr (m : regfile) (n : nat)
      (pc : mword 64) (is_rvc : bool) (i : instruction) :
    ret_pc pc = pc ->
    sie_cap_gpr kt m n true p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    wp_next true p (fun (CID : CpuId) =>
      ∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       sconf -∗
       sie_cap kt m n true p -∗
       gpr_file (tp_pin m) -∗
       nextPC ↦ᵣ pc -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpc0) "Hcg Hpc Hinstr H".
    iApply (wp_exec_step_intr pc m n p Hpc0 with "Hcg Hpc").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       which the STATEMENT never sees.  It has to come AFTER any same-section
       application (there is none here) and before the [iIntros] that binds
       the engine's hart. *)
    rename CID into CID0.
    iIntros (CID Hs σ) "%Hdisp Hsc Hcap Hfile Hpc Hsi".
    (* the caller's obligation is anchored at the entry hart; [Hs] is the
       guard that moves it to the one we are on. *)
    iDestruct (wp_next_at true p _ CID Hs with "H") as "H".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    (* unbundle for the σ-level fetch lookups *)
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Htie & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    subst menvcfg0.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    (* the translation slot: SIE = '1' forces the KPT arm *)
    iDestruct (sie_cap_on_kpt with "Hcap") as (root_ppn) "(Hstk & Hbit1 & Htlbinv & Harm & #Hwit)".
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpcr")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by exact Lmenv0.
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    (* the unified fetch through the tree invariant (may write A/D back) *)
    unshelve iMod (tlb_inv_pt_fetch (CID := CID) root_ppn σ pc r _ _
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)"; [solve_ndisj |].
    (* decode agreement + its side conditions, at σf *)
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid    with "Hreg Hmenv")  as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | exact Hmenv_σf ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    assert (Hlpad : eq_vec (register_lookup elp σf.(sregs))
                           (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Help_σf; exact Help_np).
    (* rebundle config + capability; run the caller's execute at σf *)
    iMod ("H" $! σf Lpc_σf
            with "[Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv]
                  [Hstk Hbit1 Htlbinv Harm] Hfile Hnpc [$Hreg $Hmem]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    { rewrite /sconf. iFrame "Hhw Hminv Hpriv".
      iSplitL "Hms Hhalf Htie".
      { iExists ms. iFrame "Hms Hhalf Htie". iPureIntro. exact Hmsf. }
      iSplitL "Hmie Hmdl".
      { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
      iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
      repeat split; try assumption; reflexivity. }
    { rewrite /sie_cap. iFrame "Hstk Harm Hwit".
      iApply (strans_inv_intro (CID := CID) root_ppn with "Hbit1 Htlbinv"). }
    iDestruct (reg_valid with "Hreg' Hpcr") as %Lpc_exec.
    rewrite Lpc_σf in Hexec.
    (* assemble the run_hart_active retire witness *)
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w : direct decode, single execute *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (zero_extend' 32 w), s_exec.
      iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_base_gen Supervisor σ σf s_exec w i
                 pc RETIRE_SUCCESS
                 Lpriv Hdisp Hfetcheq Hdec0 Hlpad Hnlpad Lpc_σf Hexec I). }
      rewrite Lpc_exec. iFrame "Hpcr Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h : indirect decode, ExecuteAs redispatch *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      assert (Hzca : exec (currentlyEnabled Ext_Zca) σf = Some (true, σf))
        by (apply exec_currentlyEnabled_Zca; rewrite Hmisa_σf; exact HmisaC).
      iModIntro. iExists (zero_extend' 32 h), s_exec.
      iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_RVC_gen Supervisor σ σf s_exec h i0 i
                 pc RETIRE_SUCCESS
                 Lpriv Hdisp Hfetcheq Hdec Hlpad Lpc_σf Hzca
                 (Hexp (set_reg σf nextPC (add_vec_int pc 2))) Hexec). }
      rewrite Lpc_exec. iFrame "Hpcr Hreg' Hmem'". iExact "Hcont".
  Qed.

  (* =================================================================== *)
  (* §2 THE SIE-AGNOSTIC FUNNEL over [sconf] + [sie_cap]: the capability's *)
  (* SIE INDEX [b] picks the arm (ghost agreement with the bundle's tied   *)
  (* half then pins the live bit at the '0' arm); both arms present the    *)
  (* same σf-callback.                                                    *)
  (* =================================================================== *)
  Lemma wp_instr_s_sconf
      (m : regfile) (n : nat) (b : bool)
      (pc : mword 64) (is_rvc : bool) (i : instruction) :
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc is_rvc i -∗
    (* THE σ-CALLBACK IS HART-GENERIC: after the absorbing engine has run, the
       instruction executes on the hart the LAST trap returned to, so a leaf
       must supply this callback at an ARBITRARY hart, with [wp_next]'s guard
       as its only escape.  The lambda binder is named [CID], shadowing the
       section's, so every resource in the body picks the rebound hart by
       instance resolution and the body is textually unchanged.

       BOTH ARMS PASS IT ON UNCHANGED NOW.  The '1' arm hands it straight to
       [wp_instr_s_intr] (the shapes coincide -- that is what the bundle
       bought); the '0' arm collapses it with [wp_next_off], where no trap can
       be taken and the hart provably does not move. *)
    wp_next b p (fun (CID : CpuId) =>
      ∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       sconf -∗
       sie_cap kt m n b p -∗
       gpr_file (tp_pin m) -∗
       nextPC ↦ᵣ pc -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hinstr H".
    destruct b.
    - (* ---- b = true: the interrupt-absorbing engine.  The whole bundle goes
           in and the callback goes on unchanged. ---- *)
      iAssert (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝)%I as %Hal2.
      { iDestruct "Hinstr" as "[%Hnlpad Hr]".
        iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
        iEval (rewrite /instr_bytes) in "Hbytes".
        iDestruct "Hbytes" as "[%H2al _]". iPureIntro. exact H2al. }
      assert (Hpc0 : ret_pc pc = pc)
        by (unfold ret_pc; exact (update_bit0_zero_of_aligned2 pc Hal2)).
      iApply (wp_instr_s_intr m n pc is_rvc i Hpc0 with "Hcg Hpc Hinstr").
      iExact "H".
    - (* ---- b = false: the dispatch-None engine, SIE=0 from ghost ---- *)
      iDestruct (wp_next_here with "H") as "H".
      iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iRename "Harm" into "Hq0".
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
      iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
      pose proof Hmsf as Hmsf'.
      destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
      iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
      assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
        by (rewrite Hb0; vm_compute; reflexivity).
      (* [mie] is PINNED at [MIE_S] by [sconf] -- only [mideleg] is bound,
         and [Hmm] arrives already at the literal cause set, so the leaf
         below is instantiated at [MIE_S] with nothing to rewrite. *)
      iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
      iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iApply (wp_instr_s_config_regime strans_regime pc is_rvc i
                ms MIE_S mdv0 menvcfg0 (dq := DfracOwn 1)
                HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htr Hpcr Hinstr").
      iIntros (σ Hpceq) "Hpriv Hms Hmie Hmdl Hmenv Htr Hsi".
      iMod ("H" $! σ Hpceq
              with "[Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv] [Hstk Htr Hq0] Hfile Hnpc Hsi")
        as (s_exec) "(%Hexec & Hsi' & Hcont)".
      { iFrame "Hhw Hminv Hpriv".
        (* interrupts are OFF here, so no trap can be taken and mstatus is
           whatever it was: the SPP tie rides through untouched. *)
        iSplitL "Hms Hhalf Hspp".
        { iExists ms. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
        iSplitL "Hmie Hmdl".
        { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
        iExists menvcfg0. iFrame "Hmenv". iPureIntro.
        repeat split; assumption. }
      { iFrame "Hstk Htr Hwit". iExact "Hq0". }
      iModIntro. iExists s_exec.
      iSplitR; [iPureIntro; exact Hexec |].
      iFrame "Hsi'". iExact "Hcont".
  Qed.

  (* =================================================================== *)
  (* §3 The generic gpr-write engines over the funnel.  Premise              *)
  (* [ops_ok b rd rsa rsb] (IntrDefs.v), which occupies the slot the old     *)
  (* [rd <> csp_rs1] did, so no call site changes arity:                     *)
  (*   - WRITE side, its [rd_ok rd] conjunct: [sie_cap] is keyed on sp and   *)
  (*     transported across non-sp writes by [sie_cap_retarget] (sp-moving   *)
  (*     instructions re-carve their stack explicitly instead), and the      *)
  (*     register file PINS tp (HartTp.v), so a generic write may target     *)
  (*     neither.                                                           *)
  (*   - READ side, its two [src_ok b] conjuncts: the engine reads           *)
  (*     [rget m rsa] / [rget m rsb], and [rget] depends on the AMBIENT HART *)
  (*     at exactly tp.  Nothing here consumes that yet -- the σ-callback    *)
  (*     below still sits at the caller's hart, so the two spellings         *)
  (*     coincide.  It is landed now because the LATER move of that callback *)
  (*     inside [wp_next] is what makes them differ, and doing the leaf      *)
  (*     sweep separately keeps the two changes independently reviewable.    *)
  (*     DO NOT DROP IT AS REDUNDANT; see IntrDefs.rget_src_indep for the    *)
  (*     fact it buys.                                                      *)
  (* The continuation is wrapped in [wp_next b]: at [b = true] the           *)
  (* instruction can be trapped and the thread resumed on a DIFFERENT hart,  *)
  (* and every resource inside the lambda is then about THAT hart (the       *)
  (* binder is named [CID]) -- which is precisely why the read side needs a  *)
  (* premise at [b = true] and needs nothing at [b = false].                 *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = rget m rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = rget m rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hbexec)
      "Hcg Hpc Hinstr Hcont".
    pose proof (ops_ok_rd _ _ _ _ Hops) as Hrdok.
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc true base
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside the proof, so [rename] moves it out of the
       way -- which the STATEMENT never sees, so every caller that names this
       leaf's hart as [(CID := ...)] keeps working.  The alternative, introducing
       the new hart under a different name, would force a [(CID := ...)]
       annotation on every hart-indexed term the body writes out ([tp_pin m],
       [rget m rs]) -- ~480 of them across this tier.  With the rename, the body
       below is UNCHANGED and picks the rebound hart by instance resolution.

       IT HAS TO COME *AFTER* THE FUNNEL APPLICATION.  Inside a Section, a
       reference to a SIBLING lemma is resolved through the section variables
       BY NAME (they are not generalized yet), so renaming [CID] first makes
       [wp_instr_s_sconf] itself unmentionable:
         "wp_instr_s_sconf depends on the variable CID which is not declared".
       Lemmas from OTHER files are already generalized and take the hart as an
       ordinary instance argument, so they are unaffected -- which is why every
       tactic below the rename still elaborates. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    (* the two source reads survive the rebinding: at [b = true] by [ops_ok]'s
       source guards, at [b = false] because [Hs] pins the hart.  This is the
       one place the ENTRY hart has to be named, which is why it needed a name
       at all. *)
    destruct (rget_next_ops_indep (CID := CID0) b p CID m rd rsa rsb Hs Hops)
      as [Hra Hrb].
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (tp_pin m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (tp_pin m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      exact (Hbexec s_pc Lnpc0 (eq_trans Lva0 Hra) (eq_trans Lvb0 Hrb)). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    (* the leaf's own write commutes with the tp pin *)
    iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp)) in "Hfile".
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
       obligation is discharged by instantiating it here. *)
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
  Qed.

  (* the 4-byte (base-encoding) variant: pc advances by 4 *)
  Lemma wp_gpr_write_s_sconf_base
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = rget m rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = rget m rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false base -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hbexec)
      "Hcg Hpc Hinstr Hcont".
    pose proof (ops_ok_rd _ _ _ _ Hops) as Hrdok.
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc false base
              with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside the proof, so [rename] moves it out of the
       way -- which the STATEMENT never sees, so every caller that names this
       leaf's hart as [(CID := ...)] keeps working.  The alternative, introducing
       the new hart under a different name, would force a [(CID := ...)]
       annotation on every hart-indexed term the body writes out ([tp_pin m],
       [rget m rs]) -- ~480 of them across this tier.  With the rename, the body
       below is UNCHANGED and picks the rebound hart by instance resolution.

       IT HAS TO COME *AFTER* THE FUNNEL APPLICATION.  Inside a Section, a
       reference to a SIBLING lemma is resolved through the section variables
       BY NAME (they are not generalized yet), so renaming [CID] first makes
       [wp_instr_s_sconf] itself unmentionable:
         "wp_instr_s_sconf depends on the variable CID which is not declared".
       Lemmas from OTHER files are already generalized and take the hart as an
       ordinary instance argument, so they are unaffected -- which is why every
       tactic below the rename still elaborates. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    (* the two source reads survive the rebinding: at [b = true] by [ops_ok]'s
       source guards, at [b = false] because [Hs] pins the hart.  This is the
       one place the ENTRY hart has to be named, which is why it needed a name
       at all. *)
    destruct (rget_next_ops_indep (CID := CID0) b p CID m rd rsa rsb Hs Hops)
      as [Hra Hrb].
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (tp_pin m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (tp_pin m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      exact (Hbexec s_pc Lnpc0 (eq_trans Lva0 Hra) (eq_trans Lvb0 Hrb)). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    (* the leaf's own write commutes with the tp pin *)
    iEval (rewrite (tp_pin_upd m rd (regval_into_reg wval) Hrdtp)) in "Hfile".
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
       obligation is discharged by instantiating it here. *)
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
  Qed.

  (* =================================================================== *)
  (* §4 PILOT leaves + the straight-line pilot: the same three chained    *)
  (* instructions as the old SIE=1-only pilot, now SIE-AGNOSTIC -- the    *)
  (* proof is identical at either SIE value, and needs NO sret-target or  *)
  (* menvcfg premises (both derived inside the funnel).                   *)
  (* =================================================================== *)

  Lemma wp_cli_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 6) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    (* c.li reads x0 and nothing else, so the engine's source guard is
       DERIVED here rather than demanded of the caller: this leaf keeps its
       plain [rd_ok rd] premise. *)
    pose proof (ops_ok_conc b rd (zero_extend' 5 ('b"00"))
                  (zero_extend' 5 ('b"00")) Hrdok
                  ltac:(rdok_tpne) ltac:(rdok_tpne)) as Hops.
    unshelve iApply (wp_gpr_write_s_sconf pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.

  (* straight line of THREE instructions -- addi a5,a5,imm1 (4 bytes);
     c.li a4,imm2 (2 bytes); addi a4,a4,imm3 (4 bytes) -- at EITHER SIE
     value: with interrupts enabled an arbitrary number of pending
     interrupts is absorbed before each instruction, with them disabled
     this is the ordinary dispatch-None execution; the proof does not
     mention the mode. *)

End WpSmodeIntr.
