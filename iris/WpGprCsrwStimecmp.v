(* WpGprCsrwStimecmp.v -- the ONE csrw leaf that writes a cell the WRAPPER
   owns.

   [write_CSR csr_stimecmp] is [read stimecmp; write stimecmp;
   clint_dispatch false; read stimecmp], and [clint_dispatch] REFRESHES mip
   from the CLINT: it reads mtime / mtimecmp / stimecmp / the plic wires --
   none of which any leaf owns, so those are ∀-peels -- and then WRITES mip,
   whose cell lives in [pc_is]'s [clock_res] and therefore goes wholly to the
   cycle wrapper.  A leaf cannot write a cell it does not hold, so this leaf
   needs the wrapper to LEND it mip and take back an arbitrary new value.
   That is sound and not even hard to see why: [HartMCycle.mm_tick_agree]
   already constrains the post-file only OFF [tk_clock3], and mip ∈
   tk_clock3 -- the tick's own mip write is exactly as nondeterministic.
   Making it happen needs the cycle rule's post-file to be a PREDICATE rather
   than a parameter (so the body may CHOOSE it), threaded through [mm_cycle]
   and [wp_instr_ex]; that generalization is not done yet.

   The leaf is parked here, out of WpGprCsrwB, so that the four csrw leaves
   which do not touch the wrapper's cells (mideleg / sie / satp / pmpaddr0)
   are not held red behind it.  Everything it needs from the exec side is
   still in WpGprCsrwB. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec ExecCommon WpGpr.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpInstr.
Require Import WpGprCsrwCommon.
Require Import RiscvExtras.
Require Import MinstretInv.
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartMCycle
        HartMFrame HartGoodb WpDecodeBridge WpMmodeJump WpMmodeCsrSwp.
Require Import WpGprCsrrCommon.
Require Import WpGprCsrwB.
Local Open Scope Z_scope.

Section WpCsrwStimecmp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- stimecmp ---- *)
  Lemma wp_csrw_stimecmp_gpr (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (stimecmp0 : type_of_register stimecmp)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    uint rs1 <> 0 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (m !!! Regidx rs1) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat Hrs1) "Hmm Hpmpc [Hpc Hnpc] Hfmap Hcsr Hinstr Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) pmpcfg0
              Hpmp Hstat with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hcsr")     as %Lcsr.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lcsrp : register_lookup stimecmp s_pc.(sregs) = stimecmp0)
      by (unfold s_pc; tmig; exact Lcsr).
    assert (Lrs1p : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                    = m (Regidx rs1)).
    { rewrite -Lrs1u.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    assert (HmisaSp : eq_vec (_get_Misa_S (register_lookup misa s_pc.(sregs))) ('b"1") = true)
      by (rewrite Lmisap; exact HmisaS).
    destruct (exec_execute_csrw_stimecmp rs1 s_pc Hrs1 Lprivp HmisaSp) as [mp Hex].
    rewrite ?Lcsrp Lrs1p in Hex.
    (* the CSR write runs [clint_dispatch], which refreshes mip -- so this step
       scribbles a cell that lives in [clock_inv].  Open it, update, close: the
       invariant is value-agnostic, so any [mp] re-establishes it. *)
    iPoseProof "Hinv" as "#Hinvc".
    iDestruct "Hinvc" as "(_ & #Hclk & _)".
    iInv "Hclk" as ">Hcb" "Hclose".
    iDestruct "Hcb" as (c0 t0 p0) "(Hc & Ht & Hp)".
    iMod (reg_update _ stimecmp _ (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iMod (reg_update _ mip _ mp with "Hreg Hp") as "[Hreg Hp]".
    iMod ("Hclose" with "[Hc Ht Hp]") as "_".
    { iNext. iExists c0, t0, mp. iFrame "Hc Ht Hp". }
    iModIntro.
    iExists (set_reg (set_reg s_pc stimecmp (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))) mip mp).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
      exact Hex. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg s_pc stimecmp (stimecmp_legalized stimecmp0 (m !!! Regidx rs1))) mip mp).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hfmap Hcsr").
  Qed.

End WpCsrwStimecmp.
