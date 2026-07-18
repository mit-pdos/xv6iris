(* WpSconfCsr.v -- stage-7 building blocks: the sstatus CSR leaves over
   [sconf]+[sie_cap].

   [wp_csrr_sstatus_s_sconf] (push_off's intr_get) works at EITHER SIE
   value: the read needs no SIE side condition, and the continuation
   receives the capability DESTRUCTED into its arm PAIRED with the pure
   fact that the read value's SIE bit matches that arm (ghost agreement
   between the bundle's tied half and the capability quarter).  The
   caller cases on the disjunct: bit 0 -> it holds the bare '0' quarter,
   bit 1 -> it holds the quarter + the interrupt invariant + the trap
   CSRs + the stack bound -- exactly what the upcoming csrci flip leaf
   consumes or what pop_off's csrsi restore re-packs.

   The csrci/csrsi FLIP leaves themselves are NOT here yet: they need
   the SIE=1 characterization of
   [legalize_sstatus_val ms (sstatus_write_val ms 2)] (bit-preservation
   of the sconf_ms_facts set + SIE clearing), a WpGprCsrwC-style
   symbolic-mstatus effort -- see the stage-7 note in CLAUDE.md.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpDecode WpLeafCommon WpGpr WpGprCsrwCommon.
Require Import SmodeCore WpSmodeGpr WpMmodeLeafBase.
Require Import KptTree SmodeCorePt WpSmodePtCtl.
(* exec_execute_csrr_sstatus: the exported copy lives in WpPopOff.v (the
   WpSmodePtCtl one is Local) -- relocate both down when the csr leaves
   get their shared base file. *)
Require Import WpPopOff.
Require Import StackOwn WpSmodeSret AlignBits.
Require Import WpIntrBits WpIntrCore IntrDefs WpIntrInv WpSmodeIntr.
Import Defs.

(* helper copy (Local in WpSmodePtCtl.v) *)
Local Definition csr_sstatus : mword 12 := Ox"100".

Section WpSconfCsr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_csrr_sstatus_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    ( ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m) -∗
      ( (⌜ _get_Mstatus_SIE ms = ('b"0" : mword 1) ⌝ ∗
         ghost_var γ (1/4) ('b"0" : mword 1))
      ∨ (⌜ _get_Mstatus_SIE ms = ('b"1" : mword 1) ⌝ ∗
         ghost_var γ (1/4) ('b"1" : mword 1) ∗
         (∃ handler : mword 64, intr_inv γ handler root_ppn MENVCFG_S) ∗
         (∃ v : mword 64, sepc ↦ᵣ v) ∗
         (∃ v : mword 64, scause ↦ᵣ v) ∗
         (∃ v : mword 64, stval ↦ᵣ v) ∗
         (∃ n : nat, ⌜ (kv_frame_slots <= n)%nat ⌝ ∗
            stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m
                         !!! Regidx csp_rs1) n)) ) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sstatus_read ms0)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read ms0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrr_sstatus rd ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS) Hrd). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read ms0))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m !!! Regidx csp_rs1
                  = m !!! Regidx csp_rs1)
      by (apply lookup_total_insert_ne; exact Hspne).
    (* the arm report: agreement between the tied half and the quarter
       pins the read value's SIE bit to the capability's arm -- taken
       while the half is still in hand, with the '1'-arm stack already
       re-keyed to the post-write map. *)
    iAssert ( ghost_var γ (1/2) (_get_Mstatus_SIE ms0) ∗
              ( (⌜ _get_Mstatus_SIE ms0 = ('b"0" : mword 1) ⌝ ∗
                 ghost_var γ (1/4) ('b"0" : mword 1))
              ∨ (⌜ _get_Mstatus_SIE ms0 = ('b"1" : mword 1) ⌝ ∗
                 ghost_var γ (1/4) ('b"1" : mword 1) ∗
                 (∃ handler : mword 64, intr_inv γ handler root_ppn MENVCFG_S) ∗
                 (∃ v : mword 64, sepc ↦ᵣ v) ∗
                 (∃ v : mword 64, scause ↦ᵣ v) ∗
                 (∃ v : mword 64, stval ↦ᵣ v) ∗
                 (∃ n : nat, ⌜ (kv_frame_slots <= n)%nat ⌝ ∗
                    stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                                 !!! Regidx csp_rs1) n)) ) )%I
      with "[Hcap Hhalf]" as "[Hhalf Harm]".
    { iDestruct "Hcap" as "[Hq0 | (Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & Hstk)]".
      - iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb.
        iFrame "Hhalf". iLeft. iFrame "Hq0". iPureIntro. exact Hb.
      - iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb.
        iFrame "Hhalf". iRight. iFrame "Hq1 Hhx Hsepcx Hscausex Hstvalx".
        iSplitR; [iPureIntro; exact Hb |].
        iDestruct "Hstk" as (n) "[%Hn Hstk]".
        iExists n. iSplit; [iPureIntro; exact Hn |].
        rewrite Hsp. iExact "Hstk". }
    iApply ("Hcont" $! ms0 with "[%] Hhs' [Hpriv Hms Hhalf Hmiex Hmenvx] Htlbinv
                          [$Hpc' $Hnpc] [Hfmap] Harm").
    { exact Hmsf. }
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpSconfCsr.
