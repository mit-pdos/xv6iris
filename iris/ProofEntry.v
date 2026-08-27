(* ProofEntry.v -- the top-level M-mode boot theorem: [ENTRY] (SpecEntry.v),
   discharged by linking the piecemeal M-mode proofs into one WP that runs
   from CPU power-up at [_entry] to <main> in Supervisor mode.

   The pieces, each proven in its own file and left there:
     - [wp_entry]     (WpEntryNew.v)  _entry: la sp,stack0; sp += 4096*(hart+1);
                                      jal start
     - [wp_start]     (WpStartNew.v)  start(): the whole function, including the
                                      call to timerinit() ([wp_timerinit],
                                      WpTimerinit.v) and the closing MRET
   so this file is purely the plumbing between them:
     - wp_entry's output gpr file [m_jal m v_stack0 mhartid_in] is wp_start's
       input file; its sp entry (the loaded+offset stack pointer) is wp_start's
       [sp0], its ra entry is the (irrelevant, overwritten) [ra0], and s0 is
       untouched from the reset file [m].
     - wp_start's stack-geometry side conditions (the TOR bound for timerinit's
       two frame slots) are premises of the composed spec, phrased over the
       SAME symbolic sp0. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpEntryNew WpTimerinit WpStartNew.
Require Import WpGprMretWp WpGprCsrwA WpGprCsrwB.
Require Import SpecEntry.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import CodeEntryAux.
Require Import CodeStartAux.
Require Import CodeTimerinitAux.
Require Import TsoCtx.
Local Open Scope Z_scope.

Module EntryProof : ENTRY.
Section ProofEntry.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_entry_boot
      (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (sp0 : mword 64) (n : nat) {dq : dfrac} :
    wp_entry_boot_body m v_stack0 mhartid_in mepc0 satp0 medeleg0 mideleg0
      mie0 menvcfg0 stimecmp0 mcounteren0 pmpcfg0 pmpaddr00 sp0 n dq.
  Proof.
    cbv beta delta [wp_entry_boot_body].
    intros pcE pcMain Hsp0 Hn4 Hpmp Hmenv0 Hmie0 Hmdl0 Hbnd_ra Hbnd_s0.
    iIntros "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen
             Hstc Hstk #Hpr Hstko Hrun #Htext Hcont".
    (* The contract's premises are stated in [MbootVocab]'s vocabulary; the
       three M-mode lemmas want their own.  Convert once, here: this file is
       the only place the two spellings meet. *)
    assert (HlpeE : _get_MEnvcfg_LPE menvcfg0 = ('b"0"))
      by (rewrite Hmenv0; vm_compute; reflexivity).
    rewrite <- (ti_ea_ra_mb sp0) in Hbnd_ra.
    rewrite <- (ti_ea_s0_mb sp0) in Hbnd_s0.
    iEval (rewrite <- entry_ld_ea_mb) in "Hstk".
    iAssert (TsoCtx.pristine_win entry_ld_ea 8) as "#Hpr'";
      first by rewrite entry_ld_ea_mb.
    (* ---- _entry: reset -> jal start (PC = 0x80000058) ---- *)
    iEval (change pcE with pc_e0) in "Hpc".
    iApply (wp_entry m v_stack0 mhartid_in pmpcfg0 (dq := dq) Hpmp
              with "Hmm Hpcf Hpc Hfile Hmh Hstk Hpr' Htext").
    iIntros "Hmm Hpcf Hpc Hfile Hmh Hstk".
    iEval (change pc_start with st_pc30) in "Hpc".
    (* wp_start's entry-file lookups over _entry's output map *)
    assert (Hkra : (Regidx i_jal : regidx) = Regidx ti_ra) by (vm_compute; reflexivity).
    assert (HEra : m_jal m v_stack0 mhartid_in !!! Regidx ti_ra = add_vec_int pc_e7 4).
    { unfold m_jal. rewrite Hkra. rewrite upd_eq. reflexivity. }
    assert (HEs0 : m_jal m v_stack0 mhartid_in !!! Regidx ti_s0 = m !!! Regidx ti_s0).
    { unfold m_jal, m_cadd, m_mul, m_caddi, m_csrr, m_clui, m_ld, m_auipc.
      repeat (rewrite upd_ne;
              [ | let H := fresh in intro H;
                  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
                  vm_compute in H; discriminate H ]).
      reflexivity. }
    (* ---- start(): jal-entry -> MRET (Supervisor mode at <main>) ---- *)
    iApply (wp_start (m_jal m v_stack0 mhartid_in) sp0 (add_vec_int pc_e7 4)
              (m !!! Regidx ti_s0)
              mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 mhartid_in
              mcounteren0 pmpcfg0 pmpaddr00 n
              Hn4 Hpmp HlpeE (eq_trans (m_jal_sp m v_stack0 mhartid_in) Hsp0) HEra HEs0
              Hbnd_ra Hbnd_s0
              with "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
                    Hmcen Hstc Hstko Hrun Htext [Hcont Hstk]").
    iIntros (tv ms0 HoIE HoPRV HoSXL HoKF)
      "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
       Hmenv Hmcen Hstc Hstko Hrun".
    (* ---- <main>, in S-mode: the composed continuation ----
       Here the M-mode symbolic execution is DISCHARGED into facts: the client
       is handed the post-state as eleven opaque values plus the eight things
       it consumes about them, and never sees [st_mout]'s tower again. *)
    iEval (change st_main with pcMain) in "Hpc".
    iEval (change st_main with pcMain) in "Hmepc".
    iEval (rewrite entry_ld_ea_mb) in "Hstk".
    destruct (st_boot_csr_facts menvcfg0 mie0 mideleg0 satp0 Hmenv0 Hmie0 Hmdl0)
      as (Hmenvf & Hmief & Hsatpf & Hmiepin).
    iApply ("Hcont" $! (st_mout (m_jal m v_stack0 mhartid_in) sp0 ms0 mie0 mideleg0
                          menvcfg0 mcounteren0 tv mhartid_in)
                       (cms5 (st_ms1 ms0))
                       (satp_legalized satp0 (mword_of_int 0))
                       (legalize_medeleg medeleg0 st_ffff)
                       (st_mdl1 mideleg0)
                       (st_mie1 mie0 mideleg0)
                       (menvcfg_legalized (st_menv_adue menvcfg0)
                          (ti_menv1 (st_menv_adue menvcfg0)))
                       (stimecmp_legalized stimecmp0 (ti_deadline tv))
                       (legalize_mcounteren mcounteren0 (ti_mcen1 mcounteren0))
                       (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00)
              with "[] Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede
                    Hmdl Hmie Hmenv Hmcen Hstc Hstk Hstko Hrun").
    iPureIntro. split_and!.
    - exact (st_mout_sp _ _ _ _ _ _ _ _ _).
    - exact (st_mout_tp _ _ _ _ _ _ _ _ _).
    - exact (st_boot_ms_kernel_facts ms0 HoKF).
    - exact Hmenvf.
    - exact Hmief.
    - exact Hmiepin.
    - exact Hsatpf.
    - exact (st_pmp_open pmpcfg0 pmpaddr00 Hpmp).
    - exact (ti_mcen1_TM mcounteren0).
    - (* [legalize_medeleg] ignores its old-value argument, so the value
         start() wrote IS the closed constant. *)
      reflexivity.
  Qed.

End ProofEntry.
End EntryProof.
