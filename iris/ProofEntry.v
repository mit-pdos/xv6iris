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
Require Import RiscvLang RiscvPtsto RiscvFetchExec WpEntry WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpGprCsrwA WpGprCsrwB.
Require Import WpGprMretWp.
Require Import InstrBytes WpEntryNew WpTimerinit WpStartNew StackOwn.
Require Import KernelText.
Require Import SpecEntry.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Module EntryProof : ENTRY.
Section ProofEntry.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma wp_entry_boot (Φ : mval -> iProp Σ)
      (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (n : nat) {dq : dfrac} :
    wp_entry_boot_body Φ m v_stack0 mhartid_in mepc0 satp0 medeleg0 mideleg0
      mie0 menvcfg0 stimecmp0 mcounteren0 pmpcfg0 pmpaddr00 n dq.
  Proof.
    cbv beta delta [wp_entry_boot_body].
    intros pcE pcMain sp0 Hn4 Hpmp HlpeE Hbnd_ra Hbnd_s0.
    iIntros "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen
             Hstc Hstk Hstko #Htext Hcont".
    (* ---- _entry: reset -> jal start (PC = 0x80000058) ---- *)
    iEval (change pcE with pc_e0) in "Hpc".
    iApply (wp_entry Φ m v_stack0 mhartid_in pmpcfg0 (dq := dq) Hpmp
              with "Hmm Hpcf Hpc Hfile Hmh Hstk Htext").
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
    iApply (wp_start Φ (m_jal m v_stack0 mhartid_in) sp0 (add_vec_int pc_e7 4)
              (m !!! Regidx ti_s0)
              mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 mhartid_in
              mcounteren0 pmpcfg0 pmpaddr00 n
              Hn4 Hpmp HlpeE eq_refl HEra HEs0
              Hbnd_ra Hbnd_s0
              with "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
                    Hmcen Hstc Hstko Htext [Hcont Hstk]").
    iIntros (tv ms0 HoIE HoPRV HoSXL)
      "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
       Hmenv Hmcen Hstc Hstko".
    (* ---- <main>, in S-mode: the composed continuation ---- *)
    iEval (change st_main with pcMain) in "Hpc".
    iEval (change st_main with pcMain) in "Hmepc".
    iApply ("Hcont" $! tv ms0 HoIE HoPRV HoSXL
              with "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl
                    Hmie Hmenv Hmcen Hstc Hstk Hstko").
  Qed.

End ProofEntry.
End EntryProof.
