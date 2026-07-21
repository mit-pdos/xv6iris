(* WpKernelvecSpec.v -- kernelvec satisfies the interrupt-handler
   CONTRACT ([intr_handler_spec], IntrDefs.v): the high-altitude cap of
   the interrupt stack, split out of WpIntrInv.v so the definitions and
   the absorbing step engine stay importable from leaf-level files.

   Contents: the kernelvec trap-vector facts (Direct mode, base = itself
   -- feed [intr_inv_alloc] when the handler is kernelvec), the [pa_stk]
   re-addressing of kernelvec's sparse save windows, and
   [kernelvec_handler_spec] -- the proof that a trap into kernelvec
   returns idempotently to the interrupted pc with SIE re-enabled, the
   register file preserved and the per-trap frame intact.  The SIE ghost
   kernelvec's spec consumes is a FRESH per-trap name [γk] (allocated
   here, tied to the trapped SIE=0 and discarded at the sret) -- the
   REAL [γ]'s pieces stay outside the handler run, untouched, so the
   live-bit tie is restored for free when SRET brings SIE back to 1.    *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv.
Require Import WpMmodeLeafBase StackOwn.
Require Import SmodeCore KernelText.
Require Import WpKernelvecNew.
Require Import WpIntrBits WpIntrCore.
Require Import IntrDefs.
Require Import IntrDefs.
(* legalize_sie_clear_idem + have_nom_val: kept QUALIFIED (no Import) so the
   WpGprCsrwCommon/C namespaces don't shadow anything here. *)
Require WpGprCsrwCommon WpGprCsrwC.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* the kernelvec trap-vector facts (Direct mode, base = itself) -- feed
   [intr_inv_alloc] when the handler is kernelvec. *)
Lemma kernelvec_tv_direct :
  trapVectorMode_forwards
    (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct.
Proof. vm_compute. reflexivity. Qed.

Lemma kernelvec_stvec_base :
  stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
    = (mword_of_int KernelSyms.kernelvec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* kernelvec's sparse positive-offset save slots, re-addressed as [pa_stk]
   slots below the INTERRUPTED sp: kv_sp1 = sp - 256, so the window at
   kv_sp1 + 8j is stack slot 32 - j. *)
Lemma kv_slot_addr (m : regfile) (off : mword 64) (k : nat) :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1)) off
    = (mword_of_int (- (8 * Z.of_nat k)) : mword 64) ->
  add_vec (kv_sp1 m) off = pa_stk (m !!! Regidx csp_rs1) k.
Proof.
  intros H.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr kv_addv_assoc H. unfold pa_stk, add_vec_int. reflexivity.
Qed.

Lemma kv_slot_addr0 (m : regfile) :
  kv_sp1 m = pa_stk (m !!! Regidx csp_rs1) 32.
Proof.
  assert (Hr : kv_sp1 m
               = add_vec (m !!! Regidx csp_rs1)
                         (sign_extend' 64 (caddi16sp_imm kv_imm1))) by reflexivity.
  rewrite Hr. unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq. vm_compute. reflexivity.
Qed.

Section WpKernelvecSpec.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  Lemma kernelvec_handler_spec (root_ppn : mword 44) (menvcfg0 : mword 64) :
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    kernel_text -∗
    intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64)
      root_ppn menvcfg0.
  Proof.
    intros HPBMTE Hmenvval0 Hpmm Hlpe0 HFIOM.
    iIntros "#Hhw #Hinv #Htext".
    iModIntro.
    iIntros (elp_v ms pc0 mie_v mdv0 m Φ)
      "%Hfacts %Hpc0 %Hmm Hhs Hpriv Hms Hmie Hmdl Hsepc Hpc Hfile HF Hcont".
    pose proof Hfacts as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iDestruct "HF" as "(Hmenv & Htlbinv & Hstk)".
    (* re-address kernelvec's 17 sparse save windows as [pa_stk] slots *)
    pose proof (kv_slot_addr0 m) as Hb32.
    assert (Hb30 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 30)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb28 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 28)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb27 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 27)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb26 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 26)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb23 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 23)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb22 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 22)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb21 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 21)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb20 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 20)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb19 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 19)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb18 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 18)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb17 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 17)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb16 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 16)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb5 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 5)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb4 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 4)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb3 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 3)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    assert (Hb2 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = pa_stk (m !!! Regidx csp_rs1) 2)
      by (apply kv_slot_addr; apply bv_eq; vm_compute; reflexivity).
    (* open the 32-slot frame and pull out the 17 save slots *)
    iEval (rewrite /kv_frame_slots stack_own_slots; cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 &
      S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 &
      S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32 & _)".
    iDestruct "S32" as (w1) "Hw1".   iEval (rewrite -Hb32) in "Hw1".
    iDestruct "S30" as (w2) "Hw2".   iEval (rewrite -Hb30) in "Hw2".
    iDestruct "S28" as (w3) "Hw3".   iEval (rewrite -Hb28) in "Hw3".
    iDestruct "S27" as (w4) "Hw4".   iEval (rewrite -Hb27) in "Hw4".
    iDestruct "S26" as (w5) "Hw5".   iEval (rewrite -Hb26) in "Hw5".
    iDestruct "S23" as (w6) "Hw6".   iEval (rewrite -Hb23) in "Hw6".
    iDestruct "S22" as (w7) "Hw7".   iEval (rewrite -Hb22) in "Hw7".
    iDestruct "S21" as (w8) "Hw8".   iEval (rewrite -Hb21) in "Hw8".
    iDestruct "S20" as (w9) "Hw9".   iEval (rewrite -Hb20) in "Hw9".
    iDestruct "S19" as (w10) "Hw10". iEval (rewrite -Hb19) in "Hw10".
    iDestruct "S18" as (w11) "Hw11". iEval (rewrite -Hb18) in "Hw11".
    iDestruct "S17" as (w12) "Hw12". iEval (rewrite -Hb17) in "Hw12".
    iDestruct "S16" as (w13) "Hw13". iEval (rewrite -Hb16) in "Hw13".
    iDestruct "S5" as (w14) "Hw14".  iEval (rewrite -Hb5) in "Hw14".
    iDestruct "S4" as (w15) "Hw15".  iEval (rewrite -Hb4) in "Hw15".
    iDestruct "S3" as (w16) "Hw16".  iEval (rewrite -Hb3) in "Hw16".
    iDestruct "S2" as (w17) "Hw17".  iEval (rewrite -Hb2) in "Hw17".
    (* clearing SIE on the trap-time mstatus is idempotent under legalization
       (the ext-state / dirty / MPP well-formedness rides in via intr_ms_facts) *)
    assert (Hleg_trap :
      WpGprCsrwCommon.legalize_sstatus_val (trap_ms elp_v ms)
        (WpGprCsrwCommon.sstatus_write_val (trap_ms elp_v ms) (mword_of_int 2))
      = trap_ms elp_v ms).
    { apply WpGprCsrwC.legalize_sie_clear_idem.
      - apply trap_ms_SIE.
      - rewrite trap_ms_XS; exact HXS.
      - rewrite trap_ms_FS; exact HFS.
      - rewrite trap_ms_VS; exact HVS.
      - rewrite trap_ms_SD; exact HSD.
      - rewrite trap_ms_MPP; exact HMPP. }
    (* kernelvec's spec assumes a SIE ghost half tied to ITS entering mstatus
       (SIE=0); the real γ's pieces stay outside the handler run, so allocate
       a fresh per-trap name and hand kernelvec one half. *)
    iMod (ghost_var_alloc (_get_Mstatus_SIE (trap_ms elp_v ms))) as (γk) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[Hsie _]".
    iApply (wp_kernelvec root_ppn γk m (trap_ms elp_v ms) mie_v mdv0 menvcfg0 pc0
              w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 Φ
              (trap_ms_SIE_false elp_v ms)
              (trap_ms_MPRV_false elp_v ms HMPRV0)
              (trap_ms_SXL_eq elp_v ms HSXL)
              Hmm HPBMTE Hmenvval0
              (trap_ms_MXR_true elp_v ms HMXR)
              Hpmm
              (trap_ms_TSR_false elp_v ms HTSR)
              (sret_newpriv_trap_ms elp_v ms)
              Hlpe0
              HFIOM
              Hleg_trap
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hsepc
                    Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite Hpc0) in "Hpc".
    (* the save slots come back holding [m]'s registers; re-address them as
       [pa_stk] slots and rebuild the 32-slot [stack_own] frame *)
    iEval (rewrite Hb32) in "Hw1".
    iEval (rewrite Hb30) in "Hw2".
    iEval (rewrite Hb28) in "Hw3".
    iEval (rewrite Hb27) in "Hw4".
    iEval (rewrite Hb26) in "Hw5".
    iEval (rewrite Hb23) in "Hw6".
    iEval (rewrite Hb22) in "Hw7".
    iEval (rewrite Hb21) in "Hw8".
    iEval (rewrite Hb20) in "Hw9".
    iEval (rewrite Hb19) in "Hw10".
    iEval (rewrite Hb18) in "Hw11".
    iEval (rewrite Hb17) in "Hw12".
    iEval (rewrite Hb16) in "Hw13".
    iEval (rewrite Hb5) in "Hw14".
    iEval (rewrite Hb4) in "Hw15".
    iEval (rewrite Hb3) in "Hw16".
    iEval (rewrite Hb2) in "Hw17".
    iAssert (stack_own (m !!! Regidx csp_rs1) kv_frame_slots)
      with "[S1 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S24 S25 S29 S31
            Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17]"
      as "Hstk".
    2:{ iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl [Hsepc] Hpc Hfile [Hmenv Htlbinv Hstk]").
        { iExists pc0. iFrame "Hsepc". }
        iFrame "Hmenv Htlbinv". iExact "Hstk". }
    rewrite /kv_frame_slots stack_own_slots. cbn [seq].
    iSplitL "S1"; [iExact "S1" |].
    iSplitL "Hw17"; [by iExists _ |].
    iSplitL "Hw16"; [by iExists _ |].
    iSplitL "Hw15"; [by iExists _ |].
    iSplitL "Hw14"; [by iExists _ |].
    iSplitL "S6"; [iExact "S6" |].
    iSplitL "S7"; [iExact "S7" |].
    iSplitL "S8"; [iExact "S8" |].
    iSplitL "S9"; [iExact "S9" |].
    iSplitL "S10"; [iExact "S10" |].
    iSplitL "S11"; [iExact "S11" |].
    iSplitL "S12"; [iExact "S12" |].
    iSplitL "S13"; [iExact "S13" |].
    iSplitL "S14"; [iExact "S14" |].
    iSplitL "S15"; [iExact "S15" |].
    iSplitL "Hw13"; [by iExists _ |].
    iSplitL "Hw12"; [by iExists _ |].
    iSplitL "Hw11"; [by iExists _ |].
    iSplitL "Hw10"; [by iExists _ |].
    iSplitL "Hw9"; [by iExists _ |].
    iSplitL "Hw8"; [by iExists _ |].
    iSplitL "Hw7"; [by iExists _ |].
    iSplitL "Hw6"; [by iExists _ |].
    iSplitL "S24"; [iExact "S24" |].
    iSplitL "S25"; [iExact "S25" |].
    iSplitL "Hw5"; [by iExists _ |].
    iSplitL "Hw4"; [by iExists _ |].
    iSplitL "Hw3"; [by iExists _ |].
    iSplitL "S29"; [iExact "S29" |].
    iSplitL "Hw2"; [by iExists _ |].
    iSplitL "S31"; [iExact "S31" |].
    iSplitL "Hw1"; [by iExists _ |].
    done.
  Qed.

End WpKernelvecSpec.
