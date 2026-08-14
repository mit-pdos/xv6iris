(* ProofDevintr.v -- devintr() over the SIE-agnostic sconf world.

   devintr() @ 0x8000253a is xv6's interrupt demultiplexer: it reads scause and
   dispatches on it, returning 1 (a device interrupt, served through the PLIC),
   2 (a timer interrupt, served by clockintr) or 0 (unrecognised).

   THE SHAPE OF THE PROOF is the shape of the code: four exits, one epilogue.
   gcc puts the common epilogue at +0x22 -- in the middle of the function, on
   the fall-through of the timer test -- and every other path reaches it by a
   [c.j].  So [di_epi] is proved ONCE over an arbitrary arrival map and applied
   four times: from the +0x1e fall-through (a0 = 0), from +0x46 (irq = 0), from
   +0x6c (after plic_complete) and from +0x74 (after clockintr).  Likewise the
   plic_complete tail at +0x62 is reached from BOTH device handlers, so it is
   [di_plic_tail], applied twice.

   s1 IS SHRINK-WRAPPED.  [c.sdsp s1,8(sp)] is the first instruction of the
   PLIC arm (+0x2a), not of the prologue, and the two exits from that arm each
   reload s1 before jumping to the epilogue.  So the frame's third slot holds
   the caller's s1 only inside the PLIC arm, and holds an arbitrary word on the
   timer and unrecognised paths -- which is why [di_epi] takes slots 3 and 4
   existentially and only slots 1 and 2 at pinned values.

   THE printk ARM IS DEAD, AND THAT IS THE ONE INTERESTING OBLIGATION.  After
   the claim, [PlicClaim]'s postcondition gives [plic_claim_a0_ok]: the id is
   0, [uart_irq_id] = 10 or [virtio_irq_id] = 1, and nothing else, because the
   kernel's PLIC plan lets a hart's S-context enable no other source
   (PlicPlan.v).  The two [beq]s at +0x36 and +0x3c take the two nonzero cases,
   so at the [c.bnez a4] at +0x42 the id is provably 0 and the branch falls
   through -- devintr never reaches printk, whose general (non-panic) path has
   no proof.  Without that fact this function could not be proved at all.

   THE SIE INDEX IS THE LITERAL [false] THROUGHOUT (SpecDevintr.v's header
   gives the two independent reasons), so every leaf is applied at [false] and
   collapsed with [wp_next_off], and the hart never moves.

   A functor over KernelSyms.plic_claim / KernelSyms.plic_complete / UARTINTR / VIRTIODISKINTR /
   CLOCKINTR. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom CpuOwn.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfCsr.
Require Import WpSmodeIntr.
Require Import DevModel DiskPtsto WpUart.
Require Import CodeDevintr.
Require Import SpecPlicClaim SpecPlicComplete SpecUartintr SpecVirtioDiskIntr SpecClockintr.
Require Import SpecDevintr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import IrefSlots.
Import Defs.

Local Open Scope Z_scope.
Set Printing Depth 40.

Module DevintrProof (PlicClaim : PLIC_CLAIM) (PlicComplete : PLIC_COMPLETE)
                    (Uartintr : UARTINTR) (VirtioDiskIntr : VIRTIODISKINTR)
                    (Clockintr : CLOCKINTR) : DEVINTR.

Section ProofDevintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation s1_idx := (mword_of_int 9 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

  (* "every callee-saved register devintr does not itself restore is still the
     caller's" -- the residual of [callee_saved] that a mid-function map can
     carry (sp and s0 are the frame's, and are put back by the epilogue). *)
  Local Definition di_thr (m0 M : regfile) : Prop :=
    forall r : mword 5, is_cs_idx r = true ->
      r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
      M !!! Regidx r = m0 !!! Regidx r.

  Local Lemma di_cs_of (m0 mf : regfile) :
    mf !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1 ->
    mf !!! Regidx s0_idx = m0 !!! Regidx s0_idx ->
    di_thr m0 mf ->
    callee_saved m0 mf.
  Proof.
    intros Hsp Hs0 Hthr. unfold callee_saved.
    split_and!;
      first [ exact Hsp | exact Hs0
            | apply Hthr; solve [ vm_compute; reflexivity | vm_compute; discriminate ] ].
  Qed.

  (* this hart's id is one of the eight the PLIC is modelled for -- the one
     premise plic_claim / plic_complete place on their caller, and a theorem
     rather than an assumption ([tp] is pinned to the hart). *)
  Local Lemma di_tp_bound (M : regfile) :
    bv_unsigned (rget M tp_idx) < Z.of_nat dev_ncpu.
  Proof.
    rewrite rget_tp. destruct (tp_ok_cid_of cpu_id) as [_ H8].
    rewrite uint_unsigned in H8. change (Z.of_nat dev_ncpu) with 8%Z. exact H8.
  Qed.

  (* ================================================================== *)
  (* THE COMMON EPILOGUE (KernelSyms.devintr+0x22 .. KernelSyms.devintr+0x28).                           *)
  (* ================================================================== *)
  Lemma di_epi
      (m0 M : regfile) (sp0 ra0 s00 retv : mword 64)
      (k lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (dq : dfrac) (sc : mword 64) (v3 v4 : mword 64) (lks : gset string) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    m0 !!! Regidx ra_idx = ra0 ->
    m0 !!! Regidx s0_idx = s00 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    M !!! Regidx a0_idx = retv ->
    di_thr m0 M ->
    sie_cap_gpr M k false p -∗
    cpu_own lvl eb p C false lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.devintr + 0x22) : mword 64) -∗
    scause ↦ᵣ{dq} sc -∗
    pa_stk sp0 1 ↦₈ ra0 -∗
    pa_stk sp0 2 ↦₈ s00 -∗
    pa_stk sp0 3 ↦₈ v3 -∗
    pa_stk sp0 4 ↦₈ v4 -∗
    ( ∀ mf : regfile,
        ⌜ callee_saved m0 mf /\ mf !!! Regidx a0_idx = retv ⌝ -∗
        sie_cap_gpr mf (k + 4) false p -∗
        cpu_own lvl eb p C false lks -∗
        scause ↦ᵣ{dq} sc -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hm0sp Hm0ra Hm0s0 HMsp HMa0 Hthr.
    iIntros "Hcg Hcnt #Htext Hpc Hsc Hb1 Hb2 Hb3 Hb4 Hcont".
    (* the three frame addresses, as offsets off the pushed sp *)
    assert (Hpa1 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HMsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (M !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HMsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x22: c.ldsp ra,24(sp) ---- *)
    iEval (rewrite -Hpa1) in "Hb1".
    iPoseProof (dii_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x22)) (mword_of_int 3 : mword 6) ra_idx
              M k ra0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hb1").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb1".
    set (E1 := <[Regidx ra_idx := regval_into_reg ra0]> M).
    change (<[Regidx ra_idx := regval_into_reg ra0]> M) with E1.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x24)) by pcw.
    iEval (rewrite Hpc24) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = M !!! Regidx csp_rs1)
      by (rewrite /E1 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* ---- +0x24: c.ldsp s0,16(sp) ---- *)
    iEval (rewrite -Hpa2 -HE1sp) in "Hb2".
    iPoseProof (dii_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x24)) (mword_of_int 2 : mword 6) s0_idx
              E1 k s00 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 Hb2").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb2".
    set (E2 := <[Regidx s0_idx := regval_into_reg s00]> E1).
    change (<[Regidx s0_idx := regval_into_reg s00]> E1) with E2.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x26)) by pcw.
    iEval (rewrite Hpc26) in "Hpc".
    (* ---- +0x26: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite HE1sp. exact HMsp. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE2sp.
      assert (Hps : pa_stk sp0 4
                    = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hps. apply frame_cancel_32. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv. exact HE2sp. }
    iEval (rewrite Hpa1) in "Hb1".
    iEval (rewrite HE1sp Hpa2) in "Hb2".
    iDestruct (stack_own_4_intro sp0 with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (dii_26 with "Htext") as "Hi26".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.devintr + 0x26)) (mword_of_int 2 : mword 6)
              E2 k 4 false Hpop
              with "Hcg Hpc Hi26 Hframe").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2) with E3.
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x28)) by pcw.
    iEval (rewrite Hpc28) in "Hpc".
    (* ---- +0x28: c.ret ---- *)
    assert (HE3ra : E3 !!! Regidx ra_idx = ra0).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1. apply upd_eq. }
    assert (HE3rg : rget E3 ra_idx = ra0) by (rgne; exact HE3ra).
    iPoseProof (dii_28 with "Htext") as "Hi28".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.devintr + 0x28)) ra_idx E3 (k + 4)%nat false
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi28").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HE3rg) in "Hpc".
    (* ---- the exit facts ---- *)
    assert (HE3sp : E3 !!! Regidx csp_rs1 = m0 !!! Regidx csp_rs1)
      by (rewrite /E3 upd_eq; rewrite Hwv; exact (eq_sym Hm0sp)).
    assert (HE3s0 : E3 !!! Regidx s0_idx = m0 !!! Regidx s0_idx).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_eq. exact (eq_sym Hm0s0). }
    assert (HE3thr : di_thr m0 E3).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      exact (Hthr r Hr Ncsp N8). }
    assert (HE3a0 : E3 !!! Regidx a0_idx = retv).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    iApply ("Hcont" $! E3 with "[%] Hcg Hcnt Hsc Hpc").
    split; [ exact (di_cs_of m0 E3 HE3sp HE3s0 HE3thr) | exact HE3a0 ].
  Qed.

  (* ================================================================== *)
  (* THE plic_complete TAIL (KernelSyms.devintr+0x62 .. KernelSyms.devintr+0x6c), reached from BOTH       *)
  (* device handlers: a0 := s1 (the claimed id), complete it, return 1.    *)
  (* ================================================================== *)
  Lemma di_plic_tail
      (γu : uart_names) (γv : disk_names)
      (m0 M : regfile) (sp0 ra0 s00 s10 irq : mword 64)
      (k lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (dq : dfrac) (sc : mword 64) (v4 : mword 64) (lks : gset string) :
    (6 <= k)%nat ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    m0 !!! Regidx ra_idx = ra0 ->
    m0 !!! Regidx s0_idx = s00 ->
    m0 !!! Regidx s1_idx = s10 ->
    M !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    M !!! Regidx s1_idx = irq ->
    ( forall r : mword 5, is_cs_idx r = true ->
        r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
        r <> (mword_of_int 9 : mword 5) -> M !!! Regidx r = m0 !!! Regidx r ) ->
    devintr_ret sc = (mword_of_int 1 : mword 64) ->
    sie_cap_gpr M k false p -∗
    cpu_own lvl eb p C false lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.devintr + 0x62) : mword 64) -∗
    scause ↦ᵣ{dq} sc -∗
    dev_inv γu γv -∗
    pa_stk sp0 1 ↦₈ ra0 -∗
    pa_stk sp0 2 ↦₈ s00 -∗
    pa_stk sp0 3 ↦₈ s10 -∗
    pa_stk sp0 4 ↦₈ v4 -∗
    ( ∀ mf : regfile,
        ⌜ callee_saved m0 mf /\ mf !!! Regidx a0_idx = devintr_ret sc ⌝ -∗
        sie_cap_gpr mf (k + 4) false p -∗
        cpu_own lvl eb p C false lks -∗
        scause ↦ᵣ{dq} sc -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hk Hm0sp Hm0ra Hm0s0 Hm0s1 HMsp HMs1 Hthr Hret.
    iIntros "Hcg Hcnt #Htext Hpc Hsc #Hdev Hb1 Hb2 Hb3 Hb4 Hcont".
    (* ---- +0x62: c.mv a0,s1 ---- *)
    iPoseProof (dii_62 with "Htext") as "Hi62".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.devintr + 0x62)) a0_idx s1_idx M k false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T0 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (rget M s1_idx))]> M).
    change (<[Regidx a0_idx := regval_into_reg (add_vec zero_reg (rget M s1_idx))]> M) with T0.
    assert (Hpc64 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x64)) by pcw.
    iEval (rewrite Hpc64) in "Hpc".
    (* ---- +0x64: jal ra,plic_complete ---- *)
    iPoseProof (dii_64 with "Htext") as "Hi64".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.devintr + 0x64)) ra_idx (mword_of_int 12392 : mword 21)
              T0 k false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi64").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T1 := <[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.devintr + 0x64) : mword 64) 4)]> T0).
    change (<[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.devintr + 0x64) : mword 64) 4)]> T0) with T1.
    assert (Hjpc : add_vec (mword_of_int (KernelSyms.devintr + 0x64) : mword 64)
                     (sign_extend' 64 (mword_of_int 12392 : mword 21))
                   = mword_of_int KernelSyms.plic_complete) by pcw.
    iEval (rewrite Hjpc) in "Hpc".
    assert (HT1ra : T1 !!! Regidx ra_idx
                    = add_vec_int (mword_of_int (KernelSyms.devintr + 0x64) : mword 64) 4)
      by (rewrite /T1 upd_eq; reflexivity).
    (* ===================== plic_complete(irq) ===================== *)
    iApply (PlicComplete.wp_plic_complete_sconf γu γv T1 k p
              (di_tp_bound T1) ltac:(lia)
              with "Hcg Htext Hpc Hdev").
    iIntros (MC) "Hcg Hpc %HcsC".
    destruct HcsC as [HcsC HraC].
    assert (Hpc68 : ret_pc (T1 !!! Regidx ra_idx) = mword_of_int (KernelSyms.devintr + 0x68))
      by (rewrite HT1ra; pcw).
    iEval (rewrite Hpc68) in "Hpc".
    (* ---- +0x68: c.li a0,1 ---- *)
    iPoseProof (dii_68 with "Htext") as "Hi68".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x68)) a0_idx (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) MC k false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi68").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T2 := <[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> MC).
    change (<[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> MC) with T2.
    assert (Hpc6a : add_vec_int (mword_of_int (KernelSyms.devintr + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x6a)) by pcw.
    iEval (rewrite Hpc6a) in "Hpc".
    (* ---- +0x6a: c.ldsp s1,8(sp) -- put the caller's s1 back ---- *)
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup HcsC csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      rewrite /T0 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa3) in "Hb3".
    iPoseProof (dii_6a with "Htext") as "Hi6a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x6a)) (mword_of_int 1 : mword 6) s1_idx
              T2 k s10 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a Hb3").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
    set (T3 := <[Regidx s1_idx := regval_into_reg s10]> T2).
    change (<[Regidx s1_idx := regval_into_reg s10]> T2) with T3.
    iEval (rewrite Hpa3) in "Hb3".
    assert (Hpc6c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x6a) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x6c)) by pcw.
    iEval (rewrite Hpc6c) in "Hpc".
    (* ---- +0x6c: c.j -0x4a, to the common epilogue ---- *)
    iPoseProof (dii_6c with "Htext") as "Hi6c".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.devintr + 0x6c))
              (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")))
              T3 k false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi6c").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hjback : add_vec (mword_of_int (KernelSyms.devintr + 0x6c) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.devintr + 0x22)) by pcw.
    iEval (rewrite Hjback) in "Hpc".
    (* ---- the epilogue ---- *)
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /T3 upd_ne; [| vm_compute; discriminate]. exact HT2sp. }
    assert (HT3a0 : T3 !!! Regidx a0_idx = devintr_ret sc).
    { rewrite Hret. rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2. apply upd_eq. }
    assert (HT3thr : di_thr m0 T3).
    { intros r Hr Ncsp N8.
      destruct (decide (r = (mword_of_int 9 : mword 5))) as [->|N9].
      - rewrite /T3 upd_eq. exact (eq_sym Hm0s1).
      - assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /T3 upd_ne; [| congruence].
        rewrite /T2 upd_ne; [| congruence].
        rewrite (callee_saved_lookup HcsC r Hr).
        rewrite /T1 upd_ne; [| congruence].
        rewrite /T0 upd_ne; [| congruence].
        exact (Hthr r Hr Ncsp N8 N9). }
    iApply (di_epi m0 T3 sp0 ra0 s00 (devintr_ret sc) k lvl eb p C dq sc s10 v4 lks
              Hm0sp Hm0ra Hm0s0 HT3sp HT3a0 HT3thr
              with "Hcg Hcnt Htext Hpc Hsc Hb1 Hb2 Hb3 Hb4 Hcont").
  Qed.

  (* ================================================================== *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ================================================================== *)
  Lemma wp_devintr_sconf
      (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
      (γs : list gname) (pd pav pu : mword 64)
      (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (dq : dfrac) (sc : mword 64) (lks : gset string)
    : wp_devintr_sconf_body γu γv γdk γtl γs pd pav pu m av lvl eb p C dq sc lks.
  Proof.
    cbv beta delta [wp_devintr_sconf_body].
    intros pcE ret_tgt Hlen Hlvl Hav Hbelow.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (ra0 := (m !!! Regidx ra_idx : mword 64)).
    set (s00 := (m !!! Regidx s0_idx : mword 64)).
    set (s10 := (m !!! Regidx s1_idx : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hsc #Hcaps".
    iDestruct "Hcaps" as "(#Hdev & #Hccaps & #Hgeom & #Hdlk & #Htcap & #Htk & #Hpinv & #Hpanic)".
    iIntros "Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (dii_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 false
              ltac:(unfold devintr_stack in Hav; lia) Hpush
              with "Hcg Hpc Hi00").
    iApply wp_next_off_intro. iIntros "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A0 upd_eq; exact Hpush).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x02)) by pcw.
    iEval (rewrite Hpc02) in "Hpc".
    iDestruct (stack_own_4_elim with "Hframe") as (w1 w2 w3 w4) "(Hb1 & Hb2 & Hb3 & Hb4)".
    assert (Hpa1 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa3 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iEval (rewrite -Hpa2) in "Hb2".
    (* ---- +0x02: c.sdsp ra,24(sp) ---- *)
    iPoseProof (dii_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x02)) (mword_of_int 3 : mword 6) ra_idx
              A0 (av - 4)%nat w1 false
              with "Hcg Hpc Hi02 Hb1").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb1".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x04)) by pcw.
    iEval (rewrite Hpc04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,16(sp) ---- *)
    iPoseProof (dii_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x04)) (mword_of_int 2 : mword 6) s0_idx
              A0 (av - 4)%nat w2 false
              with "Hcg Hpc Hi04 Hb2").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hb2".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x06)) by pcw.
    iEval (rewrite Hpc06) in "Hpc".
    assert (HA0ra : A0 !!! Regidx ra_idx = ra0)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s0 : A0 !!! Regidx s0_idx = s00)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0rag : rget A0 ra_idx = ra0) by (rgne; exact HA0ra).
    assert (HA0s0g : rget A0 s0_idx = s00) by (rgne; exact HA0s0).
    iEval (rewrite Hpa1 HA0rag) in "Hb1".
    iEval (rewrite Hpa2 HA0s0g) in "Hb2".
    (* ---- +0x06: c.addi4spn s0,sp,32 ---- *)
    iPoseProof (dii_06 with "Htext") as "Hi06".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.devintr + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) s0_idx A0 (av - 4)%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A1 := <[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x08)) by pcw.
    iEval (rewrite Hpc08) in "Hpc".
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HA0sp | vm_compute; discriminate]).
    (* the callee-saved registers devintr has not touched, at A1 *)
    assert (HA1thr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
              A1 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    (* ===================== +0x08: csrr a4,scause ===================== *)
    iPoseProof (dii_08 with "Htext") as "Hi08".
    iApply (wp_csrr_scause_s_sconf (mword_of_int (KernelSyms.devintr + 0x08)) a4_idx
              A1 (av - 4)%nat dq sc
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hsc Hpc Hi08").
    iApply wp_next_off_intro. iIntros "Hcg Hsc Hpc".
    set (A2 := <[Regidx a4_idx := regval_into_reg sc]> A1).
    change (<[Regidx a4_idx := regval_into_reg sc]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x08) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x0c)) by pcw.
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HA2a4 : rget A2 a4_idx = sc) by (rgne; rewrite /A2 upd_eq; reflexivity).
    assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A2 upd_ne; [exact HA1sp | vm_compute; discriminate]).
    assert (HA2thr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
              A2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N14 : r <> mword_of_int 14)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A2 upd_ne; [| congruence]. exact (HA1thr r Hr Ncsp N8). }
    (* ---- +0x0c .. +0x10: a5 := 0x8000000000000009 ---- *)
    iPoseProof (dii_0c with "Htext") as "Hi0c".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x0c)) a5_idx (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) A2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A3 := <[Regidx a5_idx := regval_into_reg (mword_of_int (-1) : mword 64)]> A2).
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int (-1) : mword 64)]> A2) with A3.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.devintr + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x0e)) by pcw.
    iEval (rewrite Hpc0e) in "Hpc".
    assert (HA3a5 : rget A3 a5_idx = (mword_of_int (-1) : mword 64))
      by (rgne; rewrite /A3 upd_eq; reflexivity).
    iPoseProof (dii_0e with "Htext") as "Hi0e".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.devintr + 0x0e)) (Regidx a5_idx) a5_idx
              (mword_of_int 63 : mword 6) A3 (av - 4)%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A4 := <[Regidx a5_idx := regval_into_reg
        (shift_bits_left (rget A3 a5_idx) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> A3).
    change (<[Regidx a5_idx := regval_into_reg
        (shift_bits_left (rget A3 a5_idx) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> A3) with A4.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x10)) by pcw.
    iEval (rewrite Hpc10) in "Hpc".
    assert (HA4a5 : rget A4 a5_idx = (mword_of_int 0x8000000000000000 : mword 64)).
    { rgne. rewrite /A4 upd_eq. rewrite HA3a5. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (dii_10 with "Htext") as "Hi10".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.devintr + 0x10)) a5_idx (mword_of_int 9 : mword 6)
              A4 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A5 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget A4 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 9 : mword 6))))]> A4).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget A4 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 9 : mword 6))))]> A4) with A5.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x12)) by pcw.
    iEval (rewrite Hpc12) in "Hpc".
    assert (HA5a5 : rget A5 a5_idx = (mword_of_int SCAUSE_SEXT : mword 64)).
    { rgne. rewrite /A5 upd_eq. rewrite HA4a5. apply bv_eq; vm_compute; reflexivity. }
    assert (HA5a4 : rget A5 a4_idx = sc).
    { rgne. rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_eq. reflexivity. }
    assert (HA5sp : A5 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate]. exact HA2sp. }
    assert (HA5thr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
              A5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N15 : r <> mword_of_int 15)
        by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence]. exact (HA2thr r Hr Ncsp N8). }
    iPoseProof (dii_12 with "Htext") as "Hi12".
    (* ===================== THE EXTERNAL-INTERRUPT TEST ===================== *)
    destruct (eq_vec sc (mword_of_int SCAUSE_SEXT : mword 64)) eqn:Hext.
    - (* ------------------- scause == 0x...9: the PLIC arm ---------------- *)
      assert (Hcmp : eq_vec (rget A5 a4_idx) (rget A5 a5_idx) = true)
        by (rewrite HA5a4 HA5a5; exact Hext).
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.devintr + 0x12)) (mword_of_int 24 : mword 13)
                a5_idx a4_idx A5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi12").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hj2a : add_vec (mword_of_int (KernelSyms.devintr + 0x12) : mword 64)
                       (sign_extend' 64 (mword_of_int 24 : mword 13))
                     = mword_of_int (KernelSyms.devintr + 0x2a)) by pcw.
      iEval (rewrite Hj2a) in "Hpc".
      (* ---- +0x2a: c.sdsp s1,8(sp) -- the shrink-wrapped save ---- *)
      assert (Hpa3' : add_vec (A5 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
      { rewrite HA5sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      iEval (rewrite -Hpa3') in "Hb3".
      iPoseProof (dii_2a with "Htext") as "Hi2a".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x2a)) (mword_of_int 1 : mword 6) s1_idx
                A5 (av - 4)%nat w3 false
                with "Hcg Hpc Hi2a Hb3").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
      assert (HA5s1g : rget A5 s1_idx = s10)
        by (rgne; exact (HA5thr s1_idx ltac:(vm_compute; reflexivity)
                            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate))).
      iEval (rewrite Hpa3' HA5s1g) in "Hb3".
      assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x2c)) by pcw.
      iEval (rewrite Hpc2c) in "Hpc".
      (* ---- +0x2c: jal ra,plic_claim ---- *)
      iPoseProof (dii_2c with "Htext") as "Hi2c".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.devintr + 0x2c)) ra_idx (mword_of_int 12416 : mword 21)
                A5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B0 := <[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.devintr + 0x2c) : mword 64) 4)]> A5).
      change (<[Regidx ra_idx := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.devintr + 0x2c) : mword 64) 4)]> A5) with B0.
      assert (Hjclaim : add_vec (mword_of_int (KernelSyms.devintr + 0x2c) : mword 64)
                          (sign_extend' 64 (mword_of_int 12416 : mword 21))
                        = mword_of_int KernelSyms.plic_claim) by pcw.
      iEval (rewrite Hjclaim) in "Hpc".
      assert (HB0ra : B0 !!! Regidx ra_idx
                      = add_vec_int (mword_of_int (KernelSyms.devintr + 0x2c) : mword 64) 4)
        by (rewrite /B0 upd_eq; reflexivity).
      (* ===================== plic_claim() ===================== *)
      iApply (PlicClaim.wp_plic_claim_sconf γu γv B0 (av - 4)%nat p
                (di_tp_bound B0) ltac:(unfold devintr_stack in Hav; lia)
                with "Hcg Htext Hpc Hdev").
      iIntros (MK) "Hcg Hpc %HcsK".
      destruct HcsK as (HcsK & HraK & Hok).
      assert (Hpc30 : ret_pc (B0 !!! Regidx ra_idx) = mword_of_int (KernelSyms.devintr + 0x30))
        by (rewrite HB0ra; pcw).
      iEval (rewrite Hpc30) in "Hpc".
      set (irq := (MK !!! Regidx a0_idx : mword 64)).
      assert (HMKsp : MK !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite (callee_saved_lookup HcsK csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact HA5sp. }
      assert (HMKthr : forall r : mword 5, is_cs_idx r = true ->
                r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                MK !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8.
        assert (N1 : r <> mword_of_int 1)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite (callee_saved_lookup HcsK r Hr).
        rewrite /B0 upd_ne; [| congruence]. exact (HA5thr r Hr Ncsp N8). }
      (* ---- +0x30: c.mv a4,a0 ---- *)
      iPoseProof (dii_30 with "Htext") as "Hi30".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.devintr + 0x30)) a4_idx a0_idx MK (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B1 := <[Regidx a4_idx := regval_into_reg (add_vec zero_reg (rget MK a0_idx))]> MK).
      change (<[Regidx a4_idx := regval_into_reg (add_vec zero_reg (rget MK a0_idx))]> MK) with B1.
      assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x32)) by pcw.
      iEval (rewrite Hpc32) in "Hpc".
      assert (HMKa0g : rget MK a0_idx = irq) by (rgne; reflexivity).
      assert (HB1a4 : rget B1 a4_idx = irq).
      { rgne. rewrite /B1 upd_eq. rewrite HMKa0g. apply add_vec_zero_l. }
      (* ---- +0x32: c.mv s1,a0 ---- *)
      iPoseProof (dii_32 with "Htext") as "Hi32".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.devintr + 0x32)) s1_idx a0_idx B1 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B2 := <[Regidx s1_idx := regval_into_reg (add_vec zero_reg (rget B1 a0_idx))]> B1).
      change (<[Regidx s1_idx := regval_into_reg (add_vec zero_reg (rget B1 a0_idx))]> B1) with B2.
      assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x34)) by pcw.
      iEval (rewrite Hpc34) in "Hpc".
      assert (HB1a0g : rget B1 a0_idx = irq).
      { rgne. rewrite /B1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
      assert (HB2s1 : B2 !!! Regidx s1_idx = irq).
      { rewrite /B2 upd_eq. rewrite HB1a0g. apply add_vec_zero_l. }
      assert (HB2a0 : rget B2 a0_idx = irq).
      { rgne. rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
      assert (HB2a4 : rget B2 a4_idx = irq).
      { rgne. rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite -HB1a4. rgne. reflexivity. }
      assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact HMKsp. }
      assert (HB2thr : forall r : mword 5, is_cs_idx r = true ->
                r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                r <> (mword_of_int 9 : mword 5) -> B2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9.
        assert (N14 : r <> mword_of_int 14)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B2 upd_ne; [| congruence].
        rewrite /B1 upd_ne; [| congruence]. exact (HMKthr r Hr Ncsp N8). }
      (* ---- +0x34: c.li a5,10 ---- *)
      iPoseProof (dii_34 with "Htext") as "Hi34".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x34)) a5_idx (mword_of_int 10 : mword 6)
                (mword_of_int 10 : mword 64) B2 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi34").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (B3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 10 : mword 64)]> B2).
      change (<[Regidx a5_idx := regval_into_reg (mword_of_int 10 : mword 64)]> B2) with B3.
      assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x36)) by pcw.
      iEval (rewrite Hpc36) in "Hpc".
      assert (HB3a5 : rget B3 a5_idx = (mword_of_int 10 : mword 64))
        by (rgne; rewrite /B3 upd_eq; reflexivity).
      assert (HB3a0 : rget B3 a0_idx = irq).
      { rgne. rewrite /B3 upd_ne; [| vm_compute; discriminate]. rewrite -HB2a0. rgne. reflexivity. }
      assert (HB3a4 : rget B3 a4_idx = irq).
      { rgne. rewrite /B3 upd_ne; [| vm_compute; discriminate]. rewrite -HB2a4. rgne. reflexivity. }
      assert (HB3s1 : B3 !!! Regidx s1_idx = irq)
        by (rewrite /B3 upd_ne; [exact HB2s1 | vm_compute; discriminate]).
      assert (HB3sp : B3 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /B3 upd_ne; [exact HB2sp | vm_compute; discriminate]).
      assert (HB3thr : forall r : mword 5, is_cs_idx r = true ->
                r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                r <> (mword_of_int 9 : mword 5) -> B3 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9.
        assert (N15 : r <> mword_of_int 15)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /B3 upd_ne; [| congruence]. exact (HB2thr r Hr Ncsp N8 N9). }
      iPoseProof (dii_36 with "Htext") as "Hi36".
      (* the return value on every path out of this arm *)
      assert (Hret1 : devintr_ret sc = (mword_of_int 1 : mword 64))
        by (unfold devintr_ret; rewrite Hext; reflexivity).
      (* ===================== THE THREE-WAY irq DISPATCH ===================== *)
      unfold plic_claim_a0_ok in Hok.
      destruct Hok as [H0 | [Huart | Hvirt]].
      + (* ---------------- irq = 0: nothing to serve ---------------- *)
        assert (Hirq0 : irq = (mword_of_int 0 : mword 64)) by exact H0.
        assert (Hne10 : eq_vec (rget B3 a0_idx) (rget B3 a5_idx) = false).
        { rewrite HB3a0 HB3a5 Hirq0. vm_compute. reflexivity. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x36)) (mword_of_int 18 : mword 13)
                  a5_idx a0_idx B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hne10
                  with "Hcg Hpc Hi36").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.devintr + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x3a)) by pcw.
        iEval (rewrite Hpc3a) in "Hpc".
        (* +0x3a: c.li a5,1 *)
        iPoseProof (dii_3a with "Htext") as "Hi3a".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x3a)) a5_idx (mword_of_int 1 : mword 6)
                  (mword_of_int 1 : mword 64) B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi3a").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (B4 := <[Regidx a5_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B3).
        change (<[Regidx a5_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B3) with B4.
        assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x3c)) by pcw.
        iEval (rewrite Hpc3c) in "Hpc".
        assert (HB4a5 : rget B4 a5_idx = (mword_of_int 1 : mword 64))
          by (rgne; rewrite /B4 upd_eq; reflexivity).
        assert (HB4a0 : rget B4 a0_idx = irq).
        { rgne. rewrite /B4 upd_ne; [| vm_compute; discriminate]. rewrite -HB3a0. rgne. reflexivity. }
        assert (HB4a4 : rget B4 a4_idx = irq).
        { rgne. rewrite /B4 upd_ne; [| vm_compute; discriminate]. rewrite -HB3a4. rgne. reflexivity. }
        assert (Hne1 : eq_vec (rget B4 a0_idx) (rget B4 a5_idx) = false).
        { rewrite HB4a0 HB4a5 Hirq0. vm_compute. reflexivity. }
        iPoseProof (dii_3c with "Htext") as "Hi3c".
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x3c)) (mword_of_int 18 : mword 13)
                  a5_idx a0_idx B4 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hne1
                  with "Hcg Hpc Hi3c").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc40 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x40)) by pcw.
        iEval (rewrite Hpc40) in "Hpc".
        (* +0x40: c.li a0,1 *)
        iPoseProof (dii_40 with "Htext") as "Hi40".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x40)) a0_idx (mword_of_int 1 : mword 6)
                  (mword_of_int 1 : mword 64) B4 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi40").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (B5 := <[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B4).
        change (<[Regidx a0_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B4) with B5.
        assert (Hpc42 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x42)) by pcw.
        iEval (rewrite Hpc42) in "Hpc".
        (* +0x42: c.bnez a4 -- THE DEAD printk ARM.  a4 = irq = 0. *)
        assert (HB5a4 : rget B5 a4_idx = irq).
        { rgne. rewrite /B5 upd_ne; [| vm_compute; discriminate]. rewrite -HB4a4. rgne. reflexivity. }
        assert (Hbnez : neq_vec (rget B5 a4_idx) zero_reg = false).
        { rewrite HB5a4 Hirq0. vm_compute. reflexivity. }
        iPoseProof (dii_42 with "Htext") as "Hi42".
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x42)) (mword_of_int 9 : mword 8)
                  (Cregidx (mword_of_int 6)) a4_idx B5 (av - 4)%nat false
                  creg_c6 ltac:(vm_compute; discriminate) Hbnez
                  with "Hcg Hpc Hi42").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc44 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x44)) by pcw.
        iEval (rewrite Hpc44) in "Hpc".
        (* +0x44: c.ldsp s1,8(sp) *)
        assert (HB5sp : B5 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /B5 upd_ne; [| vm_compute; discriminate].
          rewrite /B4 upd_ne; [| vm_compute; discriminate]. exact HB3sp. }
        assert (Hpa3b : add_vec (B5 !!! Regidx csp_rs1)
                          (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
        { rewrite HB5sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
          f_equal; try (apply bv_eq; vm_compute; reflexivity). }
        iEval (rewrite -Hpa3b) in "Hb3".
        iPoseProof (dii_44 with "Htext") as "Hi44".
        iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.devintr + 0x44)) (mword_of_int 1 : mword 6) s1_idx
                  B5 (av - 4)%nat s10 false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi44 Hb3").
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hb3".
        set (B6 := <[Regidx s1_idx := regval_into_reg s10]> B5).
        change (<[Regidx s1_idx := regval_into_reg s10]> B5) with B6.
        iEval (rewrite Hpa3b) in "Hb3".
        assert (Hpc46 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x46)) by pcw.
        iEval (rewrite Hpc46) in "Hpc".
        (* +0x46: c.j -0x24, to the epilogue *)
        iPoseProof (dii_46 with "Htext") as "Hi46".
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.devintr + 0x46))
                  (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")))
                  B6 (av - 4)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi46").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjb1 : add_vec (mword_of_int (KernelSyms.devintr + 0x46) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.devintr + 0x22)) by pcw.
        iEval (rewrite Hjb1) in "Hpc".
        assert (HB6sp : B6 !!! Regidx csp_rs1 = pa_stk sp0 4)
          by (rewrite /B6 upd_ne; [exact HB5sp | vm_compute; discriminate]).
        assert (HB6a0 : B6 !!! Regidx a0_idx = devintr_ret sc).
        { rewrite Hret1. rewrite /B6 upd_ne; [| vm_compute; discriminate].
          rewrite /B5. apply upd_eq. }
        assert (HB6thr : di_thr m B6).
        { intros r Hr Ncsp N8.
          destruct (decide (r = (mword_of_int 9 : mword 5))) as [->|N9].
          - rewrite /B6 upd_eq. reflexivity.
          - assert (N10 : r <> mword_of_int 10)
              by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N15 : r <> mword_of_int 15)
              by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /B6 upd_ne; [| congruence].
            rewrite /B5 upd_ne; [| congruence].
            rewrite /B4 upd_ne; [| congruence]. exact (HB3thr r Hr Ncsp N8 N9). }
        iApply (di_epi m B6 sp0 ra0 s00 (devintr_ret sc) (av - 4)%nat lvl eb p C dq sc s10 w4 lks
                  eq_refl eq_refl eq_refl HB6sp HB6a0 HB6thr
                  with "Hcg Hcnt Htext Hpc Hsc Hb1 Hb2 Hb3 Hb4").
        iIntros (mf) "%Hf Hcg Hcnt Hsc Hpc".
        replace (av - 4 + 4)%nat with av by (unfold devintr_stack in Hav; lia).
        iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hsc Hpc"). exact Hf.
      + (* ---------------- irq = uart_irq_id = 10 ---------------- *)
        assert (Hirq10 : irq = (mword_of_int 10 : mword 64)).
        { etransitivity; [ exact Huart | apply bv_eq; vm_compute; reflexivity ]. }
        assert (Heq10 : eq_vec (rget B3 a0_idx) (rget B3 a5_idx) = true).
        { rewrite HB3a0 HB3a5 Hirq10. apply eq_vec_true_iff. reflexivity. }
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.devintr + 0x36)) (mword_of_int 18 : mword 13)
                  a5_idx a0_idx B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Heq10 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi36").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hj48 : add_vec (mword_of_int (KernelSyms.devintr + 0x36) : mword 64)
                         (sign_extend' 64 (mword_of_int 18 : mword 13))
                       = mword_of_int (KernelSyms.devintr + 0x48)) by pcw.
        iEval (rewrite Hj48) in "Hpc".
        (* +0x48: jal ra,uartintr *)
        iPoseProof (dii_48 with "Htext") as "Hi48".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.devintr + 0x48)) ra_idx (mword_of_int 2090040 : mword 21)
                  B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi48").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (U0 := <[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x48) : mword 64) 4)]> B3).
        change (<[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x48) : mword 64) 4)]> B3) with U0.
        assert (Hjui : add_vec (mword_of_int (KernelSyms.devintr + 0x48) : mword 64)
                         (sign_extend' 64 (mword_of_int 2090040 : mword 21))
                       = mword_of_int KernelSyms.uartintr) by pcw.
        iEval (rewrite Hjui) in "Hpc".
        assert (HU0ra : U0 !!! Regidx ra_idx
                        = add_vec_int (mword_of_int (KernelSyms.devintr + 0x48) : mword 64) 4)
          by (rewrite /U0 upd_eq; reflexivity).
        iApply (Uartintr.wp_uartintr_sconf γu γv γs U0 (av - 4)%nat lvl eb p C false
                  _ Hlen ltac:(lia) ltac:(unfold devintr_stack, uartintr_stack in *; lia)
                  with "Hcg Hcnt Htext Hpc Hdev Hpinv Hpanic Hccaps").
        all: try lkbelow.
        iApply wp_next_off_intro. iIntros (MU) "%HcsU Hcg Hcnt Hpc".
        destruct HcsU as [HcsU HdomU].
        assert (Hpc4c : ret_pc (U0 !!! Regidx ra_idx) = mword_of_int (KernelSyms.devintr + 0x4c))
          by (rewrite HU0ra; pcw).
        iEval (rewrite Hpc4c) in "Hpc".
        (* +0x4c: c.j +0x16, to the plic_complete tail *)
        iPoseProof (dii_4c with "Htext") as "Hi4c".
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.devintr + 0x4c))
                  (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")))
                  MU (av - 4)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4c").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hj62 : add_vec (mword_of_int (KernelSyms.devintr + 0x4c) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.devintr + 0x62)) by pcw.
        iEval (rewrite Hj62) in "Hpc".
        assert (HcsU0 : callee_saved B3 U0).
        { rewrite /U0. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        assert (HcsB3MU : callee_saved B3 MU) by (apply (callee_saved_trans B3 U0 MU HcsU0 HcsU)).
        assert (HMUsp : MU !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite (callee_saved_lookup HcsB3MU csp_rs1 ltac:(vm_compute; reflexivity)). exact HB3sp. }
        assert (HMUs1 : MU !!! Regidx s1_idx = irq).
        { rewrite (callee_saved_lookup HcsB3MU s1_idx ltac:(vm_compute; reflexivity)). exact HB3s1. }
        assert (HMUthr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                  r <> (mword_of_int 9 : mword 5) -> MU !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9.
          rewrite (callee_saved_lookup HcsB3MU r Hr). exact (HB3thr r Hr Ncsp N8 N9). }
        iApply (di_plic_tail γu γv m MU sp0 ra0 s00 s10 irq (av - 4)%nat lvl eb p C dq sc w4 lks
                  ltac:(unfold devintr_stack in Hav; lia) eq_refl eq_refl eq_refl eq_refl
                  HMUsp HMUs1 HMUthr Hret1
                  with "Hcg Hcnt Htext Hpc Hsc Hdev Hb1 Hb2 Hb3 Hb4").
        iIntros (mf) "%Hf Hcg Hcnt Hsc Hpc".
        replace (av - 4 + 4)%nat with av by (unfold devintr_stack in Hav; lia).
        iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hsc Hpc"). exact Hf.
      + (* ---------------- irq = virtio_irq_id = 1 ---------------- *)
        assert (Hirq1 : irq = (mword_of_int 1 : mword 64)).
        { etransitivity; [ exact Hvirt | apply bv_eq; vm_compute; reflexivity ]. }
        assert (Hne10 : eq_vec (rget B3 a0_idx) (rget B3 a5_idx) = false).
        { rewrite HB3a0 HB3a5 Hirq1. vm_compute. reflexivity. }
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x36)) (mword_of_int 18 : mword 13)
                  a5_idx a0_idx B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hne10
                  with "Hcg Hpc Hi36").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc3a : add_vec_int (mword_of_int (KernelSyms.devintr + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x3a)) by pcw.
        iEval (rewrite Hpc3a) in "Hpc".
        (* +0x3a: c.li a5,1 *)
        iPoseProof (dii_3a with "Htext") as "Hi3a".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x3a)) a5_idx (mword_of_int 1 : mword 6)
                  (mword_of_int 1 : mword 64) B3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi3a").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (V0 := <[Regidx a5_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B3).
        change (<[Regidx a5_idx := regval_into_reg (mword_of_int 1 : mword 64)]> B3) with V0.
        assert (Hpc3c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x3c)) by pcw.
        iEval (rewrite Hpc3c) in "Hpc".
        assert (HV0a5 : rget V0 a5_idx = (mword_of_int 1 : mword 64))
          by (rgne; rewrite /V0 upd_eq; reflexivity).
        assert (HV0a0 : rget V0 a0_idx = irq).
        { rgne. rewrite /V0 upd_ne; [| vm_compute; discriminate]. rewrite -HB3a0. rgne. reflexivity. }
        assert (Heq1 : eq_vec (rget V0 a0_idx) (rget V0 a5_idx) = true).
        { rewrite HV0a0 HV0a5 Hirq1. apply eq_vec_true_iff. reflexivity. }
        iPoseProof (dii_3c with "Htext") as "Hi3c".
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.devintr + 0x3c)) (mword_of_int 18 : mword 13)
                  a5_idx a0_idx V0 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Heq1 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3c").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hj4e : add_vec (mword_of_int (KernelSyms.devintr + 0x3c) : mword 64)
                         (sign_extend' 64 (mword_of_int 18 : mword 13))
                       = mword_of_int (KernelSyms.devintr + 0x4e)) by pcw.
        iEval (rewrite Hj4e) in "Hpc".
        assert (HV0sp : V0 !!! Regidx csp_rs1 = pa_stk sp0 4)
          by (rewrite /V0 upd_ne; [exact HB3sp | vm_compute; discriminate]).
        assert (HV0s1 : V0 !!! Regidx s1_idx = irq)
          by (rewrite /V0 upd_ne; [exact HB3s1 | vm_compute; discriminate]).
        assert (HV0thr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                  r <> (mword_of_int 9 : mword 5) -> V0 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9.
          assert (N15 : r <> mword_of_int 15)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /V0 upd_ne; [| congruence]. exact (HB3thr r Hr Ncsp N8 N9). }
        (* +0x4e: jal ra,virtio_disk_intr *)
        iPoseProof (dii_4e with "Htext") as "Hi4e".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.devintr + 0x4e)) ra_idx (mword_of_int 13590 : mword 21)
                  V0 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi4e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (V1 := <[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x4e) : mword 64) 4)]> V0).
        change (<[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x4e) : mword 64) 4)]> V0) with V1.
        assert (Hjvi : add_vec (mword_of_int (KernelSyms.devintr + 0x4e) : mword 64)
                         (sign_extend' 64 (mword_of_int 13590 : mword 21))
                       = mword_of_int KernelSyms.virtio_disk_intr) by pcw.
        iEval (rewrite Hjvi) in "Hpc".
        assert (HV1ra : V1 !!! Regidx ra_idx
                        = add_vec_int (mword_of_int (KernelSyms.devintr + 0x4e) : mword 64) 4)
          by (rewrite /V1 upd_eq; reflexivity).
        iApply (VirtioDiskIntr.wp_virtio_disk_intr_sconf γs γu γv γdk pd pav pu
                  V1 (av - 4)%nat lvl eb p C false lks
                  ltac:(unfold devintr_stack, K_virtio_disk_intr in *; lia)
                  ltac:(intro r; apply rf_to_gmap_dom) Hlen ltac:(lia)
                  ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Hpanic Hpinv Hdev Hgeom Hdlk").
        all: try lkbelow.
        iApply wp_next_off_intro. iIntros (MV) "%HcsV Hcg Hcnt Htext2 Hpc".
        destruct HcsV as [HcsV HdomV].
        assert (Hpc52 : ret_pc (V1 !!! Regidx ra_idx) = mword_of_int (KernelSyms.devintr + 0x52))
          by (rewrite HV1ra; pcw).
        iEval (rewrite Hpc52) in "Hpc".
        (* +0x52: c.j +0x10, to the plic_complete tail *)
        iPoseProof (dii_52 with "Htext") as "Hi52".
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.devintr + 0x52))
                  (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")))
                  MV (av - 4)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi52").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hj62' : add_vec (mword_of_int (KernelSyms.devintr + 0x52) : mword 64)
                          (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0"))))
                        = mword_of_int (KernelSyms.devintr + 0x62)) by pcw.
        iEval (rewrite Hj62') in "Hpc".
        assert (HcsV1 : callee_saved V0 V1).
        { rewrite /V1. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        assert (HcsV0MV : callee_saved V0 MV) by (apply (callee_saved_trans V0 V1 MV HcsV1 HcsV)).
        assert (HMVsp : MV !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite (callee_saved_lookup HcsV0MV csp_rs1 ltac:(vm_compute; reflexivity)). exact HV0sp. }
        assert (HMVs1 : MV !!! Regidx s1_idx = irq).
        { rewrite (callee_saved_lookup HcsV0MV s1_idx ltac:(vm_compute; reflexivity)). exact HV0s1. }
        assert (HMVthr : forall r : mword 5, is_cs_idx r = true ->
                  r <> csp_rs1 -> r <> (mword_of_int 8 : mword 5) ->
                  r <> (mword_of_int 9 : mword 5) -> MV !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9.
          rewrite (callee_saved_lookup HcsV0MV r Hr). exact (HV0thr r Hr Ncsp N8 N9). }
        iApply (di_plic_tail γu γv m MV sp0 ra0 s00 s10 irq (av - 4)%nat lvl eb p C dq sc w4 lks
                  ltac:(unfold devintr_stack in Hav; lia) eq_refl eq_refl eq_refl eq_refl
                  HMVsp HMVs1 HMVthr Hret1
                  with "Hcg Hcnt Htext Hpc Hsc Hdev Hb1 Hb2 Hb3 Hb4").
        iIntros (mf) "%Hf Hcg Hcnt Hsc Hpc".
        replace (av - 4 + 4)%nat with av by (unfold devintr_stack in Hav; lia).
        iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hsc Hpc"). exact Hf.
    - (* ------------------- scause /= 0x...9 ------------------------------ *)
      assert (Hcmp : eq_vec (rget A5 a4_idx) (rget A5 a5_idx) = false)
        by (rewrite HA5a4 HA5a5; exact Hext).
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x12)) (mword_of_int 24 : mword 13)
                a5_idx a4_idx A5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc Hi12").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x16)) by pcw.
      iEval (rewrite Hpc16) in "Hpc".
      (* ---- +0x16 .. +0x1a: a5 := 0x8000000000000005 ---- *)
      iPoseProof (dii_16 with "Htext") as "Hi16".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x16)) a5_idx (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) A5 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi16").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T0 := <[Regidx a5_idx := regval_into_reg (mword_of_int (-1) : mword 64)]> A5).
      change (<[Regidx a5_idx := regval_into_reg (mword_of_int (-1) : mword 64)]> A5) with T0.
      assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x18)) by pcw.
      iEval (rewrite Hpc18) in "Hpc".
      assert (HT0a5 : rget T0 a5_idx = (mword_of_int (-1) : mword 64))
        by (rgne; rewrite /T0 upd_eq; reflexivity).
      iPoseProof (dii_18 with "Htext") as "Hi18".
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.devintr + 0x18)) (Regidx a5_idx) a5_idx
                (mword_of_int 63 : mword 6) T0 (av - 4)%nat false
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T1 := <[Regidx a5_idx := regval_into_reg
          (shift_bits_left (rget T0 a5_idx) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> T0).
      change (<[Regidx a5_idx := regval_into_reg
          (shift_bits_left (rget T0 a5_idx) (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))]> T0) with T1.
      assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.devintr + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x1a)) by pcw.
      iEval (rewrite Hpc1a) in "Hpc".
      assert (HT1a5 : rget T1 a5_idx = (mword_of_int 0x8000000000000000 : mword 64)).
      { rgne. rewrite /T1 upd_eq. rewrite HT0a5. apply bv_eq; vm_compute; reflexivity. }
      iPoseProof (dii_1a with "Htext") as "Hi1a".
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.devintr + 0x1a)) a5_idx (mword_of_int 5 : mword 6)
                T1 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T2 := <[Regidx a5_idx := regval_into_reg
          (add_vec (rget T1 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> T1).
      change (<[Regidx a5_idx := regval_into_reg
          (add_vec (rget T1 a5_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 5 : mword 6))))]> T1) with T2.
      assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.devintr + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x1c)) by pcw.
      iEval (rewrite Hpc1c) in "Hpc".
      assert (HT2a5 : rget T2 a5_idx = (mword_of_int SCAUSE_STIMER : mword 64)).
      { rgne. rewrite /T2 upd_eq. rewrite HT1a5. apply bv_eq; vm_compute; reflexivity. }
      (* ---- +0x1c: c.li a0,0 -- the "unrecognised" return value ---- *)
      iPoseProof (dii_1c with "Htext") as "Hi1c".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x1c)) a0_idx (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) T2 (av - 4)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi1c").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T3 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> T2).
      change (<[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> T2) with T3.
      assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.devintr + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x1e)) by pcw.
      iEval (rewrite Hpc1e) in "Hpc".
      assert (HT3a5 : rget T3 a5_idx = (mword_of_int SCAUSE_STIMER : mword 64)).
      { rgne. rewrite /T3 upd_ne; [| vm_compute; discriminate]. rewrite -HT2a5. rgne. reflexivity. }
      assert (HT3a4 : rget T3 a4_idx = sc).
      { rgne. rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1 upd_ne; [| vm_compute; discriminate].
        rewrite /T0 upd_ne; [| vm_compute; discriminate].
        rewrite -HA5a4. rgne. reflexivity. }
      assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4).
      { rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1 upd_ne; [| vm_compute; discriminate].
        rewrite /T0 upd_ne; [| vm_compute; discriminate]. exact HA5sp. }
      assert (HT3thr : di_thr m T3).
      { intros r Hr Ncsp N8.
        assert (N10 : r <> mword_of_int 10)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N15 : r <> mword_of_int 15)
          by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /T3 upd_ne; [| congruence].
        rewrite /T2 upd_ne; [| congruence].
        rewrite /T1 upd_ne; [| congruence].
        rewrite /T0 upd_ne; [| congruence]. exact (HA5thr r Hr Ncsp N8). }
      iPoseProof (dii_1e with "Htext") as "Hi1e".
      (* ===================== THE TIMER TEST ===================== *)
      destruct (eq_vec sc (mword_of_int SCAUSE_STIMER : mword 64)) eqn:Htim.
      + (* ------------- scause == 0x...5: clockintr ------------- *)
        assert (Hcmp5 : eq_vec (rget T3 a4_idx) (rget T3 a5_idx) = true)
          by (rewrite HT3a4 HT3a5; exact Htim).
        assert (Hret2 : devintr_ret sc = (mword_of_int 2 : mword 64))
          by (unfold devintr_ret; rewrite Hext Htim; reflexivity).
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.devintr + 0x1e)) (mword_of_int 80 : mword 13)
                  a5_idx a4_idx T3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp5 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1e").
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hj6e : add_vec (mword_of_int (KernelSyms.devintr + 0x1e) : mword 64)
                         (sign_extend' 64 (mword_of_int 80 : mword 13))
                       = mword_of_int (KernelSyms.devintr + 0x6e)) by pcw.
        iEval (rewrite Hj6e) in "Hpc".
        (* +0x6e: jal ra,clockintr *)
        iPoseProof (dii_6e with "Htext") as "Hi6e".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.devintr + 0x6e)) ra_idx (mword_of_int 2096956 : mword 21)
                  T3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi6e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (K0 := <[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x6e) : mword 64) 4)]> T3).
        change (<[Regidx ra_idx := regval_into_reg
            (add_vec_int (mword_of_int (KernelSyms.devintr + 0x6e) : mword 64) 4)]> T3) with K0.
        assert (Hjci : add_vec (mword_of_int (KernelSyms.devintr + 0x6e) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096956 : mword 21))
                       = mword_of_int KernelSyms.clockintr) by pcw.
        iEval (rewrite Hjci) in "Hpc".
        assert (HK0ra : K0 !!! Regidx ra_idx
                        = add_vec_int (mword_of_int (KernelSyms.devintr + 0x6e) : mword 64) 4)
          by (rewrite /K0 upd_eq; reflexivity).
        iApply (Clockintr.wp_clockintr_sconf γtl γs K0 lvl eb p C (av - 4)%nat lks
                  ltac:(lia) ltac:(unfold devintr_stack in Hav; lia) ltac:(lkbelow)
                  with "Hcg Hcnt Htext Hpc Htcap Htk").
        all: try lkbelow.
        iIntros (MC) "%HcsC Hcg Hcnt Hpc Htk2".
        assert (Hpc72 : ret_pc (K0 !!! Regidx ra_idx) = mword_of_int (KernelSyms.devintr + 0x72))
          by (rewrite HK0ra; pcw).
        iEval (rewrite Hpc72) in "Hpc".
        (* +0x72: c.li a0,2 *)
        iPoseProof (dii_72 with "Htext") as "Hi72".
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.devintr + 0x72)) a0_idx (mword_of_int 2 : mword 6)
                  (mword_of_int 2 : mword 64) MC (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi72").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (K1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 2 : mword 64)]> MC).
        change (<[Regidx a0_idx := regval_into_reg (mword_of_int 2 : mword 64)]> MC) with K1.
        assert (Hpc74 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.devintr + 0x74)) by pcw.
        iEval (rewrite Hpc74) in "Hpc".
        (* +0x74: c.j -0x52, to the epilogue *)
        iPoseProof (dii_74 with "Htext") as "Hi74".
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.devintr + 0x74))
                  (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")))
                  K1 (av - 4)%nat false ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi74").
        iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Hjb2 : add_vec (mword_of_int (KernelSyms.devintr + 0x74) : mword 64)
                         (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.devintr + 0x22)) by pcw.
        iEval (rewrite Hjb2) in "Hpc".
        assert (HcsK0 : callee_saved T3 K0).
        { rewrite /K0. apply callee_saved_insert_r; [vm_compute; reflexivity|].
          apply callee_saved_refl. }
        assert (HcsT3MC : callee_saved T3 MC) by (apply (callee_saved_trans T3 K0 MC HcsK0 HcsC)).
        assert (HK1sp : K1 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /K1 upd_ne; [| vm_compute; discriminate].
          rewrite (callee_saved_lookup HcsT3MC csp_rs1 ltac:(vm_compute; reflexivity)). exact HT3sp. }
        assert (HK1a0 : K1 !!! Regidx a0_idx = devintr_ret sc)
          by (rewrite Hret2; rewrite /K1; apply upd_eq).
        assert (HK1thr : di_thr m K1).
        { intros r Hr Ncsp N8.
          assert (N10 : r <> mword_of_int 10)
            by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /K1 upd_ne; [| congruence].
          rewrite (callee_saved_lookup HcsT3MC r Hr). exact (HT3thr r Hr Ncsp N8). }
        iApply (di_epi m K1 sp0 ra0 s00 (devintr_ret sc) (av - 4)%nat lvl eb p C dq sc w3 w4 lks
                  eq_refl eq_refl eq_refl HK1sp HK1a0 HK1thr
                  with "Hcg Hcnt Htext Hpc Hsc Hb1 Hb2 Hb3 Hb4").
        iIntros (mf) "%Hf Hcg Hcnt Hsc Hpc".
        replace (av - 4 + 4)%nat with av by (unfold devintr_stack in Hav; lia).
        iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hsc Hpc"). exact Hf.
      + (* ------------- neither: return 0 ------------- *)
        assert (Hcmp5 : eq_vec (rget T3 a4_idx) (rget T3 a5_idx) = false)
          by (rewrite HT3a4 HT3a5; exact Htim).
        assert (Hret0 : devintr_ret sc = (mword_of_int 0 : mword 64))
          by (unfold devintr_ret; rewrite Hext Htim; reflexivity).
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.devintr + 0x1e)) (mword_of_int 80 : mword 13)
                  a5_idx a4_idx T3 (av - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp5
                  with "Hcg Hpc Hi1e").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.devintr + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.devintr + 0x22)) by pcw.
        iEval (rewrite Hpc22) in "Hpc".
        assert (HT3a0 : T3 !!! Regidx a0_idx = devintr_ret sc)
          by (rewrite Hret0; rewrite /T3; apply upd_eq).
        iApply (di_epi m T3 sp0 ra0 s00 (devintr_ret sc) (av - 4)%nat lvl eb p C dq sc w3 w4 lks
                  eq_refl eq_refl eq_refl HT3sp HT3a0 HT3thr
                  with "Hcg Hcnt Htext Hpc Hsc Hb1 Hb2 Hb3 Hb4").
        iIntros (mf) "%Hf Hcg Hcnt Hsc Hpc".
        replace (av - 4 + 4)%nat with av by (unfold devintr_stack in Hav; lia).
        iApply ("Hcont" $! mf with "[%] Hcg Hcnt Hsc Hpc"). exact Hf.
  Qed.

End ProofDevintr.
End DevintrProof.
