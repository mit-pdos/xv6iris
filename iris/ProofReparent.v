(* ProofReparent.v -- reparent(p), the whole function, over sconf.

   Structurally this is wakeup's proc[] scan with a different body: instead of
   acquiring each proc's lock it reads the slot's [parent] cell out of
   [WaitInv.parents_own] (the caller already holds wait_lock, so no lock is
   taken anywhere here), and where wakeup wakes it CALLS wakeup.  So the loop
   invariant is hart-generic for the same reason -- the call may trap and resume
   the thread on another hart -- and it carries the partial map
   [rp_upto p ip k ps] as its one extra conjunct.

   THREE THINGS WORTH KNOWING.

   * THE TWO PATHS THROUGH AN ITERATION REACH THE TAIL AT THE SAME TABLE.  On
     the [bne]-taken path the cell was not equal to [p], and [rp_slot p ip v = v]
     there, so [rp_upto _ _ (S k) ps] is what BOTH arms hold at +0x2c -- the
     no-match arm by [list_insert_id], the store arm by [rp_upto_step].  That is
     what lets the p++/test tail be ONE [wp_next]-wrapped block rather than two.

   * THE FRAME IS SIX SLOTS AND EVERY ONE IS USED (ra/s0/s1/s2/s3/s4), so unlike
     wakeup's there is no padding cell to carry through untouched.

   * [initproc] IS RE-READ EVERY ITERATION.  The [ld a0,0(s4)] is inside the
     loop, so the fraction of the global travels through the loop invariant; it
     is what makes every reparented child get the same [ip]. *)
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import IntrDefs HartTp WpNext.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcGeom.
Require Import WaitInv.
Require Import CodeReparent.
Require Import SpecWakeup.
Require Import SpecReparent.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]).  Written
   name-free (durable-notes: an Ltac body cannot mention a hypothesis by
   literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* the scan's exit test, as an index fact.  Stated at the TOP LEVEL, with only
   [nat] in context: inside the loop the context is full of [bv_unsigned]s and
   the [bitvector.tactics] zify hook makes [lia] answer "Cannot find witness"
   (claude-notes/durable-notes.md). *)
Lemma rp_end_of_eq (k : nat) :
  (k < NPROC)%nat -> proc_addr (S k) = proc_addr NPROC -> S k = NPROC.
Proof. intro Hk. apply proc_addr_inj_le; lia. Qed.

(* reparent's 6-entry callee-save frame at spF+0 .. spF+40, in the [c.sdsp]
   leaf's own address form so the prologue's and the epilogue's cells unify
   without arithmetic.  Cell [u] holds, top down: ra(5) s0(4) s1(3) s2(2)
   s3(1) s4(0). *)
Definition rp_fcell (spF : mword 64) (u : Z) : mword 64 :=
  add_vec spF (zero_extend' 64 (concat_vec (mword_of_int u : mword 6) ('b"000"))).

Definition rp_frame `{XI : CurCtx} `{!riscvGS Σ} (spF : mword 64)
    (vra vs0 vs1 vs2 vs3 vs4 : mword 64) : iProp Σ :=
  (rp_fcell spF 5 ↦₈[KT1] vra ∗ rp_fcell spF 4 ↦₈[KT1] vs0 ∗ rp_fcell spF 3 ↦₈[KT1] vs1 ∗
   rp_fcell spF 2 ↦₈[KT1] vs2 ∗ rp_fcell spF 1 ↦₈[KT1] vs3 ∗ rp_fcell spF 0 ↦₈[KT1] vs4)%I.

(* the register shape the loop threads: the cursor, the frame pointer, the
   three loop constants, and the seven callee-saved registers reparent never
   touches. *)
Definition rpl_regs (M : regfile) (spF pv : mword 64)
    (vs5 vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (k : nat) : Prop :=
  M !!! Regidx (mword_of_int 9)  = proc_addr k /\
  M !!! Regidx (mword_of_int 2)  = spF /\
  M !!! Regidx (mword_of_int 18) = pv /\
  M !!! Regidx (mword_of_int 19) = proc_addr NPROC /\
  M !!! Regidx (mword_of_int 20) = (mword_of_int KernelSyms.initproc : mword 64) /\
  M !!! Regidx (mword_of_int 21) = vs5 /\
  M !!! Regidx (mword_of_int 22) = vs6 /\
  M !!! Regidx (mword_of_int 23) = vs7 /\
  M !!! Regidx (mword_of_int 24) = vs8 /\
  M !!! Regidx (mword_of_int 25) = vs9 /\
  M !!! Regidx (mword_of_int 26) = vs10 /\
  M !!! Regidx (mword_of_int 27) = vs11 /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).

(* the exit register shape: everything the epilogue does not restore. *)
Definition rpx_regs (M : regfile) (spF : mword 64)
    (vs5 vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) : Prop :=
  M !!! Regidx csp_rs1 = spF /\
  M !!! Regidx (mword_of_int 21) = vs5 /\
  M !!! Regidx (mword_of_int 22) = vs6 /\
  M !!! Regidx (mword_of_int 23) = vs7 /\
  M !!! Regidx (mword_of_int 24) = vs8 /\
  M !!! Regidx (mword_of_int 25) = vs9 /\
  M !!! Regidx (mword_of_int 26) = vs10 /\
  M !!! Regidx (mword_of_int 27) = vs11 /\
  (forall r : regidx, r ∈ dom (rf_to_gmap M)).

Module ReparentProof (Wakeup : WAKEUP) : REPARENT.

(* ===================================================================== *)
(* Prologue and epilogue: both run at a FIXED hart (no call in either),   *)
(* so [CID] can be a section variable.                                    *)
(* ===================================================================== *)
Section ProofReparentEnds.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* +0x00 .. +0x2a: carve the 6-slot frame, save ra/s0/s1..s4, set s0, park
     the argument in s2, materialise &proc[0] / &initproc / &proc[NPROC], and
     jump to the loop test at +0x34. *)
  Lemma rp_prologue (m : regfile) (K : nat)
      (b : bool) (pme : mword 64) :
    let sp0 : mword 64 := m !!! Regidx csp_rs1 in
    let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (6 <= K)%nat ->
    (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
    sie_cap_gpr KT1 m K b pme -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.reparent) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ rpl_regs M spF (m !!! Regidx (mword_of_int 10))
            (m !!! Regidx (mword_of_int 21)) (m !!! Regidx (mword_of_int 22))
            (m !!! Regidx (mword_of_int 23)) (m !!! Regidx (mword_of_int 24))
            (m !!! Regidx (mword_of_int 25)) (m !!! Regidx (mword_of_int 26))
            (m !!! Regidx (mword_of_int 27)) 0 ⌝ -∗
        sie_cap_gpr KT1 M (K - 6) b pme -∗
        pc_is (mword_of_int (KernelSyms.reparent + 0x34)) -∗
        rp_frame spF (m !!! Regidx (mword_of_int 1)) (m !!! Regidx (mword_of_int 8))
                     (m !!! Regidx (mword_of_int 9)) (m !!! Regidx (mword_of_int 18))
                     (m !!! Regidx (mword_of_int 19)) (m !!! Regidx (mword_of_int 20)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spF HK6 Hdom.
    iIntros "Hcg #Htext Hpc Hcont".
    (* +0x00 c.addi16sp sp,-48 : trade 6 slots out of the capability *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hsp1 : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                   = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spF) by (rewrite /R1 upd_eq; reflexivity).
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.reparent) (mword_of_int 61 : mword 6) m K 6 b HK6 Hsp1
              with "Hcg Hpc []").
    { iApply (rpi_00 with "Htext"). }
    iIntros (CID1 Hst1) "Hcg Hframe Hpc".
    assert (Hsp0f : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    iEval (rewrite Hsp0f (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(C1 & C2 & C3 & C4 & C5 & C6 & _)".
    iDestruct "C1" as (v1) "Hc1". iDestruct "C2" as (v2) "Hc2".
    iDestruct "C3" as (v3) "Hc3". iDestruct "C4" as (v4) "Hc4".
    iDestruct "C5" as (v5) "Hc5". iDestruct "C6" as (v6) "Hc6".
    (* the six cells at [pa_stk sp0 1..6] are [rp_fcell spF 5..0] *)
    assert (Hb5 : pa_stk sp0 1 = rp_fcell spF 5).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : pa_stk sp0 2 = rp_fcell spF 4).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : pa_stk sp0 3 = rp_fcell spF 3).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : pa_stk sp0 4 = rp_fcell spF 2).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : pa_stk sp0 5 = rp_fcell spF 1).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb0 : pa_stk sp0 6 = rp_fcell spF 0).
    { unfold rp_fcell, spF, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hb5) in "Hc1". iEval (rewrite Hb4) in "Hc2". iEval (rewrite Hb3) in "Hc3".
    iEval (rewrite Hb2) in "Hc4". iEval (rewrite Hb1) in "Hc5". iEval (rewrite Hb0) in "Hc6".
    assert (Hra : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0 : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1 : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2 : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3 : R1 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs4 : R1 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20)) by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.reparent : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    assert (Hra_rg : rget (CID := CID1) R1 (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rgne; exact Hra).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x02)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5) R1 (K - 6)%nat v1 b
              with "Hcg Hpc [] [Hc1]").
    { iApply (rpi_02 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc1". }
    iIntros (CID2 Hst2) "Hcg Hpc Hc1".
    iEval (rewrite HspR1 Hra_rg) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    assert (Hs0_rg : rget (CID := CID2) R1 (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rgne; exact Hs0).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x04)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5) R1 (K - 6)%nat v2 b
              with "Hcg Hpc [] [Hc2]").
    { iApply (rpi_04 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc2". }
    iIntros (CID3 Hst3) "Hcg Hpc Hc2".
    iEval (rewrite HspR1 Hs0_rg) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    assert (Hs1_rg : rget (CID := CID3) R1 (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rgne; exact Hs1).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x06)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5) R1 (K - 6)%nat v3 b
              with "Hcg Hpc [] [Hc3]").
    { iApply (rpi_06 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc3". }
    iIntros (CID4 Hst4) "Hcg Hpc Hc3".
    iEval (rewrite HspR1 Hs1_rg) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    assert (Hs2_rg : rget (CID := CID4) R1 (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rgne; exact Hs2).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x08)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5) R1 (K - 6)%nat v4 b
              with "Hcg Hpc [] [Hc4]").
    { iApply (rpi_08 with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc4". }
    iIntros (CID5 Hst5) "Hcg Hpc Hc4".
    iEval (rewrite HspR1 Hs2_rg) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.reparent + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    assert (Hs3_rg : rget (CID := CID5) R1 (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5))
      by (rgne; exact Hs3).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x0a)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5) R1 (K - 6)%nat v5 b
              with "Hcg Hpc [] [Hc5]").
    { iApply (rpi_0a with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc5". }
    iIntros (CID6 Hst6) "Hcg Hpc Hc5".
    iEval (rewrite HspR1 Hs3_rg) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.reparent + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.sdsp s4,0(sp) *)
    assert (Hs4_rg : rget (CID := CID6) R1 (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5))
      by (rgne; exact Hs4).
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x0c)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5) R1 (K - 6)%nat v6 b
              with "Hcg Hpc [] [Hc6]").
    { iApply (rpi_0c with "Htext"). }
    { iEval (rewrite HspR1). iExact "Hc6". }
    iIntros (CID7 Hst7) "Hcg Hpc Hc6".
    iEval (rewrite HspR1 Hs4_rg) in "Hc6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.reparent + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.reparent + 0x0e)) (Cregidx (mword_of_int 0)) (mword_of_int 12 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 6)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_0e with "Htext"). }
    iIntros (CID8 Hst8) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s2,a0 : s2 := p *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.reparent + 0x10)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5)
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_10 with "Htext"). }
    iIntros (CID9 Hst9) "Hcg Hpc".
    assert (Ha0_rg : rget (CID := CID8) R2 (mword_of_int 10 : mword 5) = R2 !!! Regidx (mword_of_int 10 : mword 5))
      by (rgne; reflexivity).
    iEval (rewrite Ha0_rg) in "Hcg".
    set (R3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (R2 !!! Regidx (mword_of_int 10 : mword 5)))]> R2).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 auipc s1,0x11 ; +0x16 addi s1,s1,1952 : s1 := &proc[0] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.reparent + 0x12)) (mword_of_int 9 : mword 5) (mword_of_int 0x11 : mword 20)
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_12 with "Htext"). }
    iIntros (CID10 Hst10) "Hcg Hpc".
    set (R4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.reparent + 0x12) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R3).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.reparent + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 2064 : mword 12)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_16 with "Htext"). }
    iIntros (CID11 Hst11) "Hcg Hpc".
    assert (Haddi_s1_rg : rget (CID := CID10) R4 (mword_of_int 9 : mword 5) = R4 !!! Regidx (mword_of_int 9 : mword 5))
      by (rgne; reflexivity).
    iEval (rewrite Haddi_s1_rg) in "Hcg".
    set (R5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (R4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 2064 : mword 12)))]> R4).
    assert (Hs1proc : R5 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr 0).
    { rewrite /R5 upd_eq. rewrite /R4 upd_eq. unfold proc_addr, proc_base, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.reparent + 0x16) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a auipc s4,0x8 ; +0x1e addi s4,s4,608 : s4 := &initproc *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.reparent + 0x1a)) (mword_of_int 20 : mword 5) (mword_of_int 0x8 : mword 20)
              R5 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_1a with "Htext"). }
    iIntros (CID12 Hst12) "Hcg Hpc".
    set (R6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.reparent + 0x1a) : mword 64) (auipc_off (mword_of_int 0x8 : mword 20)))]> R5).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.reparent + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.reparent + 0x1e)) (mword_of_int 20 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 720 : mword 12)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_1e with "Htext"). }
    iIntros (CID13 Hst13) "Hcg Hpc".
    assert (Haddi_s4_rg : rget (CID := CID12) R6 (mword_of_int 20 : mword 5) = R6 !!! Regidx (mword_of_int 20 : mword 5))
      by (rgne; reflexivity).
    iEval (rewrite Haddi_s4_rg) in "Hcg".
    set (R7 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec (R6 !!! Regidx (mword_of_int 20 : mword 5)) (sign_extend' 64 (mword_of_int 720 : mword 12)))]> R6).
    assert (Hs4init : R7 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.initproc : mword 64)).
    { rewrite /R7 upd_eq. rewrite /R6 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 auipc s3,0x16 ; +0x26 addi s3,s3,400 : s3 := &proc[NPROC] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.reparent + 0x22)) (mword_of_int 19 : mword 5) (mword_of_int 0x16 : mword 20)
              R7 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_22 with "Htext"). }
    iIntros (CID14 Hst14) "Hcg Hpc".
    set (R8 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.reparent + 0x22) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> R7).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.reparent + 0x26)) (mword_of_int 19 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 512 : mword 12)
              R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (rpi_26 with "Htext"). }
    iIntros (CID15 Hst15) "Hcg Hpc".
    assert (Haddi_s3_rg : rget (CID := CID14) R8 (mword_of_int 19 : mword 5) = R8 !!! Regidx (mword_of_int 19 : mword 5))
      by (rgne; reflexivity).
    iEval (rewrite Haddi_s3_rg) in "Hcg".
    set (R9 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (add_vec (R8 !!! Regidx (mword_of_int 19 : mword 5)) (sign_extend' 64 (mword_of_int 512 : mword 12)))]> R8).
    assert (Hs3end : R9 !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC).
    { rewrite /R9 upd_eq. rewrite /R8 upd_eq. unfold proc_addr, proc_base, NPROC, proc_size.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.reparent + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a c.j -> reparent+0x34 (loop test) *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.reparent + 0x2a))
              (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")))
              R9 (K - 6)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (rpi_2a with "Htext"). }
    iIntros (CID16 Hst16).
    iNext. iIntros "Hcg Hpc".
    assert (Htgtj : add_vec (mword_of_int (KernelSyms.reparent + 0x2a) : mword 64) (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")))) = mword_of_int (KernelSyms.reparent + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtj) in "Hpc".
    iSpecialize ("Hcont" $! CID16 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! R9 with "[%] Hcg Hpc [Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]").
    - (* rpl_regs R9 spF p ... 0 *)
      assert (Hthread : forall c : mword 5, c <> mword_of_int 8 -> c <> mword_of_int 9 ->
                c <> mword_of_int 18 -> c <> mword_of_int 19 -> c <> mword_of_int 20 ->
                c <> csp_rs1 -> R9 !!! Regidx c = m !!! Regidx c).
      { intros c N8 N9 N18 N19 N20 Ncsp.
        rewrite /R9 upd_ne; [| congruence].
        rewrite /R8 upd_ne; [| congruence].
        rewrite /R7 upd_ne; [| congruence].
        rewrite /R6 upd_ne; [| congruence].
        rewrite /R5 upd_ne; [| congruence].
        rewrite /R4 upd_ne; [| congruence].
        rewrite /R3 upd_ne; [| congruence].
        rewrite /R2 upd_ne; [| congruence].
        rewrite /R1 upd_ne; [reflexivity | congruence]. }
      unfold rpl_regs.
      repeat apply conj.
      + (* s1 = &proc[0] *)
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        rewrite /R7 upd_ne; [| vm_compute; discriminate].
        rewrite /R6 upd_ne; [| vm_compute; discriminate].
        exact Hs1proc.
      + (* sp = spF *)
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        rewrite /R7 upd_ne; [| vm_compute; discriminate].
        rewrite /R6 upd_ne; [| vm_compute; discriminate].
        rewrite /R5 upd_ne; [| vm_compute; discriminate].
        rewrite /R4 upd_ne; [| vm_compute; discriminate].
        rewrite /R3 upd_ne; [| vm_compute; discriminate].
        rewrite /R2 upd_ne; [| vm_compute; discriminate].
        exact HspR1.
      + (* s2 = p (= m!!!a0) *)
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        rewrite /R7 upd_ne; [| vm_compute; discriminate].
        rewrite /R6 upd_ne; [| vm_compute; discriminate].
        rewrite /R5 upd_ne; [| vm_compute; discriminate].
        rewrite /R4 upd_ne; [| vm_compute; discriminate].
        rewrite /R3 upd_eq. unfold regval_into_reg. rewrite add_vec_zero_l.
        rewrite /R2 upd_ne; [| vm_compute; discriminate].
        rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate].
      + (* s3 = &proc[NPROC] *) exact Hs3end.
      + (* s4 = &initproc *)
        rewrite /R9 upd_ne; [| vm_compute; discriminate].
        rewrite /R8 upd_ne; [| vm_compute; discriminate].
        exact Hs4init.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + apply Hthread; vm_compute; discriminate.
      + intro r. apply rf_to_gmap_dom.
    - rewrite /rp_frame. iFrame "Hc1 Hc2 Hc3 Hc4 Hc5 Hc6".
  Qed.

  (* +0x46 .. +0x54: restore the six saved registers, pop the frame, return. *)
  Lemma rp_epilogue (M : regfile) (K : nat)
      (vra vs0 vs1 vs2 vs3 vs4 : mword 64) (b : bool) (pme : mword 64) :
    let spF := M !!! Regidx csp_rs1 in
    let sp0 := add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) in
    (6 <= K)%nat ->
    (forall r : regidx, r ∈ dom (rf_to_gmap M)) ->
    sie_cap_gpr KT1 M (K - 6) b pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.reparent + 0x46)) -∗
    rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ Mf : regfile,
        ⌜ Mf !!! Regidx (mword_of_int 1)  = vra
        /\ Mf !!! Regidx (mword_of_int 8)  = vs0
        /\ Mf !!! Regidx (mword_of_int 9)  = vs1
        /\ Mf !!! Regidx (mword_of_int 18) = vs2
        /\ Mf !!! Regidx (mword_of_int 19) = vs3
        /\ Mf !!! Regidx (mword_of_int 20) = vs4
        /\ Mf !!! Regidx csp_rs1 = sp0
        /\ Mf !!! Regidx (mword_of_int 21) = M !!! Regidx (mword_of_int 21)
        /\ Mf !!! Regidx (mword_of_int 22) = M !!! Regidx (mword_of_int 22)
        /\ Mf !!! Regidx (mword_of_int 23) = M !!! Regidx (mword_of_int 23)
        /\ Mf !!! Regidx (mword_of_int 24) = M !!! Regidx (mword_of_int 24)
        /\ Mf !!! Regidx (mword_of_int 25) = M !!! Regidx (mword_of_int 25)
        /\ Mf !!! Regidx (mword_of_int 26) = M !!! Regidx (mword_of_int 26)
        /\ Mf !!! Regidx (mword_of_int 27) = M !!! Regidx (mword_of_int 27)
        /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
        sie_cap_gpr KT1 Mf K b pme -∗
        pc_is (ret_pc vra) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros spF sp0 HK6 Hdom.
    iIntros "Hcg #Htext Hpc Hframe Hcont".
    iDestruct "Hframe" as "(Hf5 & Hf4 & Hf3 & Hf2 & Hf1 & Hf0)".
    assert (HspE0 : M !!! Regidx csp_rs1 = spF) by reflexivity.
    (* +0x46 c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x46)) (mword_of_int 5 : mword 6) (mword_of_int 1 : mword 5)
              M (K - 6)%nat vra b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf5]").
    { iApply (rpi_46 with "Htext"). }
    { unfold rp_fcell. iExact "Hf5". }
    iIntros (CID1 Hst1) "Hcg Hpc Hf5".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> M).
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spF) by (rewrite /E1 upd_ne; [ exact HspE0 | vm_compute; discriminate ]).
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x48)) (mword_of_int 4 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 6)%nat vs0 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf4]").
    { iApply (rpi_48 with "Htext"). }
    { unfold rp_fcell. iEval (rewrite HspE1). iExact "Hf4". }
    iIntros (CID2 Hst2) "Hcg Hpc Hf4".
    iEval (rewrite HspE1) in "Hf4".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> E1).
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spF) by (rewrite /E2 upd_ne; [ exact HspE1 | vm_compute; discriminate ]).
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.reparent + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x4a)) (mword_of_int 3 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 6)%nat vs1 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf3]").
    { iApply (rpi_4a with "Htext"). }
    { unfold rp_fcell. iEval (rewrite HspE2). iExact "Hf3". }
    iIntros (CID3 Hst3) "Hcg Hpc Hf3".
    iEval (rewrite HspE2) in "Hf3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg vs1]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spF) by (rewrite /E3 upd_ne; [ exact HspE2 | vm_compute; discriminate ]).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.reparent + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    (* +0x4c c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x4c)) (mword_of_int 2 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 6)%nat vs2 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf2]").
    { iApply (rpi_4c with "Htext"). }
    { unfold rp_fcell. iEval (rewrite HspE3). iExact "Hf2". }
    iIntros (CID4 Hst4) "Hcg Hpc Hf2".
    iEval (rewrite HspE3) in "Hf2".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg vs2]> E3).
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spF) by (rewrite /E4 upd_ne; [ exact HspE3 | vm_compute; discriminate ]).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.reparent + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* +0x4e c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x4e)) (mword_of_int 1 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 6)%nat vs3 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf1]").
    { iApply (rpi_4e with "Htext"). }
    { unfold rp_fcell. iEval (rewrite HspE4). iExact "Hf1". }
    iIntros (CID5 Hst5) "Hcg Hpc Hf1".
    iEval (rewrite HspE4) in "Hf1".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg vs3]> E4).
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spF) by (rewrite /E5 upd_ne; [ exact HspE4 | vm_compute; discriminate ]).
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 c.ldsp s4,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.reparent + 0x50)) (mword_of_int 0 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 6)%nat vs4 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hf0]").
    { iApply (rpi_50 with "Htext"). }
    { unfold rp_fcell. iEval (rewrite HspE5). iExact "Hf0". }
    iIntros (CID6 Hst6) "Hcg Hpc Hf0".
    iEval (rewrite HspE5) in "Hf0".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg vs4]> E5).
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spF) by (rewrite /E6 upd_ne; [ exact HspE5 | vm_compute; discriminate ]).
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp52) in "Hpc".
    (* +0x52 c.addi16sp sp,+48 -- give the 6 slots back to the capability *)
    set (E7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6).
    assert (Hwv : add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HspE6; reflexivity).
    assert (Hup : E6 !!! Regidx csp_rs1 = pa_stk (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HspE6. symmetry. unfold sp0, pa_stk, add_vec_int.
      apply frame_cancel. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb5 : rp_fcell spF 5 = pa_stk sp0 1).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : rp_fcell spF 4 = pa_stk sp0 2).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : rp_fcell spF 3 = pa_stk sp0 3).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : rp_fcell spF 2 = pa_stk sp0 4).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : rp_fcell spF 1 = pa_stk sp0 5).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb0 : rp_fcell spF 0 = pa_stk sp0 6).
    { unfold rp_fcell, sp0, pa_stk, add_vec_int. rewrite add_vec_assoc. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hf5 Hf4 Hf3 Hf2 Hf1 Hf0]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hf5"; [iEval (rewrite -Hb5); iExists _; iExact "Hf5"|].
      iSplitL "Hf4"; [iEval (rewrite -Hb4); iExists _; iExact "Hf4"|].
      iSplitL "Hf3"; [iEval (rewrite -Hb3); iExists _; iExact "Hf3"|].
      iSplitL "Hf2"; [iEval (rewrite -Hb2); iExists _; iExact "Hf2"|].
      iSplitL "Hf1"; [iEval (rewrite -Hb1); iExists _; iExact "Hf1"|].
      iSplitL "Hf0"; [iEval (rewrite -Hb0); iExists _; iExact "Hf0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.reparent + 0x52)) (mword_of_int 3 : mword 6)
              E6 (K - 6)%nat 6 b Hup
              with "Hcg Hpc [] Hframe").
    { iApply (rpi_52 with "Htext"). }
    iIntros (CID7 Hst7) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E6 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> E6) with E7.
    assert (HKfix : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite HKfix) in "Hcg".
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.ret *)
    assert (HE7ra : E7 !!! Regidx (mword_of_int 1 : mword 5) = vra).
    { rewrite /E7 upd_ne; [| vm_compute; discriminate].
      rewrite /E6 upd_ne; [| vm_compute; discriminate].
      rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.reparent + 0x54)) (mword_of_int 1 : mword 5) E7 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (rpi_54 with "Htext"). }
    iIntros (CID8 Hst8) "Hcg Hpc".
    assert (HE7ra_rg : rget (CID := CID7) E7 (mword_of_int 1 : mword 5) = vra)
      by (rgne; exact HE7ra).
    iEval (rewrite HE7ra_rg) in "Hpc".
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E7 with "[%] Hcg Hpc").
    rewrite /E7 /E6 /E5 /E4 /E3 /E2 /E1.
    repeat split.
    all: intro r; apply rf_to_gmap_dom.
  Qed.

End ProofReparentEnds.

(* ===================================================================== *)
(* The scan.  No [Context CID]: the loop is applied at the hart the        *)
(* prologue's own [wp_next] hands back, which a section variable could     *)
(* not express.                                                           *)
(* ===================================================================== *)
Section ProofReparentLoop.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Lemma rp_loop `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      
      (γs : list gname) (spF pme pv ip : mword 64)
      (ps : list (mword 64)) (dqi : dfrac)
      (vra vs0 vs1 vs2 vs3 vs4 : mword 64)
      (vs5 vs6 vs7 vs8 vs9 vs10 vs11 : mword 64)
      (lvl av : nat) (eb : bool) (b : bool) (lks : gset string) :
    length γs = NPROC ->
    length ps = NPROC ->
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (18 <= av)%nat ->
    (* wakeup's order premise, carried verbatim through the scan: the loop
       neither acquires nor releases anything itself, so [lks] -- and hence
       this bound -- is a loop INVARIANT, unchanged across every iteration. *)
    locks_below lks "proc" ->
    procs_inv γs -∗
    (* the exit continuation: control at the epilogue entry [reparent+0x46]. *)
    wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
      ∀ Mexit : regfile,
        ⌜ rpx_regs Mexit spF vs5 vs6 vs7 vs8 vs9 vs10 vs11 ⌝ -∗
        sie_cap_gpr KT1 Mexit av b pme -∗
        cpu_own lvl eb pme b lks -∗
        kernel_text -∗ pc_is (mword_of_int (KernelSyms.reparent + 0x46)) -∗
        rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
        (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
        parents_own (rp_map pv ip ps) -∗
        WP (Loop : expr riscv_lang)) -∗
    ∀ (k : nat) (M : regfile),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜rpl_regs M spF pv vs5 vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
      sie_cap_gpr KT1 M av b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.reparent + 0x34)) -∗
      rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
      (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
      parents_own (rp_upto pv ip k ps) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hlen Hpslen Hlvl Hav Hno.
    iIntros "#Hpinv Hqexit".
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                 ∀ (k : nat) (M : regfile),
                   ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
                   ⌜rpl_regs M spF pv vs5 vs6 vs7 vs8 vs9 vs10 vs11 k⌝ -∗
                   wp_next (CID0 := CID0) b pme (fun (CIDq : CpuId) =>
                     ∀ Mexit : regfile,
                       ⌜ rpx_regs Mexit spF vs5 vs6 vs7 vs8 vs9 vs10 vs11 ⌝ -∗
                       sie_cap_gpr KT1 Mexit av b pme -∗
                       cpu_own lvl eb pme b lks -∗
                       kernel_text -∗ pc_is (mword_of_int (KernelSyms.reparent + 0x46)) -∗
                       rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
                       (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
                       parents_own (rp_map pv ip ps) -∗
                       WP (Loop : expr riscv_lang)) -∗
                   sie_cap_gpr KT1 M av b pme -∗
                   cpu_own lvl eb pme b lks -∗
                   kernel_text -∗ pc_is (mword_of_int (KernelSyms.reparent + 0x34)) -∗
                   rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
                   (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
                   parents_own (rp_upto pv ip k ps) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown Htext Hpc Hframe Hinit Hpar".
        exfalso. lia. }
      iIntros (CIDk Hsk k M) "%Hfuel %Hk %Hregs Hqx Hcg Hown #Htext Hpc Hframe Hinit Hpar".
      destruct Hregs as (Hs1 & Hsp & Hs2 & Hs3 & Hs4 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hdom).
      (* ---- the shared p++/test tail at +0x2c, reached from BOTH arms of the
         [bne] -- and from different harts, hence the [wp_next] wrapper.  Both
         arms arrive at the SAME table [rp_upto pv ip (S k) ps]. ---- *)
      iAssert (wp_next (CID0 := CID0) b pme (fun (CIDt : CpuId) =>
                 ∀ Mt : regfile,
                   ⌜ rpl_regs Mt spF pv vs5 vs6 vs7 vs8 vs9 vs10 vs11 k ⌝ -∗
                   sie_cap_gpr KT1 Mt av b pme -∗
                   cpu_own lvl eb pme b lks -∗
                   pc_is (mword_of_int (KernelSyms.reparent + 0x2c)) -∗
                   rp_frame spF vra vs0 vs1 vs2 vs3 vs4 -∗
                   (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
                   parents_own (rp_upto pv ip (S k) ps) -∗
                   WP (Loop : expr riscv_lang)))%I
        with "[Hqx]" as "Htail".
      { iIntros (CIDt Hst Mt) "%Hmt Hcg Hown Hpc Hframe Hinit Hpar".
        destruct Hmt as (Ht9 & Htsp & Ht18 & Ht19 & Ht20 & Ht21 & Ht22 & Ht23 & Ht24 & Ht25 & Ht26 & Ht27 & Htdom).
        (* +0x2c addi s1,s1,360 : s1 := &proc[k+1] *)
        assert (Hrgt9 : rget (CID := CIDt) Mt (mword_of_int 9 : mword 5)
                        = Mt !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        iApply (wp_addi4_s_sconf (CID := CIDt) (mword_of_int (KernelSyms.reparent + 0x2c))
                  (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12)
                  Mt av b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (rpi_2c with "Htext"). }
        iIntros (CIDt1 Hst1) "Hcg Hpc".
        iEval (rewrite Hrgt9) in "Hcg".
        set (Mt2c := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
             (add_vec (Mt !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Mt).
        assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x30))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp30) in "Hpc".
        assert (HMt2c_9 : Mt2c !!! Regidx (mword_of_int 9 : mword 5) = proc_addr (S k)).
        { rewrite /Mt2c upd_eq. rewrite Ht9. apply (proc_addr_succ k). }
        assert (HMt2c_19 : Mt2c !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC).
        { rewrite /Mt2c upd_ne; [| vm_compute; discriminate]. exact Ht19. }
        (* +0x30 beq s1,s3 : exit iff &proc[k+1] = &proc[NPROC] *)
        assert (Hrg2c_9 : rget (CID := CIDt1) Mt2c (mword_of_int 9 : mword 5)
                          = Mt2c !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        assert (Hrg2c_19 : rget (CID := CIDt1) Mt2c (mword_of_int 19 : mword 5)
                           = Mt2c !!! Regidx (mword_of_int 19 : mword 5)) by (rgne; reflexivity).
        destruct (eq_vec (Mt2c !!! Regidx (mword_of_int 9 : mword 5))
                         (Mt2c !!! Regidx (mword_of_int 19 : mword 5))) eqn:Hcmp.
        + (* TAKEN: the scan is done; the table is fully mapped *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt2c (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt2c (mword_of_int 19 : mword 5)) = true)
            by (rewrite Hrg2c_9 Hrg2c_19; exact Hcmp).
          iApply (wp_beq_taken_s_sconf (CID := CIDt1) (mword_of_int (KernelSyms.reparent + 0x30))
                    (mword_of_int 22 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
                    Mt2c av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (rpi_30 with "Htext"). }
          iNext. iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (Htgt46 : add_vec (mword_of_int (KernelSyms.reparent + 0x30) : mword 64)
                             (sign_extend' 64 (mword_of_int 22 : mword 13)) = mword_of_int (KernelSyms.reparent + 0x46))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt46) in "Hpc".
          (* S k = NPROC, so the partial map is the whole map *)
          assert (HkS : S k = NPROC).
          { apply (rp_end_of_eq k Hk).
            apply (proj1 (eq_vec_true_iff (proc_addr (S k)) (proc_addr NPROC))).
            rewrite -HMt2c_9 -HMt2c_19. exact Hcmp. }
          assert (Hfull : rp_upto pv ip (S k) ps = rp_map pv ip ps)
            by (apply rp_upto_all; rewrite Hpslen HkS; lia).
          iEval (rewrite Hfull) in "Hpar".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("Hqx" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! Mt2c with "[] Hcg Hown Htext Hpc Hframe Hinit Hpar").
          iPureIntro. unfold rpx_regs.
          split; [rewrite /Mt2c upd_ne; [exact Htsp | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht21 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht22 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht23 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht24 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht25 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht26 | vm_compute; discriminate]|].
          split; [rewrite /Mt2c upd_ne; [exact Ht27 | vm_compute; discriminate]|].
          intro r. rewrite /Mt2c rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Htdom.
        + (* FALL: recurse into iteration k+1 *)
          assert (Hcmpr : eq_vec (rget (CID := CIDt1) Mt2c (mword_of_int 9 : mword 5))
                                 (rget (CID := CIDt1) Mt2c (mword_of_int 19 : mword 5)) = false)
            by (rewrite Hrg2c_9 Hrg2c_19; exact Hcmp).
          iApply (wp_beq_fall_s_sconf (CID := CIDt1) (mword_of_int (KernelSyms.reparent + 0x30))
                    (mword_of_int 22 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 9 : mword 5)
                    Mt2c av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmpr with "Hcg Hpc []").
          { iApply (rpi_30 with "Htext"). }
          iIntros (CIDt2 Hst2) "Hcg Hpc".
          assert (HkS : (S k < NPROC)%nat).
          { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
            assert (HeqN : S k = NPROC) by lia.
            exfalso.
            assert (Hbad : eq_vec (Mt2c !!! Regidx (mword_of_int 9 : mword 5))
                             (Mt2c !!! Regidx (mword_of_int 19 : mword 5)) = true).
            { rewrite HMt2c_9 HMt2c_19 HeqN. apply eq_vec_refl. }
            rewrite Hcmp in Hbad. discriminate. }
          assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x34))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp34) in "Hpc".
          iDestruct (cpu_own_transport CIDt CIDt2 lvl eb pme b ltac:(wp_next_chain)
                       with "Hown") as "Hown".
          iSpecialize ("IHf" $! CIDt2 with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) Mt2c with "[%] [%] [%] Hqx Hcg Hown Htext Hpc Hframe Hinit Hpar").
          * lia.
          * exact HkS.
          * unfold rpl_regs.
            split; [exact HMt2c_9|].
            split; [rewrite /Mt2c upd_ne; [exact Htsp | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht18 | vm_compute; discriminate]|].
            split; [exact HMt2c_19|].
            split; [rewrite /Mt2c upd_ne; [exact Ht20 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht21 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht22 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht23 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht24 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht25 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht26 | vm_compute; discriminate]|].
            split; [rewrite /Mt2c upd_ne; [exact Ht27 | vm_compute; discriminate]|].
            intro r. rewrite /Mt2c rf_to_gmap_upd dom_insert_L. apply elem_of_union_r. apply Htdom. }
      (* ================= loop body [+0x34 .. +0x2c] ================= *)
      (* the cell this iteration is about still holds its ORIGINAL value *)
      destruct (lookup_lt_is_Some_2 ps k ltac:(rewrite Hpslen; exact Hk)) as [v Hv].
      assert (Hvk : rp_upto pv ip k ps !! k = Some v) by (apply rp_upto_lookup_k; exact Hv).
      iDestruct (parents_own_acc _ k v Hvk with "Hpar") as "[Hcell Hback]".
      (* +0x34 c.ld a5,56(s1) : a5 := pp->parent *)
      assert (Hrgk9 : rget (CID := CIDk) M (mword_of_int 9 : mword 5)
                      = M !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDk) (mword_of_int (KernelSyms.reparent + 0x34))
                (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 56 : mword 12)
                M av v b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hcell]").
      { iApply (rpi_34 with "Htext"). }
      { iEval (rewrite Hrgk9 Hs1 p_parent_sext). iExact "Hcell". }
      iIntros (CIDl Hsl) "Hcg Hpc Hcell".
      iEval (rewrite Hrgk9 Hs1 p_parent_sext) in "Hcell".
      set (M34 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v]> M).
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      assert (HM34_15 : M34 !!! Regidx (mword_of_int 15 : mword 5) = v) by (rewrite /M34; apply upd_eq).
      assert (HM34_18 : M34 !!! Regidx (mword_of_int 18 : mword 5) = pv)
        by (rewrite /M34 upd_ne; [exact Hs2 | vm_compute; discriminate]).
      assert (HM34_9 : M34 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
        by (rewrite /M34 upd_ne; [exact Hs1 | vm_compute; discriminate]).
      assert (HM34_20 : M34 !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int KernelSyms.initproc : mword 64))
        by (rewrite /M34 upd_ne; [exact Hs4 | vm_compute; discriminate]).
      assert (HM34dom : forall r : regidx, r ∈ dom (rf_to_gmap M34)) by (intro r; apply rf_to_gmap_dom).
      assert (Hrgl15 : rget (CID := CIDl) M34 (mword_of_int 15 : mword 5)
                       = M34 !!! Regidx (mword_of_int 15 : mword 5)) by (rgne; reflexivity).
      assert (Hrgl18 : rget (CID := CIDl) M34 (mword_of_int 18 : mword 5)
                       = M34 !!! Regidx (mword_of_int 18 : mword 5)) by (rgne; reflexivity).
      (* the [rpl_regs] shape of [M34], shared by both arms *)
      assert (HM34regs : rpl_regs M34 spF pv vs5 vs6 vs7 vs8 vs9 vs10 vs11 k).
      { unfold rpl_regs.
        split; [exact HM34_9|].
        split; [rewrite /M34 upd_ne; [exact Hsp | vm_compute; discriminate]|].
        split; [exact HM34_18|].
        split; [rewrite /M34 upd_ne; [exact Hs3 | vm_compute; discriminate]|].
        split; [exact HM34_20|].
        split; [rewrite /M34 upd_ne; [exact H21 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H22 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H23 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H24 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H25 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H26 | vm_compute; discriminate]|].
        split; [rewrite /M34 upd_ne; [exact H27 | vm_compute; discriminate]|].
        exact HM34dom. }
      (* +0x36 bne a5,s2 : skip this slot unless its parent is [p] *)
      destruct (eq_vec v pv) eqn:Hcmp.
      - (* MATCH: the [bne] falls through -- reparent this child *)
        assert (Hfall : neq_vec (rget (CID := CIDl) M34 (mword_of_int 15 : mword 5))
                                (rget (CID := CIDl) M34 (mword_of_int 18 : mword 5)) = false).
        { rewrite Hrgl15 Hrgl18 HM34_15 HM34_18. unfold neq_vec. rewrite Hcmp. reflexivity. }
        iApply (wp_bne_fall_s_sconf (CID := CIDl) (mword_of_int (KernelSyms.reparent + 0x36))
                  (mword_of_int 8182 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
                  M34 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hfall with "Hcg Hpc []").
        { iApply (rpi_36 with "Htext"). }
        iIntros (CIDm Hsm) "Hcg Hpc".
        assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.reparent + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x3a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp3a) in "Hpc".
        (* +0x3a ld a0,0(s4) : a0 := initproc *)
        assert (Hrgm20 : rget (CID := CIDm) M34 (mword_of_int 20 : mword 5)
                         = M34 !!! Regidx (mword_of_int 20 : mword 5)) by (rgne; reflexivity).
        iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDm) (mword_of_int (KernelSyms.reparent + 0x3a))
                  (mword_of_int 10 : mword 5) (mword_of_int 20 : mword 5) (mword_of_int 0 : mword 12)
                  M34 av ip b (dqm := dqi) ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] [Hinit]").
        { iApply (rpi_3a with "Htext"). }
        { iEval (rewrite Hrgm20 HM34_20 addv_sext0). iExact "Hinit". }
        iIntros (CIDn Hsn) "Hcg Hpc Hinit".
        iEval (rewrite Hrgm20 HM34_20 addv_sext0) in "Hinit".
        set (M3a := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg ip]> M34).
        assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.reparent + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.reparent + 0x3e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp3e) in "Hpc".
        assert (HM3a_10 : M3a !!! Regidx (mword_of_int 10 : mword 5) = ip) by (rewrite /M3a; apply upd_eq).
        assert (HM3a_9 : M3a !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
          by (rewrite /M3a upd_ne; [exact HM34_9 | vm_compute; discriminate]).
        (* +0x3e c.sd a0,56(s1) : pp->parent = initproc *)
        assert (Hrgn9 : rget (CID := CIDn) M3a (mword_of_int 9 : mword 5)
                        = M3a !!! Regidx (mword_of_int 9 : mword 5)) by (rgne; reflexivity).
        assert (Hrgn10 : rget (CID := CIDn) M3a (mword_of_int 10 : mword 5)
                         = M3a !!! Regidx (mword_of_int 10 : mword 5)) by (rgne; reflexivity).
        iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDn) (mword_of_int (KernelSyms.reparent + 0x3e))
                  (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 56 : mword 12)
                  M3a av v b
                  with "Hcg Hpc [] [Hcell]").
        { iApply (rpi_3e with "Htext"). }
        { iEval (rewrite Hrgn9 HM3a_9 p_parent_sext). iExact "Hcell". }
        iIntros (CIDo Hso) "Hcg Hpc Hcell".
        iEval (rewrite Hrgn9 HM3a_9 p_parent_sext Hrgn10 HM3a_10) in "Hcell".
        (* close the accessor: slot [k] now holds [ip], i.e. [rp_slot pv ip v] *)
        iDestruct ("Hback" $! ip with "Hcell") as "Hpar".
        assert (Hslot : rp_slot pv ip v = ip) by (unfold rp_slot; rewrite Hcmp; reflexivity).
        pose proof (rp_upto_step pv ip k ps v Hv) as Hstep.
        rewrite Hslot in Hstep.
        iEval (rewrite Hstep) in "Hpar".
        assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.reparent + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.reparent + 0x40))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp40) in "Hpc".
        (* +0x40 jal ra,wakeup *)
        iApply (wp_jal_s_sconf (CID := CIDo) (mword_of_int (KernelSyms.reparent + 0x40))
                  (mword_of_int 1 : mword 5) (mword_of_int 2096986 : mword 21) M3a av b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (rpi_40 with "Htext"). }
        iIntros (CIDp Hsp2) "Hcg Hpc".
        set (M40 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
             (add_vec_int (mword_of_int (KernelSyms.reparent + 0x40) : mword 64) 4)]> M3a).
        assert (Hjtgt : add_vec (mword_of_int (KernelSyms.reparent + 0x40) : mword 64)
                          (sign_extend' 64 (mword_of_int 2096986 : mword 21)) = mword_of_int KernelSyms.wakeup)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtgt) in "Hpc".
        assert (HM40ra : M40 !!! Regidx (mword_of_int 1 : mword 5)
                         = add_vec_int (mword_of_int (KernelSyms.reparent + 0x40) : mword 64) 4)
          by (rewrite /M40; apply upd_eq).
        iDestruct (cpu_own_transport CIDk CIDp lvl eb pme b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        (* wakeup(initproc): everything it changes is invisible; [procs_inv] is
           persistent and the level round-trips. *)
        (* the held set round-trips: reparent takes no lock of its own, and
           wakeup is BALANCED in [lks] (it acquires and releases each
           [pp->lock] within a single iteration, so its own entry and exit
           sets agree).  So both the set and wakeup's order bound [Hno] are
           pure passthroughs of the enclosing contract's -- reparent adds
           nothing to the held set, hence nothing to the premise. *)
        iApply (Wakeup.wp_wakeup_sconf (CID := CIDp)  M40 γs
                  pme lvl av eb b lks
                  ltac:(lia)
                  ltac:(intro r; apply rf_to_gmap_dom)
                  Hlen
                  ltac:(lia)
                  Hno
                  with "Hcg Hown Htext Hpc Hpinv").
        all: try lkbelow.
        iIntros (CIDq Hsq Mw) "[%Hwcs %Hwdom] Hcg Hown Htext2 Hpc".
        assert (Hpc44 : ret_pc (M40 !!! Regidx (mword_of_int 1 : mword 5))
                        = mword_of_int (KernelSyms.reparent + 0x44)).
        { rewrite HM40ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc44) in "Hpc".
        (* +0x44 c.j -> reparent+0x2c *)
        iApply (wp_cj_s_sconf (CID := CIDq) (mword_of_int (KernelSyms.reparent + 0x44))
                  (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                  Mw av b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (rpi_44 with "Htext"). }
        iIntros (CIDr Hsr).
        iNext. iIntros "Hcg Hpc".
        assert (Htgt2c : add_vec (mword_of_int (KernelSyms.reparent + 0x44) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0"))))
                         = mword_of_int (KernelSyms.reparent + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt2c) in "Hpc".
        iDestruct (cpu_own_transport CIDq CIDr lvl eb pme b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iSpecialize ("Htail" $! CIDr with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! Mw with "[%] Hcg Hown Hpc Hframe Hinit Hpar").
        (* the [rpl_regs] shape survives wakeup by [callee_saved] *)
        unfold rpl_regs.
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate]. exact HM3a_9. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 2 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact Hsp | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [exact HM34_18 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact Hs3 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [exact HM34_20 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H21 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H22 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H23 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H24 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H25 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H26 | vm_compute; discriminate]. }
        split.
        { rewrite (callee_saved_lookup Hwcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)).
          rewrite /M40 upd_ne; [| vm_compute; discriminate].
          rewrite /M3a upd_ne; [| vm_compute; discriminate].
          rewrite /M34 upd_ne; [exact H27 | vm_compute; discriminate]. }
        exact Hwdom.
      - (* NO MATCH: the [bne] is taken -- straight to the p++/test tail, with
           the table unchanged, which IS [rp_upto _ _ (S k) ps]. *)
        assert (Htaken : neq_vec (rget (CID := CIDl) M34 (mword_of_int 15 : mword 5))
                                 (rget (CID := CIDl) M34 (mword_of_int 18 : mword 5)) = true).
        { rewrite Hrgl15 Hrgl18 HM34_15 HM34_18. unfold neq_vec. rewrite Hcmp. reflexivity. }
        assert (Htgt2c : add_vec (mword_of_int (KernelSyms.reparent + 0x36) : mword 64)
                           (sign_extend' 64 (mword_of_int 8182 : mword 13)) = mword_of_int (KernelSyms.reparent + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bne_taken_s_sconf (CID := CIDl) (mword_of_int (KernelSyms.reparent + 0x36))
                  (mword_of_int 8182 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
                  M34 av b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Htaken ltac:(rewrite Htgt2c; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (rpi_36 with "Htext"). }
        iNext. iIntros (CIDm Hsm) "Hcg Hpc".
        iEval (rewrite Htgt2c) in "Hpc".
        (* the cell goes back unchanged, and [rp_slot pv ip v = v] *)
        iDestruct ("Hback" $! v with "Hcell") as "Hpar".
        assert (Hslot : rp_slot pv ip v = v) by (unfold rp_slot; rewrite Hcmp; reflexivity).
        pose proof (rp_upto_step pv ip k ps v Hv) as Hstep.
        rewrite Hslot in Hstep.
        iEval (rewrite Hstep) in "Hpar".
        iDestruct (cpu_own_transport CIDk CIDm lvl eb pme b ltac:(wp_next_chain)
                     with "Hown") as "Hown".
        iSpecialize ("Htail" $! CIDm with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! M34 with "[%] Hcg Hown Hpc Hframe Hinit Hpar").
        exact HM34regs. }
    iIntros (k M) "%Hk %Hregs Hcg Hown Htext Hpc Hframe Hinit Hpar".
    iSpecialize ("Hloop" $! (NPROC - k)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! k M with "[%] [%] [%] Hqexit Hcg Hown Htext Hpc Hframe Hinit Hpar");
      [lia | exact Hk | exact Hregs].
  Qed.

End ProofReparentLoop.

(* ===================================================================== *)
(* The whole function.                                                    *)
(* ===================================================================== *)
Section ProofReparent.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  Lemma wp_reparent_sconf `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
       (m : regfile) (γs : list gname) (pme ip : mword 64)
      (ps : list (mword 64)) (dqi : dfrac) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string)
    : wp_reparent_sconf_body m γs pme ip ps dqi lvl K eb b lks.
  Proof.
    cbv beta delta [wp_reparent_sconf_body].
    intros pcE pv rettgt HK Hdom Hlen Hlvl Hno.
    iIntros "Hcg Hown #Htext Hpc #Hpinv Hinit Hpar".
    iDestruct (parents_own_length with "Hpar") as %Hpslen.
    iIntros "Hcont".
    (* ---- prologue ---- *)
    iApply (rp_prologue (CID := CID0) m K b pme ltac:(lia) Hdom
              with "Hcg Htext Hpc").
    iIntros (CIDpro Hspro M) "%Hpro Hcg Hpc Hframe".
    iDestruct (cpu_own_transport CID0 CIDpro lvl eb pme b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* ---- the scan, with the epilogue as its exit continuation ---- *)
    iPoseProof (rp_loop (CID0 := CIDpro)  γs
                  (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))
                  pme pv ip ps dqi
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                  (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                  (m !!! Regidx (mword_of_int 21 : mword 5)) (m !!! Regidx (mword_of_int 22 : mword 5))
                  (m !!! Regidx (mword_of_int 23 : mword 5)) (m !!! Regidx (mword_of_int 24 : mword 5))
                  (m !!! Regidx (mword_of_int 25 : mword 5)) (m !!! Regidx (mword_of_int 26 : mword 5))
                  (m !!! Regidx (mword_of_int 27 : mword 5))
                  lvl (K - 6)%nat eb b lks
                  Hlen Hpslen Hlvl ltac:(lia) Hno
                  with "Hpinv") as "Hloop".
    iSpecialize ("Hloop" with "[Hcont]").
    { (* exit continuation = the epilogue at +0x46 *)
      iIntros (CIDex Hsex Mexit) "%Hex Hcg Hown Htextx Hpc Hframe Hinit Hpar".
      destruct Hex as (Hecsp & He21 & He22 & He23 & He24 & He25 & He26 & He27 & Hedom).
      iApply (rp_epilogue (CID := CIDex) Mexit K
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                b pme
                ltac:(lia) Hedom
                with "Hcg Htextx Hpc [Hframe]").
      { iEval (rewrite Hecsp). iExact "Hframe". }
      iIntros (CIDend Hsend Mf) "%Hepi Hcg Hpc".
      destruct Hepi as (Hf1v & Hf0v & Hf9v & Hf18v & Hf19v & Hf20v & Hfcsp & Hf21v & Hf22v & Hf23v & Hf24v & Hf25v & Hf26v & Hf27v & Hfdom).
      assert (Hspcancel : add_vec (Mexit !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                          = m !!! Regidx csp_rs1)
        by (rewrite Hecsp; apply frame_cancel_48).
      iDestruct (cpu_own_transport CIDex CIDend lvl eb pme b ltac:(wp_next_chain)
                   with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDend with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! Mf with "[%] Hcg Hown Htext [Hpc] Hinit Hpar").
      - split; [| exact Hfdom].
        unfold callee_saved.
        rewrite Hfcsp Hf0v Hf9v Hf18v Hf19v Hf20v Hf21v Hf22v Hf23v Hf24v Hf25v Hf26v Hf27v.
        rewrite He21 He22 He23 He24 He25 He26 He27.
        repeat split; try reflexivity. exact Hspcancel.
      - iExact "Hpc". }
    (* discharge the loop at k = 0 *)
    iApply ("Hloop" $! 0%nat M with "[%] [%] Hcg Hown Htext Hpc Hframe Hinit [Hpar]").
    - unfold NPROC. lia.
    - exact Hpro.
    - rewrite rp_upto_0. iExact "Hpar".
  Qed.

End ProofReparent.

End ReparentProof.
