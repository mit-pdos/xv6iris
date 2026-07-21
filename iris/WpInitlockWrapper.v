(* WpInitlockWrapper.v -- the ONE proof of the thin-initlock-wrapper shape
   ([SpecInitlockWrapper.v]): a whole function whose body is exactly
   [initlock(&L, "name")].  printkinit, trapinit and fileinit are all compiled
   to these same thirteen instructions and differ only in the entry address and
   the three relocated immediates, so each of them instantiates this lemma
   instead of re-deriving a 250-line straight-line proof.

   Everything here is stated over a SYMBOLIC entry [F], so no step may
   [vm_compute] an address: pc stepping goes through [pc_step] (over
   [avi_mword]), and the return from initlock through [jalr_ret_id]
   (AlignBits.v) off the spec's one 2-byte-alignment premise.  A member's
   concrete addresses are only ever touched by its own decode file. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase WpAuipc.
Require Import AlignBits.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpInitlock SpecInitlock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecInitlockWrapper.
Local Open Scope Z_scope.
Import Defs.

(* pc stepping over a symbolic entry: [F+a] plus [n] bytes is [F+b].  The
   [a + n = b] premise is a closed numeral equation at every call site. *)
Lemma pc_step (F a n b : Z) : (a + n)%Z = b ->
  add_vec_int (mword_of_int (F + a) : mword 64) n = mword_of_int (F + b).
Proof. intros <-. rewrite avi_mword Z.add_assoc. reflexivity. Qed.

Module InitlockWrapperProof (Initlock : INITLOCK) : INITLOCK_WRAPPER.

Section WpInitlockWrapper.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_initlock_wrapper_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (F : Z) (uname ulk : mword 20) (iname ilk : mword 12) (j : mword 21)
      (lk name : mword 64) (s : string) (vlock : bv 32) (vname vcpu : bv 64)
    : wp_initlock_wrapper_sconf_body γ root_ppn Φ m K F uname ulk iname ilk j lk name s vlock vname vcpu.
  Proof.
    cbv beta delta [wp_initlock_wrapper_sconf_body].
    intros ret_tgt c_name c_cpu HK Hretm Halign Hnamerel Hlkrel Hjrel.
    (* [sp0] is proof-local shorthand, not spec vocabulary. *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hcode Hpc #Hstr Hlock Hname Hcpu Hcont".
    iDestruct "Hcode" as "(Hi00 & Hi02 & Hi04 & Hi06 & Hi08 & Hi0c & Hi10 & Hi14 & Hi18 & Hi1c & Hi1e & Hi20 & Hi22)".
    assert (Hspr2 : spr = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE: 2-slot frame trade (move_down 2) + save ra/s0 ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ (mword_of_int F : mword 64) (mword_of_int 48 : mword 6) m K 2 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    iEval (rewrite (avi_mword F 2)) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (F + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hras] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite HspR1 Hb1) in "Hras".
    assert (Hrav : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hrav) in "Hras".
    iEval (rewrite (pc_step F 0x02 2 0x04 eq_refl)) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (F + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HspR1 Hb2) in "Hs0s".
    assert (Hs0v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hs0v) in "Hs0s".
    iEval (rewrite (pc_step F 0x04 2 0x06 eq_refl)) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (F + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    iEval (rewrite (pc_step F 0x06 2 0x08 eq_refl)) in "Hpc".
    (* ===== compute a1 = &"name", a0 = &lock (0x08..0x14) ===== *)
    (* +0x08 auipc a1,<uname> *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (F + 0x08)) (mword_of_int 11 : mword 5) uname
              R2 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (F + 0x08) : mword 64) (auipc_off uname))]> R2).
    iEval (rewrite (pc_step F 0x08 4 0x0c eq_refl)) in "Hpc".
    (* +0x0c addi a1,a1,<iname> *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (F + 0x0c)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) iname
              R3 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 iname))]> R3).
    iEval (rewrite (pc_step F 0x0c 4 0x10 eq_refl)) in "Hpc".
    assert (HR4a1 : R4 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R4 upd_eq. rewrite /R3 upd_eq. exact Hnamerel. }
    (* +0x10 auipc a0,<ulk> *)
    iApply (wp_auipc_s_sconf γ root_ppn Φ (mword_of_int (F + 0x10)) (mword_of_int 10 : mword 5) ulk
              R4 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (F + 0x10) : mword 64) (auipc_off ulk))]> R4).
    iEval (rewrite (pc_step F 0x10 4 0x14 eq_refl)) in "Hpc".
    (* +0x14 addi a0,a0,<ilk>  (a0 := &lock) *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (F + 0x14)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) ilk
              R5 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 ilk))]> R5).
    iEval (rewrite (pc_step F 0x14 4 0x18 eq_refl)) in "Hpc".
    assert (HR6a0 : R6 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq. exact Hlkrel. }
    assert (HR6a1 : R6 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4a1 | vm_compute; discriminate]. }
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr).
    { rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    (* ===== jal initlock ===== *)
    iApply (wp_jal_s_sconf γ root_ppn Φ (mword_of_int (F + 0x18)) (mword_of_int 1 : mword 5) j
              R6 (K - 2)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hjrel; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (F + 0x18) : mword 64) 4)]> R6).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HR7a0 : R7 !!! Regidx (mword_of_int 10 : mword 5) = lk)
      by (rewrite /R7 upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HR7a1 : R7 !!! Regidx (mword_of_int 11 : mword 5) = name)
      by (rewrite /R7 upd_ne; [exact HR6a1 | vm_compute; discriminate]).
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr)
      by (rewrite /R7 upd_ne; [exact HR6sp | vm_compute; discriminate]).
    assert (HR7ra : R7 !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (F + 0x1c)).
    { rewrite /R7 upd_eq. exact (pc_step F 0x18 4 0x1c eq_refl). }
    (* initlock(&lock, "name") : owns lk's 3 struct fields, returns them init'd *)
    iApply (Initlock.wp_initlock_sconf γ root_ppn Φ R7 vlock vname vcpu s (K - 2)
              ltac:(lia)
              ltac:(rewrite HR7ra; rewrite (jalr_ret_id _ Halign); exact Halign)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HR7a1). iExact "Hstr". }
    { iEval (rewrite HR7a0). iExact "Hlock". }
    { iEval (rewrite HR7a0). iExact "Hname". }
    { iEval (rewrite HR7a0). iExact "Hcpu". }
    iIntros (mil) "Hsc Hhs Hcg Htlbinv Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HR7a0) in "Hlock".
    iEval (rewrite HR7a0) in "Hlname".
    iEval (rewrite HR7a0) in "Hcpu".
    assert (Hpcil : update_vec_dec (add_vec (R7 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (F + 0x1c)).
    { rewrite HR7ra. exact (jalr_ret_id _ Halign). }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hiltp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr) by (rewrite Hilsp; exact HR7sp).
    (* ===== EPILOGUE (0x1c..0x22): restore ra/s0, frame trade back, ret ===== *)
    (* +0x1c c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (F + 0x1c)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              mil (K - 2)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1c [Hras] [-]").
    { iEval (rewrite -Hb1 -Hmilsp) in "Hras". iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite Hmilsp Hb1) in "Hras".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil).
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    iEval (rewrite (pc_step F 0x1c 2 0x1e eq_refl)) in "Hpc".
    (* +0x1e c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (F + 0x1e)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [Hs0s] [-]").
    { iEval (rewrite -Hb2 -HE1sp) in "Hs0s". iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HE1sp Hb2) in "Hs0s".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HE1sp | vm_compute; discriminate]).
    iEval (rewrite (pc_step F 0x1e 2 0x20 eq_refl)) in "Hpc".
    (* +0x20 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (E3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HE3csp : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HE2sp. unfold regval_into_reg, spr, sp0.
      apply initlock_sp_cancel. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HE3csp /E3 upd_eq. reflexivity. }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HE2sp. exact Hspr2. }
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|]. done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (F + 0x20)) (mword_of_int 16 : mword 6) E2 (K - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi20 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2) with E3.
    iEval (rewrite (pc_step F 0x20 2 0x22 eq_refl)) in "Hpc".
    (* +0x22 c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq; reflexivity. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HE3ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (F + 0x22)) (mword_of_int 1 : mword 5) E3 K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (E3 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iApply ("Hcont" $! E3 with "Hsc Hhs Hcg Htlbinv Hpc [%] Hlock Hlname Hcpu").
    (* callee_saved m E3: the sub-call preserves s1..s11/tp; the epilogue
       restores sp/s0, and ra (caller-saved) is irrelevant. *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              E3 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs_full c Hc).
      rewrite /R7 upd_ne; [| congruence].
      rewrite /R6 upd_ne; [| congruence].
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split. { rewrite HE3csp. reflexivity. }
    split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split. { rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpInitlockWrapper.

End InitlockWrapperProof.
