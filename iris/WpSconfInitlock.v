(* WpSconfInitlock.v -- initlock over the SIE-agnostic sconf world.

   The sconf mirror of [wp_initlock_r] (WpInitlock.v): a straight-line
   function with NO locking (no push_off/acquire), so it does NOT thread
   [intr_count] at all.  It owns the spinlock's three struct fields
   (locked : 4B @ +0, name : 8B @ +8, cpu : 8B @ +16) as raw memory and
   returns them initialised.  sp moves only at the prologue/epilogue
   (2-slot frame), traded through [sie_cap_move_down]/[sie_cap_move_up] 2.

   The [locked := 0] store is a plain 4-byte zero store over a PLAINLY-
   owned word (the lock is not yet an invariant) -- for that we use
   [wp_sw_zero_s_sconf] (WpSconfMem.v), the width-4 sibling of
   [wp_sd_zero_s_sconf].  The decode facts + [initlock_sp_
   cancel] are reused from the smode file WpInitlock.v, exactly as
   WpSconfKfree reuses WpKfree's [kfi_*]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpInitlock WpLock.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecInitlock.
Local Open Scope Z_scope.
Import Defs.

Module InitlockProof : INITLOCK.

Section WpSconfInitlock.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Notation IL := KernelSyms.initlock.

  (* ============================================================= *)
  (* initlock: whole-function WP over the sconf world.  Owns the     *)
  (* spinlock's three struct fields as raw memory and returns them   *)
  (* initialised; makes no sub-calls (a pure prologue / three        *)
  (* stores / epilogue).  NO [intr_count] -- it does no locking.     *)
  (* ============================================================= *)
  Lemma wp_initlock_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile)
      (vlock : bv 32) (vname vcpu : bv 64) (s : string)
      (K : nat)
    : wp_initlock_sconf_body γ root_ppn Φ m vlock vname vcpu s K.
  Proof.
    cbv beta delta [wp_initlock_sconf_body].
    intros pcE lk name ret_tgt c_name c_cpu HK Hretm.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc #Hstr Hlock Hname Hcpu Hcont".
    iPoseProof (ini_00 with "Htext") as "Hi00".
    iPoseProof (ini_02 with "Htext") as "Hi02".
    iPoseProof (ini_04 with "Htext") as "Hi04".
    iPoseProof (ini_06 with "Htext") as "Hi06".
    iPoseProof (ini_08 with "Htext") as "Hi08".
    iPoseProof (ini_0a with "Htext") as "Hi0a".
    iPoseProof (ini_0e with "Htext") as "Hi0e".
    iPoseProof (ini_12 with "Htext") as "Hi12".
    iPoseProof (ini_14 with "Htext") as "Hi14".
    iPoseProof (ini_16 with "Htext") as "Hi16".
    iPoseProof (ini_18 with "Htext") as "Hi18".
    (* ===== PROLOGUE: 2-slot frame trade + saves ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* +0x00 c.addi sp,-16 -- the frame push (k := 2) *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE (mword_of_int 48 : mword 6) m K 2 ltac:(lia) Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    (* frame cells at [pa_stk sp0 1..2] *)
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (vra0) "Hras". iDestruct "S2" as (vs00) "Hs0s".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hras". iEval (rewrite -Hb2) in "Hs0s".
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (IL + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 with "Hsc Hhs Hcg Htlbinv Hpc Hi02 [Hras] [-]").
    { iEval (rewrite HspR1). iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite HspR1) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (IL + 0x02) : mword 64) 2 = mword_of_int (IL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 with "Hsc Hhs Hcg Htlbinv Hpc Hi04 [Hs0s] [-]").
    { iEval (rewrite HspR1). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HspR1) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (IL + 0x04) : mword 64) 2 = mword_of_int (IL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HspR2 : R2 !!! Regidx csp_rs1 = spr).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (Hpp08 : add_vec_int (mword_of_int (IL + 0x06) : mword 64) 2 = mword_of_int (IL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sd a1,8(a0):  lk->name := a1 *)
    assert (Hea_name : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))) = c_name).
    { rewrite HR2a0. unfold c_name, lock_name_field. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) R2 (K - 2)%nat vname
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [Hname] [-]").
    { iEval (rewrite Hea_name). iExact "Hname". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hname".
    iEval (rewrite Hea_name HR2a1) in "Hname".
    assert (Hpp0a : add_vec_int (mword_of_int (IL + 0x08) : mword 64) 2 = mword_of_int (IL + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a sw zero,0(a0):  lk->locked := 0 *)
    assert (Hea_lock : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HR2a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_sw_zero_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x0a)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) R2 (K - 2)%nat vlock
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [Hlock] [-]").
    { iEval (rewrite Hea_lock). iExact "Hlock". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hlock".
    iEval (rewrite Hea_lock) in "Hlock".
    assert (Hpp0e : add_vec_int (mword_of_int (IL + 0x0a) : mword 64) 4 = mword_of_int (IL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e sd zero,16(a0):  lk->cpu := 0 *)
    assert (Hea_cpu : add_vec (R2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x10 : mword 12)) = c_cpu).
    { rewrite HR2a0. reflexivity. }
    iApply (wp_sd_zero_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x0e)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x10 : mword 12) R2 (K - 2)%nat vcpu
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e [Hcpu] [-]").
    { iEval (rewrite Hea_cpu). iExact "Hcpu". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hcpu".
    iEval (rewrite Hea_cpu) in "Hcpu".
    assert (Hpp12 : add_vec_int (mword_of_int (IL + 0x0e) : mword 64) 4 = mword_of_int (IL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== EPILOGUE: restore ra/s0, frame trade back, ret ===== *)
    (* +0x12 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R2 (K - 2)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [Hras] [-]").
    { iEval (rewrite HspR2). iExact "Hras". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hras".
    iEval (rewrite HspR2) in "Hras".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate]. exact HspR2. }
    assert (Hpp14 : add_vec_int (mword_of_int (IL + 0x12) : mword 64) 2 = mword_of_int (IL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x14)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R3 (K - 2)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [Hs0s] [-]").
    { iEval (rewrite HspR3). iExact "Hs0s". }
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hs0s".
    iEval (rewrite HspR3) in "Hs0s".
    set (R4 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HspR3. }
    assert (Hpp16 : add_vec_int (mword_of_int (IL + 0x14) : mword 64) 2 = mword_of_int (IL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* rebuild the 2-slot frame from the restored cells *)
    iEval (rewrite Hb1) in "Hras". iEval (rewrite Hb2) in "Hs0s".
    (* +0x16 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (R5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4).
    assert (HR5csp : R5 !!! Regidx csp_rs1 = sp0).
    { rewrite /R5 upd_eq. rewrite HspR4. unfold regval_into_reg, spr, sp0. apply initlock_sp_cancel. }
    assert (Hwv : add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HR5csp /R5 upd_eq. reflexivity. }
    assert (Hpop : R4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HspR4. unfold spr, sp0, pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 2) with "[Hras Hs0s]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hras"; [iExists _; iExact "Hras"|].
      iSplitL "Hs0s"; [iExists _; iExact "Hs0s"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x16)) (mword_of_int 16 : mword 6) R4 (K - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4) with R5.
    assert (Hpp18 : add_vec_int (mword_of_int (IL + 0x16) : mword 64) 2 = mword_of_int (IL + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.ret *)
    assert (HR5ra : R5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_eq.
      unfold regval_into_reg.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hretaligned : eq_vec (access_vec_dec (update_vec_dec (add_vec (R5 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HR5ra; exact Hretm).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (IL + 0x18)) (mword_of_int 1 : mword 5) R5 K
              ltac:(vm_compute; discriminate) Hretaligned
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hretf : update_vec_dec (add_vec (R5 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HR5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* the name field is now written for good: discard its fraction, so what
       the caller gets back is the persistent [lock_name lk s]. *)
    iApply fupd_wp.
    iMod (word_pointsto_persist with "Hname") as "#Hnamep".
    iModIntro.
    iApply ("Hcont" $! R5 with "Hsc Hhs Hcg Htlbinv Hpc [%] Hlock [] Hcpu").
    2:{ iExists name. iFrame "Hnamep Hstr". }
    (* callee_saved m R5 *)
    assert (Hthread : forall c : mword 5, c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 1 ->
                R5 !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N1.
      rewrite /R5 upd_ne; [| congruence].
      rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence].
      rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [| congruence].
      reflexivity. }
    unfold callee_saved.
    split.
    { (* sp *)
      rewrite /R5 upd_eq. rewrite HspR4.
      unfold regval_into_reg, spr. apply initlock_sp_cancel. }
    split.
    { (* tp *) apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    split.
    { (* s0 *)
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_eq.
      unfold regval_into_reg.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End WpSconfInitlock.

End InitlockProof.
