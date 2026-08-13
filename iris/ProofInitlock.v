(* ProofInitlock.v -- initlock over the SIE-agnostic sconf world.

   The sconf mirror of [wp_initlock_r] (CodeInitlock.v): a straight-line
   function with NO locking (no push_off/acquire), so it does NOT thread
   [intr_count] at all.  It owns the spinlock's three struct fields
   (locked : 4B @ +0, name : 8B @ +8, cpu : 8B @ +16) as raw memory and
   returns them initialised.  sp moves only at the prologue/epilogue
   (2-slot frame), traded through [sie_cap_move_down]/[sie_cap_move_up] 2.

   The [locked := 0] store is a plain 4-byte zero store over a PLAINLY-
   owned word (the lock is not yet an invariant) -- for that we use
   [wp_sw_zero_s_sconf] (WpSconfMem.v), the width-4 sibling of
   [wp_sd_zero_s_sconf].  The decode facts + [initlock_sp_
   cancel] are reused from the smode file CodeInitlock.v, exactly as
   ProofKfree reuses WpKfree's [kfi_*]. *)
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
Require Import HartTp WpNext IntrDefs.
Require Import StackOwn CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import CodeInitlock WpLock.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecInitlock.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module InitlockProof : INITLOCK.

Section ProofInitlock.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ============================================================= *)
  (* initlock: whole-function WP over the sconf world.  Owns the     *)
  (* spinlock's three struct fields as raw memory and returns them   *)
  (* initialised; makes no sub-calls (a pure prologue / three        *)
  (* stores / epilogue).  NO [intr_count] -- it does no locking.     *)
  (* ============================================================= *)
  Lemma wp_initlock_sconf
      (m : regfile)
      (vlock : bv 32) (vname vcpu : bv 64) (s : string)
      (K : nat) (b : bool) (p : mword 64)
    : wp_initlock_sconf_body m vlock vname vcpu s K b p.
  Proof.
    cbv beta delta [wp_initlock_sconf_body].
    intros pcE lk name ret_tgt c_name c_cpu HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    iIntros "Hcg #Htext Hpc #Hstr Hlock Hname Hcpu Hcont".
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
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
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
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (KernelSyms.initlock + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlock + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 2)%nat vra0 b with "Hcg Hpc Hi02 [Hras]").
    { iEval (rewrite HspR1). iExact "Hras". }
    iIntros (CID2 Hs2) "Hcg Hpc Hras".
    iEval (rewrite HspR1) in "Hras".
    (* the leaf's stored value is [rget R1 _] (a VARIABLE-index read); ra is
       not tp, so [rgne] bridges it back to the plain map fact everything
       downstream expects.  Stated generically over the hart: "Hras" is
       concrete at whichever hart the c.sdsp step landed on (CID2), so a fact
       tied to one arbitrarily-picked instance would not [rewrite] into it. *)
    assert (Hra1v : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 1 : mword 5) = R1 !!! Regidx (mword_of_int 1 : mword 5))
      by (intros CID'; rgne; reflexivity).
    iEval (rewrite Hra1v) in "Hras".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlock + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat vs00 b with "Hcg Hpc Hi04 [Hs0s]").
    { iEval (rewrite HspR1). iExact "Hs0s". }
    iIntros (CID3 Hs3) "Hcg Hpc Hs0s".
    iEval (rewrite HspR1) in "Hs0s".
    assert (Hs01v : forall (CID' : CpuId), rget (CID := CID') R1 (mword_of_int 8 : mword 5) = R1 !!! Regidx (mword_of_int 8 : mword 5))
      by (intros CID'; rgne; reflexivity).
    iEval (rewrite Hs01v) in "Hs0s".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.initlock + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              R1 (K - 2)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    assert (HR2a0 : R2 !!! Regidx (mword_of_int 10 : mword 5) = lk).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HR2a1 : R2 !!! Regidx (mword_of_int 11 : mword 5) = name).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HspR2 : R2 !!! Regidx csp_rs1 = spr).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate]. exact HspR1. }
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sd a1,8(a0):  lk->name := a1.  Stated generically over the
       hart throughout this [b]-generic proof: every fresh [wp_next] binder
       (CID1, CID2, ...) is a DIFFERENT hart instance in scope, so a fact
       about [rget] tied to whichever one TC search happens to pick at
       [assert] time need not be the instance the USE SITE's resource is
       actually stated at -- quantify over the hart instead, exactly as
       [rget_ne] does. *)
    assert (Hea_name : forall (CID' : CpuId),
              add_vec (rget (CID := CID') R2 (mword_of_int 10 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))) = c_name).
    { intros CID'. rgne. rewrite HR2a0. unfold c_name, lock_name_field. f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.initlock + 0x08)) (mword_of_int 11 : mword 5) (mword_of_int 10 : mword 5)
              (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) R2 (K - 2)%nat vname b
              with "Hcg Hpc Hi08 [Hname]").
    { iEval (rewrite Hea_name). iExact "Hname". }
    iIntros (CID5 Hs5) "Hcg Hpc Hname".
    (* the leaf's stored value is [rget R2 (mword_of_int 11)] (a1, a
       VARIABLE-index read); bridge it back to the plain map fact [HR2a1]. *)
    assert (Ha1v : forall (CID' : CpuId), rget (CID := CID') R2 (mword_of_int 11 : mword 5) = R2 !!! Regidx (mword_of_int 11 : mword 5))
      by (intros CID'; rgne; reflexivity).
    iEval (rewrite Ha1v Hea_name HR2a1) in "Hname".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.initlock + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a sw zero,0(a0):  lk->locked := 0.  The leaf's [pa] reads a0 via
       [rget] (a VARIABLE-index read); bridge to [HR2a0] with [rgne].
       Generic over the hart: used both before AND after the leaf's own
       [wp_next] binder (CID6), i.e. at two DIFFERENT concrete hart
       instances. *)
    assert (Hea_lock : forall (CID' : CpuId),
              add_vec (rget (CID := CID') R2 (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { intros CID'. rgne. rewrite HR2a0. replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity). apply kv_addv_zero. }
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.initlock + 0x0a)) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12) R2 (K - 2)%nat vlock b
              with "Hcg Hpc Hi0a [Hlock]").
    { iEval (rewrite Hea_lock). iExact "Hlock". }
    iIntros (CID6 Hs6) "Hcg Hpc Hlock".
    iEval (rewrite Hea_lock) in "Hlock".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.initlock + 0x0a) : mword 64) 4 = mword_of_int (KernelSyms.initlock + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e sd zero,16(a0):  lk->cpu := 0 *)
    assert (Hea_cpu : forall (CID' : CpuId),
              add_vec (rget (CID := CID') R2 (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x10 : mword 12)) = c_cpu).
    { intros CID'. rgne. rewrite HR2a0. reflexivity. }
    iApply (wp_sd_zero_s_sconf (mword_of_int (KernelSyms.initlock + 0x0e)) (mword_of_int 10 : mword 5)
              (mword_of_int 0x10 : mword 12) R2 (K - 2)%nat vcpu b
              with "Hcg Hpc Hi0e [Hcpu]").
    { iEval (rewrite Hea_cpu). iExact "Hcpu". }
    iIntros (CID7 Hs7) "Hcg Hpc Hcpu".
    iEval (rewrite Hea_cpu) in "Hcpu".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.initlock + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== EPILOGUE: restore ra/s0, frame trade back, ret ===== *)
    (* +0x12 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlock + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              R2 (K - 2)%nat (R1 !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [Hras]").
    { iEval (rewrite HspR2). iExact "Hras". }
    iIntros (CID8 Hs8) "Hcg Hpc Hras".
    iEval (rewrite HspR2) in "Hras".
    set (R3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> R2).
    assert (HspR3 : R3 !!! Regidx csp_rs1 = spr).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate]. exact HspR2. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 c.ldsp s0,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlock + 0x14)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              R3 (K - 2)%nat (R1 !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hs0s]").
    { iEval (rewrite HspR3). iExact "Hs0s". }
    iIntros (CID9 Hs9) "Hcg Hpc Hs0s".
    iEval (rewrite HspR3) in "Hs0s".
    set (R4 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> R3).
    assert (HspR4 : R4 !!! Regidx csp_rs1 = spr).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate]. exact HspR3. }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* rebuild the 2-slot frame from the restored cells *)
    iEval (rewrite Hb1) in "Hras". iEval (rewrite Hb2) in "Hs0s".
    (* +0x16 c.addi sp,16 -- the frame trade back (move_up 2) *)
    set (R5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4).
    assert (HR5csp : R5 !!! Regidx csp_rs1 = sp0).
    { rewrite /R5 upd_eq. rewrite HspR4. unfold regval_into_reg, spr, sp0. apply frame_cancel_16. }
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
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.initlock + 0x16)) (mword_of_int 16 : mword 6) R4 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi16 Hframe").
    iIntros (CID10 Hs10) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (R4 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> R4) with R5.
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.initlock + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.initlock + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.ret *)
    assert (HR5ra : R5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_eq.
      unfold regval_into_reg.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.initlock + 0x18)) (mword_of_int 1 : mword 5) R5 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18").
    iIntros (CID11 Hs11) "Hcg Hpc".
    assert (Hretf : forall (CID' : CpuId), ret_pc (rget (CID := CID') R5 (mword_of_int 1 : mword 5)) = ret_tgt)
      by (intros CID'; rgne; rewrite HR5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* the name field goes back to the caller OWNED, holding the string
       pointer just stored -- sealing it into [lock_name] is the caller's
       call, not ours (SpecInitlock.v). *)
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! R5 with "Hcg Hpc [%] Hlock Hname Hcpu").
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
      unfold regval_into_reg, spr. apply frame_cancel_16. }
    split.
    { (* s0 *)
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_eq.
      unfold regval_into_reg.
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofInitlock.

End InitlockProof.
