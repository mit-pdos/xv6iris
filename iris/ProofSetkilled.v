(* ProofSetkilled.v -- whole-function WP for setkilled().

     void setkilled(struct proc *p) {
       acquire(&p->lock); p->killed = 1; release(&p->lock);
     }

   Sixteen instructions @ 0x8000211e.  The 32-byte frame saves ra/s0/s1 in
   slots 1..3; slot 0 is padding and is handed back untouched.  [p] is parked
   in s1 across both calls.

   The one interesting step is the [c.sw a5,40(s1)]: [p_killed] sits in
   [SchedCtx.proc_pub], at the TOP LEVEL of [proc_lock_res], so the write
   costs one existential destruct and one existential intro -- and because
   [proc_pub] quantifies the flag, the value stored never has to be computed.
   setkilled never learns the process's state and never touches either
   [proc_slots] guard. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots FileInv.
Require Import SchedCtx.
Require Import SpecAcquire SpecRelease.
Require Import SpecSetkilled.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodeSetkilled.
Import Defs.
Local Open Scope Z_scope.

Notation sk_ra := (mword_of_int 1 : mword 5).
(* a failing tactic in a whole-function WP over the proc invariant otherwise
   spends tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

(* the [c.sw]'s 40-byte displacement is p->killed's offset *)
Lemma sk_killed_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 40 : mword 12)) = p_killed X.
Proof. rewrite /p_killed. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Module SetkilledProof (Acquire : ACQUIRE) (Release : RELEASE) : SETKILLED.

Section ProofSetkilled.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation sk_s0 := (mword_of_int 8 : mword 5).
  Notation sk_s1 := (mword_of_int 9 : mword 5).
  Notation sk_a0 := (mword_of_int 10 : mword 5).
  Notation sk_a5 := (mword_of_int 15 : mword 5).

  Lemma wp_setkilled_sconf (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool)
    : wp_setkilled_sconf_body Φ γs j γl m av n eb p C b.
  Proof.
    cbv beta delta [wp_setkilled_sconf_body].
    intros pcE ret_tgt Ha0 Hj Hgl Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs Hpanic Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    iDestruct (procs_inv_lookup Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    (* ===================== PROLOGUE (32-byte frame, 3 slots used) ======= *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spd) by (rewrite /M1 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (ski_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (v1) "Hb1". iDestruct "S2c" as (v2) "Hb2".
    iDestruct "S3c" as (v3) "Hb3". iDestruct "S4c" as (v4) "Hb4".
    assert (Hslot : forall (k u : nat), (k + u = 4)%nat -> (u < 4)%nat ->
              pa_stk sp0 k = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))).
    { intros k u Hku Hu. rewrite -Hspd4.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1a := Hslot 1%nat 3%nat ltac:(lia) ltac:(lia)).
    assert (Hb2a := Hslot 2%nat 2%nat ltac:(lia) ltac:(lia)).
    assert (Hb3a := Hslot 3%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hb4a := Hslot 4%nat 0%nat ltac:(lia) ltac:(lia)).
    (* +0x02..+0x06: save ra/s0/s1.  Slot 0 (Hb4) is never written. *)
    iPoseProof (ski_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x02)) (mword_of_int 3 : mword 6) sk_ra M1 (av - 4)%nat v1 b
              with "Hcg Hpc Hi02 [Hb1] [-]").
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (ski_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x04)) (mword_of_int 2 : mword 6) sk_s0 M1 (av - 4)%nat v2 b
              with "Hcg Hpc Hi04 [Hb2] [-]").
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (ski_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x06)) (mword_of_int 1 : mword 6) sk_s1 M1 (av - 4)%nat v3 b
              with "Hcg Hpc Hi06 [Hb3] [-]").
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* normalize the three saved cells to [add_vec spd _ ↦₈ (m !!! r)] *)
    assert (HraM1 : M1 !!! Regidx sk_ra = m !!! Regidx sk_ra) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0M1 : M1 !!! Regidx sk_s0 = m !!! Regidx sk_s0) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1M1 : M1 !!! Regidx sk_s1 = m !!! Regidx sk_s1) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite HcspM1 HraM1) in "Hb1".
    iEval (rgne; rewrite HcspM1 Hs0M1) in "Hb2".
    iEval (rgne; rewrite HcspM1 Hs1M1) in "Hb3".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (ski_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.setkilled + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) sk_s0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx sk_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx sk_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a: c.mv s1,a0 -- park [p] in a callee-saved register *)
    iPoseProof (ski_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.setkilled + 0x0a)) sk_s1 sk_a0 A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 :=<[Regidx sk_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx sk_a0))]> A1).
    change (<[Regidx sk_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx sk_a0))]> A1) with A2.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx sk_s1 = proc_addr j).
    { rewrite /A2 upd_eq add_vec_zero_l.
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    assert (HA2a0 : A2 !!! Regidx sk_a0 = proc_addr j).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    (* +0x0c: jal ra,acquire *)
    iPoseProof (ski_0c with "Htext") as "Hi0c".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.setkilled + 0x0c)) sk_ra (mword_of_int 2091732 : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (B1 := <[Regidx sk_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.setkilled + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx sk_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.setkilled + 0x0c) : mword 64) 4)]> A2) with B1.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.setkilled + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2091732 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HB1ra : B1 !!! Regidx sk_ra = add_vec_int (mword_of_int (KernelSyms.setkilled + 0x0c) : mword 64) 4) by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1a0 : B1 !!! Regidx sk_a0 = proc_addr j)
      by (rewrite /B1 upd_ne; [exact HA2a0 | vm_compute; discriminate]).
    (* ===================== acquire(&p->lock) ===================== *)
    iDestruct (cpu_own_transport CID CID7 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf γl "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) B1 n eb p C (av - 4)%nat b
              Hn ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic [-]").
    { iEval (rewrite HB1a0). iExact "Hislock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsf Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hp10 : ret_pc (B1 !!! Regidx sk_ra) = mword_of_int (KernelSyms.setkilled + 0x10))
      by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* ---- open the lock: p->killed is in the ALWAYS-RESIDENT row ---- *)
    iDestruct (proc_lock_res_elim Φ γs γl (proc_addr j) with "HR") as (st ch) "(Hstate & Hpg & Hchan & Hpub & Hslot)".
    iDestruct "Hpub" as (kl xs pid) "(Hkilled & Hxstate & Hpidhalf)".
    assert (Hmacq_s1 : macq !!! Regidx sk_s1 = proc_addr j).
    { rewrite (callee_saved_lookup Hcs_acq sk_s1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact HA2s1. }
    (* +0x10: c.li a5,1 *)
    iPoseProof (ski_10 with "Htext") as "Hi10".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.setkilled + 0x10)) sk_a5 (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              macq (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C1 := <[Regidx sk_a5 := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> macq).
    change (<[Regidx sk_a5 := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> macq) with C1.
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    assert (HC1s1 : C1 !!! Regidx sk_s1 = proc_addr j)
      by (rewrite /C1 upd_ne; [exact Hmacq_s1 | vm_compute; discriminate]).
    (* +0x12: c.sw a5,40(s1) -- p->killed = 1 *)
    iPoseProof (ski_12 with "Htext") as "Hi12".
    assert (Hsaddr : add_vec (C1 !!! Regidx sk_s1) (sign_extend' 64 (mword_of_int 40 : mword 12))
                     = p_killed (proc_addr j))
      by (rewrite HC1s1; apply sk_killed_off).
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.setkilled + 0x12)) sk_a5 sk_s1
              (mword_of_int 40 : mword 12) C1 (av - 4)%nat kl false
              with "Hcg Hpc Hi12 [Hkilled] [-]").
    { iEval (rgne; rewrite Hsaddr). iExact "Hkilled". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hkilled". iEval (rgne; rewrite Hsaddr) in "Hkilled".
    (* +0x14: c.mv a0,s1 *)
    iPoseProof (ski_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.setkilled + 0x14)) sk_a0 sk_s1 C1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C2 := <[Regidx sk_a0 := regval_into_reg (add_vec zero_reg (C1 !!! Regidx sk_s1))]> C1).
    change (<[Regidx sk_a0 := regval_into_reg (add_vec zero_reg (C1 !!! Regidx sk_s1))]> C1) with C2.
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    assert (HC2a0 : C2 !!! Regidx sk_a0 = proc_addr j)
      by (rewrite /C2 upd_eq add_vec_zero_l; exact HC1s1).
    (* +0x16: jal ra,release *)
    iPoseProof (ski_16 with "Htext") as "Hi16".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.setkilled + 0x16)) sk_ra (mword_of_int 2091858 : mword 21)
              C2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C3 := <[Regidx sk_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.setkilled + 0x16) : mword 64) 4)]> C2).
    change (<[Regidx sk_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.setkilled + 0x16) : mword 64) 4)]> C2) with C3.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.setkilled + 0x16) : mword 64) (sign_extend' 64 (mword_of_int 2091858 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HC3ra : C3 !!! Regidx sk_ra = add_vec_int (mword_of_int (KernelSyms.setkilled + 0x16) : mword 64) 4) by (rewrite /C3 upd_eq; reflexivity).
    assert (HC3a0 : C3 !!! Regidx sk_a0 = proc_addr j)
      by (rewrite /C3 upd_ne; [exact HC2a0 | vm_compute; discriminate]).
    assert (Hlka : add_vec (C3 !!! Regidx sk_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite HC3a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* reassemble the lock resource: [proc_pub] quantifies [killed], so the
       stored value need never be named. *)
    iAssert (proc_lock_res Φ γs γl (proc_addr j)) with "[Hstate Hpg Hchan Hkilled Hxstate Hpidhalf Hslot]" as "HR2".
    { iApply (proc_lock_res_intro Φ γs γl (proc_addr j) st ch with "Hstate Hpg Hchan [-Hslot] Hslot").
      iExists _, xs, pid. iFrame "Hkilled Hxstate Hpidhalf". }
    (* ===================== release(&p->lock) ===================== *)
    iApply (Release.wp_release_sconf γl (proc_addr j) "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) C3 n eb p C (av - 4)%nat
              Hlka ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Hpay [-]").
    iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcs_rel Hcpu".
    rewrite Hbeq in Hsrel.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu".
    assert (Hp1a : ret_pc (C3 !!! Regidx sk_ra) = mword_of_int (KernelSyms.setkilled + 0x1a))
      by (rewrite HC3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* ===================== EPILOGUE ===================== *)
    assert (Hmrelcsp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspM1. }
    iPoseProof (ski_1a with "Htext") as "Hi1a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x1a)) (mword_of_int 3 : mword 6) sk_ra
              mrel (av - 4)%nat (m !!! Regidx sk_ra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a [Hb1] [-]").
    { iEval (rewrite Hmrelcsp). iExact "Hb1". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hb1".
    set (E0 := <[Regidx sk_ra := regval_into_reg (m !!! Regidx sk_ra)]> mrel).
    change (<[Regidx sk_ra := regval_into_reg (m !!! Regidx sk_ra)]> mrel) with E0.
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    assert (HE0csp : E0 !!! Regidx csp_rs1 = spd) by (rewrite /E0 upd_ne; [exact Hmrelcsp | vm_compute; discriminate]).
    iPoseProof (ski_1c with "Htext") as "Hi1c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x1c)) (mword_of_int 2 : mword 6) sk_s0
              E0 (av - 4)%nat (m !!! Regidx sk_s0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [Hb2] [-]").
    { iEval (rewrite HE0csp). iExact "Hb2". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hb2".
    set (E1 := <[Regidx sk_s0 := regval_into_reg (m !!! Regidx sk_s0)]> E0).
    change (<[Regidx sk_s0 := regval_into_reg (m !!! Regidx sk_s0)]> E0) with E1.
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
    iPoseProof (ski_1e with "Htext") as "Hi1e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.setkilled + 0x1e)) (mword_of_int 1 : mword 6) sk_s1
              E1 (av - 4)%nat (m !!! Regidx sk_s1) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [Hb3] [-]").
    { iEval (rewrite HE1csp). iExact "Hb3". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hb3".
    set (E2 := <[Regidx sk_s1 := regval_into_reg (m !!! Regidx sk_s1)]> E1).
    change (<[Regidx sk_s1 := regval_into_reg (m !!! Regidx sk_s1)]> E1) with E2.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    (* +0x20: c.addi16sp sp,32 -- the frame pop *)
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
    assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite /spd /sp0; apply frame_cancel_32).
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE2csp; exact Hup).
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HE2csp; symmetry; exact Hspd4).
    iPoseProof (ski_20 with "Htext") as "Hi20".
    iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -Hmrelcsp). iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE0csp). iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE1csp). iExact "Hb3". }
      (* slot 0 is padding: never stored to, so it is still at [pa_stk sp0 4] *)
      iSplitL "Hb4". { iExists _. iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.setkilled + 0x20)) (mword_of_int 2 : mword 6) E2 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi20 Hframe4 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2) with E3.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.setkilled + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.setkilled + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* +0x22: c.ret *)
    assert (HE3ra : E3 !!! Regidx sk_ra = m !!! Regidx sk_ra).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0. apply upd_eq. }
    iPoseProof (ski_22 with "Htext") as "Hi22".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.setkilled + 0x22)) sk_ra E3 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi22 [-]").
    iIntros (CIDe7 Hse7) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E3 !!! Regidx sk_ra) = ret_tgt) by (rewrite HE3ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== the postcondition ===================== *)
    assert (HE3csp : E3 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E3 upd_eq; exact Hwv).
    assert (HE3s0 : E3 !!! Regidx sk_s0 = m !!! Regidx sk_s0).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    assert (HE3s1 : E3 !!! Regidx sk_s1 = m !!! Regidx sk_s1).
    { rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2. apply upd_eq. }
    (* every other callee-saved register threads through both calls *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     E3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_rel r Hr).
      rewrite /C3 upd_ne; [| congruence].
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_acq r Hr).
      rewrite /B1 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CIDrel CIDe7 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E3 with "[%] Hcg Hcpu Hpc").
    unfold callee_saved.
    split; [exact HE3csp|].
    split; [exact HE3s0|]. split; [exact HE3s1|].
    repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSetkilled.

End SetkilledProof.
