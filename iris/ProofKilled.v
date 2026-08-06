(* ProofKilled.v -- whole-function WP for killed().

     int killed(struct proc *p) {
       acquire(&p->lock); k = p->killed; release(&p->lock); return k;
     }

   Nineteen instructions @ 0x80002142.  The 32-byte frame saves ra/s0/s1/s2
   in all four slots (no gap): [p] is parked in s1 across acquire, and the
   value in s2 across release.

   The one interesting step is the [c.lw a5,40(s1)]: [p_killed] sits in
   [SchedCtx.proc_pub], at the TOP LEVEL of [proc_lock_res], so the read
   costs one existential destruct and never touches either [proc_slots]
   guard -- killed() never learns the process's state.  That is exactly what
   the invariant's always-resident row is for. *)
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
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots FileInv.
Require Import SchedCtx.
Require Import SpecAcquire SpecRelease.
Require Import SpecKilled.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodeKilled.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP over the proc invariant otherwise
   spends tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.






(* the [c.lw]'s 40-byte displacement is p->killed's offset *)
Lemma kl_killed_off (X : mword 64) :
  add_vec X (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))))
  = p_killed X.
Proof. rewrite /p_killed. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.


Module KilledProof (Acquire : ACQUIRE) (Release : RELEASE) : KILLED.

Section ProofKilled.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation kl_s0 := (mword_of_int 8 : mword 5).
  Notation kl_s1 := (mword_of_int 9 : mword 5).
  Notation kl_a0 := (mword_of_int 10 : mword 5).
  Notation kl_a5 := (mword_of_int 15 : mword 5).
  Notation kl_s2 := (mword_of_int 18 : mword 5).





















  Lemma wp_killed_sconf (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool)
    : wp_killed_sconf_body Φ γs j γl m av n eb p C b.
  Proof.
    cbv beta delta [wp_killed_sconf_body].
    intros pcE ret_tgt Ha0 Hj Hgl Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs Hpanic Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    iDestruct (procs_inv_lookup Φ γs j γl Hgl with "Hprocs") as "#Hislock".
    (* ===================== PROLOGUE (32-byte frame, 4 slots) ============ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spd) by (rewrite /M1 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (kli_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
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
    (* +0x02..+0x08: save ra/s0/s1/s2 *)
    iPoseProof (kli_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x02)) (mword_of_int 3 : mword 6) kl_ra M1 (av - 4)%nat v1 b
              with "Hcg Hpc Hi02 [Hb1] [-]").
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.killed + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (kli_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x04)) (mword_of_int 2 : mword 6) kl_s0 M1 (av - 4)%nat v2 b
              with "Hcg Hpc Hi04 [Hb2] [-]").
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.killed + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (kli_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x06)) (mword_of_int 1 : mword 6) kl_s1 M1 (av - 4)%nat v3 b
              with "Hcg Hpc Hi06 [Hb3] [-]").
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.killed + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iPoseProof (kli_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x08)) (mword_of_int 0 : mword 6) kl_s2 M1 (av - 4)%nat v4 b
              with "Hcg Hpc Hi08 [Hb4] [-]").
    { iEval (rewrite HcspM1 -Hb4a). iExact "Hb4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hb4".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.killed + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* normalize the four saved cells to [add_vec spd _ ↦₈ (m !!! r)] *)
    assert (HraM1 : M1 !!! Regidx kl_ra = m !!! Regidx kl_ra) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0M1 : M1 !!! Regidx kl_s0 = m !!! Regidx kl_s0) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1M1 : M1 !!! Regidx kl_s1 = m !!! Regidx kl_s1) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2M1 : M1 !!! Regidx kl_s2 = m !!! Regidx kl_s2) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite HcspM1 HraM1) in "Hb1".
    iEval (rgne; rewrite HcspM1 Hs0M1) in "Hb2".
    iEval (rgne; rewrite HcspM1 Hs1M1) in "Hb3".
    iEval (rgne; rewrite HcspM1 Hs2M1) in "Hb4".
    (* +0x0a: c.addi4spn s0,sp,32 *)
    iPoseProof (kli_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) kl_s0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx kl_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx kl_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.killed + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c: c.mv s1,a0 -- park [p] in a callee-saved register *)
    iPoseProof (kli_0c with "Htext") as "Hi0c".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x0c)) kl_s1 kl_a0 A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 :=<[Regidx kl_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx kl_a0))]> A1).
    change (<[Regidx kl_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx kl_a0))]> A1) with A2.
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.killed + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx kl_s1 = proc_addr j).
    { rewrite /A2 upd_eq add_vec_zero_l.
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    assert (HA2a0 : A2 !!! Regidx kl_a0 = proc_addr j).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    (* +0x0e: jal ra,acquire *)
    iPoseProof (kli_0e with "Htext") as "Hi0e".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x0e)) kl_ra (mword_of_int 2091704 : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (B1 := <[Regidx kl_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.killed + 0x0e) : mword 64) 4)]> A2).
    change (<[Regidx kl_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.killed + 0x0e) : mword 64) 4)]> A2) with B1.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.killed + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2091704 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HB1ra : B1 !!! Regidx kl_ra = add_vec_int (mword_of_int (KernelSyms.killed + 0x0e) : mword 64) 4) by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1a0 : B1 !!! Regidx kl_a0 = proc_addr j)
      by (rewrite /B1 upd_ne; [exact HA2a0 | vm_compute; discriminate]).
    (* ===================== acquire(&p->lock) ===================== *)
    (* [Hcpu] was introduced at this function's ENTRY hart; the eight plain
       instructions above each moved to a fresh hart, so acquire wants it
       at [CID8]. *)
    iDestruct (cpu_own_transport CID CID8 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf Φ γl "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) B1 n eb p C (av - 4)%nat b
              Hn ltac:(lia)
              with "Hcg Hcpu Htext Hpc [Hislock] Hpanic [-]").
    { iEval (rewrite HB1a0). iExact "Hislock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsf Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hp12 : ret_pc (B1 !!! Regidx kl_ra) = mword_of_int (KernelSyms.killed + 0x12))
      by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* ---- open the lock: p->killed is in the ALWAYS-RESIDENT row ---- *)
    iDestruct (proc_lock_res_elim Φ γs γl (proc_addr j) with "HR") as (st ch) "(Hstate & Hchan & Hpub & Hslot)".
    iDestruct "Hpub" as (kl xs pid) "(Hkilled & Hxstate & Hpidhalf)".
    (* +0x12: c.lw a5,40(s1) *)
    assert (Hmacq_s1 : macq !!! Regidx kl_s1 = proc_addr j).
    { rewrite (callee_saved_lookup Hcs_acq kl_s1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact HA2s1. }
    iPoseProof (kli_12 with "Htext") as "Hi12".
    iEval (rewrite creg_c1; rewrite creg_c7) in "Hi12".
    assert (Haddr : add_vec (macq !!! Regidx kl_s1)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))))
                    = p_killed (proc_addr j))
      by (rewrite Hmacq_s1; apply kl_killed_off).
    iApply (wp_clw_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x12)) kl_a5 kl_s1
              (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00"))) macq (av - 4)%nat kl false
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [Hkilled] [-]").
    { iEval (rgne; rewrite Haddr). iExact "Hkilled". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hkilled". iEval (rgne; rewrite Haddr) in "Hkilled".
    set (C1 := <[Regidx kl_a5 := regval_into_reg (sign_extend' 64 kl)]> macq).
    change (<[Regidx kl_a5 := regval_into_reg (sign_extend' 64 kl)]> macq) with C1.
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.killed + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14: c.mv s2,a5 -- park the value across release *)
    iPoseProof (kli_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x14)) kl_s2 kl_a5 C1 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C2 := <[Regidx kl_s2 := regval_into_reg (add_vec zero_reg (C1 !!! Regidx kl_a5))]> C1).
    change (<[Regidx kl_s2 := regval_into_reg (add_vec zero_reg (C1 !!! Regidx kl_a5))]> C1) with C2.
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.killed + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    assert (HC2s2 : C2 !!! Regidx kl_s2 = sign_extend' 64 kl).
    { rewrite /C2 upd_eq add_vec_zero_l /C1 upd_eq. reflexivity. }
    (* +0x16: c.mv a0,s1 *)
    iPoseProof (kli_16 with "Htext") as "Hi16".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x16)) kl_a0 kl_s1 C2 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C3 := <[Regidx kl_a0 := regval_into_reg (add_vec zero_reg (C2 !!! Regidx kl_s1))]> C2).
    change (<[Regidx kl_a0 := regval_into_reg (add_vec zero_reg (C2 !!! Regidx kl_s1))]> C2) with C3.
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.killed + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    assert (HC2s1 : C2 !!! Regidx kl_s1 = proc_addr j).
    { rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact Hmacq_s1. }
    assert (HC3a0 : C3 !!! Regidx kl_a0 = proc_addr j)
      by (rewrite /C3 upd_eq add_vec_zero_l; exact HC2s1).
    (* +0x18: jal ra,release *)
    iPoseProof (kli_18 with "Htext") as "Hi18".
    iApply (wp_jal_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x18)) kl_ra (mword_of_int 2091830 : mword 21)
              C3 (av - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C4 := <[Regidx kl_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.killed + 0x18) : mword 64) 4)]> C3).
    change (<[Regidx kl_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.killed + 0x18) : mword 64) 4)]> C3) with C4.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.killed + 0x18) : mword 64) (sign_extend' 64 (mword_of_int 2091830 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HC4ra : C4 !!! Regidx kl_ra = add_vec_int (mword_of_int (KernelSyms.killed + 0x18) : mword 64) 4) by (rewrite /C4 upd_eq; reflexivity).
    assert (HC4a0 : C4 !!! Regidx kl_a0 = proc_addr j)
      by (rewrite /C4 upd_ne; [exact HC3a0 | vm_compute; discriminate]).
    assert (Hlka :add_vec (C4 !!! Regidx kl_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite HC4a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* reassemble the lock resource: nothing moved, so the slots go back as-is *)
    iAssert (proc_lock_res Φ γs γl (proc_addr j)) with "[Hstate Hchan Hkilled Hxstate Hpidhalf Hslot]" as "HR2".
    { iApply (proc_lock_res_intro Φ γs γl (proc_addr j) st ch with "Hstate Hchan [-Hslot] Hslot").
      iExists kl, xs, pid. iFrame "Hkilled Hxstate Hpidhalf". }
    (* ===================== release(&p->lock) ===================== *)
    iApply (Release.wp_release_sconf Φ γl (proc_addr j) "proc"%string
              (proc_lock_res Φ γs γl (proc_addr j)) C4 n eb p C (av - 4)%nat
              Hlka ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Hpay [-]").
    iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcs_rel Hcpu".
    (* release's exit index is [outb := match n with O => eb | S _ => false
       end]; [Hbeq] (derived up front) folds it back to [b] so the whole
       epilogue -- and the closing [wp_next_chain] -- sees a uniform [b]. *)
    rewrite Hbeq in Hsrel.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu".
    assert (Hp1c :ret_pc (C4 !!! Regidx kl_ra) = mword_of_int (KernelSyms.killed + 0x1c))
      by (rewrite HC4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* +0x1c: c.mv a0,s2 -- the return value *)
    assert (Hmrel_s2 : mrel !!! Regidx kl_s2 = sign_extend' 64 kl).
    { rewrite (callee_saved_lookup Hcs_rel kl_s2 ltac:(vm_compute; reflexivity)).
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate]. exact HC2s2. }
    iPoseProof (kli_1c with "Htext") as "Hi1c".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x1c)) kl_a0 kl_s2 mrel (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E0 := <[Regidx kl_a0 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx kl_s2))]> mrel).
    change (<[Regidx kl_a0 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx kl_s2))]> mrel) with E0.
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.killed + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* ===================== EPILOGUE ===================== *)
    assert (HE0csp : E0 !!! Regidx csp_rs1 = spd).
    { rewrite /E0 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspM1. }
    iPoseProof (kli_1e with "Htext") as "Hi1e".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x1e)) (mword_of_int 3 : mword 6) kl_ra
              E0 (av - 4)%nat (m !!! Regidx kl_ra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [Hb1] [-]").
    { iEval (rewrite HE0csp). iExact "Hb1". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hb1".
    set (E1 := <[Regidx kl_ra := regval_into_reg (m !!! Regidx kl_ra)]> E0).
    change (<[Regidx kl_ra := regval_into_reg (m !!! Regidx kl_ra)]> E0) with E1.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.killed + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
    iPoseProof (kli_20 with "Htext") as "Hi20".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x20)) (mword_of_int 2 : mword 6) kl_s0
              E1 (av - 4)%nat (m !!! Regidx kl_s0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [Hb2] [-]").
    { iEval (rewrite HE1csp). iExact "Hb2". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hb2".
    set (E2 := <[Regidx kl_s0 := regval_into_reg (m !!! Regidx kl_s0)]> E1).
    change (<[Regidx kl_s0 := regval_into_reg (m !!! Regidx kl_s0)]> E1) with E2.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.killed + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
    iPoseProof (kli_22 with "Htext") as "Hi22".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x22)) (mword_of_int 1 : mword 6) kl_s1
              E2 (av - 4)%nat (m !!! Regidx kl_s1) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [Hb3] [-]").
    { iEval (rewrite HE2csp). iExact "Hb3". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hb3".
    set (E3 := <[Regidx kl_s1 := regval_into_reg (m !!! Regidx kl_s1)]> E2).
    change (<[Regidx kl_s1 := regval_into_reg (m !!! Regidx kl_s1)]> E2) with E3.
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.killed + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
    iPoseProof (kli_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x24)) (mword_of_int 0 : mword 6) kl_s2
              E3 (av - 4)%nat (m !!! Regidx kl_s2) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hb4] [-]").
    { iEval (rewrite HE3csp). iExact "Hb4". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hb4".
    set (E4 := <[Regidx kl_s2 := regval_into_reg (m !!! Regidx kl_s2)]> E3).
    change (<[Regidx kl_s2 := regval_into_reg (m !!! Regidx kl_s2)]> E3) with E4.
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.killed + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.addi16sp sp,32 -- the frame pop *)
    assert (HE4csp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3csp | vm_compute; discriminate]).
    assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite /spd /sp0; apply frame_cancel_32).
    assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE4csp; exact Hup).
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HE4csp; symmetry; exact Hspd4).
    iPoseProof (kli_26 with "Htext") as "Hi26".
    iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -HE0csp). iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE1csp). iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE2csp). iExact "Hb3". }
      iSplitL "Hb4". { iExists _. iEval (rewrite Hb4a -HE3csp). iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x26)) (mword_of_int 2 : mword 6) E4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi26 Hframe4 [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.killed + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.killed + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28: c.ret *)
    assert (HE5ra : E5 !!! Regidx kl_ra = m !!! Regidx kl_ra).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iPoseProof (kli_28 with "Htext") as "Hi28".
    iApply (wp_cret_s_sconf Φ (mword_of_int (KernelSyms.killed + 0x28)) kl_ra E5 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi28 [-]").
    iIntros (CIDe7 Hse7) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E5 !!! Regidx kl_ra) = ret_tgt) by (rewrite HE5ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== the postcondition ===================== *)
    assert (HE5a0 : E5 !!! Regidx kl_a0 = sign_extend' 64 kl).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_eq add_vec_zero_l. exact Hmrel_s2. }
    assert (HE5csp : E5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E5 upd_eq; exact Hwv).
    assert (HE5s0 : E5 !!! Regidx kl_s0 = m !!! Regidx kl_s0).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2. apply upd_eq. }
    assert (HE5s1 : E5 !!! Regidx kl_s1 = m !!! Regidx kl_s1).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3. apply upd_eq. }
    assert (HE5s2 : E5 !!! Regidx kl_s2 = m !!! Regidx kl_s2).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4. apply upd_eq. }
    (* every other callee-saved register threads through both calls *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     r <> mword_of_int 18 -> E5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_rel r Hr).
      rewrite /C4 upd_ne; [| congruence].
      rewrite /C3 upd_ne; [| congruence].
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_acq r Hr).
      rewrite /B1 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* [Hcpu] came back from release at [CIDrel]; the seven plain epilogue
       instructions have each moved to a fresh hart, so [Hcont] -- specialized
       at the last one, [CIDe7] -- wants it there. *)
    iDestruct (cpu_own_transport CIDrel CIDe7 n eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 kl with "[%] Hcg Hcpu Hpc").
    split; [| exact HE5a0].
    unfold callee_saved.
    split; [exact HE5csp|].
    split; [exact HE5s0|]. split; [exact HE5s1|].
    split; [exact HE5s2|].
    repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofKilled.

End KilledProof.
