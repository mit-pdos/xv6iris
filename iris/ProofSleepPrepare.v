(* ProofSleepPrepare.v -- whole-function WP for sleep_prepare().

     void sleep_prepare(void *chan) {
       struct proc *p = myproc();
       acquire(&p->lock);
       if (chan == 0) panic("sleep_prepare: zero chan");
       p->chan = chan;
       release(&p->lock);
     }

   Twenty instructions @ KernelSyms.sleep_prepare (60 bytes).  The 32-byte
   frame saves ra/s0/s1/s2 in all four slots -- s1 parks the CHANNEL across
   both calls, s2 parks the PROC the interior myproc() returns.

   THE SHAPE IS setkilled's, with two differences.  The proc is not an
   argument: it is read out of [cpu_own]'s c->proc cell by the interior
   myproc(), whose contract pins the returned [a0] to the [p] the resource
   names -- here [proc_addr j].  And there is a [panic] arm, refuted rather
   than proved: the contract's [eq_vec chan zero_reg = false] makes the
   [c.beqz s1] fall through, which is what keeps [printk] out of this cone.

   The one interesting step is the [sd s1,32(s2)]: [p_chan] sits at the TOP
   LEVEL of [SchedCtx.proc_lock_res], so the write costs one existential
   destruct and one existential intro -- and because the invariant quantifies
   the channel, the value stored never has to be named.  sleep_prepare never
   learns the process's state and never touches either [proc_slots] guard. *)
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
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import FdSlots.
Require Import SchedCtx.
Require Import SpecMyproc SpecAcquire SpecRelease.
Require Import SpecSleepPrepare.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import CodeSleepPrepare.
Require Import ProcAvail.
Import Defs.
Local Open Scope Z_scope.

(* a failing tactic in a whole-function WP over the proc invariant otherwise
   spends tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

(* the [sd]'s 32-byte displacement is p->chan's offset *)
Lemma spr_chan_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 32 : mword 12)) = p_chan X.
Proof. rewrite /p_chan. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Module SleepPrepareProof (Myproc : MYPROC) (Acquire : ACQUIRE) (Release : RELEASE)
  : SLEEP_PREPARE.

Section ProofSleepPrepare.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation spr_ra := (mword_of_int 1 : mword 5).
  Notation spr_s0 := (mword_of_int 8 : mword 5).
  Notation spr_s1 := (mword_of_int 9 : mword 5).
  Notation spr_a0 := (mword_of_int 10 : mword 5).
  Notation spr_s2 := (mword_of_int 18 : mword 5).

  Lemma wp_sleep_prepare_sconf (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (b : bool)
      (lks : gset string)
    : wp_sleep_prepare_sconf_body γs j γl m av n eb b lks.
  Proof.
    cbv beta delta [wp_sleep_prepare_sconf_body].
    intros pcE pj chan ret_tgt Hj Hgl Hchan Hn Hav Hno.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    iDestruct (procs_inv_lookup γs j γl Hgl with "Hprocs") as "#Hislock".
    (* ===================== PROLOGUE (32-byte frame, 4 slots) ============ *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spd) by (rewrite /M1 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (spri_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
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
    (* +0x02..+0x08: save ra/s0/s1/s2 -- every slot is used here. *)
    iPoseProof (spri_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x02)) (mword_of_int 3 : mword 6) spr_ra M1 (av - 4)%nat v1 b
              with "Hcg Hpc Hi02 [Hb1]").
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (spri_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x04)) (mword_of_int 2 : mword 6) spr_s0 M1 (av - 4)%nat v2 b
              with "Hcg Hpc Hi04 [Hb2]").
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (spri_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x06)) (mword_of_int 1 : mword 6) spr_s1 M1 (av - 4)%nat v3 b
              with "Hcg Hpc Hi06 [Hb3]").
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iPoseProof (spri_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x08)) (mword_of_int 0 : mword 6) spr_s2 M1 (av - 4)%nat v4 b
              with "Hcg Hpc Hi08 [Hb4]").
    { iEval (rewrite HcspM1 -Hb4a). iExact "Hb4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hb4".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* normalize the four saved cells to [add_vec spd _ ↦₈ (m !!! r)] *)
    assert (HraM1 : M1 !!! Regidx spr_ra = m !!! Regidx spr_ra) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0M1 : M1 !!! Regidx spr_s0 = m !!! Regidx spr_s0) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1M1 : M1 !!! Regidx spr_s1 = m !!! Regidx spr_s1) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2M1 : M1 !!! Regidx spr_s2 = m !!! Regidx spr_s2) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite HcspM1 HraM1) in "Hb1".
    iEval (rgne; rewrite HcspM1 Hs0M1) in "Hb2".
    iEval (rgne; rewrite HcspM1 Hs1M1) in "Hb3".
    iEval (rgne; rewrite HcspM1 Hs2M1) in "Hb4".
    (* +0x0a: c.addi4spn s0,sp,32 *)
    iPoseProof (spri_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) spr_s0
              M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx spr_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx spr_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c: c.mv s1,a0 -- park the CHANNEL in a callee-saved register *)
    iPoseProof (spri_0c with "Htext") as "Hi0c".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x0c)) spr_s1 spr_a0 A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx spr_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx spr_a0))]> A1).
    change (<[Regidx spr_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx spr_a0))]> A1) with A2.
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    assert (HA1a0 : A1 !!! Regidx spr_a0 = chan).
    { rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /M1 upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HA2s1 : A2 !!! Regidx spr_s1 = chan)
      by (rewrite /A2 upd_eq add_vec_zero_l; exact HA1a0).
    (* ===================== p = myproc() ===================== *)
    iPoseProof (spri_0e with "Htext") as "Hi0e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x0e)) spr_ra (mword_of_int 2095592 : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (A3 := <[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x0e) : mword 64) 4)]> A2).
    change (<[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x0e) : mword 64) 4)]> A2) with A3.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.sleep_prepare + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2095592 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA3ra : A3 !!! Regidx spr_ra = add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x0e) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3s1 : A3 !!! Regidx spr_s1 = chan)
      by (rewrite /A3 upd_ne; [exact HA2s1 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID CID8 n eb pj b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf A3 (av - 4)%nat n eb pj b
              _ ltac:(lia) ltac:(lia)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID9 Hs9 ms mp) "%Hmsf Hcg Hcpu Hpc %Hmp".
    destruct Hmp as [Hcs_mp Ha0_mp].
    assert (Hp12 : ret_pc (A3 !!! Regidx spr_ra) = mword_of_int (KernelSyms.sleep_prepare + 0x12))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    assert (Hmp_s1 : mp !!! Regidx spr_s1 = chan).
    { rewrite (callee_saved_lookup Hcs_mp spr_s1 ltac:(vm_compute; reflexivity)). exact HA3s1. }
    (* +0x12: c.mv s2,a0 -- park the PROC *)
    iPoseProof (spri_12 with "Htext") as "Hi12".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x12)) spr_s2 spr_a0 mp (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B1 := <[Regidx spr_s2 := regval_into_reg (add_vec zero_reg (mp !!! Regidx spr_a0))]> mp).
    change (<[Regidx spr_s2 := regval_into_reg (add_vec zero_reg (mp !!! Regidx spr_a0))]> mp) with B1.
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HB1s2 : B1 !!! Regidx spr_s2 = proc_addr j)
      by (rewrite /B1 upd_eq add_vec_zero_l; exact Ha0_mp).
    assert (HB1s1 : B1 !!! Regidx spr_s1 = chan)
      by (rewrite /B1 upd_ne; [exact Hmp_s1 | vm_compute; discriminate]).
    assert (HB1a0 : B1 !!! Regidx spr_a0 = proc_addr j)
      by (rewrite /B1 upd_ne; [exact Ha0_mp | vm_compute; discriminate]).
    (* +0x14: jal ra,acquire *)
    iPoseProof (spri_14 with "Htext") as "Hi14".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x14)) spr_ra (mword_of_int 2092226 : mword 21)
              B1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (B2 := <[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x14) : mword 64) 4)]> B1).
    change (<[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x14) : mword 64) 4)]> B1) with B2.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.sleep_prepare + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2092226 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjacq) in "Hpc".
    assert (HB2ra : B2 !!! Regidx spr_ra = add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x14) : mword 64) 4) by (rewrite /B2 upd_eq; reflexivity).
    assert (HB2a0 : B2 !!! Regidx spr_a0 = proc_addr j)
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HB2s1 : B2 !!! Regidx spr_s1 = chan)
      by (rewrite /B2 upd_ne; [exact HB1s1 | vm_compute; discriminate]).
    assert (HB2s2 : B2 !!! Regidx spr_s2 = proc_addr j)
      by (rewrite /B2 upd_ne; [exact HB1s2 | vm_compute; discriminate]).
    (* ===================== acquire(&p->lock) ===================== *)
    iDestruct (cpu_own_transport CID9 CID11 n eb pj b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf γl "proc"%string
              (proc_lock_res γs γl (proc_addr j)) B2 n eb pj (av - 4)%nat b lks
              Hn ltac:(lia) Hno
              with "Hcg Hcpu Htext Hpc [Hislock]").
    all: try lkbelow.
    { iEval (rewrite HB2a0). iExact "Hislock". }
    iIntros (CIDacq Hsacq ms2 macq) "%Hmsf2 Hcg Hpc %Hcs_acq Hlocked HR Hcpu Hpay".
    assert (Hp18 : ret_pc (B2 !!! Regidx spr_ra) = mword_of_int (KernelSyms.sleep_prepare + 0x18))
      by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    assert (Hmacq_s1 : macq !!! Regidx spr_s1 = chan).
    { rewrite (callee_saved_lookup Hcs_acq spr_s1 ltac:(vm_compute; reflexivity)). exact HB2s1. }
    assert (Hmacq_s2 : macq !!! Regidx spr_s2 = proc_addr j).
    { rewrite (callee_saved_lookup Hcs_acq spr_s2 ltac:(vm_compute; reflexivity)). exact HB2s2. }
    (* ---- open the lock: p->chan is in the ALWAYS-RESIDENT row ---- *)
    iDestruct (proc_lock_res_elim γs γl (proc_addr j) with "HR") as (st ch) "(Hstate & Hpg & Hchcell & Hpub & Hslot)".
    (* +0x18: c.beqz s1,+0x30 -- the panic arm, REFUTED by the contract. *)
    iPoseProof (spri_18 with "Htext") as "Hi18".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x18)) (mword_of_int 12 : mword 8)
              (Cregidx (mword_of_int 1)) spr_s1
              macq (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hmacq_s1; exact Hchan)
              with "Hcg Hpc Hi18").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a: sd s1,32(s2) -- p->chan = chan *)
    iPoseProof (spri_1a with "Htext") as "Hi1a".
    assert (Hsaddr : add_vec (macq !!! Regidx spr_s2) (sign_extend' 64 (mword_of_int 32 : mword 12))
                     = p_chan (proc_addr j))
      by (rewrite Hmacq_s2; apply spr_chan_off).
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x1a)) spr_s1 spr_s2
              (mword_of_int 32 : mword 12) macq (trap_res b + (av - 4))%nat ch false
              with "Hcg Hpc Hi1a [Hchcell]").
    { iEval (rgne; rewrite Hsaddr). iExact "Hchcell". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hchcell".
    iEval (repeat rgne; rewrite Hsaddr) in "Hchcell".
    iAssert (∃ chv : mword 64, p_chan (proc_addr j) ↦₈ chv)%I with "[Hchcell]" as (chv) "Hchcell".
    { iExists _. iExact "Hchcell". }
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.sleep_prepare + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* +0x1e: c.mv a0,s2 *)
    iPoseProof (spri_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x1e)) spr_a0 spr_s2 macq (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (C1 := <[Regidx spr_a0 := regval_into_reg (add_vec zero_reg (macq !!! Regidx spr_s2))]> macq).
    change (<[Regidx spr_a0 := regval_into_reg (add_vec zero_reg (macq !!! Regidx spr_s2))]> macq) with C1.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x1e) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HC1a0 : C1 !!! Regidx spr_a0 = proc_addr j)
      by (rewrite /C1 upd_eq add_vec_zero_l; exact Hmacq_s2).
    (* +0x20: jal ra,release *)
    iPoseProof (spri_20 with "Htext") as "Hi20".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x20)) spr_ra (mword_of_int 2092350 : mword 21)
              C1 (trap_res b + (av - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi20").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (C2 := <[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x20) : mword 64) 4)]> C1).
    change (<[Regidx spr_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x20) : mword 64) 4)]> C1) with C2.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.sleep_prepare + 0x20) : mword 64) (sign_extend' 64 (mword_of_int 2092350 : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HC2ra : C2 !!! Regidx spr_ra = add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x20) : mword 64) 4) by (rewrite /C2 upd_eq; reflexivity).
    assert (HC2a0 : C2 !!! Regidx spr_a0 = proc_addr j)
      by (rewrite /C2 upd_ne; [exact HC1a0 | vm_compute; discriminate]).
    assert (Hlka : add_vec (C2 !!! Regidx spr_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr j).
    { rewrite HC2a0.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* reassemble the lock resource: [proc_lock_res] quantifies the channel,
       so the stored value need never be named. *)
    iAssert (proc_lock_res γs γl (proc_addr j)) with "[Hstate Hpg Hchcell Hpub Hslot]" as "HR2".
    { iApply (proc_lock_res_intro γs γl (proc_addr j) st chv with "Hstate Hpg Hchcell Hpub Hslot"). }
    (* ===================== release(&p->lock) ===================== *)
    iEval (rewrite -Hbeq) in "Hcg".
    iApply (Release.wp_release_sconf γl (proc_addr j) "proc"%string
              (proc_lock_res γs γl (proc_addr j)) C2 n eb pj (av - 4)%nat
              ({["proc"]} ∪ lks)
              Hlka ltac:(lia)
              with "Hcg Htext Hpc Hislock Hlocked HR2 Hcpu Hpay").
    iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcs_rel Hcpu".
    (* acquire handed back [{[rank "proc"]} ∪ lks]; release hands back that
       set minus the same singleton.  [Hno], via [locks_below_not_elem],
       says "proc" was fresh in [lks], so the round trip is a no-op. *)
    pose proof (locks_below_not_elem lks "proc" Hno) as Hnotin.
    assert (Heqlks : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Heqlks) in "Hcpu".
    rewrite Hbeq in Hsrel.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcpu".
    assert (Hp24 : ret_pc (C2 !!! Regidx spr_ra) = mword_of_int (KernelSyms.sleep_prepare + 0x24))
      by (rewrite HC2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* ===================== EPILOGUE ===================== *)
    assert (Hmrelcsp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs_rel csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_acq csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs_mp csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspM1. }
    iPoseProof (spri_24 with "Htext") as "Hi24".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x24)) (mword_of_int 3 : mword 6) spr_ra
              mrel (av - 4)%nat (m !!! Regidx spr_ra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [Hb1]").
    { iEval (rewrite Hmrelcsp). iExact "Hb1". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hb1".
    set (E0 := <[Regidx spr_ra := regval_into_reg (m !!! Regidx spr_ra)]> mrel).
    change (<[Regidx spr_ra := regval_into_reg (m !!! Regidx spr_ra)]> mrel) with E0.
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    assert (HE0csp : E0 !!! Regidx csp_rs1 = spd) by (rewrite /E0 upd_ne; [exact Hmrelcsp | vm_compute; discriminate]).
    iPoseProof (spri_26 with "Htext") as "Hi26".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x26)) (mword_of_int 2 : mword 6) spr_s0
              E0 (av - 4)%nat (m !!! Regidx spr_s0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [Hb2]").
    { iEval (rewrite HE0csp). iExact "Hb2". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hb2".
    set (E1 := <[Regidx spr_s0 := regval_into_reg (m !!! Regidx spr_s0)]> E0).
    change (<[Regidx spr_s0 := regval_into_reg (m !!! Regidx spr_s0)]> E0) with E1.
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
    iPoseProof (spri_28 with "Htext") as "Hi28".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x28)) (mword_of_int 1 : mword 6) spr_s1
              E1 (av - 4)%nat (m !!! Regidx spr_s1) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi28 [Hb3]").
    { iEval (rewrite HE1csp). iExact "Hb3". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hb3".
    set (E2 := <[Regidx spr_s1 := regval_into_reg (m !!! Regidx spr_s1)]> E1).
    change (<[Regidx spr_s1 := regval_into_reg (m !!! Regidx spr_s1)]> E1) with E2.
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
    iPoseProof (spri_2a with "Htext") as "Hi2a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x2a)) (mword_of_int 0 : mword 6) spr_s2
              E2 (av - 4)%nat (m !!! Regidx spr_s2) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hb4]").
    { iEval (rewrite HE2csp). iExact "Hb4". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hb4".
    set (E3 := <[Regidx spr_s2 := regval_into_reg (m !!! Regidx spr_s2)]> E2).
    change (<[Regidx spr_s2 := regval_into_reg (m !!! Regidx spr_s2)]> E2) with E3.
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c: c.addi16sp sp,32 -- the frame pop *)
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
    assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite /spd /sp0; apply frame_cancel_32).
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE3csp; exact Hup).
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HE3csp; symmetry; exact Hspd4).
    iPoseProof (spri_2c with "Htext") as "Hi2c".
    iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -Hmrelcsp). iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE0csp). iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE1csp). iExact "Hb3". }
      iSplitL "Hb4". { iExists _. iEval (rewrite Hb4a -HE2csp). iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x2c)) (mword_of_int 2 : mword 6) E3 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi2c Hframe4").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.sleep_prepare + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.sleep_prepare + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e: c.ret *)
    assert (HE4ra : E4 !!! Regidx spr_ra = m !!! Regidx spr_ra).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0. apply upd_eq. }
    iPoseProof (spri_2e with "Htext") as "Hi2e".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.sleep_prepare + 0x2e)) spr_ra E4 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi2e").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E4 !!! Regidx spr_ra) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== the postcondition ===================== *)
    assert (HE4csp : E4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E4 upd_eq; exact Hwv).
    assert (HE4s0 : E4 !!! Regidx spr_s0 = m !!! Regidx spr_s0).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    assert (HE4s1 : E4 !!! Regidx spr_s1 = m !!! Regidx spr_s1).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2. apply upd_eq. }
    assert (HE4s2 : E4 !!! Regidx spr_s2 = m !!! Regidx spr_s2).
    { rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3. apply upd_eq. }
    (* every other callee-saved register threads through all three calls *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     r <> mword_of_int 18 ->
                     E4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E4 upd_ne; [| reg_ne_side].
      rewrite /E3 upd_ne; [| reg_ne_side].
      rewrite /E2 upd_ne; [| reg_ne_side].
      rewrite /E1 upd_ne; [| reg_ne_side].
      rewrite /E0 upd_ne; [| reg_ne_side].
      rewrite (callee_saved_lookup Hcs_rel r Hr).
      rewrite /C2 upd_ne; [| reg_ne_side].
      rewrite /C1 upd_ne; [| reg_ne_side].
      rewrite (callee_saved_lookup Hcs_acq r Hr).
      rewrite /B2 upd_ne; [| reg_ne_side].
      rewrite /B1 upd_ne; [| reg_ne_side].
      rewrite (callee_saved_lookup Hcs_mp r Hr).
      rewrite /A3 upd_ne; [| reg_ne_side].
      rewrite /A2 upd_ne; [| reg_ne_side].
      rewrite /A1 upd_ne; [| reg_ne_side].
      rewrite /M1 upd_ne; [| reg_ne_side]. reflexivity. }
    iDestruct (cpu_own_transport CIDrel CIDe6 n eb pj b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E4 with "[%] Hcg Hcpu Hpc").
    unfold callee_saved.
    split; [exact HE4csp|].
    split; [exact HE4s0|]. split; [exact HE4s1|]. split; [exact HE4s2|].
    repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSleepPrepare.

End SleepPrepareProof.
