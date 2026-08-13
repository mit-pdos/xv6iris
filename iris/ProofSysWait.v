(* ProofSysWait.v -- whole-function WP for sys_wait().

   The C, the instruction map and the contract are in SpecSysWait.v.  The
   function is sys_kill's shape byte for byte (a 32-byte ra/s0 frame, an
   argument read into a frame local, one call, one tail), so this proof is
   ProofSysKill.v's with three differences, all of them in what the local
   IS and what the second callee wants:

   * [uint64 p] is a WHOLE frame slot (slot 3), not the upper half of one,
     so there is no [word_pointsto_split4]/[join] pair here -- the cell goes
     into argaddr as [↦₈] and comes back as [↦₈ v0].

   * the trapframe fraction argaddr wants is SPLIT OUT of [proc_priv] for
     the duration of the call ([ProcInv.proc_priv_tf]) and put straight
     back, because the second callee wants the whole block.  That is the
     only reason this contract names [pv_tf V] rather than a free [ws].

   * kwait carries far more than kkill did -- wait_lock, the scheduler
     chain, the running-thread bundle -- but sys_wait adds nothing to any of
     it: every one of those resources is threaded from the precondition to
     the call untouched. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ProcGeom.
Require Import KallocInv.
Require Import UserPtTree.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgaddr SpecKwait.
Require Import SpecSysWait.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeSysWait.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a WP over [proc_priv] otherwise spends tens of
   minutes FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation SW := KernelSyms.sys_wait.

(* [addi a1,s0,-24] and [ld a0,-24(s0)]: the [uint64 p] local is frame
   slot 3 outright, so ONE address lemma serves both. *)
Lemma swt_addr_p (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4072 : mword 12)) = StackOwn.pa_stk X 3.
Proof.
  unfold StackOwn.pa_stk, add_vec_int.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* The stack budgets and the nesting bound, as NAMED lemmas with only
   [nat]/[Z] in scope: an inline [ltac:(lia)] answers "Cannot find witness"
   under the zify hook once the context carries [bv_unsigned]s. *)
Lemma sw_frame (av : nat) : (sys_wait_stack <= av)%nat -> (4 <= av)%nat.
Proof. unfold sys_wait_stack, K_kwait. lia. Qed.
Lemma sw_Kaa (av : nat) : (sys_wait_stack <= av)%nat -> (argaddr_stack <= av - 4)%nat.
Proof. unfold sys_wait_stack, K_kwait, argaddr_stack. lia. Qed.
Lemma sw_Kkw (av : nat) : (sys_wait_stack <= av)%nat -> (K_kwait <= av - 4)%nat.
Proof. unfold sys_wait_stack. lia. Qed.
Lemma sw_back (av : nat) : (sys_wait_stack <= av)%nat -> ((av - 4) + 4)%nat = av.
Proof. unfold sys_wait_stack, K_kwait. lia. Qed.
Lemma sw_ilvl0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma sw_arg0 : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Module SysWaitProof (Argaddr : ARGADDR) (Kwait : KWAIT) : SYSWAIT.

Section ProofSysWait.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Lemma wp_sys_wait_sconf
      (γa γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) (v0 : mword 64)
    : wp_sys_wait_sconf_body γa γf γw γs j γl m av eb C b pid V v0.
  Proof.
    cbv beta delta [wp_sys_wait_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Hv0 Hav Heb.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc #Hprocs #Hpanic
             #Hlk #Henv Hpriv Hcont".
    iPoseProof (swi_00 with "Htext") as "Hi00".
    iPoseProof (swi_02 with "Htext") as "Hi02".
    iPoseProof (swi_04 with "Htext") as "Hi04".
    iPoseProof (swi_06 with "Htext") as "Hi06".
    iPoseProof (swi_08 with "Htext") as "Hi08".
    iPoseProof (swi_0c with "Htext") as "Hi0c".
    iPoseProof (swi_0e with "Htext") as "Hi0e".
    iPoseProof (swi_12 with "Htext") as "Hi12".
    iPoseProof (swi_16 with "Htext") as "Hi16".
    iPoseProof (swi_1a with "Htext") as "Hi1a".
    iPoseProof (swi_1c with "Htext") as "Hi1c".
    iPoseProof (swi_1e with "Htext") as "Hi1e".
    iPoseProof (swi_20 with "Htext") as "Hi20".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              (sw_frame av Hav) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SW + 0x02)) by pcstep.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (w3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    (* the two save-slot addresses, as the c.sdsp displacements compute them *)
    assert (Hpa : forall u k : nat, (k + u = 4)%nat -> (u < 4)%nat ->
              add_vec (M1 !!! Regidx csp_rs1)
                (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))
              = pa_stk sp0 k).
    { intros u k Hku Hu. rewrite HM1sp.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
        apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hpa1 := Hpa 3%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hpa2 := Hpa 2%nat 2%nat ltac:(lia) ltac:(lia)).
    (* +0x02 c.sdsp ra,24(sp) ; +0x04 c.sdsp s0,16(sp) *)
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SW + 0x02)) (mword_of_int 3 : mword 6) Rra
              M1 (av - 4)%nat u1 b with "Hcg Hpc Hi02 Hb1 [-]").
    iIntros (CID2 Hk2) "Hcg Hpc Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (SW + 0x02) : mword 64) 2 = mword_of_int (SW + 0x04)) by pcstep.
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SW + 0x04)) (mword_of_int 2 : mword 6) Rs0
              M1 (av - 4)%nat u2 b with "Hcg Hpc Hi04 Hb2 [-]").
    iIntros (CID3 Hk3) "Hcg Hpc Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (SW + 0x04) : mword 64) 2 = mword_of_int (SW + 0x06)) by pcstep.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite Hpa1 HM1ra) in "Hb1".
    iEval (rgne; rewrite Hpa2 HM1s0) in "Hb2".
    (* +0x06 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SW + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hk4) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hpp08 : add_vec_int (mword_of_int (SW + 0x06) : mword 64) 2 = mword_of_int (SW + 0x08)) by pcstep.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0)
      by (rewrite /A1 upd_eq HM1sp; apply stk_fp_32).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    (* +0x08 addi a1,s0,-24 : a1 := &p *)
    assert (Hrg08 : rget (CID := CID4) A1 Rs0 = A1 !!! Regidx Rs0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (SW + 0x08)) Ra1 Rs0 (mword_of_int 4072 : mword 12)
              A1 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hk5) "Hcg Hpc".
    iEval (rewrite Hrg08) in "Hcg".
    set (A2 := <[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 4072 : mword 12)))]> A1).
    change (<[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 4072 : mword 12)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (SW + 0x08) : mword 64) 4 = mword_of_int (SW + 0x0c)) by pcstep.
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx Ra1 = pa_stk sp0 3)
      by (rewrite /A2 upd_eq HA1s0; apply swt_addr_p).
    (* +0x0c c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (SW + 0x0c)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (A3 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2) with A3.
    assert (Hpp0e : add_vec_int (mword_of_int (SW + 0x0c) : mword 64) 2 = mword_of_int (SW + 0x0e)) by pcstep.
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e jal ra,argaddr *)
    iApply (wp_jal_s_sconf (mword_of_int (SW + 0x0e)) Rra (mword_of_int 2096892 : mword 21)
              A3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (A4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SW + 0x0e) : mword 64) 4)]> A3).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SW + 0x0e) : mword 64) 4)]> A3) with A4.
    assert (Hjaa : add_vec (mword_of_int (SW + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096892 : mword 21)) = mword_of_int KernelSyms.argaddr)
      by pcstep.
    iEval (rewrite Hjaa) in "Hpc".
    assert (HA4ra : A4 !!! Regidx Rra = add_vec_int (mword_of_int (SW + 0x0e) : mword 64) 4)
      by (rewrite /A4; apply upd_eq).
    assert (HA4a0 : A4 !!! Regidx Ra0 = mword_of_int (Z.of_nat 0%nat)).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate]. rewrite /A3. apply upd_eq. }
    assert (HA4a1 : A4 !!! Regidx Ra1 = pa_stk sp0 3).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate]. exact HA2a1. }
    assert (HA4s0 : A4 !!! Regidx Rs0 = sp0).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. exact HA1s0. }
    assert (HA4sp : A4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate]. exact HA1sp. }
    (* ===================== argaddr(0, &p) ===================== *)
    (* the trapframe fraction is BORROWED out of the private block: kwait
       wants the block back whole, so it goes straight back below. *)
    iDestruct (proc_priv_tf γf pj pid V with "Hpriv") as "(Htf & Hpage & Hback)".
    iEval (rewrite -HA4a1) in "Hb3".
    iDestruct (cpu_own_transport CID CID7 0%nat eb pj C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argaddr.wp_argaddr_sconf A4 (av - 4)%nat 0%nat eb pj C 0%nat
              (ud_tfp (pv_upt V)) (pv_tf V) v0 w3 (DfracOwn (1/4)) b
              sw_arg0 HA4a0 Hv0 sw_ilvl0 (sw_Kaa av Hav)
              with "Hcg Hcpu Htext Hdata Hpc Htf Hpage Hb3 [-]").
    iIntros (CID8 Hk8 Mai) "%HcsAi Hcg Hcpu Hpc Htf Hpage Hb3".
    iEval (rewrite HA4a1) in "Hb3".
    iDestruct ("Hback" with "Htf Hpage") as "Hpriv".
    assert (Hpp12 : ret_pc (A4 !!! Regidx Rra) = mword_of_int (SW + 0x12))
      by (rewrite HA4ra; pcstep).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HAis0 : Mai !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsAi Rs0 ltac:(vm_compute; reflexivity)); exact HA4s0).
    assert (HAisp : Mai !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsAi csp_rs1 ltac:(vm_compute; reflexivity)); exact HA4sp).
    (* +0x12 ld a0,-24(s0) : a0 := p *)
    assert (Haddrp : add_vec (rget (CID := CID8) Mai Rs0)
                       (sign_extend' 64 (mword_of_int 4072 : mword 12)) = pa_stk sp0 3).
    { rewrite (rget_ne (CID := CID8) Mai Rs0 ltac:(vm_compute; discriminate)) HAis0.
      apply swt_addr_p. }
    iEval (rewrite -Haddrp) in "Hb3".
    iApply (wp_ld_s_sconf (mword_of_int (SW + 0x12)) Ra0 Rs0 (mword_of_int 4072 : mword 12)
              Mai (av - 4)%nat v0 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 Hb3 [-]").
    iIntros (CID9 Hk9) "Hcg Hpc Hb3".
    iEval (rewrite Haddrp) in "Hb3".
    set (B1 := <[Regidx Ra0 := regval_into_reg v0]> Mai).
    change (<[Regidx Ra0 := regval_into_reg v0]> Mai) with B1.
    assert (Hpp16 : add_vec_int (mword_of_int (SW + 0x12) : mword 64) 4 = mword_of_int (SW + 0x16)) by pcstep.
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 jal ra,kwait *)
    iApply (wp_jal_s_sconf (mword_of_int (SW + 0x16)) Rra (mword_of_int 2095138 : mword 21)
              B1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID10 Hk10) "Hcg Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SW + 0x16) : mword 64) 4)]> B1).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SW + 0x16) : mword 64) 4)]> B1) with B2.
    assert (Hjkw : add_vec (mword_of_int (SW + 0x16) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095138 : mword 21)) = mword_of_int KernelSyms.kwait)
      by pcstep.
    iEval (rewrite Hjkw) in "Hpc".
    assert (HB2ra : B2 !!! Regidx Rra = add_vec_int (mword_of_int (SW + 0x16) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact HAisp. }
    (* ===================== kwait(p) ===================== *)
    iDestruct (cpu_own_transport CID8 CID10 0%nat eb pj C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Kwait.wp_kwait_sconf γa γf γw γs j γl B2 (av - 4)%nat eb C b pid V
              Hj Hgl (sw_Kkw av Hav) Heb
              with "Hcg Hcpu Htext Hpc Hprocs Hpanic Hlk Henv Hpriv [-]").
    iIntros (CID11 Hk11 Mkw P' rv) "%Hkw %Hext Hcg Hcpu Hpc Hpriv".
    destruct Hkw as (HcsKw & HKwa0).
    assert (Hpp1a : ret_pc (B2 !!! Regidx Rra) = mword_of_int (SW + 0x1a))
      by (rewrite HB2ra; pcstep).
    iEval (rewrite Hpp1a) in "Hpc".
    assert (HKwsp : Mkw !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsKw csp_rs1 ltac:(vm_compute; reflexivity)); exact HB2sp).
    (* ===================== EPILOGUE ===================== *)
    assert (Hqa : forall u k : nat, (k + u = 4)%nat -> (u < 4)%nat ->
              add_vec (pa_stk sp0 4)
                (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))
              = pa_stk sp0 k).
    { intros u k Hku Hu.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite pa_stk_off2;
        apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hqa1 := Hqa 3%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hqa2 := Hqa 2%nat 2%nat ltac:(lia) ltac:(lia)).
    (* +0x1a c.ldsp ra,24(sp) *)
    iEval (rewrite -Hqa1 -HKwsp) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (SW + 0x1a)) (mword_of_int 3 : mword 6) Rra
              Mkw (av - 4)%nat (m !!! Regidx Rra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a Hb1 [-]").
    iIntros (CID12 Hk12) "Hcg Hpc Hb1".
    iEval (rewrite HKwsp Hqa1) in "Hb1".
    set (E0 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Mkw).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> Mkw) with E0.
    assert (Hpp1c : add_vec_int (mword_of_int (SW + 0x1a) : mword 64) 2 = mword_of_int (SW + 0x1c)) by pcstep.
    iEval (rewrite Hpp1c) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /E0 upd_ne; [exact HKwsp | vm_compute; discriminate]).
    (* +0x1c c.ldsp s0,16(sp) *)
    iEval (rewrite -Hqa2 -HE0sp) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (SW + 0x1c)) (mword_of_int 2 : mword 6) Rs0
              E0 (av - 4)%nat (m !!! Regidx Rs0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c Hb2 [-]").
    iIntros (CID13 Hk13) "Hcg Hpc Hb2".
    iEval (rewrite HE0sp Hqa2) in "Hb2".
    set (E1 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E0).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E0) with E1.
    assert (Hpp1e : add_vec_int (mword_of_int (SW + 0x1c) : mword 64) 2 = mword_of_int (SW + 0x1e)) by pcstep.
    iEval (rewrite Hpp1e) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /E1 upd_ne; [exact HE0sp | vm_compute; discriminate]).
    (* +0x1e c.addi16sp sp,32 -- the frame pop *)
    assert (Hwv : add_vec (E1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE1sp; apply stk_pop_32).
    assert (Hpop : E1 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HE1sp).
    iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1". { iExists _. iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iExact "Hb3". }
      iSplitL "Hb4". { iExists _. iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SW + 0x1e)) (mword_of_int 2 : mword 6)
              E1 (av - 4)%nat 4 b Hpop with "Hcg Hpc Hi1e Hframe [-]").
    iIntros (CID14 Hk14) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by (exact (sw_back av Hav)).
    iEval (rewrite Hnk) in "Hcg".
    set (E2 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E1).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E1) with E2.
    assert (Hpp20 : add_vec_int (mword_of_int (SW + 0x1e) : mword 64) 2 = mword_of_int (SW + 0x20)) by pcstep.
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.ret *)
    assert (HE2ra : E2 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0. apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (SW + 0x20)) Rra E2 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi20 [-]").
    iIntros (CID15 Hk15) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E2 !!! Regidx Rra) = ret_tgt) by (rewrite HE2ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== the postcondition ===================== *)
    assert (HE2sp : E2 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1) by (rewrite /E2 upd_eq; exact Hwv).
    assert (HE2s0 : E2 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1. apply upd_eq. }
    assert (HE2a0 : E2 !!! Regidx Ra0 = sign_extend' 64 rv).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact HKwa0. }
    (* every other callee-saved register threads through both calls *)
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 ->
                     E2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsKw r Hr).
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsAi r Hr).
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID11 CID15 0%nat eb pj C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID15 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E2 P' rv with "[%] [%] Hcg Hcpu Hpc Hpriv").
    { split; [| exact HE2a0].
      unfold callee_saved.
      split; [exact HE2sp|]. split; [exact HE2s0|].
      repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
      apply Hthr; vm_compute; first [reflexivity | discriminate]. }
    { exact Hext. }
  Qed.

End ProofSysWait.

End SysWaitProof.
