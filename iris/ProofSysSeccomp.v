(* ProofSysSeccomp.v -- whole-function WP for sys_seccomp() (upstream
   a083670).

   The C, the instruction map and the contract are in SpecSysSeccomp.v.
   The first seven instructions are sys_wait's byte for byte (a 32-byte
   ra/s0 frame, [addi a1,s0,-24; li a0,0; jal argaddr], the mask local in
   frame slot 3), so the prologue and the argaddr call are ProofSysWait.v's;
   the myproc call is ProofSysGetpid.v's.  What is new is the body:

     +0x16  ld a5,360(a0)     the mask cell, out of [proc_priv]
                              ([ProcInv.proc_priv_secc])
     +0x1a  ld a4,-24(s0)     the local argaddr wrote
     +0x1e  c.and a5,a5,a4
     +0x20  sd a5,360(a0)     the cell back, at [and_vec (pv_secc V) v0]
     +0x24  c.li a0,0         return 0

   The block comes back at [ProcInv.us_set_secc U (and_vec ..)], which is
   [ProcInv.us_secc U v0] on the nose ([ProcInv.us_secc_set]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import PageGeom ProcPtOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecArgaddr SpecMyproc.
Require Import SpecSysSeccomp.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeSysSeccomp.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import CtxIdDefs.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a WP over [proc_priv] otherwise spends tens of
   minutes FORMATTING the goal -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

Notation SC := KernelSyms.sys_seccomp.

(* [addi a1,s0,-24] and [ld a4,-24(s0)]: the [uint64 mask] local is frame
   slot 3 outright ([ProofSysWait.swt_addr_p]'s twin). *)
Lemma scc_addr_mask (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4072 : mword 12)) = StackOwn.pa_stk X 3.
Proof.
  unfold StackOwn.pa_stk, add_vec_int.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* the budgets, as NAMED lemmas with only [nat] in scope *)
Lemma scc_frame (av : nat) : (sys_seccomp_stack <= av)%nat -> (4 <= av)%nat.
Proof. lia. Qed.
Lemma scc_Kaa (av : nat) : (sys_seccomp_stack <= av)%nat -> (argaddr_stack <= av - 4)%nat.
Proof. lia. Qed.
Lemma scc_Kmp (av : nat) : (sys_seccomp_stack <= av)%nat -> (10 <= av - 4)%nat.
Proof. lia. Qed.
Lemma scc_back (av : nat) : (sys_seccomp_stack <= av)%nat -> ((av - 4) + 4)%nat = av.
Proof. lia. Qed.
Lemma scc_arg0 : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Module SysSeccompProof (Argaddr : ARGADDR) (Myproc : MYPROC) : SYSSECCOMP.

Section ProofSysSeccomp.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !wchG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* argaddr's page-validity premise off the block ([ProofKforkParts]'s
     [proc_priv_tfp_valid], restated here to keep this proof off kfork's
     cone). *)
  Local Lemma scc_tfp_valid (γf : gname) (pa : mword 64) (pid : mword 32)
      (U : ustate) :
    proc_priv γf pa pid U -∗ ⌜page_valid (page_base (ud_tfp (pv_upt (us_V U))))⌝.
  Proof using .
    iIntros "[(_ & _ & _ & _ & Hpt & _) _]".
    rewrite /proc_ptm_at. iDestruct "Hpt" as "(_ & _ & Hptt)".
    iDestruct (proc_ptm_wf with "Hptt") as "%Hwf".
    iPureIntro. exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  Lemma wp_sys_seccomp_sconf (γf : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (U : ustate) (v0 : mword 64) (b : bool) (lks : gset string)
    : wp_sys_seccomp_sconf_body γf m av n eb p pid U v0 b lks.
  Proof using .
    cbv beta delta [wp_sys_seccomp_sconf_body].
    intros pcE ret_tgt Hv0 Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hpriv Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b
              (scc_frame av Hav) (stk_push_32 (m !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (secci_00 with "Htext"). }
    iIntros (CID1 Hk1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (SC + 0x02)) by pcstep.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /M1 upd_eq; apply stk_push_32).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (w3) "Hb3". iDestruct "S4" as (u4) "Hb4".
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
    iApply (wp_csdsp_s_sconf (mword_of_int (SC + 0x02)) (mword_of_int 3 : mword 6) Rra
              M1 (av - 4)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (secci_02 with "Htext"). }
    iIntros (CID2 Hk2) "Hcg Hpc Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (SC + 0x02) : mword 64) 2 = mword_of_int (SC + 0x04)) by pcstep.
    iEval (rewrite Hpp04) in "Hpc".
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SC + 0x04)) (mword_of_int 2 : mword 6) Rs0
              M1 (av - 4)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (secci_04 with "Htext"). }
    iIntros (CID3 Hk3) "Hcg Hpc Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (SC + 0x04) : mword 64) 2 = mword_of_int (SC + 0x06)) by pcstep.
    iEval (rewrite Hpp06) in "Hpc".
    assert (HM1ra : M1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HM1s0 : M1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rgne; rewrite Hpa1 HM1ra) in "Hb1".
    iEval (rgne; rewrite Hpa2 HM1s0) in "Hb2".
    (* +0x06 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SC + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 M1 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (secci_06 with "Htext"). }
    iIntros (CID4 Hk4) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hpp08 : add_vec_int (mword_of_int (SC + 0x06) : mword 64) 2 = mword_of_int (SC + 0x08)) by pcstep.
    iEval (rewrite Hpp08) in "Hpc".
    assert (HA1s0 : A1 !!! Regidx Rs0 = sp0)
      by (rewrite /A1 upd_eq HM1sp; apply stk_fp_32).
    assert (HA1sp : A1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /A1 upd_ne; [exact HM1sp | vm_compute; discriminate]).
    (* +0x08 addi a1,s0,-24 : a1 := &mask *)
    assert (Hrg08 : rget (CID := CID4) A1 Rs0 = A1 !!! Regidx Rs0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf (mword_of_int (SC + 0x08)) Ra1 Rs0 (mword_of_int 4072 : mword 12)
              A1 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (secci_08 with "Htext"). }
    iIntros (CID5 Hk5) "Hcg Hpc".
    iEval (rewrite Hrg08) in "Hcg".
    set (A2 := <[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 4072 : mword 12)))]> A1).
    change (<[Regidx Ra1 := regval_into_reg
        (add_vec (A1 !!! Regidx Rs0) (sign_extend' 64 (mword_of_int 4072 : mword 12)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (SC + 0x08) : mword 64) 4 = mword_of_int (SC + 0x0c)) by pcstep.
    iEval (rewrite Hpp0c) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx Ra1 = pa_stk sp0 3)
      by (rewrite /A2 upd_eq HA1s0; apply scc_addr_mask).
    (* +0x0c c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (SC + 0x0c)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (secci_0c with "Htext"). }
    iIntros (CID6 Hk6) "Hcg Hpc".
    set (A3 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> A2) with A3.
    assert (Hpp0e : add_vec_int (mword_of_int (SC + 0x0c) : mword 64) 2 = mword_of_int (SC + 0x0e)) by pcstep.
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e jal ra,argaddr *)
    iApply (wp_jal_s_sconf (mword_of_int (SC + 0x0e)) Rra (mword_of_int 2096446 : mword 21)
              A3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (secci_0e with "Htext"). }
    iIntros (CID7 Hk7) "Hcg Hpc".
    set (A4 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SC + 0x0e) : mword 64) 4)]> A3).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SC + 0x0e) : mword 64) 4)]> A3) with A4.
    assert (Hjaa : add_vec (mword_of_int (SC + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2096446 : mword 21)) = mword_of_int KernelSyms.argaddr)
      by pcstep.
    iEval (rewrite Hjaa) in "Hpc".
    assert (HA4ra : A4 !!! Regidx Rra = add_vec_int (mword_of_int (SC + 0x0e) : mword 64) 4)
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
    (* ===================== argaddr(0, &mask) ===================== *)
    iDestruct (scc_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf γf p pid U with "Hpriv") as "(Htf & Hpage & Hback)".
    iEval (rewrite -HA4a1) in "Hb3".
    iDestruct (cpu_own_transport CID CID7 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argaddr.wp_argaddr_sconf A4 (av - 4)%nat n eb p 0%nat
              (ud_tfp (pv_upt (us_V U))) (pv_tf (us_V U)) v0 w3 (DfracOwn (1/4)) b
              _ scc_arg0 HA4a0 Hv0 Hn (scc_Kaa av Hav) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htf Hpage Hb3").
    iIntros (CID8 Hk8 Mai) "%HcsAi Hcg Hcpu Hpc Htf Hpage Hb3".
    iEval (rewrite HA4a1) in "Hb3".
    iDestruct ("Hback" with "Htf Hpage") as "Hpriv".
    assert (Hpp12 : ret_pc (A4 !!! Regidx Rra) = mword_of_int (SC + 0x12))
      by (rewrite HA4ra; pcstep).
    iEval (rewrite Hpp12) in "Hpc".
    assert (HAis0 : Mai !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsAi Rs0 ltac:(vm_compute; reflexivity)); exact HA4s0).
    assert (HAisp : Mai !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsAi csp_rs1 ltac:(vm_compute; reflexivity)); exact HA4sp).
    (* +0x12 jal ra,myproc *)
    iApply (wp_jal_s_sconf (mword_of_int (SC + 0x12)) Rra (mword_of_int 2092420 : mword 21)
              Mai (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (secci_12 with "Htext"). }
    iIntros (CID9 Hk9) "Hcg Hpc".
    set (B1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SC + 0x12) : mword 64) 4)]> Mai).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (SC + 0x12) : mword 64) 4)]> Mai) with B1.
    assert (Hjmp : add_vec (mword_of_int (SC + 0x12) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092420 : mword 21)) = mword_of_int KernelSyms.myproc)
      by pcstep.
    iEval (rewrite Hjmp) in "Hpc".
    assert (HB1ra : B1 !!! Regidx Rra = add_vec_int (mword_of_int (SC + 0x12) : mword 64) 4)
      by (rewrite /B1; apply upd_eq).
    assert (HB1s0 : B1 !!! Regidx Rs0 = sp0)
      by (rewrite /B1 upd_ne; [exact HAis0 | vm_compute; discriminate]).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /B1 upd_ne; [exact HAisp | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID8 CID9 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    (* ===================== myproc() ===================== *)
    iApply (Myproc.wp_myproc_sconf B1 (av - 4)%nat n eb p b
              _ Hn (scc_Kmp av Hav)
              with "Hcg Hcpu Htext Hpc").
    iIntros (CID10 Hk10 ms MF) "%Hms Hcg Hcpu Hpc %HcsMF".
    destruct HcsMF as [HcsMF HMFa0].
    assert (Hpc16 : ret_pc (B1 !!! Regidx Rra) = mword_of_int (SC + 0x16))
      by (rewrite HB1ra; pcstep).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HMFs0 : MF !!! Regidx Rs0 = sp0)
      by (rewrite (callee_saved_lookup HcsMF Rs0 ltac:(vm_compute; reflexivity)); exact HB1s0).
    assert (HMFsp : MF !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite (callee_saved_lookup HcsMF csp_rs1 ltac:(vm_compute; reflexivity)); exact HB1sp).
    (* +0x16 ld a5,360(a0) : a5 := p->seccomp *)
    iDestruct (proc_priv_secc with "Hpriv") as "[Hsecc Hsback]".
    assert (Hsaddr : add_vec (rget (CID := CID10) MF Ra0)
                       (sign_extend' 64 (mword_of_int 360 : mword 12)) = p_secc p).
    { rewrite (rget_ne (CID := CID10) MF Ra0 ltac:(vm_compute; discriminate)) HMFa0.
      reflexivity. }
    iEval (rewrite -Hsaddr) in "Hsecc".
    iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (SC + 0x16)) Ra5 Ra0
              (mword_of_int 360 : mword 12)
              MF (av - 4)%nat (pv_secc (us_V U)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hsecc").
    { iApply (secci_16 with "Htext"). }
    iIntros (CID11 Hk11) "Hcg Hpc Hsecc".
    iEval (rewrite Hsaddr) in "Hsecc".
    set (C1 := <[Regidx Ra5 := regval_into_reg (pv_secc (us_V U))]> MF).
    change (<[Regidx Ra5 := regval_into_reg (pv_secc (us_V U))]> MF) with C1.
    assert (Hpp1a : add_vec_int (mword_of_int (SC + 0x16) : mword 64) 4 = mword_of_int (SC + 0x1a)) by pcstep.
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ld a4,-24(s0) : a4 := mask *)
    assert (HC1s0 : C1 !!! Regidx Rs0 = sp0)
      by (rewrite /C1 upd_ne; [exact HMFs0 | vm_compute; discriminate]).
    assert (Haddrm : add_vec (rget (CID := CID11) C1 Rs0)
                       (sign_extend' 64 (mword_of_int 4072 : mword 12)) = pa_stk sp0 3).
    { rewrite (rget_ne (CID := CID11) C1 Rs0 ltac:(vm_compute; discriminate)) HC1s0.
      apply scc_addr_mask. }
    iEval (rewrite -Haddrm) in "Hb3".
    iApply (wp_ld_s_sconf (mword_of_int (SC + 0x1a)) Ra4 Rs0 (mword_of_int 4072 : mword 12)
              C1 (av - 4)%nat v0 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb3").
    { iApply (secci_1a with "Htext"). }
    iIntros (CID12 Hk12) "Hcg Hpc Hb3".
    iEval (rewrite Haddrm) in "Hb3".
    set (C2 := <[Regidx Ra4 := regval_into_reg v0]> C1).
    change (<[Regidx Ra4 := regval_into_reg v0]> C1) with C2.
    assert (Hpp1e : add_vec_int (mword_of_int (SC + 0x1a) : mword 64) 4 = mword_of_int (SC + 0x1e)) by pcstep.
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.and a5,a5,a4 *)
    assert (Hcr : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx Ra4 /\
                  creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
      by (split; vm_compute; reflexivity).
    destruct Hcr as [Hcr6 Hcr7].
    iApply (wp_cand_s_sconf (mword_of_int (SC + 0x1e)) Ra5 Ra4 C2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iEval (rewrite -Hcr6 -Hcr7). iApply (secci_1e with "Htext"). }
    iIntros (CID13 Hk13) "Hcg Hpc".
    assert (HC2a5 : rget (CID := CID12) C2 Ra5 = pv_secc (us_V U)).
    { rewrite (rget_ne (CID := CID12) C2 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /C2 upd_ne; [| vm_compute; discriminate]. rewrite /C1. apply upd_eq. }
    assert (HC2a4 : rget (CID := CID12) C2 Ra4 = v0).
    { rewrite (rget_ne (CID := CID12) C2 Ra4 ltac:(vm_compute; discriminate)).
      rewrite /C2. apply upd_eq. }
    iEval (rewrite HC2a5 HC2a4) in "Hcg".
    set (C3 := <[Regidx Ra5 := regval_into_reg (and_vec (pv_secc (us_V U)) v0)]> C2).
    change (<[Regidx Ra5 := regval_into_reg (and_vec (pv_secc (us_V U)) v0)]> C2) with C3.
    assert (Hpp20 : add_vec_int (mword_of_int (SC + 0x1e) : mword 64) 2 = mword_of_int (SC + 0x20)) by pcstep.
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 sd a5,360(a0) : p->seccomp := mask & p->seccomp *)
    assert (HC3a0 : C3 !!! Regidx Ra0 = p).
    { rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HMFa0. }
    assert (Hsaddr3 : add_vec (rget (CID := CID13) C3 Ra0)
                        (sign_extend' 64 (mword_of_int 360 : mword 12)) = p_secc p).
    { rewrite (rget_ne (CID := CID13) C3 Ra0 ltac:(vm_compute; discriminate)) HC3a0.
      reflexivity. }
    iEval (rewrite -Hsaddr3) in "Hsecc".
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (SC + 0x20)) Ra5 Ra0
              (mword_of_int 360 : mword 12)
              C3 (av - 4)%nat (pv_secc (us_V U)) b
              with "Hcg Hpc [] Hsecc").
    { iApply (secci_20 with "Htext"). }
    iIntros (CID14 Hk14) "Hcg Hpc Hsecc".
    assert (Hstv : rget (CID := CID13) C3 Ra5 = and_vec (pv_secc (us_V U)) v0).
    { rewrite (rget_ne (CID := CID13) C3 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /C3. apply upd_eq. }
    iEval (rewrite Hstv Hsaddr3) in "Hsecc".
    iDestruct ("Hsback" with "Hsecc") as "Hpriv".
    rewrite -(us_secc_set U v0).
    assert (Hpp24 : add_vec_int (mword_of_int (SC + 0x20) : mword 64) 4 = mword_of_int (SC + 0x24)) by pcstep.
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (SC + 0x24)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) C3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (secci_24 with "Htext"). }
    iIntros (CID15 Hk15) "Hcg Hpc".
    set (C4 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> C3).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> C3) with C4.
    assert (Hpp26 : add_vec_int (mword_of_int (SC + 0x24) : mword 64) 2 = mword_of_int (SC + 0x26)) by pcstep.
    iEval (rewrite Hpp26) in "Hpc".
    assert (HC4sp : C4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C4 upd_ne; [| vm_compute; discriminate].
      rewrite /C3 upd_ne; [| vm_compute; discriminate].
      rewrite /C2 upd_ne; [| vm_compute; discriminate].
      rewrite /C1 upd_ne; [| vm_compute; discriminate]. exact HMFsp. }
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
    (* +0x26 c.ldsp ra,24(sp) *)
    iEval (rewrite -Hqa1 -HC4sp) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (SC + 0x26)) (mword_of_int 3 : mword 6) Rra
              C4 (av - 4)%nat (m !!! Regidx Rra) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (secci_26 with "Htext"). }
    iIntros (CID16 Hk16) "Hcg Hpc Hb1".
    iEval (rewrite HC4sp Hqa1) in "Hb1".
    set (E0 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> C4).
    change (<[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> C4) with E0.
    assert (Hpp28 : add_vec_int (mword_of_int (SC + 0x26) : mword 64) 2 = mword_of_int (SC + 0x28)) by pcstep.
    iEval (rewrite Hpp28) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /E0 upd_ne; [exact HC4sp | vm_compute; discriminate]).
    (* +0x28 c.ldsp s0,16(sp) *)
    iEval (rewrite -Hqa2 -HE0sp) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (SC + 0x28)) (mword_of_int 2 : mword 6) Rs0
              E0 (av - 4)%nat (m !!! Regidx Rs0) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (secci_28 with "Htext"). }
    iIntros (CID17 Hk17) "Hcg Hpc Hb2".
    iEval (rewrite HE0sp Hqa2) in "Hb2".
    set (E1 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E0).
    change (<[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> E0) with E1.
    assert (Hpp2a : add_vec_int (mword_of_int (SC + 0x28) : mword 64) 2 = mword_of_int (SC + 0x2a)) by pcstep.
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /E1 upd_ne; [exact HE0sp | vm_compute; discriminate]).
    (* +0x2a c.addi16sp sp,32 -- the frame pop *)
    assert (Hwv : add_vec (E1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HE1sp; apply stk_pop_32).
    assert (Hpop : E1 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HE1sp).
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hb1". { iExists _. iExact "Hb1". }
      iSplitL "Hb2". { iExists _. iExact "Hb2". }
      iSplitL "Hb3". { iExists _. iExact "Hb3". }
      iSplitL "Hb4". { iExists _. iExact "Hb4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SC + 0x2a)) (mword_of_int 2 : mword 6)
              E1 (av - 4)%nat 4 b Hpop with "Hcg Hpc [] Hframe").
    { iApply (secci_2a with "Htext"). }
    iIntros (CID18 Hk18) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by (exact (scc_back av Hav)).
    iEval (rewrite Hnk) in "Hcg".
    set (E2 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E1).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E1) with E2.
    assert (Hpp2c : add_vec_int (mword_of_int (SC + 0x2a) : mword 64) 2 = mword_of_int (SC + 0x2c)) by pcstep.
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.ret *)
    assert (HE2ra : E2 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0. apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (SC + 0x2c)) Rra E2 av b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (secci_2c with "Htext"). }
    iIntros (CID19 Hk19) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretfin : ret_pc (E2 !!! Regidx Rra) = ret_tgt) by (rewrite HE2ra; reflexivity).
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== the postcondition ===================== *)
    assert (HE2sp : E2 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1) by (rewrite /E2 upd_eq; exact Hwv).
    assert (HE2s0 : E2 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate]. rewrite /E1. apply upd_eq. }
    assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int 0 : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate].
      rewrite /C4. apply upd_eq. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 ->
                     E2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N11 : r <> mword_of_int 11) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      rewrite /C4 upd_ne; [| congruence].
      rewrite /C3 upd_ne; [| congruence].
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMF r Hr).
      rewrite /B1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsAi r Hr).
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    iDestruct (cpu_own_transport CID10 CID19 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID19 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E2 with "[%] Hcg Hcpu Hpc Hpriv").
    split; [| exact HE2a0].
    unfold callee_saved.
    split; [exact HE2sp|]. split; [exact HE2s0|].
    repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofSysSeccomp.

End SysSeccompProof.
