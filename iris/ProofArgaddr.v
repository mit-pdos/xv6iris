(* ProofArgaddr.v -- whole-function WP for argaddr().

     void argaddr(int n, uint64 *ip) { *ip = argraw(n); }

   Thirteen instructions @ 0x80002820, byte-identical to argint's except for
   the jal's relocation and the store: [c.sd a0,0(s1)] rather than
   [c.sw a0,0(s1)], because the destination is a [uint64 *].  So the value
   that lands in the caller's cell is argraw's result ITSELF -- no [trunc32]
   -- and the frame, the [c.mv s1,a1] that parks [ip] across the call, and the
   epilogue are argint's, step for step.

   As in ProofArgint / ProofSysGetpid, ra/s0/s1 are saved and restored ACROSS
   the call, so the final [callee_saved] is discharged componentwise rather
   than through [callee_saved_trans]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import CodeArgaddr.
Require Import SpecArgraw.
Require Import SpecArgaddr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Require Import IrefSlots.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.


(* argaddr's balanced 32-byte frame: entry [addi sp,-32] and exit
   [addi16sp sp,32] cancel. *)

Module ArgaddrProof (Argraw : ARGRAW) : ARGADDR.

Section ProofArgaddr.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Lemma wp_argaddr_sconf
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (old : mword 64) (dqt : dfrac) (b : bool) (lks : gset string)
    : wp_argaddr_sconf_body m av n eb p i tfp ws v old dqt b lks.
  Proof.
    cbv beta delta [wp_argaddr_sconf_body].
    intros pcE ip ret_tgt Hi Ha0 Hargs Hn Hav Hpv.
    
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Htfp Htfa Hip Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (aai_00 with "Htext") as "Hi00".
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                   = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02/+0x04/+0x06: c.sdsp ra/s0/s1 *)
    iPoseProof (aai_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (aai_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (aai_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* normalize the three saved cells to [add_vec spd _ ↦₈ (m !!! r)], the
       form the epilogue's reloads unify against. *)
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (aai_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.argaddr + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a: c.mv s1,a1 -- park [ip] in a callee-saved register *)
    iPoseProof (aai_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.argaddr + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 11 : mword 5)
              A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 11 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 11 : mword 5)))]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx (mword_of_int 9 : mword 5) = ip).
    { rewrite /A2 upd_eq. rewrite add_vec_zero_l.
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    (* +0x0c: jal ra,argraw *)
    iPoseProof (aai_0c with "Htext") as "Hi0c".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.argaddr + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 2096876 : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) 4)]> A2) with A3.
    assert (Hjmp : add_vec (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2096876 : mword 21)) = mword_of_int KernelSyms.argraw)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA3ra : A3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a0 : A3 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i)).
    { rewrite /A3 upd_ne; [| reg_neq].
      rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Ha0. }
    (* ===================== argraw() ===================== *)
    (* carry [Hcpu] (cpu_own, hart-indexed) from the entry hart to the current
       chain hart [CID7] before the callee wants it. *)
    iDestruct (cpu_own_transport CID CID7 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Argraw.wp_argraw_sconf A3 (av - 4)%nat n eb p i tfp ws v dqt b lks
              Hi HA3a0 Hargs Hn ltac:(lia) Hpv
              with "Hcg Hcpu Htext Hdata Hpc Htfp Htfa").
    iIntros (CID8 Hs8 MF) "%HcsMF Hcg Hcpu Hpc Htfp Htfa".
    destruct HcsMF as [HcsMF HMFa0].
    assert (Hpc10 : ret_pc (A3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.argaddr + 0x10))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* ---- +0x10: c.sd a0,0(s1) -- *ip = a0, full width ---- *)
    assert (HMFs1 : MF !!! Regidx (mword_of_int 9 : mword 5) = ip).
    { rewrite (callee_saved_lookup HcsMF (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| reg_neq]. exact HA2s1. }
    iPoseProof (aai_10 with "Htext") as "Hi10".
    assert (Haddr10 : add_vec (rget MF (mword_of_int 9 : mword 5))
                        (sign_extend' 64 (mword_of_int 0 : mword 12)) = ip).
    { rgne. rewrite HMFs1. apply addv_sext0. }
    iApply (wp_csd_s_sconf (mword_of_int (KernelSyms.argaddr + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 0 : mword 12) MF (av - 4)%nat old b
              with "Hcg Hpc Hi10 [Hip]").
    { iEval (rewrite Haddr10). iExact "Hip". }
    iIntros (CID9 Hs9) "Hcg Hpc Hip".
    iEval (rewrite Haddr10) in "Hip".
    iEval (rgne) in "Hip".
    iEval (rewrite HMFa0) in "Hip".
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    (* ===================== EPILOGUE ===================== *)
    assert (HMFcsp : MF !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup HcsMF csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| reg_neq].
      rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HcspA0. }
    iPoseProof (aai_12 with "Htext") as "Hi12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x12)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              MF (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [Hr24]").
    { iEval (rewrite HMFcsp). iExact "Hr24". }
    iIntros (CID10 Hs10) "Hcg Hpc Hr24".
    set (E2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> MF).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> MF) with E2.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HE2csp : E2 !!! Regidx csp_rs1 = spd)
      by (rewrite /E2 upd_ne; [exact HMFcsp | reg_neq]).
    iPoseProof (aai_14 with "Htext") as "Hi14".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x14)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hr16]").
    { iEval (rewrite HE2csp). iExact "Hr16". }
    iIntros (CID11 Hs11) "Hcg Hpc Hr16".
    set (E3 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E2) with E3.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HE3csp : E3 !!! Regidx csp_rs1 = spd)
      by (rewrite /E3 upd_ne; [exact HE2csp | reg_neq]).
    iPoseProof (aai_16 with "Htext") as "Hi16".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.argaddr + 0x16)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E3 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hr8]").
    { iEval (rewrite HE3csp). iExact "Hr8". }
    iIntros (CID12 Hs12) "Hcg Hpc Hr8".
    set (E4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E3).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E3) with E4.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18: c.addi16sp sp,32 -- the frame pop *)
    assert (HE4csp : E4 !!! Regidx csp_rs1 = spd)
      by (rewrite /E4 upd_ne; [exact HE3csp | reg_neq]).
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite /spd; apply frame_cancel_32).
    assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE4csp. exact Hsp0up. }
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE4csp. symmetry. exact Hspd4. }
    iPoseProof (aai_18 with "Htext") as "Hi18".
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HMFcsp). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HE2csp). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HE3csp). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.argaddr + 0x18)) (mword_of_int 2 : mword 6) E4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi18 Hframe4").
    iIntros (CID13 Hs13) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.argaddr + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.argaddr + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* +0x1a: c.ret *)
    assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2. apply upd_eq. }
    iPoseProof (aai_1a with "Htext") as "Hi1a".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.argaddr + 0x1a)) (mword_of_int 1 : mword 5) E5 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a").
    iIntros (CID14 Hs14) "Hcg Hpc".
    assert (Hretfin : ret_pc (rget E5 (mword_of_int 1 : mword 5)) = ret_tgt).
    { rgne. rewrite HE5ra. reflexivity. }
    iEval (rewrite Hretfin) in "Hpc".
    (* ===================== return ===================== *)
    assert (HE5csp : E5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /E5 upd_eq HE4csp; exact Hsp0up).
    assert (HE5s0 : E5 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq].
      rewrite /E3. apply upd_eq. }
    assert (HE5s1 : E5 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4. apply upd_eq. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                     r <> csp_rs1 -> r <> mword_of_int 8 -> r <> mword_of_int 9 ->
                     E5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMF r Hr).
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    (* [Hcpu] was delivered at [CID8] by argraw's own [wp_next]; six more
       plain instructions have moved the hart to [CID14]. *)
    iDestruct (cpu_own_transport CID8 CID14 n eb p b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID14 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 with "[%] Hcg Hcpu Hpc Htfp Htfa Hip").
    unfold callee_saved.
    split; [exact HE5csp|].
    split; [exact HE5s0|].
    split; [exact HE5s1|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
    apply Hthr; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofArgaddr.

End ArgaddrProof.
