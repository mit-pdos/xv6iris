(* ProofInitsleeplock.v -- the whole-function WP for xv6's initsleeplock()
   over the SIE-agnostic sconf world.

     initsleeplock(lk, name) =
       initlock(&lk->lk, "sleep lock");
       lk->name = name;     // sd s2,32(s1)
       lk->locked = 0;      // sw zero,0(s1)
       lk->pid = 0;         // sw zero,40(s1)

   A 32-byte, 4-register frame (ra/s0/s1/s2, no gap) -- prologue/epilogue in the
   4-slot myproc shape -- with one [jal initlock] sub-call and three struct
   stores.  s1 holds [slk] and s2 holds [name] across the call (callee-saved),
   so the stores land at the SleepLock.v cell forms directly.  The post hands
   back the freshly zeroed fields plus the two persistent names
   ([lock_name]/[sl_name]), ready for [new_sleeplock].  A functor over INITLOCK. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import HartTp WpNext IntrDefs.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpLock SleepLock.
Require Import SpecInitlock.
Require Import KernelRvcDecode.
Require Import CodeSleeplock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecInitsleeplock.
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

(* ===================================================================== *)
(* Pure address / value reconciliation lemmas.                            *)
(* ===================================================================== *)




Module InitsleeplockProof (Initlock : INITLOCK) : INITSLEEPLOCK.

Section ProofInitsleeplock.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma wp_initsleeplock_sconf
      (m : regfile) (s : string)
      (vlocked vlk vpid : mword 32) (vlkname vcpu vname : mword 64)
      (av : nat) (b : bool) (p : mword 64)
    : wp_initsleeplock_sconf_body m s vlocked vlk vpid vlkname vcpu vname av b p.
  Proof.
    cbv beta delta [wp_initsleeplock_sconf_body].
    intros pcE slk name ret_tgt Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg #Htext Hpc #Hstr #Hnames Hlocked Hlk Hlkname Hcpu Hnamefield Hpid Hcont".
    (* the "sleep lock" cpu-word cell in the leaf offset form initlock produces *)
    iPoseProof (isl_00 with "Htext") as "Hi00".
    iPoseProof (isl_02 with "Htext") as "Hi02".
    iPoseProof (isl_04 with "Htext") as "Hi04".
    iPoseProof (isl_06 with "Htext") as "Hi06".
    iPoseProof (isl_08 with "Htext") as "Hi08".
    iPoseProof (isl_0a with "Htext") as "Hi0a".
    iPoseProof (isl_0c with "Htext") as "Hi0c".
    iPoseProof (isl_0e with "Htext") as "Hi0e".
    iPoseProof (isl_10 with "Htext") as "Hi10".
    iPoseProof (isl_14 with "Htext") as "Hi14".
    iPoseProof (isl_18 with "Htext") as "Hi18".
    iPoseProof (isl_1a with "Htext") as "Hi1a".
    iPoseProof (isl_1e with "Htext") as "Hi1e".
    iPoseProof (isl_22 with "Htext") as "Hi22".
    iPoseProof (isl_26 with "Htext") as "Hi26".
    iPoseProof (isl_2a with "Htext") as "Hi2a".
    iPoseProof (isl_2c with "Htext") as "Hi2c".
    iPoseProof (isl_2e with "Htext") as "Hi2e".
    iPoseProof (isl_30 with "Htext") as "Hi30".
    iPoseProof (isl_32 with "Htext") as "Hi32".
    iPoseProof (isl_34 with "Htext") as "Hi34".
    (* ===== PROLOGUE: 4-slot frame push + save ra/s0/s1/s2 ===== *)
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x02)) by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vr0) "Hr0".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : pa_stk sp0 4 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 (av - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (HraA0 : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0; rgne; rewrite HraA0) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hs0A0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0; rgne; rewrite Hs0A0) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 (av - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hs1A0 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0; rgne; rewrite Hs1A0) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              A0 (av - 4)%nat vr0 b with "Hcg Hpc Hi08 [Hr0] [-]").
    { iEval (rewrite HcspA0 -Hb4). iExact "Hr0". }
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    assert (Hs2A0 : A0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HcspA0; rgne; rewrite Hs2A0) in "Hr0".
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (av - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* +0x0c c.mv s1,a0  (s1 := slk) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x0c)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (rget A1 (mword_of_int 10 : mword 5)))]> A1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (rget A1 (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* +0x0e c.mv s2,a1  (s2 := name) *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x0e)) (mword_of_int 18 : mword 5) (mword_of_int 11 : mword 5)
              A2 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (rget A2 (mword_of_int 11 : mword 5)))]> A2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (rget A2 (mword_of_int 11 : mword 5)))]> A2) with A3.
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    (* +0x10 auipc a1,0x3 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x10)) (mword_of_int 11 : mword 5) (mword_of_int 0x3 : mword 20)
              A3 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.initsleeplock + 0x10) : mword 64) (auipc_off (mword_of_int 0x3 : mword 20)))]> A3).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.initsleeplock + 0x10) : mword 64) (auipc_off (mword_of_int 0x3 : mword 20)))]> A3) with A4.
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.initsleeplock + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    (* +0x14 addi a1,a1,0x6a2  (a1 := sl_str_addr) *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x14)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 0x68e : mword 12)
              A4 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (A5 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (rget A4 (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1678 : mword 12)))]> A4).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (rget A4 (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 1678 : mword 12)))]> A4) with A5.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.initsleeplock + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    assert (HA5a1 : A5 !!! Regidx (mword_of_int 11 : mword 5) = sl_str_addr).
    { rewrite /A5 upd_eq. rgne. rewrite /A4 upd_eq. unfold sl_str_addr. apply bv_eq; vm_compute; reflexivity. }
    (* +0x18 c.addi a0,a0,8  (a0 := sl_lk slk) *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x18)) (mword_of_int 10 : mword 5) (mword_of_int 8 : mword 6)
              A5 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (A6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget A5 (mword_of_int 10 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> A5).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (rget A5 (mword_of_int 10 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> A5) with A6.
    assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* a0 now holds sl_lk slk *)
    assert (HA5a0 : A5 !!! Regidx (mword_of_int 10 : mword 5) = slk).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HA6a0 : A6 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk).
    { rewrite /A6 upd_eq. rgne. rewrite HA5a0. unfold sl_lk. apply (f_equal (add_vec slk)).
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x1a jal ra,initlock *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x1a)) (mword_of_int 1 : mword 5) (mword_of_int 2084036 : mword 21)
              A6 (av - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (A7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x1a) : mword 64) 4)]> A6).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x1a) : mword 64) 4)]> A6) with A7.
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.initsleeplock + 0x1a) : mword 64) (sign_extend' 64 (mword_of_int 2084036 : mword 21)) = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    (* the registers initlock consumes *)
    assert (HA7a0 : A7 !!! Regidx (mword_of_int 10 : mword 5) = sl_lk slk)
      by (rewrite /A7 upd_ne; [exact HA6a0 | vm_compute; discriminate]).
    assert (HA7a1 : A7 !!! Regidx (mword_of_int 11 : mword 5) = sl_str_addr).
    { rewrite /A7 upd_ne; [| vm_compute; discriminate].
      rewrite /A6 upd_ne; [exact HA5a1 | vm_compute; discriminate]. }
    assert (HA7ra : A7 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x1a) : mword 64) 4)
      by (rewrite /A7; apply upd_eq).
    assert (HA7sp : A7 !!! Regidx csp_rs1 = spd).
    { rewrite /A7 upd_ne; [| vm_compute; discriminate].
      rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [exact HcspA0 | vm_compute; discriminate]. }
    (* s1 = slk and s2 = name persist to the initlock entry (used post-call) *)
    assert (HA7s1 : A7 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg slk).
    { rewrite /A7 upd_ne; [| vm_compute; discriminate].
      rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_eq.
      rgne.
      assert (HA1a0 : A1 !!! Regidx (mword_of_int 10 : mword 5) = slk).
      { rewrite /A1 upd_ne; [| vm_compute; discriminate].
        rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]. }
      rewrite HA1a0. reflexivity. }
    assert (HA7s2 : A7 !!! Regidx (mword_of_int 18 : mword 5) = add_vec zero_reg name).
    { rewrite /A7 upd_ne; [| vm_compute; discriminate].
      rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_eq.
      rgne.
      assert (HA2a1 : A2 !!! Regidx (mword_of_int 11 : mword 5) = name).
      { rewrite /A2 upd_ne; [| vm_compute; discriminate].
        rewrite /A1 upd_ne; [| vm_compute; discriminate].
        rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]. }
      rewrite HA2a1. reflexivity. }
    (* the cpu-word cell in initlock's [add_vec lk (sext 0x10)] form *)
    iEval (rewrite /sl_lkcpu) in "Hcpu".
    (* ===== jal initlock: initlock(&lk->lk, "sleep lock") ===== *)
    iApply (Initlock.wp_initlock_sconf A7 vlk vlkname vcpu "sleep lock"%string (av - 4) b p
              ltac:(lia)
              with "Hcg Htext Hpc [] [Hlk] [Hlkname] [Hcpu]").
    { iEval (rewrite HA7a1). iExact "Hstr". }
    { iEval (rewrite HA7a0). iExact "Hlk". }
    { iEval (rewrite HA7a0). iExact "Hlkname". }
    { iEval (rewrite HA7a0). iExact "Hcpu". }
    iIntros (CID13 Hs13 mil) "Hcg Hpc %Hilcs Hlk Hlname Hcpu".
    iEval (rewrite HA7a0) in "Hlk". iEval (rewrite HA7a0 HA7a1) in "Hlname". iEval (rewrite HA7a0) in "Hcpu".
    iMod (lock_name_intro with "Hstr Hlname") as "#Hlnm".
    assert (Hpcil : ret_pc (A7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.initsleeplock + 0x1e)).
    { rewrite HA7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    (* project the registers we need out of initlock's callee_saved fact
       (13 conjuncts -- sp,s0,s1,s2,s3..s11 -- tp is NOT among them). *)
    pose proof Hilcs as Hilcs_full. unfold callee_saved in Hilcs.
    destruct Hilcs as (Hilsp & Hils0 & Hils1 & Hils2 & Hils3 & Hils4 & Hils5 & Hils6 & Hils7 & Hils8 & Hils9 & Hils10 & Hils11).
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spd) by (rewrite Hilsp; exact HA7sp).
    assert (Hmils1 : mil !!! Regidx (mword_of_int 9 : mword 5) = slk)
      by (rewrite Hils1 HA7s1; apply add_vec_zero_l).
    assert (Hmils2 : mil !!! Regidx (mword_of_int 18 : mword 5) = name)
      by (rewrite Hils2 HA7s2; apply add_vec_zero_l).
    (* ===== the three struct stores ===== *)
    (* +0x1e sd s2,32(s1)  (lk->name := name) *)
    iApply (wp_sd_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x1e)) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x20 : mword 12)
              mil (av - 4)%nat vname b with "Hcg Hpc Hi1e [Hnamefield] [-]").
    { iEval (rgne; rewrite Hmils1). unfold sl_name_field. iExact "Hnamefield". }
    iIntros (CID14 Hs14) "Hcg Hpc Hnamefield".
    iEval (rgne; rewrite Hmils1; rgne; rewrite Hmils2) in "Hnamefield".
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.initsleeplock + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    (* +0x22 sw zero,0(s1)  (lk->locked := 0) *)
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x22)) (mword_of_int 9 : mword 5) (mword_of_int 0x0 : mword 12)
              mil (av - 4)%nat vlocked b with "Hcg Hpc Hi22 [Hlocked] [-]").
    { iEval (rgne; rewrite Hmils1 addv_sext0). iExact "Hlocked". }
    iIntros (CID15 Hs15) "Hcg Hpc Hlocked".
    iEval (rgne; rewrite Hmils1 addv_sext0) in "Hlocked".
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.initsleeplock + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    (* +0x26 sw zero,40(s1)  (lk->pid := 0) *)
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 0x28 : mword 12)
              mil (av - 4)%nat vpid b with "Hcg Hpc Hi26 [Hpid] [-]").
    { iEval (rgne; rewrite Hmils1). unfold sl_pid. iExact "Hpid". }
    iIntros (CID16 Hs16) "Hcg Hpc Hpid".
    iEval (rgne; rewrite Hmils1) in "Hpid".
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.initsleeplock + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* persist the name field, pairing with the caller's [name ↦ₛ□ s] -> sl_name *)
    iApply fupd_wp.
    iMod (word_pointsto_persist with "Hnamefield") as "#Hnamefield".
    iModIntro.
    iAssert (sl_name slk s) as "#Hslname".
    { iExists name. iFrame "Hnamefield". iExact "Hnames". }
    (* ===== EPILOGUE: restore ra/s0/s1/s2, pop frame, ret =====
       from here on nothing reads a variable register any more -- the
       reload values are the explicit [wp_c{ld,ldsp}] arguments, not
       [rget], so the rest of the map chain is plain lookups exactly as
       before the port. *)
    (* +0x2a c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x2a)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mil (av - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [Hr24] [-]").
    { iEval (rewrite Hmilsp). iExact "Hr24". }
    iIntros (CID17 Hs17) "Hcg Hpc Hr24".
    iEval (rewrite Hmilsp) in "Hr24".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mil) with E1.
    assert (HcspE1 : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    (* +0x2c c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x2c)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (av - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr16] [-]").
    { iEval (rewrite HcspE1). iExact "Hr16". }
    iIntros (CID18 Hs18) "Hcg Hpc Hr16".
    iEval (rewrite HcspE1) in "Hr16".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> E1) with E2.
    assert (HcspE2 : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HcspE1 | vm_compute; discriminate]).
    assert (Hpc2e : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2e) in "Hpc".
    (* +0x2e c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x2e)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (av - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hr8] [-]").
    { iEval (rewrite HcspE2). iExact "Hr8". }
    iIntros (CID19 Hs19) "Hcg Hpc Hr8".
    iEval (rewrite HcspE2) in "Hr8".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> E2) with E3.
    assert (HcspE3 : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HcspE2 | vm_compute; discriminate]).
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc30) in "Hpc".
    (* +0x30 c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x30)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              E3 (av - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [Hr0] [-]").
    { iEval (rewrite HcspE3). iExact "Hr0". }
    iIntros (CID20 Hs20) "Hcg Hpc Hr0".
    iEval (rewrite HcspE3) in "Hr0".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> E3) with E4.
    assert (HcspE4 : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HcspE3 | vm_compute; discriminate]).
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc32) in "Hpc".
    (* +0x32 c.addi16sp sp,32 -- pop the frame *)
    set (E5 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
    assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite /spd /sp0 po_addv_assoc.
      assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply avi0. }
    assert (HE5sp : E5 !!! Regidx csp_rs1 = sp0).
    { rewrite /E5 upd_eq HcspE4. exact Hsp0up. }
    assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HcspE4. exact Hsp0up. }
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, sp0, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpop : E4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HcspE4. symmetry. exact Hspd4. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3). iExact "Hr8". }
      iSplitL "Hr0".  { iExists _. iEval (rewrite Hb4). iExact "Hr0". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x32)) (mword_of_int 2 : mword 6) E4 (av - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi32 Hframe4 [-]").
    iIntros (CID21 Hs21) "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.initsleeplock + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.initsleeplock + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc34) in "Hpc".
    (* +0x34 c.ret *)
    assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /E5 upd_ne; [| vm_compute; discriminate].
      rewrite /E4 upd_ne; [| vm_compute; discriminate].
      rewrite /E3 upd_ne; [| vm_compute; discriminate].
      rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1. apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.initsleeplock + 0x34)) (mword_of_int 1 : mword 5) E5 av b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID22 Hs22) "Hcg Hpc".
    iEval (rgne; rewrite HE5ra) in "Hpc".
    (* ===== hand everything back to the caller ===== *)
    iSpecialize ("Hcont" $! CID22 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! E5 with "Hcg Hpc [%] Hlocked Hlk Hlnm Hcpu Hslname Hpid").
    (* callee_saved m E5 (13 conjuncts -- sp,s0,s1,s2,s3..s11) *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 ->
              c <> mword_of_int 8 -> c <> mword_of_int 9 -> c <> mword_of_int 18 ->
              E5 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8 N9 N18.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na0.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Na1.
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs_full c Hc).
      rewrite /A7 upd_ne; [| congruence].
      rewrite /A6 upd_ne; [| congruence].
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [reflexivity | congruence]. }
    unfold callee_saved.
    split. { rewrite HE5sp. reflexivity. }
    split. { rewrite /E5 upd_ne; [| vm_compute; discriminate].
             rewrite /E4 upd_ne; [| vm_compute; discriminate].
             rewrite /E3 upd_ne; [| vm_compute; discriminate].
             rewrite /E2 upd_eq; reflexivity. }
    split. { rewrite /E5 upd_ne; [| vm_compute; discriminate].
             rewrite /E4 upd_ne; [| vm_compute; discriminate].
             rewrite /E3 upd_eq; reflexivity. }
    split. { rewrite /E5 upd_ne; [| vm_compute; discriminate].
             rewrite /E4 upd_eq; reflexivity. }
    repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofInitsleeplock.

End InitsleeplockProof.
