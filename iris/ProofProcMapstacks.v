(* ProofProcMapstacks.v -- whole-function proof of proc_mapstacks
   (kernel/proc.c): kalloc a page for each of the 64 process kernel stacks
   and kvmmap it at KSTACK(i).

   This file currently holds the VALIDATED arithmetic + instruction-WP
   foundation the whole-function proof rests on:
     - the magic-reciprocal KSTACK address bridge (srai/mul/slli/addw/sub),
     - sconf WP lemmas for the three instructions with no pre-existing
       leaf (SRAI, MUL, ADDW), built on the generic gpr-write engine,
     - the [va_i] svpn/alignment/range facts feeding KM.wp_kvmmap_sconf.
   The instruction-walk (sealed epilogue, fuel-inducted loop, prologue) and
   the sealed functor [ProcMapstacksProof (K : KALLOC) (KM : KVMMAP)] build
   on top of these; see the report/worklist. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpMmodeLeafBase.
Require Import WpNext.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSconfVc.
Require Import WpLock CpuOwn.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes KernelText.
Require Import KstackArith.
Require Import KallocInv.
Require Import PtTree PtBuild KptPt KvmMap KvmSpec.
Require Import CodeProcMapstacks.
Require Import SpecKalloc SpecKvmmap SpecProcMapstacks.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.


Definition va_i (i : nat) : mword 64 := mword_of_int (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)).

Lemma va_i_uns (i : nat) : (i < 64)%nat -> bv_unsigned (va_i i) = 0x3FFFFFF000 - 8192 * (Z.of_nat i + 1).
Proof.
  intro Hi. unfold va_i, mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split; [| lia]. assert (8192 * (Z.of_nat i + 1) <= 8192 * 64) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma va_i_svpn (i : nat) : (i < 64)%nat -> svpn_of (va_i i) = kstack_vpn i.
Proof.
  intro Hi. apply bv_eq.
  rewrite (svpn_of_unsigned_lo (va_i i) ltac:(rewrite uint_unsigned; rewrite (va_i_uns i Hi); assert (8192*(Z.of_nat i+1)<=8192*64) by (apply Z.mul_le_mono_nonneg_l; lia); lia)).
  rewrite uint_unsigned. rewrite (va_i_uns i Hi).
  rewrite (kstack_vpn_uns i Hi).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2^12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.div_mul; [| lia]. reflexivity.
Qed.

Lemma va_i_align (i : nat) : (i < 64)%nat -> subrange_vec_dec (va_i i) 11 0 = (zeros' 12 : mword 12).
Proof.
  intro Hi. apply bv_eq.
  rewrite subrange64_unsigned_11_0. rewrite (va_i_uns i Hi).
  change (2^12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.mod_mul; [| lia]. vm_compute. reflexivity.
Qed.

Lemma va_i_range (i : nat) : (i < 64)%nat -> (uint (va_i i) + Z.of_nat 1 * 4096 <= 2 ^ 38)%Z.
Proof.
  intro Hi. rewrite uint_unsigned. rewrite (va_i_uns i Hi).
  change (2^38) with 274877906944.
  assert (8192 * 1 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.



Lemma pms_seq_peel (i : nat) : (i < 64)%nat -> seq i (64 - i) = i :: seq (S i) (63 - i).
Proof. intro H. replace (64 - i)%nat with (S (63 - i)) by lia. reflexivity. Qed.

Module ProcMapstacksProof (K : KALLOC) (KM : KVMMAP) : PROC_MAPSTACKS.

Section ProofPMS.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  (* NOTE: no shared [Context `{GEN : GenId} `{CID : CpuId}] here -- the epilogue/loop/
     prologue lemmas below apply EACH OTHER at a hart that a [wp_next]
     crossing may have migrated to, so each needs its OWN implicit
     per-lemma [CID] binder (shadowing what a section Context would give)
     rather than sharing one rigid section-wide hart; see the porting
     guide's "Two things a DECOMPOSED proof needs". *)


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel ONE update layer at a time (unfold-then-peel on the whole set-chain
     is O(depth^2): see claude-notes/optimization.md). [peel_reg_step] leaves
     whatever residual goal the peel bottoms out at, for a caller-supplied
     closing tactic; [peel_reg] is the reflexivity-closed special case. *)
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  Ltac peel_reg := peel_reg_step; reflexivity.

  (* ================================================================= *)
  (* THE SEALED EPILOGUE (+0x80..+0x96): restore the 10-slot frame and  *)
  (* ret, producing the success-only proc_mapstacks post.               *)
  (* ================================================================= *)
  Lemma wp_proc_mapstacks_epilogue_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm Mf : regfile) (t tf : ptree)
      (m : gmap (mword 27) (mword 64)) (K lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (g : nat)
      (pas : nat -> mword 44) (b : bool) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (* kvmmap's kalloc: the transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (44 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tf = pt_base t ->
    pt_rep0 tf (kvm_stacks pas 64 m) ->
    pt_nodes tf = (pt_nodes t + g)%nat ->
    kvm_pas_ok pas ->
    (g <= kstacks_missing t)%nat ->
    sie_cap_gpr Mf (K - 10)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.proc_mapstacks + 0x80)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    pa_stk sp0 9 ↦₈ (mm !!! Regidx (mword_of_int 23)) -∗
    pa_stk sp0 10 ↦₈ (mm !!! Regidx (mword_of_int 24)) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on (64 + g)) -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g' : nat) (pas' : nat -> mword 44),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗ pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g')%nat⌝ -∗
      kalloc_env γa (avail_sub on (64 + g')) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜kvm_pas_ok pas'⌝ -∗
      ⌜pt_rep0 t' (kvm_stacks pas' 64 m)⌝ -∗
      ⌜(g' <= kstacks_missing t)%nat⌝ -∗
      ([∗ list] i ∈ seq 0 64,
         page_own (zero_extend' 64 (concat_vec (pas' i) (zeros' 12 : mword 12)))) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt Hlvl HK Hsp Hx25 Hx26 Hx27 Hbase Hrep Hnodes Hpasok Hmiss.
    iIntros "Hcg Hcnt #Htext Hpc
             Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00
             Hptree Henv Hpages Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 10).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 10 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (pmsi_80 with "Htext") as "Hi80".
    iPoseProof (pmsi_82 with "Htext") as "Hi82".
    iPoseProof (pmsi_84 with "Htext") as "Hi84".
    iPoseProof (pmsi_86 with "Htext") as "Hi86".
    iPoseProof (pmsi_88 with "Htext") as "Hi88".
    iPoseProof (pmsi_8a with "Htext") as "Hi8a".
    iPoseProof (pmsi_8c with "Htext") as "Hi8c".
    iPoseProof (pmsi_8e with "Htext") as "Hi8e".
    iPoseProof (pmsi_90 with "Htext") as "Hi90".
    iPoseProof (pmsi_92 with "Htext") as "Hi92".
    iPoseProof (pmsi_94 with "Htext") as "Hi94".
    iPoseProof (pmsi_96 with "Htext") as "Hi96".
    pose proof Hsp as HspE0.
    (* +0x80 ld ra,72(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x80)) (mword_of_int 9 : mword 6) (mword_of_int 1 : mword 5)
              Mf (K - 10)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hc72] [-]").
    { iEval (rewrite HspE0 Hb1). iExact "Hc72". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hc72".
    iEval (rewrite HspE0 Hb1) in "Hc72".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> Mf).
    assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HspE0).
    (* +0x82 ld s0,64(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x82)) (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 10)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hc64] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc64". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hc64".
    iEval (rewrite HspE1 Hb2) in "Hc64".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HspE1).
    (* +0x84 ld s1,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x84)) (mword_of_int 7 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 10)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hc56] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc56". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hc56".
    iEval (rewrite HspE2 Hb3) in "Hc56".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HspE2).
    (* +0x86 ld s2,48(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x86)) (mword_of_int 6 : mword 6) (mword_of_int 18 : mword 5)
              E3 (K - 10)%nat (mm !!! Regidx (mword_of_int 18 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [Hc48] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc48". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hc48".
    iEval (rewrite HspE3 Hb4) in "Hc48".
    set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
    assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x86) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4; rewrite upd_ne; [| reg_neq]; exact HspE3).
    (* +0x88 ld s3,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x88)) (mword_of_int 5 : mword 6) (mword_of_int 19 : mword 5)
              E4 (K - 10)%nat (mm !!! Regidx (mword_of_int 19 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [Hc40] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc40". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hc40".
    iEval (rewrite HspE4 Hb5) in "Hc40".
    set (E5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 19 : mword 5))]> E4).
    assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr) by (rewrite /E5; rewrite upd_ne; [| reg_neq]; exact HspE4).
    (* +0x8a ld s4,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x8a)) (mword_of_int 4 : mword 6) (mword_of_int 20 : mword 5)
              E5 (K - 10)%nat (mm !!! Regidx (mword_of_int 20 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [Hc32] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc32". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hc32".
    iEval (rewrite HspE5 Hb6) in "Hc32".
    set (E6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 20 : mword 5))]> E5).
    assert (Hp8c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8c) in "Hpc".
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr) by (rewrite /E6; rewrite upd_ne; [| reg_neq]; exact HspE5).
    (* +0x8c ld s5,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x8c)) (mword_of_int 3 : mword 6) (mword_of_int 21 : mword 5)
              E6 (K - 10)%nat (mm !!! Regidx (mword_of_int 21 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8c [Hc24] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc24". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hc24".
    iEval (rewrite HspE6 Hb7) in "Hc24".
    set (E7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 21 : mword 5))]> E6).
    assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x8c) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr) by (rewrite /E7; rewrite upd_ne; [| reg_neq]; exact HspE6).
    (* +0x8e ld s6,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x8e)) (mword_of_int 2 : mword 6) (mword_of_int 22 : mword 5)
              E7 (K - 10)%nat (mm !!! Regidx (mword_of_int 22 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8e [Hc16] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc16". }
    iIntros (CIDe8 Hse8) "Hcg Hpc Hc16".
    iEval (rewrite HspE7 Hb8) in "Hc16".
    set (E8 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 22 : mword 5))]> E7).
    assert (Hp90 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp90) in "Hpc".
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr) by (rewrite /E8; rewrite upd_ne; [| reg_neq]; exact HspE7).
    (* +0x90 ld s7,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x90)) (mword_of_int 1 : mword 6) (mword_of_int 23 : mword 5)
              E8 (K - 10)%nat (mm !!! Regidx (mword_of_int 23 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [Hc08] [-]").
    { iEval (rewrite HspE8 Hb9). iExact "Hc08". }
    iIntros (CIDe9 Hse9) "Hcg Hpc Hc08".
    iEval (rewrite HspE8 Hb9) in "Hc08".
    set (E9 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 23 : mword 5))]> E8).
    assert (Hp92 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x90) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp92) in "Hpc".
    assert (HspE9 : E9 !!! Regidx csp_rs1 = spr) by (rewrite /E9; rewrite upd_ne; [| reg_neq]; exact HspE8).
    (* +0x92 ld s8,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x92)) (mword_of_int 0 : mword 6) (mword_of_int 24 : mword 5)
              E9 (K - 10)%nat (mm !!! Regidx (mword_of_int 24 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [Hc00] [-]").
    { iEval (rewrite HspE9 Hb10). iExact "Hc00". }
    iIntros (CIDe10 Hse10) "Hcg Hpc Hc00".
    iEval (rewrite HspE9 Hb10) in "Hc00".
    set (E10 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 24 : mword 5))]> E9).
    assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp94) in "Hpc".
    assert (HspE10 : E10 !!! Regidx csp_rs1 = spr) by (rewrite /E10; rewrite upd_ne; [| reg_neq]; exact HspE9).
    (* +0x94 c.addi16sp sp,+80 -- the frame pop *)
    set (E11 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E10).
    assert (Hwv : add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
    { rewrite HspE10. unfold spr. apply frame_cancel_80. }
    assert (Hpop : E10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
    { rewrite Hwv HspE10. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 10) with "[Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc72". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc72". }
      iSplitL "Hc64". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc64". }
      iSplitL "Hc56". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx (mword_of_int 19)). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx (mword_of_int 20)). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx (mword_of_int 21)). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx (mword_of_int 22)). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx (mword_of_int 23)). iExact "Hc08". }
      iSplitL "Hc00". { iExists (mm !!! Regidx (mword_of_int 24)). iExact "Hc00". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x94)) (mword_of_int 5 : mword 6)
              E10 (K - 10)%nat 10 b Hpop
              with "Hcg Hpc Hi94 Hframe [-]").
    iIntros (CIDe11 Hse11) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E10 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E10) with E11.
    assert (Hnk : ((K - 10) + 10)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp96 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x94) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp96) in "Hpc".
    (* +0x96 ret *)
    assert (HE11ra : E11 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
    assert (Hrt : ret_pc (E11 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt) by (rewrite HE11ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x96)) (mword_of_int 1 : mword 5) E11 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi96 [-]").
    iIntros (CIDe12 Hse12) "Hcg Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CIDe12 with "[%]"); [wp_next_chain|].
    (* [Hcnt] entered this lemma at its OWN entry hart [CID]; the twelve
       plain-instruction crossings above (ten loads, the pop, the ret)
       landed on [CIDe12] -- transport it there once before handing it
       to the continuation. *)
    assert (HcntCE : b = false \/ p = zero_reg -> (CIDe12 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CID CIDe12 lvl eb p C b HcntCE with "Hcnt") as "Hcnt".
    iApply ("Hcont" $! E11 tf g pas with "Hcg Hcnt Hpc Hptree [%] Henv [%] [%] [%] [%] [%] Hpages").
    { exact Hnodes. }
    { (* callee_saved mm E11 *)
      unfold callee_saved.
      split.
      { rewrite /E11 upd_eq. rewrite HspE10. unfold spr. apply frame_cancel_80. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split. { peel_reg. }
      split.
      { peel_reg_step. exact Hx25. }
      split.
      { peel_reg_step. exact Hx26. }
      { peel_reg_step. exact Hx27. }
    }
    { exact Hbase. }
    { exact Hpasok. }
    { exact Hrep. }
    { exact Hmiss. }
  Qed.

  (* mappages_perm_ok for the RW perm 6 *)
  Lemma pms_perm_ok6 : mappages_perm_ok 6.
  Proof.
    unfold mappages_perm_ok. split; [lia|].
    split; [intro s; vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity | vm_compute; reflexivity].
  Qed.

  (* pas-extension congruence on the accumulated page_own list *)
  Lemma pms_pages_ext (i : nat) (f g : nat -> mword 44) :
    (forall j, (j < i)%nat -> f j = g j) ->
    ([∗ list] j ∈ seq 0 i, page_own (zero_extend' 64 (concat_vec (f j) (zeros' 12 : mword 12))))
    ⊢ ([∗ list] j ∈ seq 0 i, page_own (zero_extend' 64 (concat_vec (g j) (zeros' 12 : mword 12)))).
  Proof.
    intro Hfg. iIntros "H". iApply (big_sepL_mono with "H").
    iIntros (k y Hy) "Hp". apply lookup_seq in Hy. destruct Hy as [-> Hlt].
    replace (g (0 + k)%nat) with (f (0 + k)%nat) by (apply Hfg; lia). iExact "Hp".
  Qed.

  (* ================================================================= *)
  (* THE LOOP (+0x52 entry): fuel induction on [rem], [i + rem = 64].    *)
  (* ================================================================= *)
  Lemma wp_proc_mapstacks_loop_sconf `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm : regfile) (t : ptree)
      (m0 : gmap (mword 27) (mword 64)) (K lvl : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (nb : nat) (rem : nat) (b : bool) :
    forall (i : nat) (Mk : regfile) (tk : ptree) (gk : nat) (pas : nat -> mword 44),
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    (* kvmmap's kalloc: the transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (44 <= K)%nat ->
    (i + rem)%nat = 64%nat -> (0 < rem)%nat ->
    (64 + kstacks_missing t < nb)%nat ->
    mm !!! Regidx (mword_of_int 10)
      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    (forall j, (j < 64)%nat -> m0 !! kstack_vpn j = None) ->
    Mk !!! Regidx csp_rs1 = spr ->
    Mk !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat i) ->
    Mk !!! Regidx (mword_of_int 24 : mword 5) = mword_of_int 0x800127d0 ->
    Mk !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 0x4fa4fa4fa4fa4fa5 ->
    Mk !!! Regidx (mword_of_int 19 : mword 5) = mword_of_int 0x3FFFFFF000 ->
    Mk !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 0x800181d0 ->
    Mk !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 4096 ->
    Mk !!! Regidx (mword_of_int 23 : mword 5) = mword_of_int 6 ->
    Mk !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10) ->
    Mk !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mk !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mk !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_base tk = pt_base t ->
    pt_rep0 tk (kvm_stacks pas i m0) ->
    pt_nodes tk = (pt_nodes t + gk)%nat ->
    (gk + sum_list_with (fun j => pt_missing tk (kstack_vpn j) 1) (seq i (64 - i))
       <= kstacks_missing t)%nat ->
    (forall j, (j < i)%nat -> node_kdata (pas j)) ->
    sie_cap_gpr Mk (K - 10)%nat b p -∗ cpu_own lvl eb p C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.proc_mapstacks + 0x52)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    pa_stk sp0 4 ↦₈ (mm !!! Regidx (mword_of_int 18)) -∗
    pa_stk sp0 5 ↦₈ (mm !!! Regidx (mword_of_int 19)) -∗
    pa_stk sp0 6 ↦₈ (mm !!! Regidx (mword_of_int 20)) -∗
    pa_stk sp0 7 ↦₈ (mm !!! Regidx (mword_of_int 21)) -∗
    pa_stk sp0 8 ↦₈ (mm !!! Regidx (mword_of_int 22)) -∗
    pa_stk sp0 9 ↦₈ (mm !!! Regidx (mword_of_int 23)) -∗
    pa_stk sp0 10 ↦₈ (mm !!! Regidx (mword_of_int 24)) -∗
    ptree_own 2 (DfracOwn 1) tk -∗
    kalloc_env γa (avail_sub (Some nb) (i + gk)) -∗
    ([∗ list] j ∈ seq 0 i,
       page_own (zero_extend' 64 (concat_vec (pas j) (zeros' 12 : mword 12)))) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g' : nat) (pas' : nat -> mword 44),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p C b -∗ pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      ⌜pt_nodes t' = (pt_nodes t + g')%nat⌝ -∗
      kalloc_env γa (avail_sub (Some nb) (64 + g')) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜pt_base t' = pt_base t⌝ -∗
      ⌜kvm_pas_ok pas'⌝ -∗
      ⌜pt_rep0 t' (kvm_stacks pas' 64 m0)⌝ -∗
      ⌜(g' <= kstacks_missing t)%nat⌝ -∗
      ([∗ list] i0 ∈ seq 0 64,
         page_own (zero_extend' 64 (concat_vec (pas' i0) (zeros' 12 : mword 12)))) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    revert CID.
    induction rem as [| rem' IH]; intros CID i Mk tk gk pas sp0 spr ret_tgt
      Hlvl HK Hirem Hrem Hnbig Hroot Hres
      Hsp Hs1 Hs8 Hs2m Hs3 Hs5 Hs6 Hs7 Hs4 Hx25 Hx26 Hx27
      Hbase Hrep Hnodes Hbud Hpasb; [lia|].
    iIntros "Hcg Hcnt #Htext Hpc Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree Henv Hpages Hcont".
    assert (Hilt : (i < 64)%nat) by lia.
    (* the current stack vpn + address facts *)
    set (VA := va_i i).
    iPoseProof (pmsi_52 with "Htext") as "Hi52".
    iPoseProof (pmsi_56 with "Htext") as "Hi56".
    iPoseProof (pmsi_58 with "Htext") as "Hi58".
    iPoseProof (pmsi_5a with "Htext") as "Hi5a".
    iPoseProof (pmsi_5e with "Htext") as "Hi5e".
    iPoseProof (pmsi_60 with "Htext") as "Hi60".
    iPoseProof (pmsi_64 with "Htext") as "Hi64".
    iPoseProof (pmsi_66 with "Htext") as "Hi66".
    iPoseProof (pmsi_68 with "Htext") as "Hi68".
    iPoseProof (pmsi_6a with "Htext") as "Hi6a".
    iPoseProof (pmsi_6c with "Htext") as "Hi6c".
    iPoseProof (pmsi_6e with "Htext") as "Hi6e".
    iPoseProof (pmsi_72 with "Htext") as "Hi72".
    iPoseProof (pmsi_74 with "Htext") as "Hi74".
    iPoseProof (pmsi_78 with "Htext") as "Hi78".
    iPoseProof (pmsi_7c with "Htext") as "Hi7c".
    (* +0x52 jal kalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x52)) (mword_of_int 1 : mword 5) (mword_of_int 2093924 : mword 21)
              Mk (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi52 [-]").
    iIntros (CIDl1 Hsl1) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x52) : mword 64) 4)]> Mk).
    assert (Htgtk : add_vec (mword_of_int (KernelSyms.proc_mapstacks + 0x52) : mword 64) (sign_extend' 64 (mword_of_int 2093924 : mword 21)) = mword_of_int KernelSyms.kalloc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    iDestruct "Henv" as (γk) "(#Hlock & Havail & #Hqcpu)".
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J. rewrite upd_ne; [| reg_neq]. exact Hsp. }
    assert (HJ1 : J !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x52) : mword 64) 4)
      by (rewrite /J upd_eq; reflexivity).
    (* [Hcnt] was minted at THIS iteration's entry hart [CID]; the single
       [jal] above landed on [CIDl1] -- transport it there before feeding
       it to kalloc's own [cpu_own] premise. *)
    assert (HcntC0 : b = false \/ p = zero_reg -> (CIDl1 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CID CIDl1 lvl eb p C b HcntC0 with "Hcnt") as "Hcnt".
    iApply (K.wp_kalloc_sconf γa γk (mword_of_int (KernelSyms.kmem + 24))
              J (avail_sub (Some nb) (i + gk)) lvl eb p C (K - 10)%nat b
              ltac:(lia)
              ltac:(reflexivity)
              Hlvl
              with "Hcg Hcnt Htext Hpc Hlock Havail Hqcpu [-]").
    iIntros (CIDl2 Hsl2 mr0) "Hcg Hcnt Hpc %Hkcs0 Hkpost".
    assert (Hret56 : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_mapstacks + 0x56)).
    { rewrite HJ1. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret56) in "Hpc".
    (* null-refutation: at Some (nb-(i+gk)) with nb > i+gk the count is positive *)
    assert (Hgkle : (gk <= kstacks_missing t)%nat).
    { pose proof Hbud as HB. rewrite (pms_seq_peel i Hilt) in HB. cbn [sum_list_with] in HB. lia. }
    assert (Hcnt : avail_sub (Some nb) (i + gk) = Some (S (nb - (i + gk) - 1))).
    { rewrite avail_sub_Some. f_equal. lia. }
    iEval (rewrite Hcnt) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpv & Hpage & Havail2)".
    assert (Hav1 : Some (nb - (i + gk) - 1)%nat = avail_sub (Some nb) (i + gk + 1)).
    { rewrite avail_sub_Some. f_equal. lia. }
    iEval (rewrite Hav1) in "Havail2".
    (* rebuild kalloc_env at avail_sub (i+gk+1) *)
    iAssert (kalloc_env γa (avail_sub (Some nb) (i + gk + 1)))
      with "[Havail2]" as "Henv".
    { iExists γk. iFrame "Hlock Havail2 Hqcpu". }
    (* a0 = page, page_valid, nonzero *)
    set (page := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    assert (Hpanz : page <> mword_of_int 0).
    { rewrite /page. change (mword_of_int 0 : mword 64) with nullp. exact (page_valid_ne_null _ Hpv). }
    (* recovered callee-saved regs off J (kalloc preserves them) *)
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    assert (HmkJ : forall r : mword 5, is_cs_idx r = true -> Mk !!! Regidx r = J !!! Regidx r).
    { intros r Hr. rewrite /J. rewrite upd_ne; [reflexivity |].
      intro Habs; injection Habs as Habs2; subst r; vm_compute in Hr; discriminate. }
    assert (Hmr0_9 : mr0 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat i)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact Hs1. }
    assert (Hmr0_24 : mr0 !!! Regidx (mword_of_int 24 : mword 5) = mword_of_int 0x800127d0).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 24) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 24) ltac:(vm_compute; reflexivity)). exact Hs8. }
    assert (Hmr0_18 : mr0 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 0x4fa4fa4fa4fa4fa5).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact Hs2m. }
    assert (Hmr0_19 : mr0 !!! Regidx (mword_of_int 19 : mword 5) = mword_of_int 0x3FFFFFF000).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 19) ltac:(vm_compute; reflexivity)). exact Hs3. }
    assert (Hmr0_21 : mr0 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 0x800181d0).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 21) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 21) ltac:(vm_compute; reflexivity)). exact Hs5. }
    assert (Hmr0_22 : mr0 !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 4096).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 22) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 22) ltac:(vm_compute; reflexivity)). exact Hs6. }
    assert (Hmr0_23 : mr0 !!! Regidx (mword_of_int 23 : mword 5) = mword_of_int 6).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 23) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 23) ltac:(vm_compute; reflexivity)). exact Hs7. }
    assert (Hmr0_20 : mr0 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 20) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 20) ltac:(vm_compute; reflexivity)). exact Hs4. }
    assert (Hmr0_25 : mr0 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 25) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 25) ltac:(vm_compute; reflexivity)). exact Hx25. }
    assert (Hmr0_26 : mr0 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 26) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 26) ltac:(vm_compute; reflexivity)). exact Hx26. }
    assert (Hmr0_27 : mr0 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 27) ltac:(vm_compute; reflexivity)).
      rewrite <- (HmkJ (mword_of_int 27) ltac:(vm_compute; reflexivity)). exact Hx27. }
    (* +0x56 mv a2,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x56)) (mword_of_int 12 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [-]").
    iIntros (CIDl3 Hsl3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (mr0 !!! Regidx (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    (* +0x58 beqz a0 FALLS (a0 = page <> 0) *)
    assert (HW2a0 : W2 !!! Regidx (mword_of_int 10 : mword 5) = page).
    { rewrite /W2. rewrite upd_ne; [| reg_neq]. reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x58)) (mword_of_int 32 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              W2 (K - 10)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HW2a0; apply eq_vec_false_iff; intro Heq; apply Hpanz; rewrite Heq; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi58 [-]").
    iIntros (CIDl4 Hsl4) "Hcg Hpc".
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    (* +0x5a sub a1,s1,s8 => 360*i *)
    assert (HW2s1 : W2 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat i)).
    { rewrite /W2. rewrite upd_ne; [| reg_neq]. exact Hmr0_9. }
    assert (HW2s8 : W2 !!! Regidx (mword_of_int 24 : mword 5) = mword_of_int 0x800127d0).
    { rewrite /W2. rewrite upd_ne; [| reg_neq]. exact Hmr0_24. }
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x5a)) (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 5)
              (mword_of_int (360 * Z.of_nat i))
              W2 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HW2s1 HW2s8;
                    assert (Hnn : (0 <= 360 * Z.of_nat i)%Z) by (apply Z.mul_nonneg_nonneg; lia);
                    assert (Hle : (360 * Z.of_nat i <= 360 * 64)%Z) by (apply Z.mul_le_mono_nonneg_l; lia);
                    rewrite (subvec_moi (0x800127d0 + 360 * Z.of_nat i) 0x800127d0 ltac:(lia) ltac:(lia) ltac:(lia));
                    f_equal; lia)
              with "Hcg Hpc Hi5a [-]").
    iIntros (CIDl5 Hsl5) "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int (360 * Z.of_nat i))]> W2).
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x5a) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    (* +0x5e srai a1,a1,3 => 45*i *)
    assert (Hcr3 : creg2reg_idx (Cregidx (mword_of_int 3)) = Regidx (mword_of_int 11)) by (vm_compute; reflexivity).
    iEval (rewrite Hcr3) in "Hi5e".
    assert (HW3a1 : W3 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (360 * Z.of_nat i)) by (rewrite /W3 upd_eq; reflexivity).
    iApply (wp_srai_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x5e)) (mword_of_int 11 : mword 5) (mword_of_int 3 : mword 6)
              W3 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e [-]").
    iIntros (CIDl6 Hsl6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_right_arith (W3 !!! Regidx (mword_of_int 11)) (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0))]> W3).
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (45 * Z.of_nat i)).
    { rewrite /W4 upd_eq. rewrite HW3a1.
      rewrite (srai3 (360 * Z.of_nat i) ltac:(split; [lia | assert (360 * Z.of_nat i <= 360*64) by (apply Z.mul_le_mono_nonneg_l; lia); change 9223372036854775808 with (9223372036854775808%Z); lia])).
      f_equal. replace (360 * Z.of_nat i)%Z with (45 * Z.of_nat i * 8)%Z by lia. rewrite Z.div_mul; [reflexivity | lia]. }
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x5e) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* +0x60 mul a1,a1,s2 => i *)
    assert (HW4s2 : W4 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 0x4fa4fa4fa4fa4fa5).
    { peel_reg_step. exact Hmr0_18. }
    iApply (wp_mul_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x60)) (mword_of_int 11 : mword 5) (mword_of_int 11 : mword 5) (mword_of_int 18 : mword 5)
              (mword_of_int (Z.of_nat i))
              W4 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HW4a1 HW4s2; exact (kstack_mul_step i Hilt))
              with "Hcg Hpc Hi60 [-]").
    iIntros (CIDl7 Hsl7) "Hcg Hpc".
    set (W5 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat i))]> W4).
    assert (Hp64 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x60) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp64) in "Hpc".
    (* +0x64 slli a1,a1,13 => 8192*i *)
    assert (HW5a1 : W5 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (Z.of_nat i)) by (rewrite /W5 upd_eq; reflexivity).
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x64)) (Regidx (mword_of_int 11)) (mword_of_int 11 : mword 5) (mword_of_int 13 : mword 6)
              W5 (K - 10)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [-]").
    iIntros (CIDl8 Hsl8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W6 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (W5 !!! Regidx (mword_of_int 11)) (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> W5).
    assert (HW6a1 : W6 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (8192 * Z.of_nat i)).
    { rewrite /W6 upd_eq. rewrite HW5a1. change (Z.sub log2_xlen 1) with 5.
      rewrite (slli13 (Z.of_nat i) ltac:(lia) ltac:(assert (Z.of_nat i * 8192 <= 64 * 8192) by (apply Z.mul_le_mono_nonneg_r; lia); lia)).
      replace (8192 * Z.of_nat i)%Z with (Z.of_nat i * 8192)%Z by ring. reflexivity. }
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* +0x66 lui a5,0x2 => 8192 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x66)) (mword_of_int 15 : mword 5) (sign_extend' 20 (mword_of_int 2 : mword 6)) (mword_of_int 8192 : mword 64)
              W6 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi66 [-]").
    iIntros (CIDl9 Hsl9) "Hcg Hpc".
    set (W7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 8192 : mword 64)]> W6).
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* +0x68 addw a1,a1,a5 => 8192*(i+1) *)
    assert (Hcr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15)) by (vm_compute; reflexivity).
    iEval (rewrite Hcr3 Hcr7) in "Hi68".
    assert (HW7a1 : W7 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (8192 * Z.of_nat i)).
    { rewrite /W7. rewrite upd_ne; [| reg_neq]. exact HW6a1. }
    assert (HW7a5 : W7 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 8192) by (rewrite /W7 upd_eq; reflexivity).
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x68)) (mword_of_int 11 : mword 5) (mword_of_int 15 : mword 5)
              W7 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 [-]").
    iIntros (CIDl10 Hsl10) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
    set (W8 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (sign_extend' 64 (add_vec (subrange_vec_dec (W7 !!! Regidx (mword_of_int 11)) 31 0 : mword 32) (subrange_vec_dec (W7 !!! Regidx (mword_of_int 15)) 31 0 : mword 32)))]> W7).
    assert (HW8a1 : W8 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (8192 * (Z.of_nat i + 1))).
    { rewrite /W8 upd_eq. rewrite HW7a1 HW7a5. exact (addw_step i Hilt). }
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* +0x6a mv a4,s7 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x6a)) (mword_of_int 14 : mword 5) (mword_of_int 23 : mword 5)
              W8 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a [-]").
    iIntros (CIDl11 Hsl11) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (W8 !!! Regidx (mword_of_int 23 : mword 5)))]> W8).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x6a) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* +0x6c mv a3,s6 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x6c)) (mword_of_int 13 : mword 5) (mword_of_int 22 : mword 5)
              W9 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [-]").
    iIntros (CIDl12 Hsl12) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W10 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec zero_reg (W9 !!! Regidx (mword_of_int 22 : mword 5)))]> W9).
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    (* +0x6e sub a1,s3,a1 => VA = va_i i *)
    assert (HW10s3 : W10 !!! Regidx (mword_of_int 19 : mword 5) = mword_of_int 0x3FFFFFF000).
    { peel_reg_step. exact Hmr0_19. }
    assert (HW10a1 : W10 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int (8192 * (Z.of_nat i + 1))).
    { rewrite /W10 /W9. repeat (rewrite upd_ne; [| reg_neq]). exact HW8a1. }
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x6e)) (mword_of_int 11 : mword 5) (mword_of_int 19 : mword 5) (mword_of_int 11 : mword 5)
              VA
              W10 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HW10s3 HW10a1; unfold VA, va_i; apply subvec_moi; [assert (0 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_nonneg_nonneg; lia); lia | assert (8192 * (Z.of_nat i + 1) <= 8192 * 64) by (apply Z.mul_le_mono_nonneg_l; lia); lia | lia])
              with "Hcg Hpc Hi6e [-]").
    iIntros (CIDl13 Hsl13) "Hcg Hpc".
    set (W11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg VA]> W10).
    assert (Hp72 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x6e) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp72) in "Hpc".
    (* +0x72 mv a0,s4 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x72)) (mword_of_int 10 : mword 5) (mword_of_int 20 : mword 5)
              W11 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi72 [-]").
    iIntros (CIDl14 Hsl14) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W12 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (W11 !!! Regidx (mword_of_int 20 : mword 5)))]> W11).
    assert (Hp74 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp74) in "Hpc".
    (* +0x74 jal kvmmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x74)) (mword_of_int 1 : mword 5) (mword_of_int 2095356 : mword 21)
              W12 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi74 [-]").
    iIntros (CIDl15 Hsl15) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x74) : mword 64) 4)]> W12).
    assert (Htgtm : add_vec (mword_of_int (KernelSyms.proc_mapstacks + 0x74) : mword 64) (sign_extend' 64 (mword_of_int 2095356 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* the kvmmap-entry register facts *)
    set (ppn0 := (autocast (T := mword) (subrange_vec_dec page 55 12) : mword 44)).
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec (pt_base tk) (zeros' 12 : mword 12))).
    { rewrite /Wk. rewrite upd_ne; [| reg_neq]. rewrite /W12 upd_eq. rewrite add_vec_zero_l.
      peel_reg_step.
      rewrite Hmr0_20. rewrite Hroot. rewrite Hbase. reflexivity. }
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = VA).
    { rewrite /Wk /W12. repeat (rewrite upd_ne; [| reg_neq]). rewrite /W11 upd_eq. reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = page).
    { rewrite /Wk /W12 /W11. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W10 /W9 /W8 /W7 /W6 /W5 /W4 /W3. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /W2 upd_eq. rewrite add_vec_zero_l. reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /Wk /W12 /W11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /W10 upd_eq. rewrite add_vec_zero_l.
      peel_reg_step. rewrite Hmr0_22.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /Wk /W12 /W11 /W10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /W9 upd_eq. rewrite add_vec_zero_l.
      peel_reg_step. exact Hmr0_23. }
    assert (HWksp : Wk !!! Regidx csp_rs1 = spr).
    { peel_reg_step. exact Hmr0sp. }
    (* page validity facts feeding the kvmmap premises *)
    pose proof Hpv as Hpv'. destruct Hpv' as [Hpal [Hplo Hphi]].
    unfold page_aligned, PGSIZE in Hpal. unfold page_in_range, kmem_lo, kmem_hi in Hplo, Hphi.
    rewrite uint_unsigned in Hpal, Hplo, Hphi.
    assert (Hpaal : subrange_vec_dec page 11 0 = (zeros' 12 : mword 12)).
    { apply bv_eq. rewrite subrange64_unsigned_11_0. change (2^12) with 4096.
      rewrite Hpal. vm_compute; reflexivity. }
    assert (Hpab : (uint page + Z.of_nat 1 * 4096 < 2 ^ 56)%Z).
    { rewrite uint_unsigned. change (Z.of_nat 1 * 4096)%Z with 4096%Z. change (2^56)%Z with 72057594037927936%Z.
      apply (Z.lt_trans _ (0x88000000 + 4096)); [apply Z.add_lt_mono_r; exact Hphi | apply Z.ltb_lt; vm_compute; reflexivity]. }
    assert (Hpbase : zero_extend' 64 (concat_vec ppn0 (zeros' 12 : mword 12)) = page).
    { unfold ppn0. apply walk_alloc_page_base.
      - rewrite uint_unsigned. exact Hpal.
      - rewrite uint_unsigned. apply (Z.lt_trans _ 0x88000000); [exact Hphi | apply Z.ltb_lt; vm_compute; reflexivity]. }
    (* the represented map + no-remap for the kvmmap call *)
    assert (Hnone : forall k, (k < 1)%nat -> kvm_stacks pas i m0 !! vpn_at (svpn_of VA) k = None).
    { intros k Hk. assert (k = 0%nat) by lia. subst k.
      rewrite (va_i_svpn i Hilt).
      assert (Hv0 : vpn_at (kstack_vpn i) 0 = kstack_vpn i) by (apply bv_eq; apply vpn_at_0_bv).
      rewrite Hv0. rewrite (kvm_stacks_miss pas i m0 (kstack_vpn i)).
      2:{ intros j Hj. apply kstack_vpn_inj; lia. }
      apply Hres. exact Hilt. }
    (* the counted budget premise for kvmmap *)
    assert (Hkbud : (pt_missing tk (svpn_of VA) 1 < nb - (i + gk + 1))%nat).
    { rewrite (va_i_svpn i Hilt).
      pose proof Hbud as HB. rewrite (pms_seq_peel i Hilt) in HB. cbn [sum_list_with] in HB. lia. }
    (* [Hcnt] was refreshed at [CIDl2] by kalloc's own postcondition; the
       arithmetic + [jal kvmmap] straight-line stretch above landed on
       [CIDl15] -- transport it there once, rather than per instruction. *)
    assert (HcntC1 : b = false \/ p = zero_reg -> (CIDl15 : CPU) = (CIDl2 : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CIDl2 CIDl15 lvl eb p C b HcntC1 with "Hcnt") as "Hcnt".
    iApply (KM.wp_kvmmap_sconf γa Wk tk (kvm_stacks pas i m0) 1 6 lvl (K - 10)%nat eb p C (Some ((nb - (i + gk + 1))%nat)) b
              Hlvl ltac:(lia)
              HWka0
              ltac:(rewrite HWka1; unfold VA; apply va_i_align; exact Hilt)
              ltac:(rewrite HWka2; exact Hpaal) HWka3 ltac:(lia) HWka4 pms_perm_ok6
              ltac:(rewrite HWka1; unfold VA; apply va_i_range; exact Hilt)
              ltac:(rewrite HWka2; exact Hpab) Hrep ltac:(rewrite HWka1; exact Hnone)
              with "[] Hcg Hcnt Htext Hpc Hptree [Henv] [-]").
    { iPureIntro. rewrite HWka1. exact Hkbud. }
    { rewrite avail_sub_Some. iExact "Henv". }
    iIntros (CIDl16 Hsl16 mr1 t' g') "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs1 %Hbase' %Hrep' %Hpres %Hg'miss".
    assert (Henveq : avail_sub (Some ((nb - (i + gk + 1))%nat)) g' = avail_sub (Some nb) (S i + (gk + g'))).
    { rewrite !avail_sub_Some. f_equal. lia. }
    iEval (rewrite Henveq) in "Henv".
    (* define pas' *)
    set (pas' := fun j => if (j <? i)%nat then pas j else ppn0).
    assert (Hpasagree : forall j, (j < i)%nat -> pas j = pas' j).
    { intros j Hj. unfold pas'. rewrite (proj2 (Nat.ltb_lt j i) Hj). reflexivity. }
    assert (Hpasi : pas' i = ppn0) by (unfold pas'; rewrite (proj2 (Nat.ltb_ge i i) ltac:(lia)); reflexivity).
    (* the kvmmap post's represented map is [kvm_stacks pas' (S i) m0] *)
    assert (Hrepnew : pt_rep0 t' (kvm_stacks pas' (S i) m0)).
    { rewrite HWka1 in Hrep'. rewrite HWka2 in Hrep'. rewrite /VA in Hrep'.
      rewrite (va_i_svpn i Hilt) in Hrep'. fold ppn0 in Hrep'.
      rewrite (kvm_stacks_ext pas pas' i m0 Hpasagree) in Hrep'.
      cbn [kvm_stacks]. rewrite Hpasi. exact Hrep'. }
    (* pc back at +0x78 *)
    assert (HWk1 : Wk !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x74) : mword 64) 4) by (rewrite /Wk upd_eq; reflexivity).
    assert (Hret78 : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_mapstacks + 0x78)).
    { rewrite HWk1. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret78) in "Hpc".
    (* recover callee-saved through kvmmap *)
    assert (Hmr1_9 : mr1 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat i)).
    { rewrite (callee_saved_lookup Hkcs1 (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      peel_reg_step.
      exact Hmr0_9. }
    assert (Hmr1sp : mr1 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs1 csp_rs1 ltac:(vm_compute; reflexivity)). exact HWksp. }
    assert (HWkcs : forall r : mword 5, is_cs_idx r = true -> Wk !!! Regidx r = mr1 !!! Regidx r)
      by (intros r Hr; symmetry; apply (callee_saved_lookup Hkcs1 r Hr)).
    assert (Hmr1_24 : mr1 !!! Regidx (mword_of_int 24 : mword 5) = mword_of_int 0x800127d0).
    { rewrite <- (HWkcs (mword_of_int 24) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_24. }
    assert (Hmr1_18 : mr1 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 0x4fa4fa4fa4fa4fa5).
    { rewrite <- (HWkcs (mword_of_int 18) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_18. }
    assert (Hmr1_19 : mr1 !!! Regidx (mword_of_int 19 : mword 5) = mword_of_int 0x3FFFFFF000).
    { rewrite <- (HWkcs (mword_of_int 19) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_19. }
    assert (Hmr1_21 : mr1 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 0x800181d0).
    { rewrite <- (HWkcs (mword_of_int 21) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_21. }
    assert (Hmr1_22 : mr1 !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 4096).
    { rewrite <- (HWkcs (mword_of_int 22) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_22. }
    assert (Hmr1_23 : mr1 !!! Regidx (mword_of_int 23 : mword 5) = mword_of_int 6).
    { rewrite <- (HWkcs (mword_of_int 23) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_23. }
    assert (Hmr1_20 : mr1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { rewrite <- (HWkcs (mword_of_int 20) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_20. }
    assert (Hmr1_25 : mr1 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { rewrite <- (HWkcs (mword_of_int 25) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_25. }
    assert (Hmr1_26 : mr1 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { rewrite <- (HWkcs (mword_of_int 26) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_26. }
    assert (Hmr1_27 : mr1 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { rewrite <- (HWkcs (mword_of_int 27) ltac:(vm_compute; reflexivity)).
      peel_reg_step. exact Hmr0_27. }
    (* accumulate the page_own for the new slot i *)
    iAssert ([∗ list] j ∈ seq 0 (S i),
               page_own (zero_extend' 64 (concat_vec (pas' j) (zeros' 12 : mword 12))))%I
      with "[Hpages Hpage]" as "Hpages".
    { rewrite seq_S. rewrite big_sepL_app.
      iSplitL "Hpages".
      { iApply (pms_pages_ext i pas pas' Hpasagree with "Hpages"). }
      { rewrite big_sepL_singleton. replace (0 + i)%nat with i by lia.
        rewrite Hpasi. rewrite Hpbase. iExact "Hpage". } }
    (* +0x78 addi s1,s1,360 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x78)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12)
              mr1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iIntros (CIDl17 Hsl17) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (F1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mr1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mr1).
    assert (HF1s1 : F1 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat (S i))).
    { rewrite /F1 upd_eq. rewrite Hmr1_9.
      assert (Hsx : sign_extend' 64 (mword_of_int 360 : mword 12) = (mword_of_int 360 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hsx. apply bv_eq.
      unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned.
      assert (Hii : (0 <= 360 * Z.of_nat i)%Z /\ (360 * Z.of_nat i <= 360 * 64)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
      assert (Hsi : (0 <= 360 * Z.of_nat (S i))%Z /\ (360 * Z.of_nat (S i) <= 360 * 64)%Z) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
      assert (Bi : (0 <= 0x800127d0 + 360 * Z.of_nat i < 18446744073709551616)%Z).
      { split; [apply Z.add_nonneg_nonneg; [apply Z.leb_le; vm_compute; reflexivity | exact (proj1 Hii)]
               | apply (Z.le_lt_trans _ (0x800127d0 + 360 * 64)); [apply Z.add_le_mono_l; exact (proj2 Hii) | apply Z.ltb_lt; vm_compute; reflexivity]]. }
      assert (Bsi : (0 <= 0x800127d0 + 360 * Z.of_nat (S i) < 18446744073709551616)%Z).
      { split; [apply Z.add_nonneg_nonneg; [apply Z.leb_le; vm_compute; reflexivity | exact (proj1 Hsi)]
               | apply (Z.le_lt_trans _ (0x800127d0 + 360 * 64)); [apply Z.add_le_mono_l; exact (proj2 Hsi) | apply Z.ltb_lt; vm_compute; reflexivity]]. }
      rewrite (moi64_small (0x800127d0 + 360 * Z.of_nat i) Bi).
      change (bv_unsigned (mword_of_int 360 : mword 64)) with 360.
      replace (0x800127d0 + 360 * Z.of_nat i + 360)%Z with (0x800127d0 + 360 * Z.of_nat (S i))%Z by (rewrite Nat2Z.inj_succ; ring).
      rewrite (moi64_small (0x800127d0 + 360 * Z.of_nat (S i)) Bsi).
      apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact Bsi. }
    assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x78) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* facts for the new invariant / bne *)
    assert (HF1s5 : F1 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 0x800181d0).
    { rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmr1_21. }
    assert (Hg'le : (g' <= pt_missing tk (kstack_vpn i) 1)%nat).
    { rewrite HWka1 in Hg'miss. rewrite (va_i_svpn i Hilt) in Hg'miss. unfold VA in Hg'miss. exact Hg'miss. }
    (* re-establish the budget for i+1 *)
    assert (Hbudnew : (gk + g' + sum_list_with (fun j => pt_missing t' (kstack_vpn j) 1) (seq (S i) (64 - S i))
                        <= kstacks_missing t)%nat).
    { assert (Htail : (sum_list_with (fun j => pt_missing t' (kstack_vpn j) 1) (seq (S i) (64 - S i))
                        <= sum_list_with (fun j => pt_missing tk (kstack_vpn j) 1) (seq (S i) (64 - S i)))%nat).
      { apply sum_list_with_le. intros x _. apply pt_missing_present_mono. exact Hpres. }
      pose proof Hbud as HB. rewrite (pms_seq_peel i Hilt) in HB. cbn [sum_list_with] in HB.
      replace (64 - S i)%nat with (63 - i)%nat in Htail |- * by lia. lia. }
    (* the new page's ppn0 is a legal stack pa (kalloc validity): its 4096-byte
       page lies wholly in RAM, i.e. [node_kdata ppn0] = [kvm_pas_ok]'s clause *)
    assert (Hppnb : node_kdata ppn0).
    { unfold node_kdata.
      assert (Hpp : (bv_unsigned ppn0 * 4096 = bv_unsigned page)%Z).
      { unfold ppn0. pose proof Hpbase as HpbC. apply (f_equal bv_unsigned) in HpbC.
        rewrite page_base_unsigned in HpbC. exact HpbC. }
      pose proof Hpal as Hpal2. apply Z.mod_divide in Hpal2; [| discriminate]. destruct Hpal2 as [q Hq].
      pose proof Hphi as Hphi2. rewrite Hq in Hphi2.
      assert (Hqlt : (q < 557056)%Z) by nia.
      split.
      - rewrite Hpp. unfold ram_base.
        apply (Z.le_trans _ 0x80023558); [apply Z.leb_le; vm_compute; reflexivity | rewrite Hq; nia].
      - rewrite Hpp. unfold ram_base, ram_size. rewrite Hq. nia. }
    (* case on i+1 = 64 (fall to epilogue) or < 64 (recurse) *)
    destruct rem' as [| rem''].
    { (* LAST iteration: S i = 64, bne s1,s5 FALLS *)
      assert (Hlast : S i = 64%nat) by lia.
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x7c)) (mword_of_int 8150 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5)
                F1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite HF1s1 HF1s5; unfold neq_vec; apply negb_false_iff; apply eq_vec_true_iff; rewrite Hlast; apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi7c [-]").
      iIntros (CIDb1 Hsb1) "Hcg Hpc".
      assert (Hp80 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x7c) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp80) in "Hpc".
      (* build epilogue inputs at i+1 = 64 *)
      assert (Hpasok : kvm_pas_ok pas').
      { intros j Hj. unfold pas'.
        destruct (Nat.ltb_spec j i) as [Hlt | Hge].
        - apply Hpasb; exact Hlt.
        - exact Hppnb. }
      assert (Hnodestf : pt_nodes t' = (pt_nodes t + (gk + g'))%nat) by lia.
      assert (Hgfin : (gk + g' <= kstacks_missing t)%nat) by lia.
      assert (Hbasetf : pt_base t' = pt_base t) by (rewrite Hbase'; exact Hbase).
      assert (Hrep64 : pt_rep0 t' (kvm_stacks pas' 64 m0)) by (rewrite <- Hlast; exact Hrepnew).
      (* [Hcont] was anchored at THIS iteration's entry hart [CID]; the
         straight-line stretch above (kalloc/kvmmap/arith) plus this branch's
         own crossing landed on [CIDb1] -- re-anchor ONCE via the composed
         chain of every [wp_next] conditional equality collected so far,
         rather than one [wp_next_shift] per leaf. *)
      assert (Hchain1 : b = false \/ p = zero_reg -> (CIDb1 : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hchain1 with "Hcont") as "Hcont".
      (* [Hcnt] was last refreshed at [CIDl16] by kvmmap's own postcondition;
         [+0x78 addi] and this branch's own crossing moved on to [CIDb1]. *)
      assert (HcntC2 : b = false \/ p = zero_reg -> (CIDb1 : CPU) = (CIDl16 : CPU)) by wp_next_chain.
      iDestruct (cpu_own_transport CIDl16 CIDb1 lvl eb p C b HcntC2 with "Hcnt") as "Hcnt".
      iApply (wp_proc_mapstacks_epilogue_sconf γa mm F1 t t' m0 K lvl eb p C (Some nb) (gk + g')%nat pas' b
                Hlvl HK
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1sp)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_25)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_26)
                ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_27)
                Hbasetf Hrep64 Hnodestf Hpasok Hgfin
                with "Hcg Hcnt Htext Hpc Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree [Henv] [Hpages] [Hcont]").
      { rewrite <- Hlast. iExact "Henv". }
      { rewrite <- Hlast. iExact "Hpages". }
      { iExact "Hcont". } }
    (* NOT last: S i < 64, bne TAKEN, recurse *)
    assert (Hnl : (S i < 64)%nat) by lia.
    iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x7c)) (mword_of_int 8150 : mword 13) (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5)
              F1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rgne; rgne; rewrite HF1s1 HF1s5; unfold neq_vec; apply negb_true_iff; apply eq_vec_false_iff;
                    intro Heq; apply (f_equal bv_unsigned) in Heq;
                    rewrite (moi64_small (0x800127d0 + 360 * Z.of_nat (S i))
                       ltac:(split; [apply Z.add_nonneg_nonneg; [apply Z.leb_le; vm_compute; reflexivity | apply Z.mul_nonneg_nonneg; lia]
                                    | apply (Z.le_lt_trans _ (0x800127d0 + 360 * 64)); [apply Z.add_le_mono_l; apply Z.mul_le_mono_nonneg_l; lia | apply Z.ltb_lt; vm_compute; reflexivity]])) in Heq;
                    change (bv_unsigned (mword_of_int 0x800181d0 : mword 64)) with 2147582416%Z in Heq;
                    assert (Hbd : (360 * Z.of_nat (S i) <= 360 * 63)%Z) by (apply Z.mul_le_mono_nonneg_l; lia); lia)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7c [-]").
    iNext. iIntros (CIDb2 Hsb2) "Hcg Hpc".
    assert (Htgt52 : add_vec (mword_of_int (KernelSyms.proc_mapstacks + 0x7c) : mword 64) (sign_extend' 64 (mword_of_int 8150 : mword 13)) = mword_of_int (KernelSyms.proc_mapstacks + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt52) in "Hpc".
    (* recurse via IH at i+1, on the hart THIS iteration ended up on *)
    assert (Hchain2 : b = false \/ p = zero_reg -> (CIDb2 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hchain2 with "Hcont") as "Hcont".
    assert (HcntC3 : b = false \/ p = zero_reg -> (CIDb2 : CPU) = (CIDl16 : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CIDl16 CIDb2 lvl eb p C b HcntC3 with "Hcnt") as "Hcnt".
    iApply (IH CIDb2 (S i) F1 t' (gk + g')%nat pas' Hlvl HK ltac:(lia) ltac:(lia) Hnbig Hroot Hres
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1sp)
              HF1s1
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_24)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_18)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_19)
              HF1s5
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_22)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_23)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_20)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_25)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_26)
              ltac:(rewrite /F1; rewrite upd_ne; [| reg_neq]; exact Hmr1_27)
              (eq_trans Hbase' Hbase) Hrepnew ltac:(lia) Hbudnew
              ltac:(intros j Hj; unfold pas'; destruct (Nat.ltb_spec j i) as [Hlt|Hge]; [apply Hpasb; exact Hlt | exact Hppnb])
              with "Hcg Hcnt Htext Hpc Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree [Henv] Hpages Hcont").
    { iExact "Henv". }
  Qed.

  (* ================================================================= *)
  (* THE PROLOGUE (+0x00..+0x4e) + loop entry: the whole-function spec. *)
  (* ================================================================= *)
  Lemma wp_proc_mapstacks_sconf
      `{GEN : GenId} `{CID : CpuId} (γa : gname)
      (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (lvl K : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool)
    : wp_proc_mapstacks_sconf_body γa mm t m lvl K eb p C on b.
  Proof.
    cbv beta delta [wp_proc_mapstacks_sconf_body].
    intros ret_tgt Hlvl HK Hroot Hrep Hres Hnb.
    destruct Hnb as (nb & Hon & Hnbig). subst on.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 10).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (pmsi_00 with "Htext") as "Hi00". iPoseProof (pmsi_02 with "Htext") as "Hi02".
    iPoseProof (pmsi_04 with "Htext") as "Hi04". iPoseProof (pmsi_06 with "Htext") as "Hi06".
    iPoseProof (pmsi_08 with "Htext") as "Hi08". iPoseProof (pmsi_0a with "Htext") as "Hi0a".
    iPoseProof (pmsi_0c with "Htext") as "Hi0c". iPoseProof (pmsi_0e with "Htext") as "Hi0e".
    iPoseProof (pmsi_10 with "Htext") as "Hi10". iPoseProof (pmsi_12 with "Htext") as "Hi12".
    iPoseProof (pmsi_14 with "Htext") as "Hi14". iPoseProof (pmsi_16 with "Htext") as "Hi16".
    iPoseProof (pmsi_18 with "Htext") as "Hi18". iPoseProof (pmsi_1a with "Htext") as "Hi1a".
    iPoseProof (pmsi_1e with "Htext") as "Hi1e". iPoseProof (pmsi_22 with "Htext") as "Hi22".
    iPoseProof (pmsi_24 with "Htext") as "Hi24". iPoseProof (pmsi_28 with "Htext") as "Hi28".
    iPoseProof (pmsi_2c with "Htext") as "Hi2c". iPoseProof (pmsi_2e with "Htext") as "Hi2e".
    iPoseProof (pmsi_32 with "Htext") as "Hi32". iPoseProof (pmsi_36 with "Htext") as "Hi36".
    iPoseProof (pmsi_3a with "Htext") as "Hi3a". iPoseProof (pmsi_3c with "Htext") as "Hi3c".
    iPoseProof (pmsi_3e with "Htext") as "Hi3e". iPoseProof (pmsi_42 with "Htext") as "Hi42".
    iPoseProof (pmsi_44 with "Htext") as "Hi44". iPoseProof (pmsi_46 with "Htext") as "Hi46".
    iPoseProof (pmsi_48 with "Htext") as "Hi48". iPoseProof (pmsi_4a with "Htext") as "Hi4a".
    iPoseProof (pmsi_4e with "Htext") as "Hi4e".
    (* +0x00 c.addi16sp sp,-80 : the 10-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.proc_mapstacks) (mword_of_int 59 : mword 6) mm K 10 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CIDp1 Hsp1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm) with W1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (v72) "Hc72". iDestruct "S2" as (v64) "Hc64".
    iDestruct "S3" as (v56) "Hc56". iDestruct "S4" as (v48) "Hc48".
    iDestruct "S5" as (v40) "Hc40". iDestruct "S6" as (v32) "Hc32".
    iDestruct "S7" as (v24) "Hc24". iDestruct "S8" as (v16) "Hc16".
    iDestruct "S9" as (v8) "Hc08". iDestruct "S10" as (v0) "Hc00".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.proc_mapstacks : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,72(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x02)) (mword_of_int 9 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 10)%nat v72 b with "Hcg Hpc Hi02 [Hc72] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc72". }
    iIntros (CIDp2 Hsp2) "Hcg Hpc Hc72". iEval (rewrite HspW1 Hb1; rgne) in "Hc72".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc72".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,64(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x04)) (mword_of_int 8 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 10)%nat v64 b with "Hcg Hpc Hi04 [Hc64] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc64". }
    iIntros (CIDp3 Hsp3) "Hcg Hpc Hc64". iEval (rewrite HspW1 Hb2; rgne) in "Hc64".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc64".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x06)) (mword_of_int 7 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 10)%nat v56 b with "Hcg Hpc Hi06 [Hc56] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc56". }
    iIntros (CIDp4 Hsp4) "Hcg Hpc Hc56". iEval (rewrite HspW1 Hb3; rgne) in "Hc56".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r9) in "Hc56".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 sd s2,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x08)) (mword_of_int 6 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 10)%nat v48 b with "Hcg Hpc Hi08 [Hc48] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc48". }
    iIntros (CIDp5 Hsp5) "Hcg Hpc Hc48". iEval (rewrite HspW1 Hb4; rgne) in "Hc48".
    assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r18) in "Hc48".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a sd s3,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x0a)) (mword_of_int 5 : mword 6) (mword_of_int 19 : mword 5)
              W1 (K - 10)%nat v40 b with "Hcg Hpc Hi0a [Hc40] [-]").
    { iEval (rewrite HspW1 Hb5). iExact "Hc40". }
    iIntros (CIDp6 Hsp6) "Hcg Hpc Hc40". iEval (rewrite HspW1 Hb5; rgne) in "Hc40".
    assert (HW1r19 : W1 !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r19) in "Hc40".
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c sd s4,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x0c)) (mword_of_int 4 : mword 6) (mword_of_int 20 : mword 5)
              W1 (K - 10)%nat v32 b with "Hcg Hpc Hi0c [Hc32] [-]").
    { iEval (rewrite HspW1 Hb6). iExact "Hc32". }
    iIntros (CIDp7 Hsp7) "Hcg Hpc Hc32". iEval (rewrite HspW1 Hb6; rgne) in "Hc32".
    assert (HW1r20 : W1 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r20) in "Hc32".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e sd s5,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x0e)) (mword_of_int 3 : mword 6) (mword_of_int 21 : mword 5)
              W1 (K - 10)%nat v24 b with "Hcg Hpc Hi0e [Hc24] [-]").
    { iEval (rewrite HspW1 Hb7). iExact "Hc24". }
    iIntros (CIDp8 Hsp8) "Hcg Hpc Hc24". iEval (rewrite HspW1 Hb7; rgne) in "Hc24".
    assert (HW1r21 : W1 !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r21) in "Hc24".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 sd s6,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x10)) (mword_of_int 2 : mword 6) (mword_of_int 22 : mword 5)
              W1 (K - 10)%nat v16 b with "Hcg Hpc Hi10 [Hc16] [-]").
    { iEval (rewrite HspW1 Hb8). iExact "Hc16". }
    iIntros (CIDp9 Hsp9) "Hcg Hpc Hc16". iEval (rewrite HspW1 Hb8; rgne) in "Hc16".
    assert (HW1r22 : W1 !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r22) in "Hc16".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 sd s7,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x12)) (mword_of_int 1 : mword 6) (mword_of_int 23 : mword 5)
              W1 (K - 10)%nat v8 b with "Hcg Hpc Hi12 [Hc08] [-]").
    { iEval (rewrite HspW1 Hb9). iExact "Hc08". }
    iIntros (CIDp10 Hsp10) "Hcg Hpc Hc08". iEval (rewrite HspW1 Hb9; rgne) in "Hc08".
    assert (HW1r23 : W1 !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r23) in "Hc08".
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 sd s8,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x14)) (mword_of_int 0 : mword 6) (mword_of_int 24 : mword 5)
              W1 (K - 10)%nat v0 b with "Hcg Hpc Hi14 [Hc00] [-]").
    { iEval (rewrite HspW1 Hb10). iExact "Hc00". }
    iIntros (CIDp11 Hsp11) "Hcg Hpc Hc00". iEval (rewrite HspW1 Hb10; rgne) in "Hc00".
    assert (HW1r24 : W1 !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r24) in "Hc00".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* ---- constant materialization +0x16..+0x4e ---- *)
    (* +0x16 c.addi4spn s0,sp,80 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x16)) (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 10)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CIDp12 Hsp12) "Hcg Hpc".
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> W1).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 mv s4,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x18)) (mword_of_int 20 : mword 5) (mword_of_int 10 : mword 5)
              P2 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi18 [-]").
    iIntros (CIDp13 Hsp13) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P3 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg (add_vec zero_reg (P2 !!! Regidx (mword_of_int 10 : mword 5)))]> P2).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a auipc s1,0x11 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x1a)) (mword_of_int 9 : mword 5) (mword_of_int 17 : mword 20)
              P3 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi1a [-]").
    iIntros (CIDp14 Hsp14) "Hcg Hpc".
    set (P4 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.proc_mapstacks + 0x1a) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> P3).
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x1a) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* +0x1e addi s1,s1,-24 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x1e)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 114 : mword 12)
              P4 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi1e [-]").
    iIntros (CIDp15 Hsp15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P5 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (P4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 114 : mword 12)))]> P4).
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* +0x22 mv s8,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x22)) (mword_of_int 24 : mword 5) (mword_of_int 9 : mword 5)
              P5 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi22 [-]").
    iIntros (CIDp16 Hsp16) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P6 := <[Regidx (mword_of_int 24 : mword 5) := regval_into_reg (add_vec zero_reg (P5 !!! Regidx (mword_of_int 9 : mword 5)))]> P5).
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 lui a5,0xa5 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x24)) (mword_of_int 15 : mword 5) (mword_of_int 165 : mword 20) (luival (mword_of_int 165 : mword 20))
              P6 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi24 [-]").
    iIntros (CIDp17 Hsp17) "Hcg Hpc".
    set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 165 : mword 20))]> P6).
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x24) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 addi a5,a5,-91 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x28)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 4005 : mword 12)
              P7 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi28 [-]").
    iIntros (CIDp18 Hsp18) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (P7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 4005 : mword 12)))]> P7).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x28) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c slli a5,a5,0xc *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x2c)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 6)
              P8 (K - 10)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi2c [-]").
    iIntros (CIDp19 Hsp19) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_left (P8 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> P8).
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e addi a5,a5,-91 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x2e)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 4005 : mword 12)
              P9 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi2e [-]").
    iIntros (CIDp20 Hsp20) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (P9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 4005 : mword 12)))]> P9).
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* +0x32 lui s2,0x4fa50 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x32)) (mword_of_int 18 : mword 5) (mword_of_int 326224 : mword 20) (luival (mword_of_int 326224 : mword 20))
              P10 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi32 [-]").
    iIntros (CIDp21 Hsp21) "Hcg Hpc".
    set (P11 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (luival (mword_of_int 326224 : mword 20))]> P10).
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x32) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* +0x36 addi s2,s2,-1457 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x36)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 2639 : mword 12)
              P11 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi36 [-]").
    iIntros (CIDp22 Hsp22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P12 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (P11 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 2639 : mword 12)))]> P11).
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* +0x3a slli s2,s2,0x20 *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x3a)) (Regidx (mword_of_int 18)) (mword_of_int 18 : mword 5) (mword_of_int 32 : mword 6)
              P12 (K - 10)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi3a [-]").
    iIntros (CIDp23 Hsp23) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P13 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (shift_bits_left (P12 !!! Regidx (mword_of_int 18 : mword 5)) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> P12).
    assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3c) in "Hpc".
    (* +0x3c add s2,s2,a5 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x3c)) (mword_of_int 18 : mword 5) (mword_of_int 15 : mword 5)
              P13 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi3c [-]").
    iIntros (CIDp24 Hsp24) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
    set (P14 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (P13 !!! Regidx (mword_of_int 18 : mword 5)) (P13 !!! Regidx (mword_of_int 15 : mword 5)))]> P13).
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* +0x3e lui s3,0x4000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x3e)) (mword_of_int 19 : mword 5) (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
              P14 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi3e [-]").
    iIntros (CIDp25 Hsp25) "Hcg Hpc".
    set (P15 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> P14).
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    (* +0x42 addi s3,s3,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x42)) (mword_of_int 19 : mword 5) (mword_of_int 63 : mword 6)
              P15 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi42 [-]").
    iIntros (CIDp26 Hsp26) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P16 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (add_vec (P15 !!! Regidx (mword_of_int 19 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> P15).
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    (* +0x44 slli s3,s3,0xc *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x44)) (Regidx (mword_of_int 19)) (mword_of_int 19 : mword 5) (mword_of_int 12 : mword 6)
              P16 (K - 10)%nat b ltac:(reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi44 [-]").
    iIntros (CIDp27 Hsp27) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P17 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg (shift_bits_left (P16 !!! Regidx (mword_of_int 19 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> P16).
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    (* +0x46 li s7,6 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x46)) (mword_of_int 23 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              P17 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi46 [-]").
    iIntros (CIDp28 Hsp28) "Hcg Hpc".
    set (P18 := <[Regidx (mword_of_int 23 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> P17).
    assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp48) in "Hpc".
    (* +0x48 lui s6,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x48)) (mword_of_int 22 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              P18 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi48 [-]").
    iIntros (CIDp29 Hsp29) "Hcg Hpc".
    set (P19 := <[Regidx (mword_of_int 22 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> P18).
    assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.proc_mapstacks + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    (* +0x4a auipc s5,0x17 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x4a)) (mword_of_int 21 : mword 5) (mword_of_int 23 : mword 20)
              P19 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi4a [-]").
    iIntros (CIDp30 Hsp30) "Hcg Hpc".
    set (P20 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.proc_mapstacks + 0x4a) : mword 64) (auipc_off (mword_of_int 23 : mword 20)))]> P19).
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    (* +0x4e addi s5,s5,-1608 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_mapstacks + 0x4e)) (mword_of_int 21 : mword 5) (mword_of_int 21 : mword 5) (mword_of_int 2626 : mword 12)
              P20 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi4e [-]").
    iIntros (CIDp31 Hsp31) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P21 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg (add_vec (P20 !!! Regidx (mword_of_int 21 : mword 5)) (sign_extend' 64 (mword_of_int 2626 : mword 12)))]> P20).
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.proc_mapstacks + 0x4e) : mword 64) 4 = mword_of_int (KernelSyms.proc_mapstacks + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp52) in "Hpc".
    (* ---- loop-entry register facts (all concrete) ---- *)
    assert (HE_sp : P21 !!! Regidx csp_rs1 = spr).
    { peel_reg_step.
      rewrite -HspW1 /W1 upd_eq. reflexivity. }
    assert (HE_s1 : P21 !!! Regidx (mword_of_int 9 : mword 5) = mword_of_int (0x800127d0 + 360 * Z.of_nat 0)).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s8 : P21 !!! Regidx (mword_of_int 24 : mword 5) = mword_of_int 0x800127d0).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s2 : P21 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 0x4fa4fa4fa4fa4fa5).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s3 : P21 !!! Regidx (mword_of_int 19 : mword 5) = mword_of_int 0x3FFFFFF000).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s5 : P21 !!! Regidx (mword_of_int 21 : mword 5) = mword_of_int 0x800181d0).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s6 : P21 !!! Regidx (mword_of_int 22 : mword 5) = mword_of_int 4096).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s7 : P21 !!! Regidx (mword_of_int 23 : mword 5) = mword_of_int 6).
    { peel_reg_step. apply bv_eq; vm_compute; reflexivity. }
    assert (HE_s4 : P21 !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { peel_reg_step. apply add_vec_zero_l. }
    assert (HE_x25 : P21 !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25)).
    { peel_reg_step. reflexivity. }
    assert (HE_x26 : P21 !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26)).
    { peel_reg_step. reflexivity. }
    assert (HE_x27 : P21 !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27)).
    { peel_reg_step. reflexivity. }
    assert (HE_a0 : P21 !!! Regidx (mword_of_int 10 : mword 5) = mm !!! Regidx (mword_of_int 10)).
    { peel_reg_step. reflexivity. }
    (* [Hcnt] was minted at the function's ENTRY hart [CID]; the prologue's
       own 31 plain-instruction leaves above each landed on a fresh,
       generic-[b] hart, ending at [CIDp31] -- transport it there once. *)
    assert (HcntCP : b = false \/ p = zero_reg -> (CIDp31 : CPU) = (CID : CPU)) by wp_next_chain.
    iDestruct (cpu_own_transport CID CIDp31 lvl eb p C b HcntCP with "Hcnt") as "Hcnt".
    (* [Hcont] (the top-level continuation) is likewise anchored at the
       function's ENTRY hart [CID]; the loop lemma's OWN implicit [CID]
       binder gets unified with [CIDp31] at this call site, so its
       [wp_next] obligation is anchored there too -- re-anchor [Hcont] to
       match, or the final [iExact "Hcont"] fails on a hidden-CID mismatch
       that default printing cannot show. *)
    iDestruct (wp_next_shift HcntCP with "Hcont") as "Hcont".
    (* enter the loop at i = 0 *)
    iApply (wp_proc_mapstacks_loop_sconf γa mm t m K lvl eb p C nb 64 b 0%nat P21 t 0%nat (fun _ => (mword_of_int 0 : mword 44))
              Hlvl HK ltac:(lia) ltac:(lia) Hnbig Hroot Hres
              HE_sp HE_s1 HE_s8 HE_s2 HE_s3 HE_s5 HE_s6 HE_s7
              ltac:(rewrite HE_s4; exact HE_a0)
              HE_x25 HE_x26 HE_x27
              eq_refl Hrep (eq_sym (Nat.add_0_r (pt_nodes t)))
              ltac:(rewrite Nat.add_0_l; rewrite Nat.sub_0_r; unfold kstacks_missing; apply Nat.le_refl)
              ltac:(intros j Hj; exfalso; lia)
              with "Hcg Hcnt Htext Hpc Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00 Hptree [Henv] [] [Hcont]").
    { rewrite Nat.add_0_r. iExact "Henv". }
    { done. }
    { iExact "Hcont". }
  Qed.


End ProofPMS.

End ProcMapstacksProof.
