(* ProofFdalloc.v -- whole-function WP for fdalloc().

     static int fdalloc(struct file *f) {
       int fd; struct proc *p = myproc();
       for (fd = 0; fd < NOFILE; fd++)
         if (p->ofile[fd] == 0) { p->ofile[fd] = f; return fd; }
       return -1;
     }

   Thirty-two instructions @ 0x80004a5e over a 32-byte ra/s0/s1 frame (slot 0
   is a gap), one call, one counted loop and two returns joining at the single
   epilogue at +0x28.  The contract is in SpecFdalloc.v.

   THE LOOP is a FUEL induction on the descriptors left to scan, not iLoeb:
   the trip count is bounded by NOFILE, and the [bne a0,a3] back edge reduces
   to the index test [S fd =? NOFILE] via [fda_neq16], exactly the way
   procinit's proc-array walk reduces to [S j =? NPROC].  The invariant is
     - the pointer/counter pair: a0 = fd, a5 = &p->ofile[fd] (advanced by
       [ProcGeom.p_ofile_succ], the [c.addi a5,a5,8]);
     - a2 = p and s1 = f, which the loop never writes -- a2 is what the
       install arm adds the recomputed offset to, so it must survive;
     - the WHOLE [proc_priv], plus the pure fact that every earlier descriptor
       is non-null.  Only [ProcInv.proc_priv_ofile_read] is used per iteration,
       so no descriptor's payload disjunction is ever opened inside the loop.

   The two exits then differ only in what they hand back: [c.li a0,-1] with
   the block untouched, or the install arm, which is the one place a resource
   moves -- [proc_priv_ofile] borrows the null slot, [ofile_val_null] turns its
   payload into the [fd_slot] the caller receives, and the caller's own
   [ofile_val] goes in. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
Require Import VcGen.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import WpFdallocDecode.
Require Import SpecMyproc.
Require Import SpecFdalloc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The loop's arithmetic, mword-free in its CONTEXT (durable-notes' zify  *)
(*  rule: [lia] misbehaves as soon as an [mword] is in scope), so every    *)
(*  numeric step is a closed fact the Iris script applies by name.         *)
(* ===================================================================== *)

(* ---- [fd_frees], in the direction the SCAN produces it ----
   SpecFdalloc's lemmas read a `fd_frees` result; a scan instead ESTABLISHES
   one, from "descriptor [fd] is null and every earlier one is not".  These
   two are that converse, and they are the only place the spec's fixpoint is
   unfolded.  They stay in the proof file: no caller's statement mentions
   them. *)
Lemma fda_frees_from_found (fs : list (mword 64)) (i fd : nat) :
  fs !! fd = Some (zero_reg : mword 64) ->
  (forall j w, (j < fd)%nat -> fs !! j = Some w -> w <> (zero_reg : mword 64)) ->
  exists l, fd_frees_from i fs = (i + fd)%nat :: l.
Proof.
  revert i fd. induction fs as [|a fs' IH]; intros i fd Hfd Hpre; [by destruct fd|].
  destruct fd as [|fd'].
  - cbn in Hfd. injection Hfd as ->.
    cbn. case_decide as Hd; [| exfalso; apply Hd; reflexivity].
    rewrite Nat.add_0_r. by eexists.
  - assert (Ha : a <> (zero_reg : mword 64))
      by (apply (Hpre 0%nat a ltac:(lia)); reflexivity).
    cbn. case_decide as Hd; [contradiction|].
    destruct (IH (S i) fd' Hfd (fun j w Hj Hjw => Hpre (S j) w ltac:(lia) Hjw))
      as [l Hl].
    exists l. rewrite Hl. by rewrite Nat.add_succ_comm.
Qed.

Lemma fda_frees_found (fs : list (mword 64)) (fd : nat) :
  fs !! fd = Some (zero_reg : mword 64) ->
  (forall j w, (j < fd)%nat -> fs !! j = Some w -> w <> (zero_reg : mword 64)) ->
  exists l, fd_frees fs = fd :: l.
Proof.
  intros Hfd Hpre.
  destruct (fda_frees_from_found fs 0%nat fd Hfd Hpre) as [l Hl].
  exists l. by rewrite /fd_frees Hl.
Qed.

Lemma fda_frees_from_none (fs : list (mword 64)) (i : nat) :
  (forall j w, fs !! j = Some w -> w <> (zero_reg : mword 64)) ->
  fd_frees_from i fs = [].
Proof.
  revert i. induction fs as [|a fs' IH]; intros i Hall; [reflexivity|].
  assert (Ha : a <> (zero_reg : mword 64)) by (apply (Hall 0%nat); reflexivity).
  cbn. case_decide as Hd; [contradiction|].
  apply IH. intros j w Hjw. apply (Hall (S j) w). exact Hjw.
Qed.

Lemma fda_frees_none (fs : list (mword 64)) :
  (forall j w, fs !! j = Some w -> w <> (zero_reg : mword 64)) ->
  fd_frees fs = [].
Proof. intro Hall. by apply fda_frees_from_none. Qed.

(* the two zero displacements: [c.ld a4,0(a5)] and [c.sd s1,0(a2)] *)
Lemma fda_off0 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X.
Proof.
  replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  apply kv_addv_zero.
Qed.

(* [c.addiw a0,a0,1] : fd++ on an [int] counter that never leaves [0,16] *)
Lemma fda_addiw1 (fd : nat) : (fd < NOFILE)%nat ->
  sign_extend' 64 (subrange_vec_dec
    (add_vec (mword_of_int (Z.of_nat fd) : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (Z.of_nat (S fd)) : mword 64).
Proof.
  intro Hfd. unfold NOFILE in Hfd.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (Hz : (Z.of_nat fd < 16)%Z) by (apply Nat2Z.inj_lt in Hfd; lia).
  assert (Hz0 : (0 <= Z.of_nat fd)%Z) by apply Nat2Z.is_nonneg.
  replace (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64)
    with (mword_of_int 1 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  change (add_vec (mword_of_int (Z.of_nat fd) : mword 64) (mword_of_int 1))
    with (add_vec_int (mword_of_int (Z.of_nat fd) : mword 64) 1).
  rewrite avi_mword.
  rewrite <- trunc32_subrange. rewrite trunc32_mword_of_int.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat fd)) with (Z.of_nat fd + 1)%Z by lia.
  apply bv_eq.
  rewrite (sext64_moi32_unsigned (Z.of_nat fd + 1) ltac:(lia)).
  rewrite moi64_unsigned. symmetry. apply bvw64_small. lia.
Qed.

(* [bne a0,a3] : the exit test, as the index comparison the induction runs on *)
Lemma fda_neq16 (i : nat) : (i <= NOFILE)%nat ->
  neq_vec (mword_of_int (Z.of_nat i) : mword 64) (mword_of_int 16 : mword 64)
  = negb (Nat.eqb i NOFILE).
Proof.
  intro Hi. unfold NOFILE in Hi |- *.
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (Hz : (Z.of_nat i <= 16)%Z) by (apply Nat2Z.inj_le in Hi; lia).
  assert (Hz0 : (0 <= Z.of_nat i)%Z) by apply Nat2Z.is_nonneg.
  assert (Hui : bv_unsigned (mword_of_int (Z.of_nat i) : mword 64) = Z.of_nat i)
    by (rewrite moi64_unsigned; apply bvw64_small; lia).
  assert (Hu16 : bv_unsigned (mword_of_int 16 : mword 64) = 16)
    by (rewrite moi64_unsigned; apply bvw64_small; lia).
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec i 16) as [-> | Hne].
  - apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite Hui Hu16 in Hc. apply Hne. apply Nat2Z.inj. rewrite Hc. reflexivity.
Qed.

(* the install arm's [slli a5,a0,3] then [addi a5,a5,208], folded back into
   [ProcGeom.p_ofile] *)
Lemma fda_slli3 (fd : nat) : (fd < NOFILE)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat fd) : mword 64)
                  (subrange_vec_dec (mword_of_int 3 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (Z.of_nat fd * 8) : mword 64).
Proof.
  intro Hfd. unfold NOFILE in Hfd.
  assert (Hz : (Z.of_nat fd < 16)%Z) by (apply Nat2Z.inj_lt in Hfd; lia).
  apply ofile_slli3; [apply Nat2Z.is_nonneg | nia].
Qed.

Lemma fda_addi208 (pa : mword 64) (fd : nat) : (fd < NOFILE)%nat ->
  add_vec (mword_of_int (Z.of_nat fd * 8) : mword 64)
          (sign_extend' 64 (mword_of_int 208 : mword 12))
  = mword_of_int (208 + Z.of_nat fd * 8).
Proof.
  intro Hfd. unfold NOFILE in Hfd.
  assert (Hz : (Z.of_nat fd < 16)%Z) by (apply Nat2Z.inj_lt in Hfd; lia).
  assert (Hz0 : (0 <= Z.of_nat fd)%Z) by apply Nat2Z.is_nonneg.
  apply ofile_addi208; nia.
Qed.

(* fdalloc's balanced 32-byte frame: the entry [addi sp,-32] and the exit
   [addi16sp sp,32] cancel. *)
Lemma fda_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  apply bv_eq. rewrite !add_vec64_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
             = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
             = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* the numeric premise myproc takes; [lia] cannot evaluate the power, so it is
   [vm_compute]d once here rather than inline at the call site. *)
Lemma fda_n1 (n : nat) : (Z.of_nat n + 1 < 2 ^ 31)%Z -> (Z.of_nat n + 1 < 2 ^ 31)%Z.
Proof. exact id. Qed.

Module FdallocProof (Myproc : MYPROC) : FDALLOC.

Section ProofFdalloc.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{CID : CpuId}.

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* =================================================================== *)
  (*  The shared tail at +0x28: the epilogue, entered by BOTH arms.       *)
  (* =================================================================== *)
  Lemma fda_tail (γ : gname) (Φ : mval -> iProp Σ)
      (m Mt : regfile) (av : nat) (rv : mword 64)
      (sp0 ra0 s00 s10 gapv : mword 64) :
    (4 <= av)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr γ Mt (av - 4)%nat -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.fdalloc + 0x28) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) gapv -∗
    ( ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr γ mf av -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hav Hsp0 Hra0 Hs00 Hs10 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hcont".
    iPoseProof (fdi_28 with "Htext") as "Hi28".
    iPoseProof (fdi_2a with "Htext") as "Hi2a".
    iPoseProof (fdi_2c with "Htext") as "Hi2c".
    iPoseProof (fdi_2e with "Htext") as "Hi2e".
    iPoseProof (fdi_30 with "Htext") as "Hi30".
    (* ---- +0x28: c.ldsp ra,24(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KernelSyms.fdalloc + 0x28))
              (mword_of_int 3 : mword 6) Rra Mt (av - 4)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi28 Hb1 [-]").
    iIntros "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.fdalloc + 0x28) : mword 64) 2
                    = mword_of_int (KernelSyms.fdalloc + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x2a: c.ldsp s0,16(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KernelSyms.fdalloc + 0x2a))
              (mword_of_int 2 : mword 6) Rs0 T1 (av - 4)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a Hb2 [-]").
    iIntros "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.fdalloc + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.fdalloc + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x2c: c.ldsp s1,8(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HT2sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KernelSyms.fdalloc + 0x2c))
              (mword_of_int 1 : mword 6) Rs1 T2 (av - 4)%nat s10
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2c Hb3 [-]").
    iIntros "Hcg Hpc Hb3".
    iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    change (<[Regidx Rs1 := regval_into_reg s10]> T2) with T3.
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.fdalloc + 0x2c) : mword 64) 2
                    = mword_of_int (KernelSyms.fdalloc + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | reg_neq]).
    (* ---- +0x2e: c.addi16sp sp,32 (frame pop) ---- *)
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HT3sp.
      assert (Hs4 : pa_stk sp0 4
                    = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hs4. apply fda_frame_cancel. }
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv; exact HT3sp).
    iDestruct (stack_own_4_intro sp0 ra0 s00 s10 gapv with "Hb1 Hb2 Hb3 Hb4") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (fdi_2e with "Htext") as "Hi2e'".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (KernelSyms.fdalloc + 0x2e))
              (mword_of_int 2 : mword 6) T3 (av - 4)%nat 4 Hpop
              with "Hcg Hpc Hi2e' Hframe [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.fdalloc + 0x2e) : mword 64) 2
                    = mword_of_int (KernelSyms.fdalloc + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (T3 !!! Regidx csp_rs1)
              (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3) with T4.
    (* ---- +0x30: c.ret ---- *)
    assert (HT4ra : T4 !!! Regidx Rra = ra0).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (KernelSyms.fdalloc + 0x30))
              Rra T4 av ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi30 [-]").
    iIntros "Hcg Hpc".
    iEval (rewrite HT4ra) in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT4sp : T4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
      by (rewrite /T4 upd_eq Hwv; symmetry; exact Hsp0).
    assert (HT4s0 : T4 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_eq. symmetry; exact Hs00. }
    assert (HT4s1 : T4 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_eq. symmetry; exact Hs10. }
    assert (HT4a0 : T4 !!! Regidx Ra0 = rv).
    { rewrite /T4 upd_ne; [| reg_neq].
      rewrite /T3 upd_ne; [| reg_neq].
      rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (HT4thr : forall r : mword 5, is_cs_idx r = true ->
                       r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                       T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /T4 upd_ne; [| congruence].
      rewrite /T3 upd_ne; [| congruence].
      rewrite /T2 upd_ne; [| congruence].
      rewrite /T1 upd_ne; [| congruence]. apply Hthr; assumption. }
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    split; [| exact HT4a0].
    unfold callee_saved.
    split; [exact HT4sp|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [exact HT4s0|].
    split; [exact HT4s1|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    split; [apply HT4thr; vm_compute; first [reflexivity | discriminate]|].
    apply HT4thr; vm_compute; first [reflexivity | discriminate].
  Qed.

  (* =================================================================== *)
  (*  The whole function.                                                 *)
  (* =================================================================== *)
  Lemma wp_fdalloc_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γf : gname) (k : nat) (q : Qp) (Cf : fcontent)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate)
    : wp_fdalloc_sconf_body γ Φ γf k q Cf m av n eb p C pid V.
  Proof.
    cbv beta delta [wp_fdalloc_sconf_body].
    intros pcE ret_tgt Htp Ha0 Hk Hn Hav.
    unfold fdalloc_stack in Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Hpv Href Hcont".
    iDestruct (proc_priv_ofile_len with "Hpv") as "%Hlen".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (fdi_00 with "Htext") as "Hi00".
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE (mword_of_int 32 : mword 6) m av 4 ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FDA + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
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
    iPoseProof (fdi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FDA + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (av - 4)%nat vr24 with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros "Hcg Hpc Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (FDA + 0x02) : mword 64) 2 = mword_of_int (FDA + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (fdi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FDA + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (av - 4)%nat vr16 with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros "Hcg Hpc Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (FDA + 0x04) : mword 64) 2 = mword_of_int (FDA + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    iPoseProof (fdi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (FDA + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (av - 4)%nat vr8 with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros "Hcg Hpc Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (FDA + 0x06) : mword 64) 2 = mword_of_int (FDA + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    assert (HraA0 : A0 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs0A0 : A0 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (Hs1A0 : A0 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HcspA0 HraA0) in "Hr24".
    iEval (rewrite HcspA0 Hs0A0) in "Hr16".
    iEval (rewrite HcspA0 Hs1A0) in "Hr8".
    iEval (rewrite -Hb1) in "Hr24".
    iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (fdi_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (FDA + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) Rs0
              A0 (av - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (FDA + 0x08) : mword 64) 2 = mword_of_int (FDA + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* +0x0a: c.mv s1,a0 -- park [f] in a callee-saved register *)
    iPoseProof (fdi_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (FDA + 0x0a)) Rs1 Ra0
              A1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1).
    change (<[Regidx Rs1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra0))]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (FDA + 0x0a) : mword 64) 2 = mword_of_int (FDA + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx Rs1 = fnode k).
    { rewrite /A2 upd_eq. rewrite add_vec_zero_l.
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Ha0. }
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq]. exact HcspA0. }
    (* +0x0c: jal ra,myproc *)
    iPoseProof (fdi_0c with "Htext") as "Hi0c".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (FDA + 0x0c)) Rra (mword_of_int 2084506 : mword 21)
              A2 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (FDA + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (FDA + 0x0c) : mword 64) 4)]> A2) with A3.
    assert (Hjmp : add_vec (mword_of_int (FDA + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2084506 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA3ra : A3 !!! Regidx Rra = add_vec_int (mword_of_int (FDA + 0x0c) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3tp : A3 !!! Regidx Rtp = cid_word).
    { rewrite /A3 upd_ne; [| reg_neq].
      rewrite /A2 upd_ne; [| reg_neq].
      rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. exact Htp. }
    assert (HA3s1 : A3 !!! Regidx Rs1 = fnode k)
      by (rewrite /A3 upd_ne; [exact HA2s1 | reg_neq]).
    assert (HA3sp : A3 !!! Regidx csp_rs1 = spd)
      by (rewrite /A3 upd_ne; [exact HA2sp | reg_neq]).
    assert (HA3cs : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                      A3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    (* ===================== myproc() ===================== *)
    iApply (Myproc.wp_myproc_sconf γ Φ A3 (av - 4)%nat n eb p C
              HA3tp Hn ltac:(lia)
              with "Hcg Hcpu Htext Hpc [-]").
    iIntros (ms MP) "%Hms Hcg Hcpu Hpc %HcsMP".
    destruct HcsMP as [HcsMP HMPa0].
    assert (Hpc10 : ret_pc (A3 !!! Regidx Rra) = mword_of_int (FDA + 0x10))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    assert (HMPsp : MP !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite (callee_saved_lookup HcsMP csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite Hspd4. exact HA3sp. }
    assert (HMPs1 : MP !!! Regidx Rs1 = fnode k)
      by (rewrite (callee_saved_lookup HcsMP Rs1 ltac:(vm_compute; reflexivity)); exact HA3s1).
    assert (HMPcs : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                      MP !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      rewrite (callee_saved_lookup HcsMP r Hr). apply HA3cs; assumption. }
    (* +0x10: c.mv a2,a0 -- a2 := p, and it stays there across the loop *)
    iPoseProof (fdi_10 with "Htext") as "Hi10".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (FDA + 0x10)) Ra2 Ra0
              MP (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (MP !!! Regidx Ra0))]> MP).
    change (<[Regidx Ra2 := regval_into_reg (add_vec zero_reg (MP !!! Regidx Ra0))]> MP) with B1.
    assert (Hpc12 : add_vec_int (mword_of_int (FDA + 0x10) : mword 64) 2 = mword_of_int (FDA + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    assert (HB1a2 : B1 !!! Regidx Ra2 = p)
      by (rewrite /B1 upd_eq add_vec_zero_l; exact HMPa0).
    assert (HB1a0 : B1 !!! Regidx Ra0 = p)
      by (rewrite /B1 upd_ne; [exact HMPa0 | reg_neq]).
    (* +0x12: addi a5,a0,208 -- a5 := &p->ofile[0] *)
    iPoseProof (fdi_12 with "Htext") as "Hi12".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (FDA + 0x12)) Ra5 Ra0 (mword_of_int 208 : mword 12)
              B1 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
        (add_vec (B1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> B1).
    change (<[Regidx Ra5 := regval_into_reg
        (add_vec (B1 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> B1) with B2.
    assert (Hpc16 : add_vec_int (mword_of_int (FDA + 0x12) : mword 64) 4 = mword_of_int (FDA + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HB2a5 : B2 !!! Regidx Ra5 = p_ofile p 0%nat)
      by (rewrite /B2 upd_eq HB1a0; apply p_ofile_zero).
    (* +0x16: c.li a0,0 -- fd := 0 *)
    iPoseProof (fdi_16 with "Htext") as "Hi16".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (FDA + 0x16)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0%nat) : mword 64) B2 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi16 [-]").
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0%nat) : mword 64)]> B2).
    change (<[Regidx Ra0 := regval_into_reg (mword_of_int (Z.of_nat 0%nat) : mword 64)]> B2) with B3.
    assert (Hpc18 : add_vec_int (mword_of_int (FDA + 0x16) : mword 64) 2 = mword_of_int (FDA + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    (* +0x18: c.li a3,16 -- the loop bound *)
    iPoseProof (fdi_18 with "Htext") as "Hi18".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (FDA + 0x18)) Ra3 (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) B3 (av - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx Ra3 := regval_into_reg (mword_of_int 16 : mword 64)]> B3).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int 16 : mword 64)]> B3) with B4.
    assert (Hpc1a : add_vec_int (mword_of_int (FDA + 0x18) : mword 64) 2 = mword_of_int (FDA + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1a) in "Hpc".
    (* the register facts the loop is entered with *)
    assert (HB4a3 : B4 !!! Regidx Ra3 = (mword_of_int 16 : mword 64))
      by (rewrite /B4 upd_eq; reflexivity).
    assert (HB4a0 : B4 !!! Regidx Ra0 = mword_of_int (Z.of_nat 0%nat))
      by (rewrite /B4 upd_ne; [rewrite /B3 upd_eq; reflexivity | reg_neq]).
    assert (HB4a2 : B4 !!! Regidx Ra2 = p).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [exact HB1a2 | reg_neq]. }
    assert (HB4a5 : B4 !!! Regidx Ra5 = p_ofile p 0%nat).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq]. exact HB2a5. }
    assert (HB4s1 : B4 !!! Regidx Rs1 = fnode k).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [exact HMPs1 | reg_neq]. }
    assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_ne; [| reg_neq].
      rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [exact HMPsp | reg_neq]. }
    assert (HB4cs : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                      B4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      pose proof (is_cs_idx_true_neq Ra0 r ltac:(vm_compute; reflexivity) Hr) as Na0.
      pose proof (is_cs_idx_true_neq Ra2 r ltac:(vm_compute; reflexivity) Hr) as Na2.
      pose proof (is_cs_idx_true_neq Ra3 r ltac:(vm_compute; reflexivity) Hr) as Na3.
      pose proof (is_cs_idx_true_neq Ra5 r ltac:(vm_compute; reflexivity) Hr) as Na5.
      rewrite /B4 upd_ne; [| congruence]. rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence]. rewrite /B1 upd_ne; [| congruence].
      apply HMPcs; assumption. }
    (* ================================================================= *)
    (* THE LOOP.  Fuel induction on the descriptors left to scan.         *)
    (* ================================================================= *)
    iAssert (∀ (fuel fd : nat) (M : regfile),
      ⌜(NOFILE - fd <= fuel)%nat⌝ -∗
      ⌜(fd < NOFILE)%nat⌝ -∗
      ⌜(forall j w, (j < fd)%nat -> pv_ofile V !! j = Some w -> w <> (zero_reg : mword 64))⌝ -∗
      ⌜ M !!! Regidx Ra0 = mword_of_int (Z.of_nat fd)
        /\ M !!! Regidx Ra2 = p
        /\ M !!! Regidx Ra3 = (mword_of_int 16 : mword 64)
        /\ M !!! Regidx Ra5 = p_ofile p fd
        /\ M !!! Regidx Rs1 = fnode k
        /\ M !!! Regidx csp_rs1 = pa_stk sp0 4
        /\ (forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
              M !!! Regidx r = m !!! Regidx r) ⌝ -∗
      sie_cap_gpr γ M (av - 4)%nat -∗
      cpu_own γ n eb p C -∗
      pc_is (mword_of_int (FDA + 0x1a) : mword 64) -∗
      proc_priv γf p pid V -∗
      file_ref γf k q Cf -∗
      (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
      (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
      (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
      (pa_stk sp0 4) ↦₈ (vgap : mword 64) -∗
      ( ∀ mf : regfile,
          ⌜callee_saved m mf⌝ -∗
          sie_cap_gpr γ mf av -∗
          cpu_own γ n eb p C -∗
          pc_is ret_tgt -∗
          fdalloc_post γf p pid V k q Cf (mf !!! Regidx Ra0) -∗
          WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (fd M) "%Hfuel %Hfd %Hpre %Hinv Hcg Hcpu Hpc Hpv Href Hc1 Hc2 Hc3 Hc4 Hcont".
        exfalso. unfold NOFILE in Hfd, Hfuel. lia. }
      iIntros (fd M) "%Hfuel %Hfd %Hpre %Hinv Hcg Hcpu Hpc Hpv Href Hc1 Hc2 Hc3 Hc4 Hcont".
      destruct Hinv as (HMa0 & HMa2 & HMa3 & HMa5 & HMs1 & HMsp & HMcs).
      (* the descriptor this iteration reads *)
      assert (Hlk : exists w, pv_ofile V !! fd = Some w).
      { apply lookup_lt_is_Some. rewrite Hlen. exact Hfd. }
      destruct Hlk as [w Hw].
      iPoseProof (fdi_1a with "Htext") as "Hi1a".
      iPoseProof (fdi_1c with "Htext") as "Hi1c".
      iPoseProof (fdi_1e with "Htext") as "Hi1e".
      iPoseProof (fdi_20 with "Htext") as "Hi20".
      iPoseProof (fdi_22 with "Htext") as "Hi22".
      (* ---- +0x1a: c.ld a4,0(a5) -- a4 := p->ofile[fd] ---- *)
      iDestruct (proc_priv_ofile_read _ _ _ _ fd w Hw with "Hpv") as "[Hcell Hpvback]".
      assert (Haddr : add_vec (M !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                      = p_ofile p fd) by (rewrite HMa5; apply fda_off0).
      iApply (wp_cld_s_sconf γ Φ (mword_of_int (FDA + 0x1a)) Ra4 Ra5 (mword_of_int 0 : mword 12)
                M (av - 4)%nat w (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi1a [Hcell] [-]").
      { iEval (rewrite Haddr). iExact "Hcell". }
      iIntros "Hcg Hpc Hcell".
      iEval (rewrite Haddr) in "Hcell".
      iDestruct ("Hpvback" with "Hcell") as "Hpv".
      set (L1 := <[Regidx Ra4 := regval_into_reg w]> M).
      change (<[Regidx Ra4 := regval_into_reg w]> M) with L1.
      assert (Hpc1c : add_vec_int (mword_of_int (FDA + 0x1a) : mword 64) 2 = mword_of_int (FDA + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1c) in "Hpc".
      assert (HL1a4 : L1 !!! Regidx Ra4 = w) by (rewrite /L1 upd_eq; reflexivity).
      assert (HL1a0 : L1 !!! Regidx Ra0 = mword_of_int (Z.of_nat fd))
        by (rewrite /L1 upd_ne; [exact HMa0 | reg_neq]).
      assert (HL1a2 : L1 !!! Regidx Ra2 = p)
        by (rewrite /L1 upd_ne; [exact HMa2 | reg_neq]).
      assert (HL1a3 : L1 !!! Regidx Ra3 = (mword_of_int 16 : mword 64))
        by (rewrite /L1 upd_ne; [exact HMa3 | reg_neq]).
      assert (HL1a5 : L1 !!! Regidx Ra5 = p_ofile p fd)
        by (rewrite /L1 upd_ne; [exact HMa5 | reg_neq]).
      assert (HL1s1 : L1 !!! Regidx Rs1 = fnode k)
        by (rewrite /L1 upd_ne; [exact HMs1 | reg_neq]).
      assert (HL1sp : L1 !!! Regidx csp_rs1 = pa_stk sp0 4)
        by (rewrite /L1 upd_ne; [exact HMsp | reg_neq]).
      assert (HL1cs : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                        L1 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9.
        pose proof (is_cs_idx_true_neq Ra4 r ltac:(vm_compute; reflexivity) Hr) as Na4.
        rewrite /L1 upd_ne; [| congruence]. apply HMcs; assumption. }
      (* ---- +0x1c: c.beqz a4 -- the free-slot test ---- *)
      destruct (decide (w = (zero_reg : mword 64))) as [Hwz | Hwnz].
      - (* ============ FOUND: install [f] at descriptor [fd] ============ *)
        iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (FDA + 0x1c))
                  (mword_of_int 11 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  L1 (av - 4)%nat
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HL1a4 Hwz; apply eq_vec_true_iff; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi1c [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Htgt32 : add_vec (mword_of_int (FDA + 0x1c) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0"))))
                         = mword_of_int (FDA + 0x32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt32) in "Hpc".
        iPoseProof (fdi_32 with "Htext") as "Hi32".
        iPoseProof (fdi_36 with "Htext") as "Hi36".
        iPoseProof (fdi_3a with "Htext") as "Hi3a".
        iPoseProof (fdi_3c with "Htext") as "Hi3c".
        iPoseProof (fdi_3e with "Htext") as "Hi3e".
        (* +0x32: slli a5,a0,3 *)
        iApply (wp_slli_s_sconf γ Φ (mword_of_int (FDA + 0x32)) Ra5 Ra0
                  (mword_of_int 3 : mword 6) (mword_of_int (Z.of_nat fd * 8) : mword 64)
                  L1 (av - 4)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HL1a0; exact (fda_slli3 fd Hfd))
                  with "Hcg Hpc Hi32 [-]").
        iIntros "Hcg Hpc".
        set (G1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (Z.of_nat fd * 8) : mword 64)]> L1).
        change (<[Regidx Ra5 := regval_into_reg (mword_of_int (Z.of_nat fd * 8) : mword 64)]> L1) with G1.
        assert (Hpc36 : add_vec_int (mword_of_int (FDA + 0x32) : mword 64) 4 = mword_of_int (FDA + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc36) in "Hpc".
        assert (HG1a5 : G1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat fd * 8) : mword 64))
          by (rewrite /G1 upd_eq; reflexivity).
        (* +0x36: addi a5,a5,208 *)
        iApply (wp_addi4_s_sconf γ Φ (mword_of_int (FDA + 0x36)) Ra5 Ra5 (mword_of_int 208 : mword 12)
                  G1 (av - 4)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi36 [-]").
        iIntros "Hcg Hpc".
        set (G2 := <[Regidx Ra5 := regval_into_reg
            (add_vec (G1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> G1).
        change (<[Regidx Ra5 := regval_into_reg
            (add_vec (G1 !!! Regidx Ra5) (sign_extend' 64 (mword_of_int 208 : mword 12)))]> G1) with G2.
        assert (Hpc3a : add_vec_int (mword_of_int (FDA + 0x36) : mword 64) 4 = mword_of_int (FDA + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc3a) in "Hpc".
        assert (HG2a5 : G2 !!! Regidx Ra5 = (mword_of_int (208 + Z.of_nat fd * 8) : mword 64)).
        { rewrite /G2 upd_eq HG1a5. exact (fda_addi208 p fd Hfd). }
        assert (HG2a2 : G2 !!! Regidx Ra2 = p).
        { rewrite /G2 upd_ne; [| reg_neq]. rewrite /G1 upd_ne; [exact HL1a2 | reg_neq]. }
        (* +0x3a: c.add a2,a2,a5 -- a2 := &p->ofile[fd] *)
        iApply (wp_cadd_s_sconf γ Φ (mword_of_int (FDA + 0x3a)) Ra2 Ra5
                  G2 (av - 4)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi3a [-]").
        iIntros "Hcg Hpc".
        set (G3 := <[Regidx Ra2 := regval_into_reg
            (add_vec (G2 !!! Regidx Ra2) (G2 !!! Regidx Ra5))]> G2).
        change (<[Regidx Ra2 := regval_into_reg
            (add_vec (G2 !!! Regidx Ra2) (G2 !!! Regidx Ra5))]> G2) with G3.
        assert (Hpc3c : add_vec_int (mword_of_int (FDA + 0x3a) : mword 64) 2 = mword_of_int (FDA + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc3c) in "Hpc".
        assert (HG3a2 : G3 !!! Regidx Ra2 = p_ofile p fd).
        { rewrite /G3 upd_eq HG2a2 HG2a5. apply p_ofile_shift_form. }
        assert (HG3s1 : G3 !!! Regidx Rs1 = fnode k).
        { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
          rewrite /G1 upd_ne; [exact HL1s1 | reg_neq]. }
        (* +0x3c: c.sd s1,0(a2) -- p->ofile[fd] = f *)
        rewrite Hwz in Hw.
        iDestruct (proc_priv_ofile _ _ _ _ fd (zero_reg : mword 64) Hw with "Hpv")
          as "[Hslot Hpvback]".
        iDestruct (ofile_slot_null with "Hslot") as "[Hcell Hfdslot]".
        assert (Haddr3c : add_vec (G3 !!! Regidx Ra2) (sign_extend' 64 (mword_of_int 0 : mword 12))
                          = p_ofile p fd) by (rewrite HG3a2; apply fda_off0).
        iApply (wp_csd_s_sconf γ Φ (mword_of_int (FDA + 0x3c)) Rs1 Ra2 (mword_of_int 0 : mword 12)
                  G3 (av - 4)%nat (zero_reg : mword 64)
                  with "Hcg Hpc Hi3c [Hcell] [-]").
        { iEval (rewrite Haddr3c). iExact "Hcell". }
        iIntros "Hcg Hpc Hcell".
        iEval (rewrite Haddr3c HG3s1) in "Hcell".
        iDestruct (ofile_slot_file _ _ _ k q Cf Hk with "Hcell Href") as "Hslot".
        iDestruct ("Hpvback" $! (fnode k) with "Hslot") as "Hpv".
        assert (Hpc3e : add_vec_int (mword_of_int (FDA + 0x3c) : mword 64) 2 = mword_of_int (FDA + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc3e) in "Hpc".
        (* +0x3e: c.j -> the epilogue, with fd still in a0 *)
        iApply (wp_cj_s_sconf γ Φ (mword_of_int (FDA + 0x3e))
                  (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")))
                  G3 (av - 4)%nat ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3e [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Htgt28 : add_vec (mword_of_int (FDA + 0x3e) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0"))))
                         = mword_of_int (KernelSyms.fdalloc + 0x28))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt28) in "Hpc".
        (* the epilogue *)
        assert (HG3a0 : G3 !!! Regidx Ra0 = mword_of_int (Z.of_nat fd)).
        { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
          rewrite /G1 upd_ne; [exact HL1a0 | reg_neq]. }
        assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /G3 upd_ne; [| reg_neq]. rewrite /G2 upd_ne; [| reg_neq].
          rewrite /G1 upd_ne; [exact HL1sp | reg_neq]. }
        assert (HG3cs : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                          G3 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9.
          pose proof (is_cs_idx_true_neq Ra2 r ltac:(vm_compute; reflexivity) Hr) as Na2.
          pose proof (is_cs_idx_true_neq Ra5 r ltac:(vm_compute; reflexivity) Hr) as Na5.
          rewrite /G3 upd_ne; [| congruence]. rewrite /G2 upd_ne; [| congruence].
          rewrite /G1 upd_ne; [| congruence]. apply HL1cs; assumption. }
        iApply (fda_tail γ Φ m G3 av (mword_of_int (Z.of_nat fd)) sp0
                  (m !!! Regidx Rra) (m !!! Regidx Rs0) (m !!! Regidx Rs1) vgap
                  ltac:(lia) eq_refl eq_refl eq_refl eq_refl HG3sp HG3a0 HG3cs
                  with "Hcg Htext Hpc Hc1 Hc2 Hc3 Hc4 [-]").
        iIntros (mf) "[%Hcsf %Hfa0] Hcg Hpc".
        destruct (fda_frees_found _ fd Hw Hpre) as [l Hfrees].
        iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc [Hpv Hfdslot]"); [exact Hcsf|].
        rewrite /fdalloc_post. iRight. iExists fd, l.
        iSplitR; [iPureIntro; split; [exact Hfa0 | exact Hfrees]|].
        iFrame "Hpv Hfdslot".
      - (* ============ BUSY: advance, and either loop or give up ======== *)
        iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (FDA + 0x1c))
                  (mword_of_int 11 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                  L1 (av - 4)%nat
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HL1a4; apply eq_vec_false_iff; exact Hwnz)
                  with "Hcg Hpc Hi1c [-]").
        iIntros "Hcg Hpc".
        assert (Hpc1e : add_vec_int (mword_of_int (FDA + 0x1c) : mword 64) 2 = mword_of_int (FDA + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc1e) in "Hpc".
        (* +0x1e: c.addiw a0,a0,1 *)
        iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (FDA + 0x1e)) Ra0 (mword_of_int 1 : mword 6)
                  L1 (av - 4)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi1e [-]").
        iIntros "Hcg Hpc".
        set (N1 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
            (add_vec (L1 !!! Regidx Ra0) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> L1).
        change (<[Regidx Ra0 := regval_into_reg (sign_extend' 64 (subrange_vec_dec
            (add_vec (L1 !!! Regidx Ra0) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> L1) with N1.
        assert (Hpc20 : add_vec_int (mword_of_int (FDA + 0x1e) : mword 64) 2 = mword_of_int (FDA + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc20) in "Hpc".
        assert (HN1a0 : N1 !!! Regidx Ra0 = mword_of_int (Z.of_nat (S fd))).
        { rewrite /N1 upd_eq HL1a0. exact (fda_addiw1 fd Hfd). }
        assert (HN1a5 : N1 !!! Regidx Ra5 = p_ofile p fd)
          by (rewrite /N1 upd_ne; [exact HL1a5 | reg_neq]).
        (* +0x20: c.addi a5,a5,8 *)
        iApply (wp_caddi_s_sconf γ Φ (mword_of_int (FDA + 0x20)) Ra5 (mword_of_int 8 : mword 6)
                  N1 (av - 4)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi20 [-]").
        iIntros "Hcg Hpc".
        set (N2 := <[Regidx Ra5 := regval_into_reg
            (add_vec (N1 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> N1).
        change (<[Regidx Ra5 := regval_into_reg
            (add_vec (N1 !!! Regidx Ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> N1) with N2.
        assert (Hpc22 : add_vec_int (mword_of_int (FDA + 0x20) : mword 64) 2 = mword_of_int (FDA + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc22) in "Hpc".
        assert (HN2a5 : N2 !!! Regidx Ra5 = p_ofile p (S fd))
          by (rewrite /N2 upd_eq HN1a5; apply p_ofile_succ).
        assert (HN2a0 : N2 !!! Regidx Ra0 = mword_of_int (Z.of_nat (S fd)))
          by (rewrite /N2 upd_ne; [exact HN1a0 | reg_neq]).
        assert (HN2a2 : N2 !!! Regidx Ra2 = p).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact HL1a2 | reg_neq]. }
        assert (HN2a3 : N2 !!! Regidx Ra3 = (mword_of_int 16 : mword 64)).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact HL1a3 | reg_neq]. }
        assert (HN2s1 : N2 !!! Regidx Rs1 = fnode k).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact HL1s1 | reg_neq]. }
        assert (HN2sp : N2 !!! Regidx csp_rs1 = pa_stk sp0 4).
        { rewrite /N2 upd_ne; [| reg_neq]. rewrite /N1 upd_ne; [exact HL1sp | reg_neq]. }
        assert (HN2cs : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                          N2 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9.
          pose proof (is_cs_idx_true_neq Ra0 r ltac:(vm_compute; reflexivity) Hr) as Na0.
          pose proof (is_cs_idx_true_neq Ra5 r ltac:(vm_compute; reflexivity) Hr) as Na5.
          rewrite /N2 upd_ne; [| congruence]. rewrite /N1 upd_ne; [| congruence].
          apply HL1cs; assumption. }
        (* the extended "every earlier descriptor is busy" fact *)
        assert (Hpre' : forall j v, (j < S fd)%nat -> pv_ofile V !! j = Some v ->
                          v <> (zero_reg : mword 64)).
        { intros j v Hj Hjv.
          destruct (decide (j = fd)) as [-> | Hne].
          - rewrite Hw in Hjv. injection Hjv as <-. exact Hwnz.
          - apply (Hpre j v ltac:(lia) Hjv). }
        (* ---- +0x22: bne a0,a3 -- the loop's exit test ---- *)
        assert (Hcmp : neq_vec (N2 !!! Regidx Ra0) (N2 !!! Regidx Ra3)
                       = negb (Nat.eqb (S fd) NOFILE)).
        { rewrite HN2a0 HN2a3. apply fda_neq16. unfold NOFILE in Hfd |- *. lia. }
        destruct (decide (S fd = NOFILE)) as [Hend | Hne].
        + (* the array is full: fall through to [c.li a0,-1] *)
          assert (Hfall : neq_vec (N2 !!! Regidx Ra0) (N2 !!! Regidx Ra3) = false).
          { rewrite Hcmp. rewrite (proj2 (Nat.eqb_eq (S fd) NOFILE) Hend). reflexivity. }
          iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (FDA + 0x22)) (mword_of_int 8184 : mword 13) Ra3 Ra0
                    N2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hfall with "Hcg Hpc Hi22 [-]").
          iIntros "Hcg Hpc".
          assert (Hpc26 : add_vec_int (mword_of_int (FDA + 0x22) : mword 64) 4 = mword_of_int (FDA + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc26) in "Hpc".
          (* +0x26: c.li a0,-1 *)
          iPoseProof (fdi_26 with "Htext") as "Hi26".
          iApply (wp_cli_s_sconf γ Φ (mword_of_int (FDA + 0x26)) Ra0 (mword_of_int 63 : mword 6)
                    (mword_of_int (-1) : mword 64) N2 (av - 4)%nat
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc Hi26 [-]").
          iIntros "Hcg Hpc".
          set (F1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> N2).
          change (<[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> N2) with F1.
          assert (Hpc28 : add_vec_int (mword_of_int (FDA + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.fdalloc + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc28) in "Hpc".
          assert (HF1a0 : F1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
            by (rewrite /F1 upd_eq; reflexivity).
          assert (HF1sp : F1 !!! Regidx csp_rs1 = pa_stk sp0 4)
            by (rewrite /F1 upd_ne; [exact HN2sp | reg_neq]).
          assert (HF1cs : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> Rs0 -> r <> Rs1 ->
                            F1 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9.
            pose proof (is_cs_idx_true_neq Ra0 r ltac:(vm_compute; reflexivity) Hr) as Na0.
            rewrite /F1 upd_ne; [| congruence]. apply HN2cs; assumption. }
          iApply (fda_tail γ Φ m F1 av (mword_of_int (-1)) sp0
                    (m !!! Regidx Rra) (m !!! Regidx Rs0) (m !!! Regidx Rs1) vgap
                    ltac:(lia) eq_refl eq_refl eq_refl eq_refl HF1sp HF1a0 HF1cs
                    with "Hcg Htext Hpc Hc1 Hc2 Hc3 Hc4 [-]").
          iIntros (mf) "[%Hcsf %Hfa0] Hcg Hpc".
          iApply ("Hcont" $! mf with "[%] Hcg Hcpu Hpc [Hpv Href]"); [exact Hcsf|].
          rewrite /fdalloc_post. iLeft.
          iSplitR; [| iFrame "Hpv Href"].
          iPureIntro. split; [exact Hfa0|].
          apply fda_frees_none. intros j v Hjv.
          apply (Hpre' j v ltac:(unfold NOFILE in Hend |- *;
                                 pose proof (lookup_lt_Some _ _ _ Hjv);
                                 rewrite Hlen in H; unfold NOFILE in H; lia) Hjv).
        + (* more descriptors: the back edge to +0x1a at fd := S fd *)
          assert (Htaken : neq_vec (N2 !!! Regidx Ra0) (N2 !!! Regidx Ra3) = true).
          { rewrite Hcmp. rewrite (proj2 (Nat.eqb_neq (S fd) NOFILE) Hne). reflexivity. }
          assert (Htgt1a : add_vec (mword_of_int (FDA + 0x22) : mword 64)
                             (sign_extend' 64 (mword_of_int 8184 : mword 13))
                           = mword_of_int (FDA + 0x1a))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_bne_taken_s_sconf γ Φ (mword_of_int (FDA + 0x22)) (mword_of_int 8184 : mword 13) Ra3 Ra0
                    N2 (av - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Htaken ltac:(rewrite Htgt1a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi22 [-]").
          iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt1a) in "Hpc".
          iApply ("IHf" $! (S fd) N2 with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpv Href Hc1 Hc2 Hc3 Hc4 Hcont").
          * unfold NOFILE in Hfuel |- *. lia.
          * unfold NOFILE in Hfd, Hne |- *. lia.
          * exact Hpre'.
          * split; [exact HN2a0|]. split; [exact HN2a2|]. split; [exact HN2a3|].
            split; [exact HN2a5|]. split; [exact HN2s1|]. split; [exact HN2sp|].
            exact HN2cs. }
    (* enter the loop at descriptor 0 with NOFILE units of fuel *)
    iApply ("Hloop" $! NOFILE 0%nat B4 with "[%] [%] [%] [%] Hcg Hcpu Hpc Hpv Href Hr24 Hr16 Hr8 Hgap Hcont").
    - lia.
    - unfold NOFILE; lia.
    - intros j w Hj. exfalso. lia.
    - split; [exact HB4a0|]. split; [exact HB4a2|]. split; [exact HB4a3|].
      split; [exact HB4a5|]. split; [exact HB4s1|]. split; [exact HB4sp|].
      exact HB4cs.
  Qed.

End ProofFdalloc.

End FdallocProof.
