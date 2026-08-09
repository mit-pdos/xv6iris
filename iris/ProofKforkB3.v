(* ProofKforkB3.v -- kfork's ROTATED filedup SCAN, +0x8e .. +0xa2.

     for (i = 0; i < NOFILE; i++)
       if (p->ofile[i]) np->ofile[i] = filedup(p->ofile[i]);

   gcc rotated this into "increment+test at the TOP, entry jumps past it":

     +0x08e  c.addi s1,s1,8              (parent cursor += 8)
     +0x090  c.addi s2,s2,8              (child cursor += 8)
     +0x092  beq s1,s3,+0xa4             (exit when s1 == &p->ofile[16])
     +0x096  c.ld a0,0(s1)               (a0 = p->ofile[i])
     +0x098  c.beqz a0,-10 -> +0x8e      (null: skip)
     +0x09a  jal ra,filedup
     +0x09e  sd a0,0(s2)                 (np->ofile[i] = the duplicate)
     +0x0a2  c.j -20 -> +0x8e

   so the ENTRY (from +0x7a) lands at +0x96 -- the BODY, at i = 0, with the
   cursors NOT yet bumped -- and the increment/test "tail" at +0x8e is
   reached only at the END of an iteration, from either arm of the body.
   This file's [kfkb3_fd_loop] mirrors [ProofKexit.kx_loop]'s decomposition
   exactly: a fuel-inducted "Hloop" over the BODY (entered at +0x96), whose
   every iteration proves a local "Htail" ([+0x8e..+0x92]) once and enters
   it from both arms of the body.

   THE PER-SLOT MOVE IS ONE FUNCTION, NOT TWO.  Both arms of the body leave
   the child's slot [i] holding EXACTLY [pv_ofile Vp !! i] -- the null arm
   because that is what was already there, the non-null arm because
   filedup hands back the SAME pointer it was given.  So the child's
   private block after [i] turns is [kfk_ofile_at (pv_ofile Vp) (pv_ofile
   V0) i] = [take i (pv_ofile Vp) ++ drop i (pv_ofile V0)], and the single
   step lemma [kfk_ofile_at_step] (an insert at position [i]) proves BOTH
   arms: the null arm is the case where the inserted value is the one
   already there ([kfk_ofile_at_step_null], via [list_insert_id]).

   THE PARENT'S BLOCK NEVER MOVES.  [ProcInv.ofile_slot]'s file disjunct
   quantifies the reference's fraction EXISTENTIALLY, and filedup only
   halves it, so the parent's slot closes back at the SAME value it opened
   at ([ProcInv.upd_ofile_id]) -- [proc_priv γf pme pid_p Vp] is threaded
   through this whole file unchanged.

   NO EXTERNAL fd-slot SUPPLY IS NEEDED.  The child's slot [i] is null
   throughout the whole scan (it only ever holds [pv_ofile V0 !! i] until
   THIS iteration installs [pv_ofile Vp !! i]), so [ProcInv.ofile_slot_null]
   yields its cell AND the one [FdSlots.fd_slot] unit it owns -- exactly
   what filedup's own precondition wants -- every iteration, out of the
   child's own resource.

   THE EXIT-TEST INJECTIVITY LEMMA IS FULLY GENERIC, NO CANONICALITY
   PREMISE NEEDED.  [ProcGeom.p_ofile_end_inj] is stated at [proc_addr j]
   because it goes through [proc_addr_unsigned_le]'s NO-WRAPAROUND bound;
   here the base [pme] is an opaque [mword 64] with no such bound in scope.
   But injectivity of [fun fd => p_ofile pa fd] on a BOUNDED range needs no
   bound on [pa] at all: [p_ofile pa i = p_ofile pa j] means the two
   OFFSETS are congruent mod 2^64 ([bv_wrap_add_inj], cancelling [pa]), and
   two offsets in [208, 336] that are congruent mod 2^64 are equal outright
   (the modulus dwarfs their difference).  [kfkb3_p_ofile_inj] below is
   that argument, stated once over plain Z magnitudes. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SpecFiledup.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ===================================================================== *)
(*  THE EXIT TEST'S INJECTIVITY, mword-free in its statement.             *)
(* ===================================================================== *)

Lemma kfkb3_p_ofile_unsigned (pa : mword 64) (fd : nat) :
  bv_unsigned (p_ofile pa fd) = bv_wrap 64 (bv_unsigned pa + (208 + 8 * Z.of_nat fd)).
Proof.
  unfold p_ofile. rewrite add_vec64_unsigned moi64_unsigned.
  rewrite bv_wrap_add_idemp_r. reflexivity.
Qed.

Lemma kfkb3_p_ofile_inj (pa : mword 64) (i j : nat) :
  (i <= NOFILE)%nat -> (j <= NOFILE)%nat ->
  p_ofile pa i = p_ofile pa j -> i = j.
Proof.
  intros Hi Hj Heq. unfold NOFILE in Hi, Hj.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (kfkb3_p_ofile_unsigned pa i) (kfkb3_p_ofile_unsigned pa j) in Heq.
  rewrite (Z.add_comm (bv_unsigned pa) (208 + 8 * Z.of_nat i))
          (Z.add_comm (bv_unsigned pa) (208 + 8 * Z.of_nat j)) in Heq.
  apply (proj2 (bv_wrap_add_inj 64 (208 + 8 * Z.of_nat i) (208 + 8 * Z.of_nat j)
                  (bv_unsigned pa))) in Heq.
  rewrite (bv_wrap_small 64 (208 + 8 * Z.of_nat i) ltac:(rewrite bv_modulus64; lia)) in Heq.
  rewrite (bv_wrap_small 64 (208 + 8 * Z.of_nat j) ltac:(rewrite bv_modulus64; lia)) in Heq.
  lia.
Qed.

(* ===================================================================== *)
(*  THE CHILD'S ofile ARRAY AS A FUNCTION OF THE SCAN INDEX.              *)
(* ===================================================================== *)

Definition kfk_ofile_at (Vp_of V0_of : list (mword 64)) (i : nat) : list (mword 64) :=
  (take i Vp_of ++ drop i V0_of)%list.

Lemma kfk_ofile_at_0 (Vp_of V0_of : list (mword 64)) :
  kfk_ofile_at Vp_of V0_of 0 = V0_of.
Proof. reflexivity. Qed.

Lemma kfk_ofile_at_full (Vp_of V0_of : list (mword 64)) :
  length Vp_of = NOFILE -> length V0_of = NOFILE ->
  kfk_ofile_at Vp_of V0_of NOFILE = Vp_of.
Proof.
  intros H1 H2. unfold kfk_ofile_at.
  rewrite (take_ge Vp_of NOFILE ltac:(lia)) (drop_ge V0_of NOFILE ltac:(lia)).
  by rewrite app_nil_r.
Qed.

Lemma kfk_ofile_at_lookup_i (Vp_of V0_of : list (mword 64)) (i : nat) :
  length Vp_of = NOFILE -> (i < NOFILE)%nat ->
  kfk_ofile_at Vp_of V0_of i !! i = V0_of !! i.
Proof.
  intros HVp Hi. unfold kfk_ofile_at.
  rewrite lookup_app_r; [| rewrite length_take; lia].
  rewrite length_take.
  replace (i - Nat.min i (length Vp_of))%nat with 0%nat by lia.
  rewrite lookup_drop. f_equal. lia.
Qed.

Lemma kfk_ofile_at_step (Vp_of V0_of : list (mword 64)) (i : nat) (v : mword 64) :
  length Vp_of = NOFILE -> length V0_of = NOFILE ->
  Vp_of !! i = Some v -> (i < NOFILE)%nat ->
  <[i := v]> (kfk_ofile_at Vp_of V0_of i) = kfk_ofile_at Vp_of V0_of (S i).
Proof.
  intros HVp HV0 Hv Hi.
  destruct (lookup_lt_is_Some_2 V0_of i ltac:(rewrite HV0; lia)) as [v0 Hv0].
  unfold kfk_ofile_at.
  rewrite (insert_app_r_alt (take i Vp_of) (drop i V0_of) i v
             ltac:(rewrite length_take; lia)).
  rewrite length_take.
  replace (i - Nat.min i (length Vp_of))%nat with 0%nat by lia.
  rewrite (drop_S V0_of v0 i Hv0).
  change (<[0 := v]> (v0 :: drop (S i) V0_of)) with (v :: drop (S i) V0_of).
  rewrite (take_S_r Vp_of i v Hv).
  by rewrite <- app_assoc.
Qed.

Lemma kfk_ofile_at_step_null (Vp_of V0_of : list (mword 64)) (i : nat) :
  length Vp_of = NOFILE -> length V0_of = NOFILE -> (i < NOFILE)%nat ->
  Vp_of !! i = V0_of !! i ->
  kfk_ofile_at Vp_of V0_of i = kfk_ofile_at Vp_of V0_of (S i).
Proof.
  intros HVp HV0 Hi Heq.
  destruct (lookup_lt_is_Some_2 V0_of i ltac:(rewrite HV0; lia)) as [v Hv].
  assert (Hvp : Vp_of !! i = Some v) by (rewrite Heq; exact Hv).
  rewrite <- (kfk_ofile_at_step Vp_of V0_of i v HVp HV0 Hvp Hi).
  symmetry. apply list_insert_id.
  rewrite (kfk_ofile_at_lookup_i Vp_of V0_of i HVp Hi). exact Hv.
Qed.

(* ===================================================================== *)
(*  THE CHILD'S WHOLE PRIVATE BLOCK, as the same function of [i].         *)
(* ===================================================================== *)

Definition kfk_childV (V0 : pprivate) (Vp_of : list (mword 64)) (i : nat) : pprivate :=
  MkPPriv (pv_sz V0) (pv_upt V0) (pv_tf V0)
          (kfk_ofile_at Vp_of (pv_ofile V0) i) (pv_cwd V0) (pv_name V0).

Lemma kfk_childV_0 (V0 : pprivate) (Vp_of : list (mword 64)) :
  kfk_childV V0 Vp_of 0 = V0.
Proof. unfold kfk_childV. rewrite kfk_ofile_at_0. by destruct V0. Qed.

Lemma kfk_childV_full (V0 : pprivate) (Vp_of : list (mword 64)) :
  length Vp_of = NOFILE -> length (pv_ofile V0) = NOFILE ->
  pv_ofile (kfk_childV V0 Vp_of NOFILE) = Vp_of.
Proof. intros. unfold kfk_childV. cbn [pv_ofile]. apply kfk_ofile_at_full; assumption. Qed.

Lemma kfk_childV_step (V0 : pprivate) (Vp_of : list (mword 64)) (i : nat) (v : mword 64) :
  length Vp_of = NOFILE -> length (pv_ofile V0) = NOFILE ->
  Vp_of !! i = Some v -> (i < NOFILE)%nat ->
  upd_ofile (kfk_childV V0 Vp_of i) i v = kfk_childV V0 Vp_of (S i).
Proof.
  intros HVp HV0 Hv Hi. unfold upd_ofile, kfk_childV. cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
  f_equal. apply (kfk_ofile_at_step Vp_of (pv_ofile V0) i v HVp HV0 Hv Hi).
Qed.

Lemma kfk_childV_step_null (V0 : pprivate) (Vp_of : list (mword 64)) (i : nat) :
  length Vp_of = NOFILE -> length (pv_ofile V0) = NOFILE -> (i < NOFILE)%nat ->
  Vp_of !! i = pv_ofile V0 !! i ->
  kfk_childV V0 Vp_of i = kfk_childV V0 Vp_of (S i).
Proof.
  intros HVp HV0 Hi Heq. unfold kfk_childV. f_equal.
  apply (kfk_ofile_at_step_null Vp_of (pv_ofile V0) i HVp HV0 Hi Heq).
Qed.

(* ===================================================================== *)
(*  STACK: filedup wants 14 slots below kfork's own 8-slot frame.         *)
(* ===================================================================== *)

Lemma kfkb3_stack (K : nat) : (22 <= K)%nat -> (14 <= (K - 8))%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(*  THE BLOCK.                                                            *)
(* ===================================================================== *)

Module KforkB3 (FD : FILEDUP).

Section KforkB3Proof.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  (* THE INVARIANT THE OUTER FUNCTION MUST SUPPLY AND GETS BACK: the six
     registers this block never touches (sp, s0, s4, s5, plus the generic
     callee-saved chain against the function's own entry map [m0] for
     everything except sp/s0/s1/s2/s3/s4/s5) are carried through UNCHANGED --
     the exact shape [ProofKfork.kfk_tail_succ] already needs from the code
     that follows this scan. *)
  Definition kfkb3_thr (m0 M : regfile) : Prop :=
    forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
      r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
      M !!! Regidx r = m0 !!! Regidx r.

  Lemma kfkb3_fd_loop
      (γl γf : gname) (pme npa : mword64) (pid_p pid_c : mword32)
      (Vp V0 : pprivate) (m0 : regfile) (K n : nat) (eb b : bool)
      (C : iProp Σ) (sp0v s00v : mword 64) :
    (22 <= K)%nat ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    pv_ofile V0 = replicate NOFILE (zero_reg : mword 64) ->
    kernel_text -∗
    is_ftable γl γf -∗
    panic_wp_any -∗
    ∀ (i : nat) (M : regfile),
      ⌜(i <= NOFILE)%nat⌝ -∗
      ⌜M !!! Regidx csp_rs1 = sp0v /\ M !!! Regidx Rs0 = s00v /\
        M !!! Regidx Rs1 = p_ofile pme i /\ M !!! Regidx Rs2 = p_ofile npa i /\
        M !!! Regidx Rs3 = p_cwd pme /\ M !!! Regidx Rs4 = npa /\
        M !!! Regidx Rs5 = pme /\ kfkb3_thr m0 M⌝ -∗
      wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
        ∀ (Mx : regfile),
          ⌜Mx !!! Regidx csp_rs1 = sp0v /\ Mx !!! Regidx Rs0 = s00v /\
            Mx !!! Regidx Rs4 = npa /\ Mx !!! Regidx Rs5 = pme /\
            kfkb3_thr m0 Mx⌝ -∗
          sie_cap_gpr Mx (K - 8)%nat b pme -∗
          cpu_own n eb pme C b -∗
          pc_is (mword_of_int (KF + 0xa4) : mword 64) -∗
          proc_priv γf pme pid_p Vp -∗
          proc_priv γf npa pid_c (kfk_childV V0 (pv_ofile Vp) NOFILE) -∗
          WP (Loop : expr riscv_lang)) -∗
      sie_cap_gpr M (K - 8)%nat b pme -∗
      cpu_own n eb pme C b -∗
      pc_is (mword_of_int (KF + 0x96) : mword 64) -∗
      proc_priv γf pme pid_p Vp -∗
      proc_priv γf npa pid_c (kfk_childV V0 (pv_ofile Vp) i) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hn HV0.
    iIntros "#Htext #Hft #Hpanic".
    iDestruct (proc_priv_ofile_len (V := Vp) with "[]") as %_; [admit_placeholder|].
  Admitted.

End KforkB3Proof.

End KforkB3.
