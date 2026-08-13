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
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import WpLock.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SpecFiledup.
Require Import SpecPanic.
Require Import CpuOwn.
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
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* THE INVARIANT THE OUTER FUNCTION MUST SUPPLY AND GETS BACK: the generic
     callee-saved chain against the function's own entry map [m0], for every
     is_cs_idx register EXCEPT sp/s0/s1/s2/s3/s4/s5 -- exactly the exclusion
     set [ProofKfork.kfk_tail_succ] already needs from the code that follows
     this scan (s1/s2/s3 are this block's own cursors; s4/s5 are carried
     separately below as flat equalities, since [m0] does not yet know their
     meaning at function entry). *)
  Definition kfkb3_thr (m0 M : regfile) : Prop :=
    forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
      r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
      M !!! Regidx r = m0 !!! Regidx r.

  (* THE RESERVE IS AN EXPLICIT PARAMETER [r], NOT [trap_res b].
     This block is ARM-GENERIC in [b] but is applied at [b := false] -- kfork
     runs the fd scan with np->lock held -- from a window whose index already
     carries the reserve of the CALLER's arm.  Writing [trap_res b] here would
     therefore be wrong twice over: it would read [0] at the [false]
     instantiation, and it would tie the carve to the wrong arm.  So the block
     is index-generic in an opaque [rsv] that it never inspects; the
     caller instantiates [rsv := trap_res b] at its own arm.  (Same shape as
     [ProofAllocproc.ap_tail]; see claude-notes/projects/kerneltrap.md.) *)
  Lemma kfkb3_fd_loop
      (γl γf : gname) (pme npa : mword 64) (pid_p pid_c : mword 32)
      (Vp V0 : pprivate) (m0 : regfile) (rsv K n : nat) (eb b : bool)
      (C : iProp Σ) (sp0v s00v : mword 64) :
    (22 <= K)%nat ->
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    pv_ofile V0 = replicate NOFILE (zero_reg : mword 64) ->
    kernel_text -∗
    is_ftable γl γf -∗
    panic_wp_any -∗
    (∀ (i : nat) (M : regfile),
      ⌜(i < NOFILE)%nat⌝ -∗
      ⌜M !!! Regidx csp_rs1 = sp0v /\ M !!! Regidx Rs0 = s00v /\
        M !!! Regidx Rs1 = p_ofile pme i /\ M !!! Regidx Rs2 = p_ofile npa i /\
        M !!! Regidx Rs3 = p_cwd pme /\ M !!! Regidx Rs4 = npa /\
        M !!! Regidx Rs5 = pme /\ kfkb3_thr m0 M⌝ -∗
      wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
        ∀ (Mx : regfile),
          ⌜Mx !!! Regidx csp_rs1 = sp0v /\ Mx !!! Regidx Rs0 = s00v /\
            Mx !!! Regidx Rs4 = npa /\ Mx !!! Regidx Rs5 = pme /\
            kfkb3_thr m0 Mx⌝ -∗
          sie_cap_gpr Mx (rsv + (K - 8))%nat b pme -∗
          cpu_own n eb pme C b -∗
          pc_is (mword_of_int (KF + 0xa4) : mword 64) -∗
          proc_priv γf pme pid_p Vp -∗
          proc_priv_nocwd γf npa pid_c (kfk_childV V0 (pv_ofile Vp) NOFILE) -∗
          WP (Loop : expr riscv_lang)) -∗
      sie_cap_gpr M (rsv + (K - 8))%nat b pme -∗
      cpu_own n eb pme C b -∗
      pc_is (mword_of_int (KF + 0x96) : mword 64) -∗
      proc_priv γf pme pid_p Vp -∗
      proc_priv_nocwd γf npa pid_c (kfk_childV V0 (pv_ofile Vp) i) -∗
      WP (Loop : expr riscv_lang)).
  Proof.
    intros HK Hn HV0.
    iIntros "#Htext #Hft #Hpanic".
    assert (HK14 : (14 <= (rsv + (K - 8)))%nat)
      by (pose proof (kfkb3_stack K HK); lia).
    assert (HlenV0 : length (pv_ofile V0) = NOFILE)
      by (rewrite HV0 length_replicate; reflexivity).
    (* ================================================================= *)
    (*  THE FUEL-INDUCTED BODY, entered at +0x96 with [fuel] turns left.  *)
    (* ================================================================= *)
    iAssert (∀ (fuel : nat),
      wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
        ∀ (i : nat) (M : regfile),
          ⌜(NOFILE - i <= fuel)%nat⌝ -∗
          ⌜(i < NOFILE)%nat⌝ -∗
          ⌜M !!! Regidx csp_rs1 = sp0v /\ M !!! Regidx Rs0 = s00v /\
            M !!! Regidx Rs1 = p_ofile pme i /\ M !!! Regidx Rs2 = p_ofile npa i /\
            M !!! Regidx Rs3 = p_cwd pme /\ M !!! Regidx Rs4 = npa /\
            M !!! Regidx Rs5 = pme /\ kfkb3_thr m0 M⌝ -∗
          wp_next (CID0 := CID0) b pme (fun (CID2 : CpuId) =>
            ∀ (Mx : regfile),
              ⌜Mx !!! Regidx csp_rs1 = sp0v /\ Mx !!! Regidx Rs0 = s00v /\
                Mx !!! Regidx Rs4 = npa /\ Mx !!! Regidx Rs5 = pme /\
                kfkb3_thr m0 Mx⌝ -∗
              sie_cap_gpr Mx (rsv + (K - 8))%nat b pme -∗
              cpu_own n eb pme C b -∗
              pc_is (mword_of_int (KF + 0xa4) : mword 64) -∗
              proc_priv γf pme pid_p Vp -∗
              proc_priv_nocwd γf npa pid_c (kfk_childV V0 (pv_ofile Vp) NOFILE) -∗
              WP (Loop : expr riscv_lang)) -∗
          sie_cap_gpr M (rsv + (K - 8))%nat b pme -∗
          cpu_own n eb pme C b -∗
          pc_is (mword_of_int (KF + 0x96) : mword 64) -∗
          proc_priv γf pme pid_p Vp -∗
          proc_priv_nocwd γf npa pid_c (kfk_childV V0 (pv_ofile Vp) i) -∗
          WP (Loop : expr riscv_lang)))%I
      with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk i M) "%Hfuel %Hi %Hregs Hqx Hcg Hown Hpc Hpv Hpv2".
        exfalso. lia. }
      iIntros (CIDk Hsk i M) "%Hfuel %Hi %Hregs Hqx Hcg Hown Hpc Hpv Hpv2".
      destruct Hregs as (Hcsp & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hthr).
      (* --------------------------------------------------------------- *)
      (*  Htail: the increment+test at +0x8e..+0x92, shared by both arms *)
      (*  of the body below; the child's block is ALREADY at (S i).      *)
      (* --------------------------------------------------------------- *)
      iAssert (wp_next (CID0 := CID0) b pme (fun (CIDta : CpuId) =>
        ∀ (Mt : regfile),
          ⌜Mt !!! Regidx csp_rs1 = sp0v /\ Mt !!! Regidx Rs0 = s00v /\
            Mt !!! Regidx Rs1 = p_ofile pme i /\ Mt !!! Regidx Rs2 = p_ofile npa i /\
            Mt !!! Regidx Rs3 = p_cwd pme /\ Mt !!! Regidx Rs4 = npa /\
            Mt !!! Regidx Rs5 = pme /\ kfkb3_thr m0 Mt⌝ -∗
          sie_cap_gpr Mt (rsv + (K - 8))%nat b pme -∗
          cpu_own n eb pme C b -∗
          pc_is (mword_of_int (KF + 0x8e) : mword 64) -∗
          proc_priv γf pme pid_p Vp -∗
          proc_priv_nocwd γf npa pid_c (kfk_childV V0 (pv_ofile Vp) (S i)) -∗
          WP (Loop : expr riscv_lang)))%I
        with "[Hqx]" as "Htail".
      { iIntros (CIDta Hsta Mt) "%Hregst Hcg Hown Hpc Hpv Hpv2".
        destruct Hregst as (Ht0 & Ht0' & Ht1 & Ht2 & Ht3 & Ht4 & Ht5 & Htthr).
        iPoseProof (kfk_08e with "Htext") as "Hi08e".
        iPoseProof (kfk_090 with "Htext") as "Hi090".
        iPoseProof (kfk_092 with "Htext") as "Hi092".
        (* ---- +0x8e: c.addi s1,s1,8 ---- *)
        iApply (wp_caddi_s_sconf (mword_of_int (KF + 0x8e)) Rs1 (mword_of_int 8 : mword 6)
                  Mt (rsv + (K - 8))%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi08e [-]").
        iIntros (CID1 Hst1) "Hcg Hpc".
        set (T1 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (Mt !!! Regidx Rs1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> Mt).
        change (<[Regidx Rs1 := regval_into_reg
                      (add_vec (Mt !!! Regidx Rs1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> Mt)
          with T1.
        assert (Hpp090 : add_vec_int (mword_of_int (KF + 0x8e) : mword 64) 2
                         = mword_of_int (KF + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp090) in "Hpc".
        assert (HT1s1 : T1 !!! Regidx Rs1 = p_ofile pme (S i)).
        { rewrite /T1 upd_eq. rewrite Ht1. apply p_ofile_succ. }
        assert (HT1csp : T1 !!! Regidx csp_rs1 = sp0v)
          by (rewrite /T1 upd_ne; [exact Ht0 | vm_compute; discriminate]).
        assert (HT1s0 : T1 !!! Regidx Rs0 = s00v)
          by (rewrite /T1 upd_ne; [exact Ht0' | vm_compute; discriminate]).
        assert (HT1s2 : T1 !!! Regidx Rs2 = p_ofile npa i)
          by (rewrite /T1 upd_ne; [exact Ht2 | vm_compute; discriminate]).
        assert (HT1s3 : T1 !!! Regidx Rs3 = p_cwd pme)
          by (rewrite /T1 upd_ne; [exact Ht3 | vm_compute; discriminate]).
        assert (HT1s4 : T1 !!! Regidx Rs4 = npa)
          by (rewrite /T1 upd_ne; [exact Ht4 | vm_compute; discriminate]).
        assert (HT1s5 : T1 !!! Regidx Rs5 = pme)
          by (rewrite /T1 upd_ne; [exact Ht5 | vm_compute; discriminate]).
        assert (HT1thr : kfkb3_thr m0 T1).
        { intros r Hr Ncsp N0 N1 N2 N3 N4 N5.
          rewrite /T1 upd_ne; [| regne]. apply Htthr; assumption. }
        (* ---- +0x90: c.addi s2,s2,8 ---- *)
        iApply (wp_caddi_s_sconf (mword_of_int (KF + 0x90)) Rs2 (mword_of_int 8 : mword 6)
                  T1 (rsv + (K - 8))%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi090 [-]").
        iIntros (CID2 Hst2) "Hcg Hpc".
        set (T2 := <[Regidx Rs2 := regval_into_reg
                      (add_vec (T1 !!! Regidx Rs2)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> T1).
        change (<[Regidx Rs2 := regval_into_reg
                      (add_vec (T1 !!! Regidx Rs2)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> T1)
          with T2.
        assert (Hpp092 : add_vec_int (mword_of_int (KF + 0x90) : mword 64) 2
                         = mword_of_int (KF + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp092) in "Hpc".
        assert (HT2s2 : T2 !!! Regidx Rs2 = p_ofile npa (S i)).
        { rewrite /T2 upd_eq. rewrite HT1s2. apply p_ofile_succ. }
        assert (HT2s1 : T2 !!! Regidx Rs1 = p_ofile pme (S i))
          by (rewrite /T2 upd_ne; [exact HT1s1 | vm_compute; discriminate]).
        assert (HT2csp : T2 !!! Regidx csp_rs1 = sp0v)
          by (rewrite /T2 upd_ne; [exact HT1csp | vm_compute; discriminate]).
        assert (HT2s0 : T2 !!! Regidx Rs0 = s00v)
          by (rewrite /T2 upd_ne; [exact HT1s0 | vm_compute; discriminate]).
        assert (HT2s3 : T2 !!! Regidx Rs3 = p_cwd pme)
          by (rewrite /T2 upd_ne; [exact HT1s3 | vm_compute; discriminate]).
        assert (HT2s4 : T2 !!! Regidx Rs4 = npa)
          by (rewrite /T2 upd_ne; [exact HT1s4 | vm_compute; discriminate]).
        assert (HT2s5 : T2 !!! Regidx Rs5 = pme)
          by (rewrite /T2 upd_ne; [exact HT1s5 | vm_compute; discriminate]).
        assert (HT2thr : kfkb3_thr m0 T2).
        { intros r Hr Ncsp N0 N1 N2 N3 N4 N5.
          rewrite /T2 upd_ne; [| regne]. apply HT1thr; assumption. }
        (* ---- +0x92: beq s1,s3 -- exit iff (S i) = NOFILE ---- *)
        destruct (decide (S i = NOFILE)) as [Heos | Hne].
        - (* TAKEN: the scan is done *)
          assert (Hcmp : eq_vec (T2 !!! Regidx Rs1) (T2 !!! Regidx Rs3) = true).
          { rewrite HT2s1 HT2s3 Heos -p_ofile_end. apply eq_vec_refl. }
          iApply (wp_beq_taken_s_sconf (mword_of_int (KF + 0x92)) (mword_of_int 18 : mword 13)
                    Rs3 Rs1 T2 (rsv + (K - 8))%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rgne; rgne; exact Hcmp) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi092 [-]").
          iNext. iIntros (CID3 Hst3) "Hcg Hpc".
          assert (Htgta4 : add_vec (mword_of_int (KF + 0x92) : mword 64)
                             (sign_extend' 64 (mword_of_int 18 : mword 13))
                           = mword_of_int (KF + 0xa4))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgta4) in "Hpc".
          iEval (rewrite Heos) in "Hpv2".
          iDestruct (cpu_own_transport CIDta CID3 n eb pme C b ltac:(wp_next_chain) with "Hown")
            as "Hown".
          iSpecialize ("Hqx" $! CID3 with "[%]"); [wp_next_chain|].
          iApply ("Hqx" $! T2 with "[%] Hcg Hown Hpc Hpv Hpv2").
          split; [exact HT2csp|]. split; [exact HT2s0|].
          split; [exact HT2s4|]. split; [exact HT2s5|]. exact HT2thr.
        - (* FALL: one more slot to look at *)
          assert (Hne' : p_ofile pme (S i) <> p_ofile pme NOFILE).
          { intro Hbad. apply Hne.
            apply (kfkb3_p_ofile_inj pme (S i) NOFILE ltac:(lia) ltac:(lia) Hbad). }
          assert (Hcmp : eq_vec (T2 !!! Regidx Rs1) (T2 !!! Regidx Rs3) = false).
          { rewrite HT2s1 HT2s3 -p_ofile_end. apply eq_vec_false_iff. exact Hne'. }
          iApply (wp_beq_fall_s_sconf (mword_of_int (KF + 0x92)) (mword_of_int 18 : mword 13)
                    Rs3 Rs1 T2 (rsv + (K - 8))%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rgne; rgne; exact Hcmp)
                    with "Hcg Hpc Hi092 [-]").
          iIntros (CID3 Hst3) "Hcg Hpc".
          assert (Hpp96 : add_vec_int (mword_of_int (KF + 0x92) : mword 64) 4
                         = mword_of_int (KF + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp96) in "Hpc".
          iDestruct (cpu_own_transport CIDta CID3 n eb pme C b ltac:(wp_next_chain) with "Hown")
            as "Hown".
          iSpecialize ("IHf" $! CID3 with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S i) T2 with "[%] [%] [%] Hqx Hcg Hown Hpc Hpv Hpv2").
          + unfold NOFILE in Hfuel |- *. lia.
          + unfold NOFILE in Hne, Hi |- *. lia.
          + split; [exact HT2csp|]. split; [exact HT2s0|]. split; [exact HT2s1|].
            split; [exact HT2s2|]. split; [exact HT2s3|]. split; [exact HT2s4|].
            split; [exact HT2s5|]. exact HT2thr. }
      (* ================================================================= *)
      (*  THE BODY, +0x96 .. +0xa2, at index [i].                          *)
      (* ================================================================= *)
      iPoseProof (kfk_096 with "Htext") as "Hi096".
      iPoseProof (kfk_098 with "Htext") as "Hi098".
      iDestruct (proc_priv_ofile_len with "Hpv") as "%HlenVp".
      destruct (lookup_lt_is_Some_2 (pv_ofile Vp) i ltac:(rewrite HlenVp; lia)) as [v Hv].
      iDestruct (proc_priv_ofile γf pme pid_p Vp i v Hv with "Hpv") as "[[Hcell Hpay] Hback]".
      (* ---- +0x96: c.ld a0,0(s1) ---- *)
      assert (Haddr : add_vec (M !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = p_ofile pme i) by (rewrite Hs1; apply addv_sext0).
      iApply (wp_cld_s_sconf (mword_of_int (KF + 0x96)) Ra0 Rs1 (mword_of_int 0 : mword 12)
                M (rsv + (K - 8))%nat v b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi096 [Hcell] [-]").
      { iEval (rewrite Haddr). iExact "Hcell". }
      iIntros (CIDl Hstl) "Hcg Hpc Hcell". iEval (rewrite Haddr) in "Hcell".
      set (L1 := <[Regidx Ra0 := regval_into_reg v]> M).
      change (<[Regidx Ra0 := regval_into_reg v]> M) with L1.
      assert (Hpp98 : add_vec_int (mword_of_int (KF + 0x96) : mword 64) 2
                     = mword_of_int (KF + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp98) in "Hpc".
      assert (HL1a0 : L1 !!! Regidx Ra0 = v) by (rewrite /L1 upd_eq; reflexivity).
      assert (HL1csp : L1 !!! Regidx csp_rs1 = sp0v)
        by (rewrite /L1 upd_ne; [exact Hcsp | vm_compute; discriminate]).
      assert (HL1s0 : L1 !!! Regidx Rs0 = s00v)
        by (rewrite /L1 upd_ne; [exact Hs0 | vm_compute; discriminate]).
      assert (HL1s1 : L1 !!! Regidx Rs1 = p_ofile pme i)
        by (rewrite /L1 upd_ne; [exact Hs1 | vm_compute; discriminate]).
      assert (HL1s2 : L1 !!! Regidx Rs2 = p_ofile npa i)
        by (rewrite /L1 upd_ne; [exact Hs2 | vm_compute; discriminate]).
      assert (HL1s3 : L1 !!! Regidx Rs3 = p_cwd pme)
        by (rewrite /L1 upd_ne; [exact Hs3 | vm_compute; discriminate]).
      assert (HL1s4 : L1 !!! Regidx Rs4 = npa)
        by (rewrite /L1 upd_ne; [exact Hs4 | vm_compute; discriminate]).
      assert (HL1s5 : L1 !!! Regidx Rs5 = pme)
        by (rewrite /L1 upd_ne; [exact Hs5 | vm_compute; discriminate]).
      assert (HL1thr : kfkb3_thr m0 L1).
      { intros r Hr Ncsp N0 N1 N2 N3 N4 N5.
        rewrite /L1 upd_ne; [| regne]. apply Hthr; assumption. }
      (* ---- +0x98: c.beqz a0 ---- *)
      destruct (decide (v = (zero_reg : mword 64))) as [Hvz | Hvnz].
      + (* ============ NULL: skip to +0x8e, nothing changes ============ *)
        assert (Hz : eq_vec (L1 !!! Regidx Ra0) (zero_reg : mword 64) = true)
          by (rewrite HL1a0; apply eq_vec_true_iff; exact Hvz).
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KF + 0x98)) (mword_of_int 251 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 L1 (rsv + (K - 8))%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hz ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi098 [-]").
        iNext. iIntros (CIDm Hstm) "Hcg Hpc".
        assert (Htgt8e : add_vec (mword_of_int (KF + 0x98) : mword 64)
                           (sign_extend' 64 (sign_extend' 13
                              (concat_vec (mword_of_int 251 : mword 8) ('b"0"))))
                         = mword_of_int (KF + 0x8e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt8e) in "Hpc".
        iDestruct ("Hback" $! v with "[Hcell Hpay]") as "Hpv".
        { rewrite /ofile_slot. iFrame "Hcell Hpay". }
        iEval (rewrite (upd_ofile_id _ _ _ Hv)) in "Hpv".
        assert (HV0i : pv_ofile V0 !! i = Some (zero_reg : mword 64)).
        { rewrite HV0. apply lookup_replicate. split; [reflexivity | lia]. }
        assert (Hvz' : pv_ofile Vp !! i = Some (zero_reg : mword 64))
          by (rewrite Hv Hvz; reflexivity).
        assert (HeqVV0 : pv_ofile Vp !! i = pv_ofile V0 !! i) by (rewrite Hvz' HV0i; reflexivity).
        iEval (rewrite (kfk_childV_step_null V0 (pv_ofile Vp) i HlenVp HlenV0 Hi HeqVV0))
          in "Hpv2".
        iDestruct (cpu_own_transport CIDk CIDm n eb pme C b ltac:(wp_next_chain) with "Hown")
          as "Hown".
        iSpecialize ("Htail" $! CIDm with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! L1 with "[%] Hcg Hown Hpc Hpv Hpv2").
        split; [exact HL1csp|]. split; [exact HL1s0|]. split; [exact HL1s1|].
        split; [exact HL1s2|]. split; [exact HL1s3|]. split; [exact HL1s4|].
        split; [exact HL1s5|]. exact HL1thr.
      + (* ============ NON-NULL: filedup ============ *)
        iDestruct "Hpay" as "[[%Hz0 _]|(%k & %q & %Cf & [%Hfn %Hk] & Href)]".
        { exfalso. apply Hvnz. exact Hz0. }
        assert (Hz : eq_vec (L1 !!! Regidx Ra0) (zero_reg : mword 64) = false)
          by (rewrite HL1a0; apply eq_vec_false_iff; exact Hvnz).
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KF + 0x98)) (mword_of_int 251 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 L1 (rsv + (K - 8))%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hz with "Hcg Hpc Hi098 [-]").
        iIntros (CIDm Hstm) "Hcg Hpc".
        assert (Hpp9a : add_vec_int (mword_of_int (KF + 0x98) : mword 64) 2
                       = mword_of_int (KF + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp9a) in "Hpc".
        iPoseProof (kfk_09a with "Htext") as "Hi09a".
        iPoseProof (kfk_09e with "Htext") as "Hi09e".
        iPoseProof (kfk_0a2 with "Htext") as "Hi0a2".
        (* the child's slot [i] is null: open it, it owns exactly the one
           [FdSlots.fd_slot] unit filedup's precondition wants. *)
        assert (Hvc : pv_ofile (kfk_childV V0 (pv_ofile Vp) i) !! i = Some (zero_reg : mword 64)).
        { unfold kfk_childV. cbn [pv_ofile].
          rewrite (kfk_ofile_at_lookup_i (pv_ofile Vp) (pv_ofile V0) i HlenVp Hi).
          rewrite HV0. apply lookup_replicate. split; [reflexivity | lia]. }
        iDestruct (proc_priv_nocwd_ofile γf npa pid_c (kfk_childV V0 (pv_ofile Vp) i) i
                     (zero_reg : mword 64) Hvc with "Hpv2") as "[Hslot2 Hback2]".
        iDestruct (ofile_slot_null with "Hslot2") as "[Hcell2 Hfds]".
        (* ---- +0x9a: jal ra,filedup ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (KF + 0x9a)) Rra (mword_of_int 9102 : mword 21)
                  L1 (rsv + (K - 8))%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi09a [-]").
        iIntros (CIDn Hstn) "Hcg Hpc".
        set (L2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KF + 0x9a) : mword 64) 4)]> L1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KF + 0x9a) : mword 64) 4)]> L1) with L2.
        assert (Hjmp : add_vec (mword_of_int (KF + 0x9a) : mword 64)
                         (sign_extend' 64 (mword_of_int 9102 : mword 21))
                       = mword_of_int KernelSyms.filedup) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjmp) in "Hpc".
        assert (HL2ra : L2 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0x9a) : mword 64) 4)
          by (rewrite /L2; apply upd_eq).
        assert (HL2a0 : L2 !!! Regidx Ra0 = v)
          by (rewrite /L2 upd_ne; [exact HL1a0 | vm_compute; discriminate]).
        assert (HL2csp : L2 !!! Regidx csp_rs1 = sp0v)
          by (rewrite /L2 upd_ne; [exact HL1csp | vm_compute; discriminate]).
        assert (HL2s0 : L2 !!! Regidx Rs0 = s00v)
          by (rewrite /L2 upd_ne; [exact HL1s0 | vm_compute; discriminate]).
        assert (HL2s1 : L2 !!! Regidx Rs1 = p_ofile pme i)
          by (rewrite /L2 upd_ne; [exact HL1s1 | vm_compute; discriminate]).
        assert (HL2s2 : L2 !!! Regidx Rs2 = p_ofile npa i)
          by (rewrite /L2 upd_ne; [exact HL1s2 | vm_compute; discriminate]).
        assert (HL2s3 : L2 !!! Regidx Rs3 = p_cwd pme)
          by (rewrite /L2 upd_ne; [exact HL1s3 | vm_compute; discriminate]).
        assert (HL2s4 : L2 !!! Regidx Rs4 = npa)
          by (rewrite /L2 upd_ne; [exact HL1s4 | vm_compute; discriminate]).
        assert (HL2s5 : L2 !!! Regidx Rs5 = pme)
          by (rewrite /L2 upd_ne; [exact HL1s5 | vm_compute; discriminate]).
        assert (HL2thr : kfkb3_thr m0 L2).
        { intros r Hr Ncsp N0 N1 N2 N3 N4 N5.
          rewrite /L2 upd_ne; [| regne]. apply HL1thr; assumption. }
        assert (HL2a0k : L2 !!! Regidx Ra0 = fnode k) by (rewrite HL2a0; exact Hfn).
        iDestruct (cpu_own_transport CIDk CIDn n eb pme C b ltac:(wp_next_chain) with "Hown")
          as "Hown".
        iApply (FD.wp_filedup_sconf γl γf k q Cf L2 n eb pme C (rsv + (K - 8))%nat b
                  HK14 Hn HL2a0k
                  with "Hcg Hown Htext Hpc Hft Hpanic Hfds Href [-]").
        iIntros (CIDo Hsto mr) "Hcg Hown Hpc %Hcsmr Hslota Hslotb".
        destruct Hcsmr as [Hcsmr Hmra0].
        assert (Hpc9e : ret_pc (L2 !!! Regidx Rra) = mword_of_int (KF + 0x9e)).
        { rewrite HL2ra. apply bv_eq. vm_compute. reflexivity. }
        iEval (rewrite Hpc9e) in "Hpc".
        assert (Hmrcsp : mr !!! Regidx csp_rs1 = sp0v)
          by (rewrite (callee_saved_lookup Hcsmr csp_rs1 ltac:(vm_compute; reflexivity)); exact HL2csp).
        assert (Hmrs0 : mr !!! Regidx Rs0 = s00v)
          by (rewrite (callee_saved_lookup Hcsmr Rs0 ltac:(vm_compute; reflexivity)); exact HL2s0).
        assert (Hmrs1 : mr !!! Regidx Rs1 = p_ofile pme i)
          by (rewrite (callee_saved_lookup Hcsmr Rs1 ltac:(vm_compute; reflexivity)); exact HL2s1).
        assert (Hmrs2 : mr !!! Regidx Rs2 = p_ofile npa i)
          by (rewrite (callee_saved_lookup Hcsmr Rs2 ltac:(vm_compute; reflexivity)); exact HL2s2).
        assert (Hmrs3 : mr !!! Regidx Rs3 = p_cwd pme)
          by (rewrite (callee_saved_lookup Hcsmr Rs3 ltac:(vm_compute; reflexivity)); exact HL2s3).
        assert (Hmrs4 : mr !!! Regidx Rs4 = npa)
          by (rewrite (callee_saved_lookup Hcsmr Rs4 ltac:(vm_compute; reflexivity)); exact HL2s4).
        assert (Hmrs5 : mr !!! Regidx Rs5 = pme)
          by (rewrite (callee_saved_lookup Hcsmr Rs5 ltac:(vm_compute; reflexivity)); exact HL2s5).
        assert (Hmrthr : kfkb3_thr m0 mr).
        { intros r Hr Ncsp N0 N1 N2 N3 N4 N5.
          rewrite (callee_saved_lookup Hcsmr r Hr). apply HL2thr; assumption. }
        (* ---- +0x9e: sd a0,0(s2) -- np->ofile[i] = the duplicate ---- *)
        assert (Haddr2 : add_vec (mr !!! Regidx Rs2) (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = p_ofile npa i) by (rewrite Hmrs2; apply addv_sext0).
        iApply (wp_sd_s_sconf (mword_of_int (KF + 0x9e)) Ra0 Rs2 (mword_of_int 0 : mword 12)
                  mr (rsv + (K - 8))%nat (zero_reg : mword 64) b
                  with "Hcg Hpc Hi09e [Hcell2] [-]").
        { iEval (rgne; rewrite Haddr2). iExact "Hcell2". }
        iIntros (CIDp Hstp) "Hcg Hpc Hcell2".
        iEval (rgne; rgne; rewrite Haddr2 Hmra0) in "Hcell2".
        assert (Hpp0a2 : add_vec_int (mword_of_int (KF + 0x9e) : mword 64) 4
                        = mword_of_int (KF + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp0a2) in "Hpc".
        (* close the child's slot: it now names the SAME file the parent's does *)
        iDestruct (ofile_slot_file γf npa i k (q/2)%Qp Cf Hk with "Hcell2 Hslotb") as "Hslot2".
        iDestruct ("Hback2" $! (fnode k) with "Hslot2") as "Hpv2".
        assert (Hvfn : pv_ofile Vp !! i = Some (fnode k)) by (rewrite Hv Hfn; reflexivity).
        iEval (rewrite (kfk_childV_step V0 (pv_ofile Vp) i (fnode k) HlenVp HlenV0 Hvfn Hi))
          in "Hpv2".
        (* close the parent's slot back: it names the SAME file it always did *)
        iEval (rewrite Hfn) in "Hcell".
        iDestruct (ofile_slot_file γf pme i k (q/2)%Qp Cf Hk with "Hcell Hslota") as "Hslot".
        iDestruct ("Hback" $! (fnode k) with "Hslot") as "Hpv".
        iEval (rewrite (upd_ofile_id _ _ _ Hvfn)) in "Hpv".
        (* ---- +0xa2: c.j -> +0x8e ---- *)
        iApply (wp_cj_s_sconf (mword_of_int (KF + 0xa2))
                  (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")))
                  mr (rsv + (K - 8))%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi0a2 [-]").
        iIntros (CIDq Hstq). iNext. iIntros "Hcg Hpc".
        assert (Htgt8e' : add_vec (mword_of_int (KF + 0xa2) : mword 64)
                           (sign_extend' 64 (sign_extend' 21
                              (concat_vec (mword_of_int 2038 : mword 11) ('b"0"))))
                         = mword_of_int (KF + 0x8e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt8e') in "Hpc".
        iDestruct (cpu_own_transport CIDo CIDq n eb pme C b ltac:(wp_next_chain) with "Hown")
          as "Hown".
        iSpecialize ("Htail" $! CIDq with "[%]"); [wp_next_chain|].
        iApply ("Htail" $! mr with "[%] Hcg Hown Hpc Hpv Hpv2").
        split; [exact Hmrcsp|]. split; [exact Hmrs0|]. split; [exact Hmrs1|].
        split; [exact Hmrs2|]. split; [exact Hmrs3|]. split; [exact Hmrs4|].
        split; [exact Hmrs5|]. exact Hmrthr. }
    iIntros (i M) "%Hi %Hregs Hqx Hcg Hown Hpc Hpv Hpv2".
    iSpecialize ("Hloop" $! (NOFILE - i)%nat).
    iSpecialize ("Hloop" $! CID0 with "[%]"); [by intros|].
    iApply ("Hloop" $! i M with "[%] [%] [%] Hqx Hcg Hown Hpc Hpv Hpv2");
      [lia | exact Hi | exact Hregs].
  Qed.

End KforkB3Proof.

End KforkB3.
