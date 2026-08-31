(* ===================================================================== *)
(* UkCatVprintfS.v -- vprintf's '%s' ARM.                                 *)
(*                                                                        *)
(* cat's other three diagnostics are literals with no directive in them,  *)
(* and [UkCatVprintf] walks those.  The one it cannot walk is             *)
(*                                                                        *)
(*     fprintf(2, "cat: cannot open %s\n", argv[i]);                      *)
(*                                                                        *)
(* which main issues when open() fails.  Reaching its [putc] takes three  *)
(* things this file supplies: a walk of the plain prefix that STOPS at    *)
(* the '%' instead of running to the terminator; the thirty-instruction   *)
(* dispatch chain that decides, one character class at a time, that this  *)
(* directive is an 's'; and the inner loop over the argument string.      *)
(*                                                                        *)
(* The dispatch is specialised to c0 = 's'.  That is not a shortcut       *)
(* around the branches -- every one of them is stepped -- but a choice of *)
(* what to state: with c0 fixed, each test's outcome is decided by one    *)
(* [vm_compute] on a concrete pair, where a proof general in c0 would     *)
(* have to carry the whole state machine's case analysis for arms cat     *)
(* never enters.                                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.CatInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCat.
Require Import UkCatPutc.
Require Import UkCatVprintf.
Require Import UkRunBr.

Section UkCatVprintfS.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).

  (* --------------------------------------------------------------------- *)
  (* A RUN OF PLAIN CHARACTERS, 0x566 -> 0x566.                             *)
  (*                                                                        *)
  (* [wp_kcat_vprintf_loop] walks a format string with no '%' from an index *)
  (* all the way to its terminator, and ends in the epilogue.  A format     *)
  (* that HAS a '%' needs the same walk stopped short -- at the '%', with   *)
  (* the frame still spilled and the loop still to run.  This is that walk. *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_seg (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (len : nat) (f : nat -> mword 8) (k : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    forall (i0 : nat) (h : CpuId) (m : regfile) (n : nat),
      (i0 + k < len)%nat ->
      (forall j : nat, (i0 <= j < i0 + k)%nat -> bv_unsigned (f j) <> 37) ->
      vp_inv m0 m sp0 a fd ap i0 ->
      m !!! Regidx s1_idx = mword_of_int (bv_unsigned (f i0)) ->
      cat_code γt -∗
      utext_str γt a len f -∗
      urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ vp_inv m0 m' sp0 a fd ap (i0 + k)%nat ⌝ -∗
         ⌜ m' !!! Regidx s1_idx
           = mword_of_int (bv_unsigned (f (i0 + k)%nat)) ⌝ -∗
         urun γt γd γs h' m' (mword_of_int 0x566) (4 + n) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd.
    induction k as [| k IH ];
      intros i0 h m n Hlt Hpct Hinv Hs1;
      iIntros "#Hcode #Hstr Hrun Hcont";
      iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    - (* nothing to walk *)
      rewrite Nat.add_0_r.
      iApply ("Hcont" $! h m with "[] [] Hrun"); iPureIntro;
        [ exact Hinv | exact Hs1 ].
    - (* one plain round, then the rest *)
      assert (Hslt : (S i0 < len)%nat) by lia.
      iDestruct (utext_str_byte γt a len f (S i0) Hslt with "Hstr") as "#Hb1".
      iApply (wp_kcat_vprintf_step γt γd γs m0 sp0 fd ap a i0 (f i0)
                (f (S i0)) h m n Ha0 ltac:(lia) (Hpct i0 ltac:(lia)) Hinv Hs1
                with "Hcode Hb1 Hrun").
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0x562  beqz s1,0x736 -- NOT taken: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (f (S i0)) <> 0).
      { intro He. apply (Hnn (S i0) Hslt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      assert (Hb1r : 0 <= bv_unsigned (f (S i0)) < Z64).
      { assert (HH : 0 <= bv_unsigned (f (S i0)) < 256).
        { pose proof (bv_unsigned_in_range 8 (f (S i0))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hnt : false = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        rewrite (moi_eq_zero (bv_unsigned (f (S i0))) Hb1r).
        destruct (Z.eqb_spec (bv_unsigned (f (S i0))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x562)
                (mword_of_int 468 : mword 13) s1_idx BEQ false
                (add_vec (mword_of_int 0x562 : mword 64)
                   (sign_extend' 64 (mword_of_int 468 : mword 13)))
                (4 + n) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_562 with "Hcode"). }
      assert (E562 : add_vec_int (mword_of_int 0x562 : mword 64) 4
                     = mword_of_int 0x566)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E562.
      iIntros (h2) "Hrun".
      assert (Ek : (i0 + S k)%nat = (S i0 + k)%nat) by lia.
      rewrite Ek.
      iApply (IH (S i0) h2 m1 n ltac:(lia)
                ltac:(intros j Hj; apply Hpct; lia) Hinv1 Hs11
                with "Hcode Hstr Hrun Hcont").
  Qed.

End UkCatVprintfS.
