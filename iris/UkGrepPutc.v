(* ===================================================================== *)
(* UkGrepPutc.v -- ulib's [putc(fd, c)] at grep's addresses, the bottom   *)
(* of grep's printf cone, and the WRITE OBLIGATIONS the cone spends.       *)
(*                                                                        *)
(* A PORT of [UkCatPutc.v] (and of [UkCat.v]'s write-obligation block)     *)
(* to grep's image: the same C, the same instructions, 0x170 further up    *)
(* (grep.md section 3).  [kgrep_w] / [kgrep_wb] / [kgrep_pay_seq] are      *)
(* [UkCat.kcat_w] / [kcat_wb] / [kcat_pay_seq] at grep's code and write    *)
(* stub, so every walk above states its output exactly as cat's does.      *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeGrep.
Require Import CtxIdDefs.
Require User.GrepSyms User.GrepInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)


Section UkGrepW.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT PAYLOAD DOES NOT READ ITS STATUS (lane CAT-WALK,
     W2), as a CLASS so that it reaches the exit ecall without an argument
     at every call site ([UkRun.ukn_const]).  It used to be [ukn_triv] --
     "cat owes its parent nothing" -- which pinned the payload at [True]
     and so made cat's exit incapable of handing the shell the deed
     fraction, the advanced console credential or the filed alternative.
     What cat actually needs of
     its own payload is only that its two exits -- 0 on the content arm,
     1 on the diagnostic arm -- owe the SAME thing, which is exactly this
     class; echo's walk is stated at it for the same reason. *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ===================================================================== *)
  (* WHAT THE WALK SPENDS PER WRITE -- [UkCat.kcat_w]'s shape verbatim, at  *)
  (* grep's code catalog and grep's write stub.                            *)
  (* ===================================================================== *)
  Definition kgrep_w (fdw ua : mword 64) (nb : nat) (Ci Co : iProp Σ)
    : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (avail : nat),
       ⌜m !!! Regidx a0_idx = fdw⌝ -∗
       ⌜m !!! Regidx a1_idx = ua⌝ -∗
       ⌜m !!! Regidx a2_idx = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       grep_code γt -∗
       Ci -∗
       urun N h m (mword_of_int GrepSyms.write) avail -∗
       (∀ (h' : CpuId) (ret : mword 64),
          Co -∗
          urun N h'
            (<[Regidx a0_idx := ret]>
               (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
            (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ...and the output side is MONOTONE, which is what lets the LAST write
     of a chain hand its cursor straight to the exit's payload. *)
  Lemma kgrep_w_mono (fdw ua : mword 64) (nb : nat) (Ci Co Co' : iProp Σ) :
    (Co -∗ Co') -∗ kgrep_w fdw ua nb Ci Co -∗ kgrep_w fdw ua nb Ci Co'.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "HCo Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  (* ...and the INPUT side is anti-monotone, which is what lets a chain be
     re-cut at a point where the caller holds a stronger cursor. *)
  Lemma kgrep_w_mono_in (fdw ua : mword 64) (nb : nat) (Ci Ci' Co : iProp Σ) :
    (Ci' -∗ Ci) -∗ kgrep_w fdw ua nb Ci Co -∗ kgrep_w fdw ua nb Ci' Co.
  Proof using .
    iIntros "Hm Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail
              with "[%] [%] [%] Hcode [Hm HCi] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  (* ...AND IT FRAMES: a caller that HOLDS the input half a payment asks
     for hands it over once and is left with the obligation at the rest.
     This is how the WRITTEN BYTES reach the payment -- the buffer is
     linear and the conversion is not, so the two travel separately and
     meet here. *)
  Lemma kgrep_w_frame (fdw ua : mword 64) (nb : nat) (Ci Co C : iProp Σ) :
    C -∗ kgrep_w fdw ua nb (Ci ∗ C) Co -∗ kgrep_w fdw ua nb Ci Co.
  Proof using .
    iIntros "HC Hw" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! h m avail with "[%] [%] [%] Hcode [$HCi $HC] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.

  Definition kgrep_wb (fdw : mword 64) (b : bv 8) (Ci Co : iProp Σ) : iProp Σ :=
    (∀ ua : mword 64,
       kgrep_w fdw ua 1%nat
         (Ci ∗ ubyte γd (uint ua) b) (Co ∗ ubyte γd (uint ua) b))%I.

  Lemma kgrep_wb_mono (fdw : mword 64) (b : bv 8) (Ci Co Co' : iProp Σ) :
    (Co -∗ Co') -∗ kgrep_wb fdw b Ci Co -∗ kgrep_wb fdw b Ci Co'.
  Proof using .
    iIntros "Hm Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode HCi Hrun Hcont".
    iApply ("Hw" $! ua h m avail with "[%] [%] [%] Hcode HCi Hrun");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "[HCo Hb] Hrun".
    iApply ("Hcont" $! h' ret with "[Hm HCo $Hb] Hrun").
    iApply ("Hm" with "HCo").
  Qed.

  Lemma kgrep_wb_mono_in (fdw : mword 64) (b : bv 8) (Ci Ci' Co : iProp Σ) :
    (Ci' -∗ Ci) -∗ kgrep_wb fdw b Ci Co -∗ kgrep_wb fdw b Ci' Co.
  Proof using .
    iIntros "Hm Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [HCi Hb] Hrun Hcont".
    iApply ("Hw" $! ua h m avail
              with "[%] [%] [%] Hcode [Hm HCi $Hb] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iApply ("Hm" with "HCi").
  Qed.

  Lemma kgrep_wb_frame (fdw : mword 64) (b : bv 8) (Ci Co C : iProp Σ) :
    C -∗ kgrep_wb fdw b (Ci ∗ C) Co -∗ kgrep_wb fdw b Ci Co.
  Proof using .
    iIntros "HC Hw" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [HCi Hb] Hrun Hcont".
    iApply ("Hw" $! ua h m avail
              with "[%] [%] [%] Hcode [$HCi $HC $Hb] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 ].
  Qed.


  (* ...AND THE BYTE A CALLER PUTS IN a1.  Every putc call site loads the
     character as a full word whose value is the byte's, so this is the one
     step that reads it back, and it is what lets a caller state its
     payment at the CHARACTER rather than at the word. *)
  Lemma kgrep_nth_byte0_moi (b : bv 8) :
    nth_byte (mword_of_int (bv_unsigned b) : mword 64) 0%nat = b.
  Proof using .
    pose proof (bv_unsigned_in_range 8 b) as Hr.
    assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
    rewrite Em8 in Hr.
    assert (Hs : bv_unsigned (mword_of_int (bv_unsigned b) : mword 64)
                 = bv_unsigned b)
      by (apply moi_small; unfold Z64; clear -Hr; lia).
    apply bv_eq. rewrite nth_byte_unsigned.
    replace (Z.of_N (8 * N.of_nat 0)) with 0 by (vm_compute; reflexivity).
    rewrite Z.shiftr_0_r Hs.
    apply Z.mod_small. clear -Hr. lia.
  Qed.

  (* ...and the same at a zero-extended byte, which is how a character
     LOADED from memory reaches a1 ([lbu] zero-extends). *)
  Lemma kgrep_nth_byte0_zext (b : mword 8) :
    nth_byte (zero_extend' 64 b : mword 64) 0%nat = b.
  Proof using . rewrite zext8_moi. apply kgrep_nth_byte0_moi. Qed.

  Fixpoint kgrep_pay_seq (fdw : mword 64) (fb : nat -> bv 8) (i k : nat)
      (Ci Cend : iProp Σ) : iProp Σ :=
    match k with
    | O => (Ci -∗ Cend)%I
    | S k' => (∃ Cm : iProp Σ,
                 kgrep_wb fdw (fb i) Ci Cm
                 ∗ kgrep_pay_seq fdw fb (S i) k' Cm Cend)%I
    end.

  (* the output side is MONOTONE, as one write's is *)
  Lemma kgrep_pay_seq_mono (fdw : mword 64) (fb : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Cend Cend' : iProp Σ),
      (Cend -∗ Cend') -∗
      kgrep_pay_seq fdw fb i k Ci Cend -∗ kgrep_pay_seq fdw fb i k Ci Cend'.
  Proof using .
    induction k as [| k IH]; intros i Ci Cend Cend'; iIntros "Hm Hc".
    - cbn [kgrep_pay_seq]. iIntros "HCi".
      iApply "Hm". iApply ("Hc" with "HCi").
    - cbn [kgrep_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hw". iApply (IH (S i) with "Hm Hc").
  Qed.

  (* ...AND IT FRAMES AT THE HEAD, which is how a caller holding the
     resource the first write wants hands it over once. *)
  Lemma kgrep_pay_seq_frame (fdw : mword 64) (fb : nat -> bv 8) (k : nat)
      (i : nat) (Ci Cend C : iProp Σ) :
    C -∗ kgrep_pay_seq fdw fb i k (Ci ∗ C) Cend -∗
    kgrep_pay_seq fdw fb i k Ci Cend.
  Proof using .
    destruct k as [| k]; iIntros "HC Hc".
    - cbn [kgrep_pay_seq]. iIntros "HCi". iApply ("Hc" with "[$HCi $HC]").
    - cbn [kgrep_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hc". iApply (kgrep_wb_frame with "HC Hw").
  Qed.

  (* ...AND IT SPLITS AND JOINS AT ANY POINT, which is what a format string
     with a [%s] in it needs: the literal before the directive, the
     argument's own bytes and the literal after it are three runs of one
     chain. *)
  Lemma kgrep_pay_seq_in (fdw : mword 64) (fb : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Ci' Cend : iProp Σ),
      (Ci' -∗ Ci) -∗
      kgrep_pay_seq fdw fb i k Ci Cend -∗ kgrep_pay_seq fdw fb i k Ci' Cend.
  Proof using .
    induction k as [| k IH]; intros i Ci Ci' Cend; iIntros "Hm Hc".
    - cbn [kgrep_pay_seq]. iIntros "HCi".
      iApply "Hc". iApply ("Hm" with "HCi").
    - cbn [kgrep_pay_seq]. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. iFrame "Hc". iApply (kgrep_wb_mono_in with "Hm Hw").
  Qed.

  Lemma kgrep_pay_seq_split (fdw : mword 64) (fb : nat -> bv 8) (k1 : nat) :
    forall (i k2 : nat) (Ci Cend : iProp Σ),
      kgrep_pay_seq fdw fb i (k1 + k2) Ci Cend -∗
      ∃ Cm : iProp Σ,
        kgrep_pay_seq fdw fb i k1 Ci Cm
        ∗ kgrep_pay_seq fdw fb (i + k1) k2 Cm Cend.
  Proof using .
    induction k1 as [| k1 IH]; intros i k2 Ci Cend.
    - rewrite Nat.add_0_r. cbn [Nat.add]. iIntros "Hc".
      iExists Ci. iSplitR "Hc"; [ cbn [kgrep_pay_seq]; by iIntros "$" | ].
      iExact "Hc".
    - cbn [Nat.add]. iIntros "Hc". cbn [kgrep_pay_seq].
      iDestruct "Hc" as (Cn) "[Hw Hc]".
      iDestruct (IH (S i) k2 Cn Cend with "Hc") as (Cm) "[H1 H2]".
      iExists Cm. iSplitR "H2".
      + iExists Cn. iFrame "Hw H1".
      + replace (i + S k1)%nat with (S i + k1)%nat by lia. iExact "H2".
  Qed.

  Lemma kgrep_pay_seq_join (fdw : mword 64) (fb : nat -> bv 8) (k1 : nat) :
    forall (i k2 : nat) (Ci Cm Cend : iProp Σ),
      kgrep_pay_seq fdw fb i k1 Ci Cm -∗
      kgrep_pay_seq fdw fb (i + k1) k2 Cm Cend -∗
      kgrep_pay_seq fdw fb i (k1 + k2) Ci Cend.
  Proof using .
    induction k1 as [| k1 IH]; intros i k2 Ci Cm Cend.
    - rewrite Nat.add_0_r. cbn [Nat.add]. iIntros "H1 H2".
      iApply (kgrep_pay_seq_in fdw fb k2 i Cm Ci Cend with "[H1] H2").
      cbn [kgrep_pay_seq]. iExact "H1".
    - cbn [Nat.add]. iIntros "H1 H2". cbn [kgrep_pay_seq] in *.
      iDestruct "H1" as (Cn) "[Hw H1]".
      iExists Cn. iFrame "Hw".
      iApply (IH (S i) k2 Cn Cm Cend with "H1 [H2]").
      replace (S i + k1)%nat with (i + S k1)%nat by lia. iExact "H2".
  Qed.

  (* ...AND IT ONLY READS THE BYTES IT COVERS. *)
  Lemma kgrep_pay_seq_ext (fdw : mword 64) (fb fb' : nat -> bv 8) (k : nat) :
    forall (i : nat) (Ci Cend : iProp Σ),
      (forall j : nat, (i <= j)%nat -> (j < i + k)%nat -> fb j = fb' j) ->
      kgrep_pay_seq fdw fb i k Ci Cend -∗ kgrep_pay_seq fdw fb' i k Ci Cend.
  Proof using .
    induction k as [| k IH]; intros i Ci Cend Heq; iIntros "Hc".
    - cbn [kgrep_pay_seq] in *. iExact "Hc".
    - cbn [kgrep_pay_seq] in *. iDestruct "Hc" as (Cm) "[Hw Hc]".
      iExists Cm. rewrite <- (Heq i ltac:(lia) ltac:(lia)). iFrame "Hw".
      iApply (IH (S i) Cm Cend ltac:(intros j H1 H2; apply Heq; lia)
                with "Hc").
  Qed.

End UkGrepW.

Section UkGrepPutc.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT PAYLOAD DOES NOT READ ITS STATUS (lane CAT-WALK,
     W2), as a CLASS so that it reaches the exit ecall without an argument
     at every call site ([UkRun.ukn_const]).  It used to be [ukn_triv] --
     "cat owes its parent nothing" -- which pinned the payload at [True]
     and so made cat's exit incapable of handing the shell the deed
     fraction, the advanced console credential or the filed alternative.
     What cat actually needs of
     its own payload is only that its two exits -- 0 on the content arm,
     1 on the diagnostic arm -- owe the SAME thing, which is exactly this
     class; echo's walk is stated at it for the same reason. *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ===================================================================== *)
  (* THE PRINTF CONE.  cat's four format strings contain no '%', so the    *)
  (* whole cone is [printf(fmt) = write(1, fmt, strlen fmt)] spelled out    *)
  (* one character at a time: printf marshals its (unused) varargs and      *)
  (* tail-calls vprintf, vprintf walks the string and hands each byte to    *)
  (* putc, and putc spills that byte into its own frame and writes ONE      *)
  (* byte.  Nothing in the cone touches the caller's memory: every store    *)
  (* lands in a frame the function took off the free stack and gave back,   *)
  (* and write is the QUIET row.                                           *)
  (* ===================================================================== *)

  (* a callee-saved register is none of the ones a caller may clobber *)

  (* --------------------------------------------------------------------- *)
  (* putc(fd, c) @0x5cc -- ulib's one-byte write.                            *)
  (*                                                                        *)
  (*   c.addi sp,sp,-32 ; c.sdsp ra,24(sp) ; c.sdsp s0,16(sp)                *)
  (*   c.addi4spn s0,sp,32 ; sb a1,-17(s0) ; c.li a2,1 ; addi a1,s0,-17      *)
  (*   jal <write> ; c.ldsp ra,24(sp) ; c.ldsp s0,16(sp)                     *)
  (*   c.addi16sp sp,sp,32 ; c.jr ra                                         *)
  (*                                                                        *)
  (* THE BYTE GOES IN THE FRAME.  [sb a1,-17(s0)] with s0 = the entry sp     *)
  (* lands at [sp0-17], which is byte 7 of the frame word at [sp0-24] --     *)
  (* hence the [uword_8] split and the [uword_of_bytes_8] reassembly, and    *)
  (* hence the fact that putc's whole memory effect is INSIDE the four       *)
  (* words it borrowed.  The caller gets its free stack back at the same     *)
  (* [avail] and learns nothing about the frame's contents, which is why     *)
  (* the post is [ucallee_saved] and nothing else.                           *)
  (* --------------------------------------------------------------------- *)
  (* ...AND WHAT IT SPENDS (lane CAT-WALK, W1): ONE per-call obligation at
     the byte it is about to store, not the flagged deposit.  The byte is
     the low half of the caller's a1 and the descriptor is the caller's a0,
     so the premise is read straight off the entry register file and putc
     gains no argument of its own; the FRAME ADDRESS is quantified inside
     [kgrep_wb], because it is one frame below the caller's sp and no
     caller can name it. *)
  Lemma wp_kgrep_putc (h : CpuId) (m : regfile) (n : nat)
      (Ci Co : iProp Σ) :
    kgrep_wb N (m !!! Regidx a0_idx)
      (nth_byte (m !!! Regidx a1_idx) 0) Ci Co -∗
    grep_code γt -∗
    Ci -∗
    urun N h m (mword_of_int GrepSyms.putc) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       Co -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "Hw #Hcode HCi Hrun Hcont".
    destruct grep_syms_pins
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hputc & _ & Hwrite & _ & _ & _).
    rewrite Hputc.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 32 <= uint sp0) by (clear -Hroom'; lia).
    (* the frame's bottom, and the round trip back up *)
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   = bv_unsigned sp0 - 32).
    { replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp32 : uint (add_vec_int sp0 (- (8 * Z.of_nat 4))) = uint sp0 - 32)
      by (rewrite !uint_unsigned; exact Hbsp).
    (* HR IS ITS OWN ASSERT, and [Hlt4]'s [lia] runs under [clear -].  Both
       matter.  [bv_unsigned_in_range 64 sp0] fixes the width index at [64 :
       N] while the goal's [bv_unsigned sp0] carries [sp0]'s own [Z_idx 64]
       -- convertible, but TWO ATOMS to [lia], which is why splicing the
       range in directly makes the goal unprovable rather than slow.  And a
       bare [lia] here reifies the whole [envs_entails Δ Q]: this one ran
       four minutes before failing. *)
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd4 : (0 <= 8 * Z.of_nat 4)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt4 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                   + 8 * Z.of_nat 4 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                    (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 4)))
                 (8 * Z.of_nat 4) Hd4 Hlt4).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Eb7 : (uint sp0 - 17)%Z = (uint sp0 - 24 + 7)%Z) by lia.
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x5cc  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn N h m (mword_of_int 0x5cc)
              (mword_of_int 32 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_5cc with "Hcode"). }
    iIntros "Hframe".
    assert (E41a : add_vec_int (mword_of_int 0x5cc : mword 64) 2
                   = mword_of_int 0x5ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E41a.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4)))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    (* the four words of the frame, by name -- DIRECTED, never [rewrite
       ustack_4]: that fires on the whole [envs_entails Δ Q] *)
    iDestruct (ustack_4_open with "Hframe")
      as "(_ & [%vra Hwra] & [%vs0 Hws0] & [%vb Hwb] & Hw32)".
    (* ---- 0x5ce  c.sdsp ra,24(sp) ---- *)
    iApply (wp_uk_csdsp N h1 m1 (mword_of_int 0x5ce)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(rewrite Hsp1 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hwra Hrun").
    { iApply (uis_grep_5ce with "Hcode"). }
    iIntros "Hwra".
    assert (E41c : add_vec_int (mword_of_int 0x5ce : mword 64) 2
                   = mword_of_int 0x5d0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41c.
    iIntros (h2) "Hrun".
    (* ---- 0x5d0  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp N h2 m1 (mword_of_int 0x5d0)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(rewrite Hsp1 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hws0 Hrun").
    { iApply (uis_grep_5d0 with "Hcode"). }
    iIntros "Hws0".
    assert (E41e : add_vec_int (mword_of_int 0x5d0 : mword 64) 2
                   = mword_of_int 0x5d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41e.
    iIntros (h3) "Hrun".
    (* the two spilled values, as they will come back out *)
    assert (Hra1 : m1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs01 : m1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- 0x5d2  c.addi4spn s0,sp,32 -- s0 := the ENTRY sp ---- *)
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 4))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn N h3 m1 (mword_of_int 0x5d2)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx sp0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_grep_5d2 with "Hcode"). }
    assert (E420 : add_vec_int (mword_of_int 0x5d2 : mword 64) 2
                   = mword_of_int 0x5d4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E420.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (Hs02 : m2 !!! Regidx s0_idx = sp0)
      by exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp1.
      exact (upd_ne m1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg sp0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5d4  sb a1,-17(s0) -- the byte, into BYTE 7 of the third word ---- *)
    assert (Hoff17 : uoff_i12 (mword_of_int 4079 : mword 12) = -17)
      by (vm_compute; reflexivity).
    iDestruct (uword_byte7_acc γd (uint sp0 - 24) (uint sp0 - 17) vb Eb7
                 with "Hwb") as "(Hb7 & Hwbc)".
    iApply (wp_uk_sb N h4 m2 (mword_of_int 0x5d4)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (uint sp0 - 17) (nth_byte vb 7%nat) n
              ltac:(rewrite Hs02 Hoff17; lia)
              with "[] Hb7 Hrun").
    { iApply (uis_grep_5d4 with "Hcode"). }
    iIntros "Hb7".
    assert (E422 : add_vec_int (mword_of_int 0x5d4 : mword 64) 4
                   = mword_of_int 0x5d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E422.
    iIntros (h5) "Hrun".
    (* THE FRAME WORD STAYS OPEN over the write (lane CAT-WALK, W1): the
       byte just stored is the one the payment reads, so it is lent to
       [kgrep_wb] and the word is closed again only after the call
       returns it. *)
    (* ---- 0x5d8  c.li a2,1 ---- *)
    iApply (wp_uk_cli N h5 m2 (mword_of_int 0x5d8)
              (mword_of_int 1 : mword 6) a2_idx n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_grep_5d8 with "Hcode"). }
    assert (E426 : add_vec_int (mword_of_int 0x5d8 : mword 64) 2
                   = mword_of_int 0x5da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E426.
    iIntros (h6) "Hrun".
    set (m3 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)]> m2).
    assert (Hs03 : m3 !!! Regidx s0_idx = sp0).
    { rewrite <- Hs02.
      exact (upd_ne m2 (Regidx a2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5da  addi a1,s0,-17 ---- *)
    iApply (wp_uk_addi N h6 m3 (mword_of_int 0x5da)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (add_vec (m3 !!! Regidx s0_idx)
                 (sign_extend' 64 (mword_of_int 4079 : mword 12))) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_grep_5da with "Hcode"). }
    assert (E428 : add_vec_int (mword_of_int 0x5da : mword 64) 4
                   = mword_of_int 0x5de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E428.
    iIntros (h7) "Hrun".
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec (m3 !!! Regidx s0_idx)
                         (sign_extend' 64 (mword_of_int 4079 : mword 12)))]> m3).
    (* ---- 0x5de  jal ra,0x502 <write> ---- *)
    iApply (wp_uk_jal N h7 m4 (mword_of_int 0x5de)
              (mword_of_int 2096990 : mword 21) ra_idx
              (mword_of_int GrepSyms.write) (mword_of_int 0x5e2) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hwrite; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_5de with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x5e2 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0x5e2 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- write(fd, sp0-17, 1) -- THE PER-CALL OBLIGATION (lane CAT-WALK,
       W1).  The byte just stored is lent to the payment and comes back in
       its output half; the frame word is closed again below. ---- *)
    assert (Ha0m5 : m5 !!! Regidx a0_idx = m !!! Regidx a0_idx).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a2_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1m2 : m2 !!! Regidx a1_idx = m !!! Regidx a1_idx).
    { rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha2m5 : m5 !!! Regidx a2_idx
                    = (mword_of_int (Z.of_nat 1) : mword 64)).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_eq m2 (Regidx a2_idx) (regval_into_reg _)).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha1m5 : m5 !!! Regidx a1_idx
                    = (mword_of_int (uint sp0 - 17) : mword 64)).
    { rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_eq m3 (Regidx a1_idx) (regval_into_reg _)).
      rewrite Hs03. symmetry.
      apply (umoi_add_i12 sp0 (mword_of_int 4079 : mword 12) (uint sp0 - 17)).
      rewrite Hoff17. lia. }
    assert (Huaddr : uint (mword_of_int (uint sp0 - 17) : mword 64)
                     = uint sp0 - 17).
    { apply uint_moi.
      clear -HR Hlo. rewrite uint_unsigned in Hlo |- *. unfold Z64. lia. }
    iEval (rewrite Ha1m2) in "Hb7".
    iApply ("Hw" $! (mword_of_int (uint sp0 - 17) : mword 64) h8 m5 n
              with "[%] [%] [%] Hcode [$HCi Hb7] Hrun").
    { exact Ha0m5. }
    { exact Ha1m5. }
    { exact Ha2m5. }
    { rewrite Huaddr. iExact "Hb7". }
    iIntros (h9 ret) "[HCo Hb7] Hrun".
    iEval (rewrite Huaddr) in "Hb7".
    (* ...and the frame word is whole again, at SOME value *)
    iDestruct ("Hwbc" with "Hb7") as "Hwb".
    assert (Eret : ret_pc (m5 !!! Regidx ra_idx) = (mword_of_int 0x5e2 : mword 64))
      by (rewrite Hra5; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m6 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)).
    (* every callee-saved register still holds its ENTRY value: the walk
       has written sp, s0, a2, a1, ra, a7 and a0, and of those only sp and
       s0 are callee-saved -- and both are about to be restored *)
    assert (Hsp6 : m6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite /m6 (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) ret
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne _ (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne _ (Regidx a2_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp2. }
    assert (Hcs6 : forall r : mword 5, ucallee_saved_idx r = true ->
                     Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
                     m6 !!! Regidx r = m !!! Regidx r).
    (* NAMED disequalities, and [apply] before [vm_compute].  Written the
       obvious way -- [upd_ne _ (Regidx a0_idx) (Regidx r) ret ltac:(exact
       (ucs_ne r _ Hr ltac:(vm_compute; reflexivity)))] -- the INNER tactic
       runs while [ucs_ne]'s second register is still an evar, so
       [vm_compute] is handed [ucallee_saved_idx ?q = false].  That is the
       "inline [ltac:] in argument position" trap, and it cost two kills at
       41 GB and 49 GB before it was read as one.  [apply] first fixes the
       register from the goal; nothing here is spliced into a term. *)
    { intros r Hr Hrsp Hrs0.
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      assert (Na2 : Regidx r <> Regidx a2_idx)
        by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
      rewrite /m6 (upd_ne (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)
                     (Regidx a0_idx) (Regidx r) ret Na0).
      rewrite (upd_ne m5 (Regidx a7_idx) (Regidx r)
                 (mword_of_int 16 : mword 64) Na7).
      rewrite /m5 (upd_ne m4 (Regidx ra_idx) (Regidx r)
                     (regval_into_reg (mword_of_int 0x5e2 : mword 64)) Nra).
      rewrite /m4 (upd_ne m3 (Regidx a1_idx) (Regidx r)
                     (regval_into_reg
                        (add_vec (m3 !!! Regidx s0_idx)
                           (sign_extend' 64 (mword_of_int 4079 : mword 12)))) Na1).
      rewrite /m3 (upd_ne m2 (Regidx a2_idx) (Regidx r)
                     (regval_into_reg
                        (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)) Na2).
      rewrite /m2 (upd_ne m1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg sp0) Hrs0).
      rewrite /m1 (upd_ne m (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 4))))
                     Hrsp).
      reflexivity. }
    (* ---- 0x5e2  c.ldsp ra,24(sp) ---- *)
    iApply (wp_uk_cldsp N h9 m6 (mword_of_int 0x5e2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 8)
              (m1 !!! Regidx ra_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp32 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_grep_5e2 with "Hcode"). }
    iIntros "Hwra".
    assert (E430 : add_vec_int (mword_of_int 0x5e2 : mword 64) 2
                   = mword_of_int 0x5e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E430.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx ra_idx := regval_into_reg (m1 !!! Regidx ra_idx)]> m6).
    assert (Hsp7 : m7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp6.
      exact (upd_ne m6 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5e4  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp N h10 m7 (mword_of_int 0x5e4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 16)
              (m1 !!! Regidx s0_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp7 Hsp32 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_grep_5e4 with "Hcode"). }
    iIntros "Hws0".
    assert (E432 : add_vec_int (mword_of_int 0x5e4 : mword 64) 2
                   = mword_of_int 0x5e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E432.
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx s0_idx := regval_into_reg (m1 !!! Regidx s0_idx)]> m7).
    assert (Hsp8 : m8 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 4))).
    { rewrite <- Hsp7.
      exact (upd_ne m7 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5e6  c.addi16sp sp,sp,32 -- THE POP: the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up N h11 m8 (mword_of_int 0x5e6)
              (mword_of_int 2 : mword 6) 4 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hwb Hw32] Hrun").
    { iApply (uis_grep_5e6 with "Hcode"). }
    { rewrite Hsp8 Hup.
      iApply (ustack_4_close γd sp0 Hal8 with "[Hwra] [Hws0] Hwb Hw32").
      { iExists (m1 !!! Regidx ra_idx). iExact "Hwra". }
      { iExists (m1 !!! Regidx s0_idx). iExact "Hws0". } }
    assert (E434 : add_vec_int (mword_of_int 0x5e6 : mword 64) 2
                   = mword_of_int 0x5e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp8 Hup E434.
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx csp_rs1 := regval_into_reg sp0]> m8).
    assert (Hra9 : m9 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_eq m6 (Regidx ra_idx) (regval_into_reg _)).
      exact Hra1. }
    (* ---- 0x5e8  c.jr ra ---- *)
    iApply (wp_uk_cjr N h12 m9 (mword_of_int 0x5e8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra9; reflexivity)
              with "[] Hrun").
    { iApply (uis_grep_5e8 with "Hcode"). }
    iIntros (h13) "Hrun".
    iApply ("Hcont" $! h13 m9 with "[] HCo Hrun").
    iPureIntro. intros r Hr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Hrsp | Hrsp].
    { rewrite Hrsp /m9 (upd_eq m8 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity. }
    rewrite /m9 (upd_ne m8 (Regidx csp_rs1) (Regidx r)
                   (regval_into_reg sp0) Hrsp).
    destruct (decide (Regidx r = Regidx s0_idx)) as [Hrs0 | Hrs0].
    { rewrite Hrs0 /m8
        (upd_eq m7 (Regidx s0_idx) (regval_into_reg (m1 !!! Regidx s0_idx))).
      rewrite Hs01. reflexivity. }
    rewrite /m8 (upd_ne m7 (Regidx s0_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx s0_idx)) Hrs0).
    assert (Nra : Regidx r <> Regidx ra_idx)
      by (apply (ucs_ne r _ Hr); vm_compute; reflexivity).
    rewrite /m7 (upd_ne m6 (Regidx ra_idx) (Regidx r)
                   (regval_into_reg (m1 !!! Regidx ra_idx)) Nra).
    exact (Hcs6 r Hr Hrsp Hrs0).
  Qed.


  (* --------------------------------------------------------------------- *)
  (* vprintf's SHARED TAIL @0x882: restore ra, s0, s1; pop the 96-byte      *)
  (* frame; return.  The empty-string arm jumps straight here from 0x65c    *)
  (* -- it never spilled s2..s8, so those nine slots are still whatever the *)
  (* free stack had in them, and the statement says so by taking them as    *)
  (* [∃ w].                                                                  *)
End UkGrepPutc.
