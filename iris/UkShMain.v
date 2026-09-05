(* ===================================================================== *)
(* UkShMain.v -- sh's MAIN BODY, SH LANE STAGE 6: the walk from the       *)
(* blank-line test to the fork, and the two lanes it joins.               *)
(*                                                                        *)
(* [UkSh.v] walks main down to 0x97a and hands the rest over as an        *)
(* abstract continuation, [UkSh.ush_rest]; [UkShParse.v] proves the       *)
(* parser and [UkShRun.v]/[UkShDiag.v] the command-tree runner.  Nothing   *)
(* joined them, and joining them is what this file is: the twenty-odd     *)
(* instructions between the blank-line test and the loop head, plus the   *)
(* SEAM between what the parser BUILDS and what the runner CONSUMES.      *)
(*                                                                        *)
(* WHAT MAIN'S BODY IS, at the pcs the catalog names:                     *)
(*                                                                        *)
(*   0x97a  bne s5,a5   -> 0x92c      buf[k] != 'c'                        *)
(*   0x97e  lbu a5,1(s1)                                                   *)
(*   0x982  bne s3,a5   -> 0x92c      buf[k+1] != 'd'                      *)
(*   0x986  lbu a5,2(s1)                                                   *)
(*   0x98a  bne s6,a5   -> 0x92c      buf[k+2] != ' '                      *)
(*   0x98e..0x9be                     the cd builtin                       *)
(*   0x92c  jal fork1                                                      *)
(*   0x930  c.beqz a0   -> 0x9c0      the CHILD                            *)
(*   0x932  c.li a0,0 ; 0x934 jal wait  ; falls into 0x938, the loop head  *)
(*   0x9c0  c.mv a0,s1 ; 0x9c2 jal parsecmd ; 0x9c6 jal runcmd             *)
(*                                                                        *)
(* THE SEAM.  [UkShParse.ushp_tree] owns its node at [DfracOwn 1] and     *)
(* names the argument vector as INDEX PAIRS into the line;                *)
(* [UkShRun.ush_cmd] reads it at [DfracDiscarded] and names it as         *)
(* [UserHeap.uarg]s -- pointer, length, bytes.  The NUL-CUT the parser    *)
(* publishes is exactly what turns one into the other: a token (i,j)      *)
(* becomes the string at [s0+i] of length [j-i], whose terminator is the  *)
(* zero [nulterminate] wrote at [j].  The conversion DISCARDS, which is   *)
(* what makes the tree persistent and so what lets it cross the fork as a *)
(* [UkFork.Forkable] payload.                                             *)
(*                                                                        *)
(* THE SCOPE, and both halves of it are premises of the theorem rather    *)
(* than assumptions about the kernel:                                     *)
(*                                                                        *)
(*   the line is one the LEXER ACCEPTS -- no symbol byte, fewer than      *)
(*     MAXARGS tokens -- which is stage 4's own scope, and                *)
(*   the line is not a [cd] COMMAND.  sh's cd arm prints its failure with *)
(*     [fprintf] and RETURNS to the loop, so its '%s' argument is the     *)
(*     line buffer, which the loop rewrites; [UkShDiag.shd_str] is        *)
(*     persistent-only, so printing a mutable buffer needs that predicate *)
(*     re-cut at a dfrac.  Until then the arm is REFUTED from the premise *)
(*     at its three byte tests rather than walked.                        *)
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
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require UkLoad.
Require Import UkFork.
Require Import FdSlots UserFd.
Require Import UCodeShK.
Require Import UkSh.
Require Import UCodeShP.
Require Import UkShParse.
Require Import UkShRun.
Require Import UkShDiag.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkShMain.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* the four ghost names a program proof runs at, as every file in the
     lane binds them *)
  Context (γt γd γs γfd : gname).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* ===================================================================== *)
  (* §1 PERSISTING A RUN.                                                   *)
  (*                                                                        *)
  (* [UserHeap.uarea_persist] does this for a MAP; the seam below holds     *)
  (* RUNS, so here are the two run-shaped twins.  They belong beside it     *)
  (* and are local only because moving them rebuilds the tier.              *)
  (* ===================================================================== *)
  Lemma ubytes_persist (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) :
    ubytes g a n f ==∗ ubytesq g DfracDiscarded a n f.
  Proof.
    iIntros "H". rewrite /ubytes /ubytesq.
    iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!>" (i j _) "Hb". rewrite /ubyteq /ubyte.
    iApply (ghost_map_elem_persist with "Hb").
  Qed.

  Lemma uword_persist (g : gname) (a : Z) (w : mword 64) :
    uword g a w ==∗ uwordq g DfracDiscarded a w.
  Proof.
    iIntros "H". rewrite /uword /uwordq.
    iApply (ubytes_persist g a 8 (nth_byte w) with "H").
  Qed.

  Lemma ustr_persist (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) :
    ustr g (DfracOwn 1) a n f ==∗ ustr g DfracDiscarded a n f.
  Proof.
    iIntros "(%Hne & %Hlen & Hbs & Hnul)".
    iMod (ubytes_persist g a n f with "Hbs") as "#Hbs".
    iMod (ghost_map_elem_persist with "Hnul") as "#Hnul".
    iModIntro. iSplitR; [ iPureIntro; exact Hne | ].
    iSplitR; [ iPureIntro; exact Hlen | ].
    iSplitR; [ iExact "Hbs" | iExact "Hnul" ].
  Qed.

  (* ===================================================================== *)
  (* §2 THE TOKEN MODEL, ONE STEP FURTHER: SEPARATION.                      *)
  (*                                                                       *)
  (* [nulterminate] writes a zero at every token's END index, so a token's  *)
  (* BODY is only still readable as a string if no OTHER token's end lands  *)
  (* inside it.  None does, and the reason is the tokenizer's own stopping  *)
  (* rule: a token stops at the end of the line or on a WHITESPACE byte (on *)
  (* a symbol-free line), so the next token starts strictly later.  These   *)
  (* are the two facts that turn the parser's index pairs into strings.     *)
  (* ===================================================================== *)

  (* the byte a token stops on, when it did not run out of line -- the twin
     of [UkShParse.ushp_skipws_end] *)
  Lemma ushp_toklen_end (n i : nat) (f : nat -> bv 8) :
    (ushp_toklen n i f < n)%nat ->
    ushp_is_ws (f (i + ushp_toklen n i f)%nat)
    || ushp_is_sym (f (i + ushp_toklen n i f)%nat) = true.
  Proof.
    revert i. induction n as [| n IH ]; intros i H.
    - cbn [ushp_toklen] in H. lia.
    - cbn [ushp_toklen] in H |- *.
      destruct (ushp_is_ws (f i) || ushp_is_sym (f i)) eqn:Hw.
      + rewrite Nat.add_0_r. exact Hw.
      + assert (E : (i + S (ushp_toklen n (S i) f))%nat
                    = (S i + ushp_toklen n (S i) f)%nat) by lia.
        rewrite E. apply IH. lia.
  Qed.

  (* the fold leaves a byte alone unless some token ends there *)
  Lemma ushp_nulfold_miss (toks : list (nat * nat)) (g : nat -> bv 8) (j : nat) :
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk -> j <> snd tk) ->
    ushp_nulfold toks g j = g j.
  Proof.
    revert g. induction toks as [| tk r IH ]; intros g Hmiss;
      cbn [ushp_nulfold]; [ reflexivity | ].
    rewrite (IH (ushp_setb g (snd tk) ubyte0)).
    - rewrite /ushp_setb.
      destruct (Nat.eqb j (snd tk)) eqn:E; [ | reflexivity ].
      exfalso. apply Nat.eqb_eq in E.
      exact (Hmiss 0%nat tk eq_refl E).
    - intros i t Hi. exact (Hmiss (S i) t Hi).
  Qed.

  (* THE SEPARATION FACT.  On a symbol-free line, a token's end is either
     the end of the line or a whitespace byte, so the NEXT token starts
     strictly after it -- and therefore no token end falls inside another
     token's body. *)
  Lemma ushp_tokens_gap (len : nat) (f : nat -> bv 8) (off : nat)
      (toks : list (nat * nat)) :
    ushp_no_symbols len f ->
    ushp_tokens len f off toks -> (off <= len)%nat ->
    forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
    forall (j : nat) (tk' : nat * nat), toks !! j = Some tk' ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd tk'.
  Proof.
    intros Hns Htoks. revert Hns.
    induction Htoks as [ off Hnil | off toks k n Hn Htoks IH ];
      intros Hns Hoff i tk Hi j tk' Hj x Hx.
    - destruct i; cbn in Hi; discriminate Hi.
    - (* the head's own bounds, and where the rest starts *)
      assert (Hk : (k <= len - off)%nat) by exact (ushp_skipws_le (len - off) off f).
      assert (Hnle : (n <= len - (off + k))%nat)
        by exact (ushp_toklen_le (len - (off + k)) (off + k) f).
      assert (Hrest : forall (q : nat) (t : nat * nat), toks !! q = Some t ->
                (off + k + n <= fst t < snd t /\ snd t <= len)%nat)
        by (intros q t Hq;
            exact (ushp_tokens_in len f (off + k + n)%nat toks Htoks
                     ltac:(lia) q t Hq)).
      destruct i as [| i ]; cbn [lookup] in Hi.
      + (* x is in the HEAD token's body: [off+k, off+k+n) *)
        injection Hi as <-. cbn [fst snd] in Hx.
        destruct j as [| j ]; cbn [lookup] in Hj.
        * injection Hj as <-. cbn [snd]. lia.
        * destruct (Hrest j tk' Hj) as [Hlo _]. lia.
      + (* x is in a LATER token's body, hence at or above [off+k+n] *)
        destruct (Hrest i tk Hi) as [Hlo _].
        destruct j as [| j ]; cbn [lookup] in Hj.
        * (* the head's end is [off+k+n], and every later token starts
             STRICTLY above it: the head stopped on a whitespace byte (the
             line has no symbol), which the next scan skips *)
          injection Hj as <-. cbn [snd].
          assert (Hgap : forall (q : nat) (t : nat * nat),
                    toks !! q = Some t -> (off + k + n < fst t)%nat).
          { intros q t Hq.
            assert (Hlt : (n < len - (off + k))%nat).
            { destruct (Nat.lt_ge_cases n (len - (off + k))) as [Hc | Hc];
                [ exact Hc | exfalso ].
              destruct (Hrest q t Hq) as [Hlo' Hhi']. lia. }
            pose proof (ushp_toklen_end (len - (off + k)) (off + k) f Hlt) as Hstop.
            assert (Hwsb : ushp_is_ws (f (off + k + n)%nat) = true).
            { apply orb_true_iff in Hstop as [Hw | Hsy]; [ exact Hw | exfalso ].
              assert (Hin : (off + k + n < len)%nat) by lia.
              rewrite (Hns (off + k + n)%nat Hin) in Hsy. discriminate Hsy. }
            destruct toks as [| t0 rest ];
              [ destruct q; cbn in Hq; discriminate Hq | ].
            destruct (ushp_tokens_cons_inv len (off + k + n)%nat f t0 rest Htoks)
              as (Hpos & Ht0 & Hrest').
            assert (Hk0 : (0 < ushp_skipws (len - (off + k + n))
                                 (off + k + n) f)%nat).
            { destruct (len - (off + k + n))%nat as [| mm ] eqn:Em.
              - exfalso. destruct (Hrest q t Hq) as [Hlo2 Hhi2]. lia.
              - cbn [ushp_skipws]. rewrite Hwsb. lia. }
            destruct (Hrest 0%nat t0 eq_refl) as [Hlo0 Hhi0].
            rewrite Ht0 in Hlo0, Hhi0. cbn [fst snd] in Hlo0, Hhi0.
            destruct q as [| q' ]; cbn [lookup] in Hq.
            - injection Hq as <-. rewrite Ht0. cbn [fst]. lia.
            - destruct (ushp_tokens_in len f _ rest Hrest' Hhi0 q' t Hq)
                as [Hlo3 _].
              lia. }
          pose proof (Hgap i tk Hi). lia.
        * (* both tokens are in the tail: the induction hypothesis *)
          exact (IH Hns ltac:(lia) i tk Hi j tk' Hj x Hx).
  Qed.

  (* ===================================================================== *)
  (* §3 THE SEAM: the parser's NODE is the runner's TREE.                   *)
  (* ===================================================================== *)

  (* a sub-run of a PERSISTED run -- the discarded twin of                  *)
  (* [UkRunSys.ubytes_split], and easier: a persistent run can be read      *)
  (* wherever it is needed and never has to be given back. *)
  Lemma ubytesq_sub (g : gname) (a : Z) (n : nat) (f : nat -> bv 8)
      (i m : nat) :
    (i + m <= n)%nat ->
    ubytesq g DfracDiscarded a n f -∗
    ubytesq g DfracDiscarded (a + Z.of_nat i) m (fun j => f (i + j)%nat).
  Proof.
    intros Hle. iIntros "#H". rewrite {2}/ubytesq.
    iApply big_sepL_intro. iIntros "!>" (k j Hkj).
    apply lookup_seq in Hkj as [-> Hlt].
    iDestruct (big_sepL_lookup _ (seq 0 n) (i + k)%nat (i + k)%nat with "H")
      as "Hb"; [ apply lookup_seq; lia | ].
    assert (E : (a + Z.of_nat (i + k))%Z = (a + Z.of_nat i + Z.of_nat k)%Z)
      by lia.
    iEval (rewrite E) in "Hb". iExact "Hb".
  Qed.

  (* one byte of a persisted run *)
  Lemma ubytesq_at (g : gname) (a : Z) (n : nat) (f : nat -> bv 8) (i : nat) :
    (i < n)%nat ->
    ubytesq g DfracDiscarded a n f -∗
    ubyteq g DfracDiscarded (a + Z.of_nat i) (f i).
  Proof.
    intros Hi. iIntros "#H".
    iDestruct (big_sepL_lookup _ (seq 0 n) i i with "H") as "Hb";
      [ apply lookup_seq; lia | ]. iExact "Hb".
  Qed.

  (* THE ARGUMENT VECTOR the runner reads, out of the token boundaries the
     parser recorded: a token (i,j) is the string at [s0+i] of length [j-i],
     whose bytes are the line's and whose terminator is the zero
     [nulterminate] wrote at [j]. *)
  Definition ush_args (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat))
      : list uarg :=
    map (fun tk : nat * nat =>
           UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                (fun j : nat => g (fst tk + j)%nat)) toks.

  Lemma ush_args_length (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat)) :
    length (ush_args s0 g toks) = length toks.
  Proof. unfold ush_args. rewrite length_map. reflexivity. Qed.

  Lemma ush_args_lookup (s0 : Z) (g : nat -> bv 8) (toks : list (nat * nat))
      (i : nat) (tk : nat * nat) :
    toks !! i = Some tk ->
    ush_args s0 g toks !! i
    = Some (UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                 (fun j : nat => g (fst tk + j)%nat)).
  Proof. intro Hi. unfold ush_args. rewrite list_lookup_fmap Hi. reflexivity. Qed.

  (* THE CONVERSION.  Everything the runner's tree names is built here out
     of the parser's node and the NUL-cut line, and every byte of it is
     DISCARDED on the way -- which is what makes the tree persistent, hence
     what lets it cross the fork as a payload. *)
  Lemma ush_cmd_of_ushp (s0 p : Z) (len : nat) (f : nat -> bv 8)
      (toks : list (nat * nat)) :
    ushp_tokens len f 0 toks ->
    ushp_no_symbols len f ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 -> 0 < p < 2 ^ 38 ->
    ushp_tree γd s0 p (UshpExec toks) -∗
    ubytes γd s0 (S len) (ushp_nulfold toks (ushp_ext len f)) ==∗
    ush_cmd γd p (UExec (ush_args s0 (ushp_nulfold toks (ushp_ext len f)) toks)).
  Proof.
    intros Htoks Hns Hnn Hlen31 Hs0 Hs0hi Hp.
    set (g := ushp_nulfold toks (ushp_ext len f)).
    iIntros "Hnode Hline".
    iMod (ubytes_persist γd s0 (S len) g with "Hline") as "#Hline".
    iDestruct "Hnode" as "(%Hlt10 & %Hp0 & %Hp8 & [Hty _] & Hargv & _)".
    iMod (ubytes_persist γd p 4 _ with "Hty") as "#Hty".
    (* ---- the ten argv slots, persisted down to the ones that matter ---- *)
    assert (E10 : (10 = S (length toks) + (10 - S (length toks)))%nat) by lia.
    rewrite E10 seq_app big_sepL_app.
    iDestruct "Hargv" as "[Hargv _]".
    iAssert (|==> [∗ list] i ∈ seq 0 (S (length toks)),
               uwordq γd DfracDiscarded (p + 8 + 8 * Z.of_nat i)
                 (mword_of_int (match toks !! i with
                                | Some tk => s0 + Z.of_nat (fst tk)
                                | None => 0
                                end)))%I with "[Hargv]" as ">#Hargv".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "Hargv").
      iIntros "!>" (i j Hij) "Hs".
      apply lookup_seq in Hij as [Hje Hlt].
      rewrite Nat.add_0_l in Hje. subst j.
      rewrite /ushp_slot.
      destruct (toks !! i) as [tk |] eqn:Etk.
      - iApply (uword_persist with "Hs").
      - rewrite (bool_decide_eq_true_2 (i = length toks)).
        + iApply (uword_persist with "Hs").
        + apply lookup_ge_None_1 in Etk. lia. }
    (* ---- every token, as a string ---- *)
    iAssert ([∗ list] x ∈ ush_args s0 g toks, ush_str γd x)%I as "#Hstrs".
    { rewrite /ush_args big_sepL_fmap.
      iApply big_sepL_intro. iIntros "!>" (i tk Hi).
      rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes fst snd].
      assert (H0len : (0 <= len)%nat) by lia.
      destruct (ushp_tokens_in len f 0%nat toks Htoks H0len i tk Hi)
        as [Hlo Hhi].
      iSplitR; [ iPureIntro; lia | ].
      (* the body: inside the line, and untouched by the NUL cut *)
      assert (Hbody : forall j : nat, (j < snd tk - fst tk)%nat ->
                g (fst tk + j)%nat <> ubyte0).
      { intros j Hj.
        assert (Hin : (fst tk <= fst tk + j < snd tk)%nat) by lia.
        assert (Hmiss : forall (q : nat) (t : nat * nat),
                  toks !! q = Some t -> (fst tk + j)%nat <> snd t).
        { intros q t Hq.
          assert (H0 : (0 <= len)%nat) by lia.
          exact (ushp_tokens_gap len f 0%nat toks Hns Htoks H0
                   i tk Hi q t Hq (fst tk + j)%nat Hin). }
        rewrite /g (ushp_nulfold_miss toks (ushp_ext len f) (fst tk + j)%nat
                      Hmiss).
        rewrite /ushp_ext.
        assert (Hlt : ((fst tk + j) < len)%nat) by lia.
        rewrite (bool_decide_eq_true_2 _ Hlt).
        apply Hnn. exact Hlt. }
      iSplitR; [ iPureIntro; exact Hbody | ].
      iSplitR; [ iPureIntro; lia | ].
      iSplitL.
      - (* the bytes *)
        iDestruct (ubytesq_sub γd s0 (S len) g (fst tk) (snd tk - fst tk)%nat
                     ltac:(lia) with "Hline") as "Hb". iExact "Hb".
      - (* the terminator, which is the zero [nulterminate] wrote *)
        iDestruct (ubytesq_at γd s0 (S len) g (snd tk) ltac:(lia) with "Hline")
          as "Hb".
        assert (Eg : g (snd tk) = ubyte0)
          by (rewrite /g; exact (ushp_nulfold_hit toks (ushp_ext len f) i tk Hi)).
        rewrite Eg.
        assert (Ea : (s0 + Z.of_nat (snd tk))%Z
                     = (s0 + Z.of_nat (fst tk) + Z.of_nat (snd tk - fst tk))%Z)
          by lia.
        iEval (rewrite Ea) in "Hb". iExact "Hb". }
    (* ---- assemble ---- *)
    iModIntro. rewrite /ush_cmd.
    iSplitR; [ iPureIntro; lia | ].
    iSplitR; [ iPureIntro; exact Hp8 | ].
    iSplitR.
    { (* the type word: EXEC is 1 *)
      rewrite /ush_w32. iExact "Hty". }
    iSplit.
    { (* the vector *)
      rewrite /uargv.
      iSplit; [ iPureIntro; rewrite Zplus_mod Hp8; reflexivity | ].
      iSplit; [ iPureIntro; rewrite ush_args_length; lia | ].
      iApply big_sepL_intro. iIntros "!>" (i x Hi).
      (* the element is the token's image, so its fields are the token's *)
      assert (Htk : exists tk : nat * nat,
                toks !! i = Some tk /\
                x = UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                         (fun j : nat => g (fst tk + j)%nat)).
      { unfold ush_args in Hi. rewrite list_lookup_fmap in Hi.
        destruct (toks !! i) as [tk |] eqn:Etk; [ | discriminate Hi ].
        injection Hi as <-. exists tk. split; [ reflexivity | reflexivity ]. }
      destruct Htk as (tk & Hi' & ->).
      cbn [ua_ptr ua_len ua_bytes].
      iSplit.
      - iDestruct (big_sepL_lookup _ (seq 0 (S (length toks))) i i with "Hargv")
          as "Hw"; [ apply lookup_seq;
                     pose proof (lookup_lt_Some toks i tk Hi'); lia | ].
        rewrite Hi'. iExact "Hw".
      - iDestruct (big_sepL_lookup _ (ush_args s0 g toks) i
                     (UArg (s0 + Z.of_nat (fst tk)) (snd tk - fst tk)%nat
                           (fun j : nat => g (fst tk + j)%nat)) with "Hstrs")
          as "Hs"; [ exact (ush_args_lookup s0 g toks i tk Hi') | ].
        rewrite /ush_str. iDestruct "Hs" as "[_ Hs]".
        cbn [ua_ptr ua_len ua_bytes]. iExact "Hs". }
    iSplit; [ | iExact "Hstrs" ].
    (* the NULL cap, at the slot just past the last token *)
    rewrite /ush_ptr ush_args_length.
    iDestruct (big_sepL_lookup _ (seq 0 (S (length toks)))
                 (length toks) (length toks) with "Hargv") as "Hw";
      [ apply lookup_seq; lia | ].
    rewrite (lookup_ge_None_2 toks (length toks) ltac:(lia)).
    iExact "Hw".
  Qed.

End UkShMain.
