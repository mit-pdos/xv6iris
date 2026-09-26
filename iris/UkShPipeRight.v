(* ===================================================================== *)
(* UkShPipeRight.v -- THE RIGHT COMMAND'S PARSE IS THE LANDED ONE,        *)
(* lane SH-PARSE-PIPE part 2 (design/app-pipe.md SS5.1).                   *)
(*                                                                        *)
(* THE FINDING, and it replaces a 1,600-line copy with forty lines: the    *)
(* pipe line's RIGHT command needs NO new walk at all.                     *)
(*                                                                        *)
(* [parsepipe]'s turn calls [parsepipe] again on the rest of the line, and *)
(* that recursive call runs entirely ABOVE the '|'.  A SUFFIX OF A [ustr]  *)
(* IS A [ustr] -- the suffix's bytes are non-NUL because the whole         *)
(* string's are, and the terminator it needs is the whole string's own --  *)
(* so the recursive call can be given the line's own suffix at base        *)
(* [s0 + (p + 2)], where the line IS symbol-free ([ushq_pipe_nosym_from]). *)
(* Then it is [UkShParseCmd.wp_kshp_parsepipe], the LANDED symbol-free     *)
(* walk, applied once: no re-statement, no second copy of [parseexec],     *)
(* and nothing about the right-hand side is new mathematics.               *)
(*                                                                        *)
(* Three small things make that work, and they are the file:               *)
(*                                                                        *)
(*   S1 [ustr_split] -- the suffix accessor, with the prefix bytes handed  *)
(*      out and a wand to put them back.  [ubytesq_app] is                 *)
(*      [UserHeap.ubytes_app] at an arbitrary [dfrac] (its proof never     *)
(*      mentioned the fraction).                                          *)
(*   S2 the two pure re-basings the landed premises are stated at:         *)
(*      [ushq_nosym_shift] (no symbol at or above the cursor becomes       *)
(*      symbol-free at the shifted base) and [ushq_toks_right] (the right  *)
(*      command is ONE token of the suffix, measured by the same two       *)
(*      scans).                                                           *)
(*   S3 [ushp_exec_at_rebase] -- the node the recursive call builds names  *)
(*      its argv by ABSOLUTE addresses, so the same resource is the node   *)
(*      of the shifted token list at the LINE's base.  That is what lets   *)
(*      [UkShPipeSeam.ush_cmd_of_ushp_pipe] take both sides at one [s0].   *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShPipeLex.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §2a THE PURE RE-BASINGS (no Iris; stated here, beside their one use)    *)
(* ===================================================================== *)

Lemma ushq_nosym_shift (len : nat) (f : nat -> bv 8) (c : nat) :
  ushq_nosym_from len f c ->
  ushp_no_symbols (len - c)%nat (fun j : nat => f (c + j)%nat).
Proof using.
  intros H j Hj. cbn beta. exact (H (c + j)%nat ltac:(lia)).
Qed.

(* the right command is ONE token of the suffix: no leading blank (the
   cursor gettoken left is the word's first byte), the word itself, and
   then the newline the line ends with *)
Lemma ushq_toks_right (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e ->
  ushp_tokens (len - S (S p))%nat (fun j : nat => f (S (S p) + j)%nat)
    0%nat [(0%nat, (e - S (S p))%nat)].
Proof using.
  intro Hq. pose proof Hq as HQ.
  destruct HQ as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  set (c := S (S p)) in *.
  set (g := fun j : nat => f (c + j)%nat).
  (* the suffix's bytes, by index, in the two classes the scans read *)
  assert (Hgws : forall z : nat, (e <= c + z < len)%nat ->
            ushp_is_ws (g z) = true)
    by (intros z Hz; unfold g; exact (Htail (c + z)%nat ltac:(lia))).
  assert (Hgnw : forall z : nat, (c <= c + z < e)%nat ->
            ushp_is_ws (g z) = false /\ ushp_is_sym (g z) = false)
    by (intros z Hz; unfold g;
        exact (ushq_pipe_right_byte len f p e (c + z)%nat Hq ltac:(lia))).
  (* the blank scan at the word's first byte does not move *)
  assert (Hsk0 : ushp_skipws (len - c - 0)%nat 0%nat g = 0%nat).
  { apply ushp_skipws_stop. exact (proj1 (Hgnw 0%nat ltac:(lia))). }
  (* the token is the word *)
  assert (Htok : ushp_toklen (len - c - 0)%nat 0%nat g = (e - c)%nat).
  { apply (ushs_toklen_exact (len - c - 0)%nat 0%nat (e - c)%nat g).
    - lia.
    - intros j Hj. exact (Hgnw j ltac:(lia)).
    - left. apply Hgws. lia. }
  (* ...and past it, blanks to the end of the line *)
  assert (Hend : ((e - c)
                  + ushp_skipws (len - c - (e - c))%nat (e - c)%nat g)%nat
                 = (len - c)%nat).
  { assert (Hs : ushp_skipws (len - c - (e - c))%nat (e - c)%nat g
                 = (len - c - (e - c))%nat).
    { apply (ushs_skipws_exact (len - c - (e - c))%nat (e - c)%nat
               (len - c - (e - c))%nat g).
      - lia.
      - intros j Hj. apply Hgws. lia.
      - left. reflexivity. }
    rewrite Hs. lia. }
  (* ...which is ONE [ushs_toks] step at the terminator [len - c], and the
     landed [ushp_tokens] is that at [stop = len] ([ushs_toks_tokens]) *)
  apply ushs_toks_tokens.
  apply (ushs_toks_cons' (len - c)%nat (len - c)%nat g 0%nat (e - c)%nat []).
  - exact Hsk0.
  - exact Htok.
  - lia.
  - apply ushs_toks_nil'. exact Hend.
Qed.

(* the token list, shifted back to the LINE's own base *)
Definition ushq_shift (c : nat) (toks : list (nat * nat)) : list (nat * nat) :=
  map (fun tk : nat * nat => ((c + fst tk)%nat, (c + snd tk)%nat)) toks.

Lemma ushq_shift_length (c : nat) (toks : list (nat * nat)) :
  length (ushq_shift c toks) = length toks.
Proof using. unfold ushq_shift. rewrite length_map. reflexivity. Qed.

Lemma ushq_shift_lookup (c : nat) (toks : list (nat * nat)) (i : nat) :
  ushq_shift c toks !! i
  = (fun tk : nat * nat => ((c + fst tk)%nat, (c + snd tk)%nat)) <$> toks !! i.
Proof using. unfold ushq_shift. apply list_lookup_fmap. Qed.

Lemma ushq_shift_right (p e : nat) :
  (S (S p) <= e)%nat ->
  ushq_shift (S (S p)) [(0%nat, (e - S (S p))%nat)] = [(S (S p), e)].
Proof using.
  intro Hle. unfold ushq_shift. cbn [map fst snd].
  rewrite Nat.add_0_r. f_equal. f_equal. lia.
Qed.


Section UkShPipeRight.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_slot := (UkShParse.ushp_slot N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).

  Local Notation wp_kshp_parsepipe :=
    (UkShParseCmd.wp_kshp_parsepipe N UMalloc UMalloc' ushp_malloc_ok).

  (* ===================================================================== *)
  (* §1 A SUFFIX OF A [ustr] IS A [ustr]                                    *)
  (* ===================================================================== *)

  (* [UserHeap.ubytes_app] at an arbitrary fraction: its proof is
     [seq_app] and [big_sepL_app] and never mentioned the [dfrac]. *)
  Lemma ubytesq_app (dq : dfrac) (a : Z) (k n : nat) (f : nat -> bv 8) :
    ubytesq γd dq a (k + n) f ⊣⊢
    ubytesq γd dq a k f ∗
    ubytesq γd dq (a + Z.of_nat k) n (fun j : nat => f (k + j)%nat).
  Proof using .
    rewrite /ubytesq seq_app big_sepL_app.
    apply bi.sep_proper; [ reflexivity | ].
    replace (seq (0 + k) n) with (Nat.add k <$> seq 0 n)
      by (rewrite fmap_add_seq; f_equal; lia).
    rewrite big_sepL_fmap.
    apply big_opL_proper. intros i j _.
    assert (E : (a + Z.of_nat (k + j))%Z = (a + Z.of_nat k + Z.of_nat j)%Z)
      by lia.
    rewrite E. reflexivity.
  Qed.

  (* THE ACCESSOR.  The prefix comes out as bare bytes -- it has no
     terminator of its own -- and the suffix comes out as a STRING, whose
     terminator is the whole string's.  The closing wand carries the two
     pure facts, which the pieces cannot reconstruct. *)
  Lemma ustr_split (dq : dfrac) (a : Z) (len k n : nat) (f : nat -> bv 8) :
    len = (k + n)%nat ->
    ustr γd dq a len f -∗
    ubytesq γd dq a k f ∗
    ustr γd dq (a + Z.of_nat k) n (fun j : nat => f (k + j)%nat) ∗
    (ubytesq γd dq a k f -∗
     ustr γd dq (a + Z.of_nat k) n (fun j : nat => f (k + j)%nat) -∗
     ustr γd dq a len f).
  Proof using .
    intros ->. iIntros "(%Hnn & %Hlen & Hbs & Hnul)".
    assert (Enul : (a + Z.of_nat k + Z.of_nat n)%Z
                   = (a + Z.of_nat (k + n))%Z) by lia.
    rewrite (ubytesq_app dq a k n f).
    iDestruct "Hbs" as "[Hpre Hsuf]".
    iSplitL "Hpre"; [ iExact "Hpre" | ].
    iSplitL "Hsuf Hnul".
    - iSplitR;
        [ iPureIntro; intros j Hj; exact (Hnn (k + j)%nat ltac:(lia)) | ].
      iSplitR; [ iPureIntro; lia | ].
      iSplitL "Hsuf"; [ iExact "Hsuf" | ].
      rewrite Enul. iExact "Hnul".
    - iIntros "Hpre (_ & _ & Hsuf & Hnul)".
      iSplitR; [ iPureIntro; exact Hnn | ].
      iSplitR; [ iPureIntro; exact Hlen | ].
      iSplitL "Hpre Hsuf".
      + rewrite (ubytesq_app dq a k n f).
        iSplitL "Hpre"; [ iExact "Hpre" | iExact "Hsuf" ].
      + rewrite <- Enul. iExact "Hnul".
  Qed.

  (* ===================================================================== *)
  (* §3 THE NODE, AT THE LINE'S BASE                                        *)
  (*                                                                        *)
  (* [ushp_slot] stores an ABSOLUTE address, so a node built at a shifted   *)
  (* base IS the node of the shifted token list at the original one -- the  *)
  (* resource does not move, only its reading.                             *)
  (* ===================================================================== *)

  Lemma ushp_exec_at_rebase (s0 : Z) (c : nat) (q : Z)
      (toks : list (nat * nat)) :
    ushp_exec_at (s0 + Z.of_nat c) q toks -∗
    ushp_exec_at s0 q (ushq_shift c toks).
  Proof using .
    iIntros "(%Hlt & %Hq0 & %Hq8 & Hty & Hargv & Heargv)".
    iSplitR; [ iPureIntro; rewrite ushq_shift_length; exact Hlt | ].
    iSplitR; [ iPureIntro; exact Hq0 | ].
    iSplitR; [ iPureIntro; exact Hq8 | ].
    iSplitL "Hty".
    { rewrite /ushp_type_at. cbn [UkShParse.ushp_ty]. iExact "Hty". }
    iSplitL "Hargv".
    - iApply (big_sepL_mono with "Hargv"). intros i j _.
      rewrite /ushp_slot ushq_shift_lookup.
      destruct (toks !! j) as [tk |] eqn:Etk; cbn [fmap option_fmap].
      + cbn [fst snd].
        assert (E : (s0 + Z.of_nat c + Z.of_nat (fst tk))%Z
                    = (s0 + Z.of_nat (c + fst tk))%Z) by lia.
        rewrite E. reflexivity.
      + rewrite ushq_shift_length. reflexivity.
    - iApply (big_sepL_mono with "Heargv"). intros i j _.
      rewrite /ushp_slot ushq_shift_lookup.
      destruct (toks !! j) as [tk |] eqn:Etk; cbn [fmap option_fmap].
      + cbn [fst snd].
        assert (E : (s0 + Z.of_nat c + Z.of_nat (snd tk))%Z
                    = (s0 + Z.of_nat (c + snd tk))%Z) by lia.
        rewrite E. reflexivity.
      + rewrite ushq_shift_length. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §4 THE RIGHT COMMAND'S PARSE, IN THE PIPE LINE'S OWN COORDINATES       *)
  (*                                                                        *)
  (* It LOOKS like a walk of the recursive [parsepipe] call and it is one    *)
  (* application of the landed symbol-free walk.  The premises are the pipe *)
  (* line's ([ushq_pipe]) and the cursor is where [gettoken] left it after   *)
  (* the '|' ([ushq_gettok_fin_bar] = [S (S p)]).                            *)
  (* ===================================================================== *)

  (* THE LAST STAGE OF A PIPELINE OF ANY LENGTH (lane PIPES-C3): the same
     one application of the landed symbol-free walk, at ANY cursor [c]
     above which the line is symbol-free and at ANY token list of the
     suffix.  [wp_kshp_parsepipe_right] below is the one-bar line's
     instance: the cursor after its '|' and its one word. *)
  Lemma wp_kshp_parsepipe_tail {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len c : nat) (f : nat -> bv 8)
      (toks : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    (c <= len)%nat ->
    ushq_nosym_from len f c ->
    ushp_tokens (len - c) (fun j : nat => f (c + j)%nat) 0%nat toks ->
    (length toks < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat c)) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    ushp_oom Pex (18 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe) (6 + (16 + (24 + nn))) -∗
    (∀ q : Z,
       ⌜ q + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 q (ushq_shift c toks) -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int q ⌝ -∗
           UMalloc' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + nn))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Hcle Hns Htoks Htlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    (* the line's SUFFIX, at the base the cursor is at *)
    iDestruct (ustr_split dq s0 len c (len - c)%nat f ltac:(lia) with "Hstr")
      as "(Hpre & Hsuf & Hcl)".
    assert (Ea1 : (s0 + Z.of_nat c + Z.of_nat (len - c))%Z
                  = (s0 + Z.of_nat len)%Z) by lia.
    assert (Ew0 : (s0 + Z.of_nat c + Z.of_nat 0%nat)%Z
                  = (s0 + Z.of_nat c)%Z) by lia.
    iApply (wp_kshp_parsepipe h m dq dw dv ps (s0 + Z.of_nat c)
              (len - c)%nat 0%nat (fun j : nat => f (c + j)%nat)
              (mword_of_int (s0 + Z.of_nat c)) toks nn
              Ha0
              ltac:(rewrite Ha1; f_equal; lia)
              ltac:(lia)
              ltac:(rewrite Ew0; reflexivity)
              (ushq_nosym_shift len f c Hns)
              Htoks Htlen
              ltac:(lia) ltac:(lia) Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hsuf Hws Hsy HM Hpx Hpay Hrun").
    iIntros (q) "%Hqsz Hnode Hcur Hsuf Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM' Hpay Hrun".
    iDestruct ("Hcl" with "Hpre Hsuf") as "Hstr".
    iDestruct (ushp_exec_at_rebase s0 c q toks with "Hnode") as "Hnode".
    rewrite Ea1.
    iApply ("Hcont" $! q with "[] Hnode Hcur Hstr Hws Hsy [] [] HM' Hpay Hrun").
    - iPureIntro. exact Hqsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  Lemma wp_kshp_parsepipe_right {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len p e : nat) (f : nat -> bv 8)
      (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f p e ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat (S (S p)))) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UMalloc -∗
    ushp_oom Pex (18 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe) (6 + (16 + (24 + nn))) -∗
    (∀ q : Z,
       ⌜ q + 168 < Z64 ⌝ -∗
       ushp_exec_at s0 q [(S (S p), e)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int q ⌝ -∗
           UMalloc' -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + nn))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    intros Ha0 Ha1 Hq Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun Hcont".
    assert (Hcle : (S (S p) <= len)%nat)
      by (destruct Hq as (_ & _ & _ & _ & H1 & H2 & _); lia).
    assert (Hele : (S (S p) <= e)%nat)
      by (destruct Hq as (_ & _ & _ & _ & H1 & _); lia).
    iApply (wp_kshp_parsepipe_tail h m dq dw dv ps s0 len (S (S p)) f
              [(0%nat, (e - S (S p))%nat)] nn
              Ha0 Ha1 Hcle (ushq_pipe_nosym_from len f p e Hq)
              (ushq_toks_right len f p e Hq) ltac:(cbn [length]; lia)
              Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
    iIntros (q) "%Hqsz Hnode".
    rewrite (ushq_shift_right p e Hele).
    iApply ("Hcont" $! q with "[] Hnode"). iPureIntro. exact Hqsz.
  Qed.

End UkShPipeRight.
