(* ===================================================================== *)
(* UkShCat.v -- LANE EXEC-CAT, THE (W) HALF: sh's EXEC arm at the ONE     *)
(* command the PIPE line's right side spells, `cat`, and the PINNED exec  *)
(* supply it runs on.                                                     *)
(*                                                                        *)
(* [UkShEcho.v] is the mould end to end.  Three things differ, and they   *)
(* are ALL of them:                                                       *)
(*                                                                        *)
(*  1. THE COMMAND IS ONE TOKEN, NOT A WORD LIST.  The pipe line's right  *)
(*     command is [UExec (UkShMain.ush_args s0 G [(S (S gp), ge)])] --    *)
(*     [UShPipeChild.wp_kshm_child_pipe_paid]'s right-child continuation, *)
(*     verbatim -- so nothing here is indexed by a [list (list (bv 8))]   *)
(*     and no [LineWords.wl_off] appears.  The token's BASE is a          *)
(*     parameter [a] (echo's is 0, [UkShEcho.echo_off_0]); everything     *)
(*     the arm reads of the command is [cat_argv_bytes a b g] below.      *)
(*                                                                        *)
(*  2. AND SO [EchoDisc.line_ok] IS NOT AVAILABLE, AND MUST NOT BE.       *)
(*     [line_ok ws] says word 0 is "echo" AND [2 <= length ws]; cat's     *)
(*     line is the single word "cat".  That is not a matter of taste --   *)
(*     see section 6: the landed (E) half [UCatPipe.pcat_image_entry]     *)
(*     takes [line_ok ws] AND [length ws = 1] and those two are JOINTLY   *)
(*     UNSATISFIABLE, so the lemma is vacuous.  Nothing in this file      *)
(*     mentions [line_ok].                                                *)
(*                                                                        *)
(*  3. THE EXEC-FAILED DIAGNOSTIC PRINTS "cat", NOT "echo".               *)
(*     [UkShDiag.wp_kshd_execfail_paid] is stated at [ua_len x = 4] and   *)
(*     [ua_bytes x j = EchoDisc.cmd_echo !!! j], and its law is fixed at  *)
(*     [ush_execfail_law_at alt_execfail 17].  Section 3 below is that    *)
(*     walk with the COMMAND NAME and the alternative as parameters --    *)
(*     a new lemma in a new file, not a move of the landed one -- and     *)
(*     [PipeDisc.alt_execR] ("exec cat failed\n$ ") is its instance at    *)
(*     [cmd := UkShPipeLex.ushq_cat], index [13 + 3 = 16].                *)
(*                                                                        *)
(* WHAT IS NOT DUPLICATED.  [UkShEcho.wp_kshr_exec_at_cwd_holds] -- the   *)
(* three-instruction exec stub at an INDEXED deposit -- names no command  *)
(* and is applied here verbatim.                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UkRunExecRef.
Require Import UkRunMem.
Require Import FdSlots UserFd UserCwd UserChildren.
Require Import PipeNames.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShParseSym.
Require Import UkShRedirSeam.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShDiagAt.        (* the diagnostic at any command name (moved from here) *)
Require Import UkShMain.
Require Import UkShEcho.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import UkShPipeLex.
Require Import FsImg.
Require Import UexecSG.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(* S1  THE RIGHT COMMAND, AS A VALUE.                                     *)
(*                                                                        *)
(* [UkShPipeLex.ush_line_toks_holds_pipe]'s fifth conjunct: the right     *)
(* command's token list is the SINGLETON                                  *)
(*   [(length (wl_body ws) + 3, length (wl_body ws) + 3 + length right)]  *)
(* and [UShPipeChild.wp_kshm_child_pipe_paid] hands the right child       *)
(* [UExec (ush_args s0 G [(S (S gp), ge)])] at that pair.  So the         *)
(* command below is that node at an ABSTRACT token [(a, b)], and the      *)
(* pipeline's is the instance at [right := ushq_cat] (three bytes).       *)
(* ===================================================================== *)

(* the command name the pipeline's right side spells, and its length *)
Definition cmd_cat : list (bv 8) := UkShPipeLex.ushq_cat.

Lemma cmd_cat_len : length cmd_cat = 3%nat.
Proof using . exact UkShPipeLex.ushq_cat_len. Qed.

Definition cat_toks (a b : nat) : list (nat * nat) := [(a, b)].

Definition cat_cmd (a b : nat) (s0 : Z) (g : nat -> bv 8) : ushcmd :=
  UExec (UkShMain.ush_args s0 g (cat_toks a b)).

Lemma cat_cmd_simple (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  ush_simple (cat_cmd a b s0 g).
Proof using . exact I. Qed.

Lemma cat_cmd_ht (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  ush_ht (cat_cmd a b s0 g) = 1%nat.
Proof using . reflexivity. Qed.

Lemma cat_cmd_args_length (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  length (UkShMain.ush_args s0 g (cat_toks a b)) = 1%nat.
Proof using . rewrite UkShMain.ush_args_length. reflexivity. Qed.

(* ---- the argv BYTES, as a pure premise ------------------------------ *)
(* [UkShEcho.echo_argv_bytes] at the one token: the command's three bytes
   are "cat" and the cut's NUL sits at the token's end.  The LENGTH
   equation is a CONJUNCT and not a side premise, on [EchoDisc.line_ok]'s
   own pattern -- a reading that carried the bytes but left [b] free could
   be satisfied at a [b] the walk cannot use. *)
Definition cat_argv_bytes (a b : nat) (g : nat -> bv 8) : Prop :=
  b = (a + length cmd_cat)%nat
  /\ (forall j : nat, (j < length cmd_cat)%nat ->
        g (a + j)%nat = cmd_cat !!! j)
  /\ g b = ubyte0.

Lemma cat_argv_bytes_end (a b : nat) (g : nat -> bv 8) :
  cat_argv_bytes a b g -> b = (a + 3)%nat.
Proof using .
  intros (Hb & _ & _). rewrite Hb cmd_cat_len. reflexivity.
Qed.

Lemma cat_toks_lookup (a b : nat) :
  cat_toks a b !! 0%nat = Some (a, b).
Proof using . reflexivity. Qed.

Lemma cat_cmd_args_lookup (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  b = (a + 3)%nat ->
  UkShMain.ush_args s0 g (cat_toks a b) !! 0%nat
  = Some (UArg (s0 + Z.of_nat a) 3%nat (fun j : nat => g (a + j)%nat)).
Proof using .
  intro Hb.
  rewrite (UkShMain.ush_args_lookup s0 g (cat_toks a b) 0%nat (a, b)
             (cat_toks_lookup a b)).
  cbn [fst snd]. rewrite Hb.
  replace (a + 3 - a)%nat with 3%nat by lia. reflexivity.
Qed.

(* ---- the pipe line's own cut satisfies the reading ------------------- *)
(* [UkShPipeRound.ushq_cut_ok_right]'s twin on the BYTE side: the cut
   [nulterminate]'s PIPE row leaves is transparent inside the right
   command's word (every argument token of the LEFT command ends below the
   '|', which is below the right word's base) and is the terminator at its
   end.  Spelled at [UkShParseCmd]'s fold so that this file does not
   depend on [UkShPipeRound]. *)
Lemma cat_argv_bytes_of_cut (len : nat) (f : nat -> bv 8) (gp ge : nat)
    (args : list (nat * nat)) :
  UkShPipeLex.ushq_pipe len f gp ge ->
  ushs_toks len f gp 0%nat args ->
  ge = (S (S gp) + 3)%nat ->
  (forall j : nat, (j < 3)%nat -> f (S (S gp) + j)%nat = cmd_cat !!! j) ->
  cat_argv_bytes (S (S gp)) ge
    (UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
       (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f))).
Proof using .
  intros Hpq Htoks Hge Hbytes.
  (* the left command's tokens all end at or below the '|' *)
  assert (Hbelow : forall (i : nat) (tk : nat * nat),
            args !! i = Some tk -> (snd tk <= gp)%nat).
  { intros i tk Hi.
    assert (Hgl : (gp < len)%nat)
      by exact (UkShPipeLex.ushq_pipe_lt len f gp ge Hpq).
    destruct (ushp_tokens_in gp f 0%nat args
                (UkShRedirSeam.ushs_toks_below len gp f 0%nat args
                   ltac:(lia) ltac:(lia) Htoks) ltac:(lia) i tk Hi)
      as [ _ Hhi ]. lia. }
  assert (Hge_lt : (ge < len)%nat)
    by (destruct Hpq as (_ & _ & _ & _ & _ & Hhi & _ & _); exact Hhi).
  split_and!.
  - rewrite cmd_cat_len. lia.
  - intros j Hj. rewrite cmd_cat_len in Hj.
    (* the outer fold misses every index below [ge] *)
    cbn [UkShParseCmd.ushp_nulfold snd].
    rewrite /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq (S (S gp) + j) ge) ltac:(lia)).
    rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
               (S (S gp) + j)%nat
               ltac:(intros q t Hq; pose proof (Hbelow q t Hq); lia)).
    rewrite /UkShParseCmd.ushp_ext
      (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
    exact (Hbytes j Hj).
  - cbn [UkShParseCmd.ushp_nulfold snd].
    rewrite /UkShParseCmd.ushp_setb Nat.eqb_refl. reflexivity.
Qed.

Section UkShCat.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  THE NODE, ADDRESSED.  [UkShEcho]'s three accessors at the one       *)
  (*  token; everything is [DfracDiscarded] and so free to take.          *)
  (* =================================================================== *)
  Lemma cat_cmd_str (a b : nat) (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    b = (a + 3)%nat ->
    ush_cmd gd t (cat_cmd a b s0 g) -∗
    ⌜ 0 < s0 + Z.of_nat a < 2 ^ 38 ⌝ ∗
    ustr gd DfracDiscarded (s0 + Z.of_nat a) 3%nat
      (fun j : nat => g (a + j)%nat).
  Proof using .
    intro Hb. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & _ & #Hs)".
    iDestruct (big_sepL_lookup _ (UkShMain.ush_args s0 g (cat_toks a b)) 0%nat _
                 (cat_cmd_args_lookup a b s0 g Hb) with "Hs") as "#Hx".
    rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
    iDestruct "Hx" as "[%Hr #Hstr]".
    iSplit; [ iPureIntro; exact Hr | iExact "Hstr" ].
  Qed.

  Lemma cat_cmd_word (a b : nat) (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    b = (a + 3)%nat ->
    ush_cmd gd t (cat_cmd a b s0 g) -∗
    uwordq gd DfracDiscarded (t + 8) (mword_of_int (s0 + Z.of_nat a)).
  Proof using .
    intro Hb. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(#Hv & _ & _)".
    iDestruct (uargv_acc gd (t + 8) (UkShMain.ush_args s0 g (cat_toks a b))
                 0%nat _ (cat_cmd_args_lookup a b s0 g Hb) with "Hv")
      as "[[#Hw _] _]".
    cbn [ua_ptr].
    assert (E : t + 8 + 8 * Z.of_nat 0%nat = t + 8) by lia.
    iEval (rewrite E) in "Hw". iExact "Hw".
  Qed.

  Lemma cat_cmd_cap (a b : nat) (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (cat_cmd a b s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8) (mword_of_int 0).
  Proof using .
    iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & #Hn & _)".
    rewrite /ush_ptr cat_cmd_args_length.
    assert (E : t + 8 + 8 * Z.of_nat 1%nat = t + 8 + 8) by lia.
    iEval (rewrite E) in "Hn". iExact "Hn".
  Qed.

  Lemma cat_cmd_addr (a b : nat) (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (cat_cmd a b s0 g) -∗ ⌜ 0 < t < 2 ^ 38 /\ t mod 8 = 0 ⌝.
  Proof using . iIntros "#Hc". iApply (ush_cmd_addr with "Hc"). Qed.

  (* argv[0], in the two shapes runcmd's EXEC arm reads it *)
  Lemma cat_cmd_argv0 (a b : nat) (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    b = (a + 3)%nat ->
    ush_cmd gd t (cat_cmd a b s0 g) -∗
    ush_ptr gd (t + 8) (s0 + Z.of_nat a)
    ∗ ush_str gd (UArg (s0 + Z.of_nat a) 3%nat (fun j : nat => g (a + j)%nat)).
  Proof using .
    intro Hb. iIntros "#Hc". iSplit.
    - iDestruct (cat_cmd_word a b gd t s0 g Hb with "Hc") as "#Hw".
      rewrite /ush_ptr. iExact "Hw".
    - iDestruct (cat_cmd_str a b gd t s0 g Hb with "Hc") as "[%Hr #Hs]".
      rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplit; [ iPureIntro; exact Hr | iExact "Hs" ].
  Qed.

  (* =================================================================== *)
  (* S2  THE PINNED EXEC SUPPLY, at sh's own key.                         *)
  (*                                                                      *)
  (* [UkShEcho.sh_exec_sup_echo_at] with three changes and no others: the  *)
  (* argv[0] ADDRESS is [s0 + a] (echo's token starts at the line's base,  *)
  (* cat's does not), the argv reading is [cat_argv_bytes] and the ledger  *)
  (* row is about fd 0 (the pipe's READ end) instead of fd 1.             *)
  (* =================================================================== *)
  Definition sh_exec_sup_cat_at (Fd0 : list fdstate -> Prop) (a b : nat)
      (Q : Z -> iProp Σ) (Cr : iProp Σ) : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64)
          (s0 t : Z) (g : nat -> bv 8) (ld : list fdstate),
          ⌜ ukn_pay N' = Q ⌝ -∗
          (* argv[0]'s string, which is the PATH exec resolves... *)
          ⌜ m !!! Regidx a0_idx
            = (mword_of_int (s0 + Z.of_nat a) : mword 64) ⌝ -∗
          (* ...and [&argv[0]], which is the VECTOR it reads *)
          ⌜ m !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64) ⌝ -∗
          ⌜ cat_argv_bytes a b g ⌝ -∗
          ⌜ Fd0 ld ⌝ -∗
          UserFd.ustd (ukn_fd N') ld -∗
          ush_cmd (ukn_d N') t (cat_cmd a b s0 g) -∗
          Cr -∗
          udepw_at_refR N' m pc FsImg.ROOTINO
            (UserFd.ustd (ukn_fd N') ld ∗ Cr)))%I.

  (* NOT [apply _] ([UkShEcho.sh_exec_sup_echo_at_persistent]'s reason,
     durable-notes' fourth silent hang): with the body transparent AND its
     fd-0 row a VARIABLE the [Persistent] search walks [udepw_at_refR] and
     does not return. *)
  Global Instance sh_exec_sup_cat_at_persistent Fd0 a b Q Cr :
    Persistent (sh_exec_sup_cat_at Fd0 a b Q Cr).
  Proof using .
    rewrite /sh_exec_sup_cat_at. apply bi.intuitionistically_persistent.
  Qed.

  #[local] Typeclasses Opaque sh_exec_sup_cat_at.

  (* THE PIPE'S OWN ROW: fd 0 is this pipe's read end, exactly as
     [UCatPipe.pcat_round_at_g] reads it. *)
  Definition ush_fd0p (gp : pipe_names) (l : list fdstate) : Prop :=
    exists wb : bool, l !! 0%nat = Some (FdOpen true wb (FdPipe gp)).

End UkShCat.

(* ===================================================================== *)
(* S3  THE EXEC-FAILED DIAGNOSTIC, AT THE COMMAND NAME                    *)
(*                                                                        *)
(* [UkShDiag.wp_kshd_execfail_paid] prints [fprintf(2, "exec %s failed\n",*)
(* argv[0])] at 0xda and is stated at argv[0] = "echo": [ua_len x = 4],   *)
(* [ua_bytes x j = cmd_echo !!! j], and the law fixed at                  *)
(* [ush_execfail_law_at alt_execfail 17].  Its own header says a second   *)
(* line shape "supplies its own bytes by its own byte proof"; this is     *)
(* that walk with the name a parameter.                                   *)
(*                                                                        *)
(* THE THREE BYTE FAMILIES are the format's first window ("exec ", five   *)
(* bytes at indices 0-4 of the alternative), the ARGUMENT (indices        *)
(* 5..5+|cmd|-1) and the format's second window (" failed\n", the         *)
(* literal's own indices 7..14 landing at [p + (|cmd| - 2)]).  So the     *)
(* block's last index is [13 + |cmd|], which is echo's 17 at [|cmd| = 4]  *)
(* and cat's 16 at 3, and that number is the law's own [n].               *)
(* ===================================================================== *)
Section UkShCatDiag.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  Lemma wp_kshd_execfail_paid_at (N : uk_names Σ) `{!ukn_const N}
      (dg cmd : list (bv 8)) (Cr Cd : iProp Σ) (l : list fdstate)
      (h : CpuId) (m : regfile) (n : nat) (x : uarg) :
    UkSh.ush_fd2p l ->
    uint (m !!! Regidx s1_idx) mod 8 = 0 ->
    (* the name is at least two bytes -- the format's second window starts
       where the argument ends, and "%s" is two characters wide *)
    (2 <= length cmd)%nat ->
    ua_len x = length cmd ->
    (forall j : nat, (j < length cmd)%nat -> ua_bytes x j = cmd !!! j) ->
    (* the alternative is long enough for the whole block... *)
    (forall p : nat, (p < 13 + length cmd)%nat -> dg !! p = Some (dg !!! p)) ->
    (* ...and its bytes ARE the literal around the name *)
    (forall p : nat, (p < 5)%nat -> UkShDiag.shd_lit 0x1298 p = dg !!! p) ->
    (forall j : nat, (j < length cmd)%nat ->
       cmd !!! j = dg !!! (5 + j)%nat) ->
    (forall p : nat, (7 <= p < 15)%nat ->
       UkShDiag.shd_lit 0x1298 p = dg !!! (p + (length cmd - 2))%nat) ->
    UkShDiag.ush_execfail_law_at dg (13 + length cmd)%nat Cr Cd -∗
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    UkShRun.ush_ptr (ukn_d N) (uint (m !!! Regidx s1_idx) + 8) (ua_ptr x) -∗
    UkShRun.ush_str (ukn_d N) x -∗
    UserFd.ustd (ukn_fd N) l -∗
    Cr -∗
    (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0xda) (UkShDiag.ush_Dg + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    (* MOVED to [UkShDiagAt] so that [UkShEcho] can use it; this is it. *)
    exact (UkShDiagAt.wp_kshd_execfail_paid_at N dg cmd Cr Cd l h m n x).
  Qed.

  (* ...AND THE ECHO INSTANCE, as the ANTI-VACUITY witness of the three
     byte families above: the landed walk's premises are this one's at
     [cmd := EchoDisc.cmd_echo], [dg := EchoDisc.alt_execfail]. *)
  Lemma execfail_at_echo_bytes :
    (forall p : nat, (p < 5)%nat ->
       UkShDiag.shd_lit 0x1298 p = EchoDisc.alt_execfail !!! p)
    /\ (forall j : nat, (j < length EchoDisc.cmd_echo)%nat ->
          EchoDisc.cmd_echo !!! j = EchoDisc.alt_execfail !!! (5 + j)%nat)
    /\ (forall p : nat, (7 <= p < 15)%nat ->
          UkShDiag.shd_lit 0x1298 p
          = EchoDisc.alt_execfail
              !!! (p + (length EchoDisc.cmd_echo - 2))%nat).
  Proof using .
    split_and!.
    - intros p Hp. exact (UkShDiag.ush_execfail_w1 p ltac:(lia)).
    - intros j Hj. cbn in Hj. exact (UkShDiag.ush_execfail_arg j ltac:(lia)).
    - intros p Hp. cbn [length EchoDisc.cmd_echo].
      change (length EchoDisc.cmd_echo - 2)%nat with 2%nat.
      exact (UkShDiag.ush_execfail_w2 p ltac:(lia)).
  Qed.

  (* ---- and the CAT instance, closed ---------------------------------- *)
  Lemma cat_execfail_lookup (p : nat) :
    (p < 16)%nat -> alt_execR !! p = Some (alt_execR !!! p).
  Proof using .
    intro Hp. apply list_lookup_lookup_total_lt.
    rewrite /alt_execR length_app dg_execR_len. cbn [length]. lia.
  Qed.

  Lemma cat_execfail_w1 (p : nat) :
    (p < 5)%nat -> UkShDiag.shd_lit 0x1298 p = alt_execR !!! p.
  Proof using .
    intro Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => alt_execR !!! q) 0%nat 5%nat);
      [ vm_compute; reflexivity | lia ].
  Qed.

  Lemma cat_execfail_arg (j : nat) :
    (j < 3)%nat -> cmd_cat !!! j = alt_execR !!! (5 + j)%nat.
  Proof using .
    intro Hj.
    apply (UkShDiag.ush_bytes_of_forallb (fun q : nat => cmd_cat !!! q)
             (fun q : nat => alt_execR !!! (5 + q)%nat) 0%nat 3%nat);
      [ vm_compute; reflexivity | lia ].
  Qed.

  Lemma cat_execfail_w2 (p : nat) :
    (7 <= p < 15)%nat -> UkShDiag.shd_lit 0x1298 p = alt_execR !!! (p + 1)%nat.
  Proof using .
    intro Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => alt_execR !!! (q + 1)%nat) 7%nat 8%nat);
      [ vm_compute; reflexivity | lia ].
  Qed.

  (* the diagnostic at cat's line: the law the round supplies is
     [ush_execfail_law_at alt_execR 16] -- [PipeDisc.alt_execR] is
     "exec cat failed\n$ " and 16 is [dg_execR]'s own length. *)
  Lemma wp_kshd_execfail_cat (N : uk_names Σ) `{!ukn_const N}
      (Cr Cd : iProp Σ) (l : list fdstate)
      (h : CpuId) (m : regfile) (n : nat) (x : uarg) :
    UkSh.ush_fd2p l ->
    uint (m !!! Regidx s1_idx) mod 8 = 0 ->
    ua_len x = 3%nat ->
    (forall j : nat, (j < 3)%nat -> ua_bytes x j = cmd_cat !!! j) ->
    UkShDiag.ush_execfail_law_at alt_execR 16%nat Cr Cd -∗
    shk_code (ukn_t N) -∗
    shk_rodata (ukn_t N) -∗
    UkShRun.ush_ptr (ukn_d N) (uint (m !!! Regidx s1_idx) + 8) (ua_ptr x) -∗
    UkShRun.ush_str (ukn_d N) x -∗
    UserFd.ustd (ukn_fd N) l -∗
    Cr -∗
    (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0xda) (UkShDiag.ush_Dg + n) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hfd2 Hal Hxlen Hxb.
    iIntros "#Hlaw #Hcode #Hro #Hw #Hxs Hstd Hc Hpay Hrun".
    iApply (wp_kshd_execfail_paid_at N alt_execR cmd_cat Cr Cd l h m n x
              Hfd2 Hal
              ltac:(rewrite cmd_cat_len; lia)
              ltac:(rewrite cmd_cat_len; exact Hxlen)
              ltac:(rewrite cmd_cat_len; exact Hxb)
              ltac:(rewrite cmd_cat_len; exact cat_execfail_lookup)
              cat_execfail_w1
              ltac:(rewrite cmd_cat_len; exact cat_execfail_arg)
              ltac:(rewrite cmd_cat_len;
                    intros p Hp;
                    replace (p + (3 - 2))%nat with (p + 1)%nat by lia;
                    exact (cat_execfail_w2 p Hp))
              with "[Hlaw] Hcode Hro Hw Hxs Hstd Hc Hpay Hrun").
    rewrite cmd_cat_len. iExact "Hlaw".
  Qed.

End UkShCatDiag.

(* ===================================================================== *)
(* S4  THE SPECIALISED EXEC ARM.                                          *)
(*                                                                        *)
(* [UkShEcho.wp_kshr_exec_echo_at] at [cat_cmd]: runcmd's prologue, the   *)
(* jump table's EXEC row (0xce), the argv[0] load, the [beqz] that is not *)
(* taken, [&argv[0]] into a1, the call, the PINNED exec at the root, and  *)
(* the failure tail -- section 3's diagnostic, paid.                      *)
(* ===================================================================== *)
Section UkShCatArm.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  Definition wp_kshr_exec_cat_at (Fd0 : list fdstate -> Prop) (a b : nat)
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      ukn_pay N = Q ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      cat_argv_bytes a b g ->
      Fd0 ld ->
      UkSh.ush_fd2p ld ->
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_cat_at Fd0 a b Q Cr -∗
        (* the diagnostic's law at CAT's alternative, and what its end pays
           at the exit *)
        UkShDiag.ush_execfail_law_at alt_execR 16%nat Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (cat_cmd a b s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        Cr -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  #[local] Typeclasses Opaque wp_kshr_exec_cat_at.

  Lemma wp_kshr_exec_cat_at_holds (Fd0 : list fdstate -> Prop) (a b : nat)
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshr_exec_cat_at Fd0 a b Q Cr Cd.
  Proof using .
    intros N Hcc h m t szv s0 g ld n Hpeq Ha0 Hbytes Hfd0 Hfd2.
    pose proof (cat_argv_bytes_end a b g Hbytes) as Hb3.
    (* the supply is introduced LINEARLY and its box stripped by an
       explicit unfold ([UkShEcho.wp_kshr_exec_echo_at_holds]'s note: an
       [iIntros "#"] on a bundle of wands does not return at this
       altitude) *)
    iIntros "#Hcode Hexs #Hxl #Hcd #Hjt #Htree Hsz Hstd Hcwd Hch Hcr Hrun".
    rewrite /sh_exec_sup_cat_at. iDestruct "Hexs" as "#Hexs".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iDestruct (cat_cmd_addr a b _ t s0 g with "Htree") as %[Htr Ht8].
    iDestruct (cat_cmd_argv0 a b _ t s0 g Hb3 with "Htree") as "[#Hw0 #Hstr]".
    iDestruct "Hstr" as "[%Hxr #Hxs]".
    cbn [ua_ptr ua_len ua_bytes] in Hxr.
    (* ---- runcmd's prologue and the jump table ---- *)
    iApply (wp_kshr_entry N (cat_cmd a b s0 g) h m t
              (2 + (UkShDiag.ush_Dg + n)) Ha0 with "Hcode Hjt Htree Hrun").
    iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
    assert (E8 : (t + 8) mod 8 = 0)
      by (rewrite Zplus_mod Ht8; reflexivity).
    assert (Ece : add_vec_int (mword_of_int 0xce : mword 64) 2
                  = mword_of_int 0xd0)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xce  c.ld a0,8(s1) -- argv[0] ---- *)
    iApply (UkShRun.wp_uk_cldq N h1 m1 (mword_of_int 0xce)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
              (t + 8) (mword_of_int (s0 + Z.of_nat a))
              (2 + (UkShDiag.ush_Dg + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c8; lia)
              E8 ltac:(vm_compute; discriminate)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_ce with "Hcode"). }
    iIntros "_". rewrite Ece. iIntros (h2) "Hrun".
    set (k1 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat a) : mword 64)]> m1).
    assert (Hk1 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    k1 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hs1_k : k1 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by (rewrite (Hk1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    (* ---- 0xd0  c.beqz a0 -- NOT taken: argv[0] is a string ---- *)
    iApply (wp_uk_cbeqz N h2 k1 (mword_of_int 0xd0)
              (mword_of_int 16 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0xf0) (2 + (UkShDiag.ush_Dg + n))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite /k1 (upd_eq m1 (Regidx a0_idx)
                                   (mword_of_int (s0 + Z.of_nat a)
                                    : mword 64));
                    rewrite (moi_eq_zero (s0 + Z.of_nat a)
                               ltac:(unfold Z64; lia));
                    symmetry; apply Z.eqb_neq; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_d0 with "Hcode"). }
    assert (Ed0 : add_vec_int (mword_of_int 0xd0 : mword 64) 2
                  = mword_of_int 0xd2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ed0. iIntros (h3) "Hrun".
    (* ---- 0xd2  addi a1,s1,8 -- &argv[0] ---- *)
    iApply (wp_uk_addi N h3 k1 (mword_of_int 0xd2)
              (mword_of_int 8 : mword 12) s1_idx a1_idx
              (mword_of_int (t + 8)) (2 + (UkShDiag.ush_Dg + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_k;
                    assert (Es : (sign_extend' 64
                                    (mword_of_int 8 : mword 12) : mword 64)
                                 = mword_of_int 8)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Es moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d2 with "Hcode"). }
    assert (Ed2 : add_vec_int (mword_of_int 0xd2 : mword 64) 4
                  = mword_of_int 0xd6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ed2. iIntros (h4) "Hrun".
    set (k2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (t + 8)
                                     : mword 64)]> k1).
    (* ---- 0xd6  jal ra,exec ---- *)
    iApply (wp_kshr_jal N h4 k2 0xd6 ShSyms.exec 0xda
              (mword_of_int 3012 : mword 21) (2 + (UkShDiag.ush_Dg + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d6 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (k3 := <[Regidx ra_idx := (mword_of_int 0xda : mword 64)]> k2).
    assert (Hrk3 : ret_pc (k3 !!! Regidx ra_idx)
                   = (mword_of_int 0xda : mword 64))
      by (rewrite /k3 (upd_eq k2 (Regidx ra_idx) _);
          apply bv_eq; vm_compute; reflexivity).
    (* ---- THE PINNED EXEC, at the root ---- *)
    assert (Hka0 : (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                     !!! Regidx a0_idx
                   = (mword_of_int (s0 + Z.of_nat a) : mword 64)).
    { rewrite (upd_ne k3 (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_ne k1 (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k1 (upd_eq m1 (Regidx a0_idx) _). reflexivity. }
    assert (Hka1 : (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                     !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64)).
    { rewrite (upd_ne k3 (Regidx a7_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_eq k1 (Regidx a1_idx) _). reflexivity. }
    (* THE DEPOSIT, BUILT FIRST AND FULLY EXPLICITLY
       ([UkShEcho.wp_kshr_exec_echo_at_holds]'s note). *)
    iAssert (udepw_at_refR N
               (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
               (mword_of_int 0xc9c) FsImg.ROOTINO
               (UserFd.ustd (ukn_fd N) ld ∗ Cr))
      with "[Hstd Hcr]" as "Hdepx".
    { iApply ("Hexs" $! N
                (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                (mword_of_int 0xc9c) s0 t g ld
                with "[%] [%] [%] [%] [%] Hstd Htree Hcr").
      - exact Hpeq.
      - exact Hka0.
      - exact Hka1.
      - exact Hbytes.
      - exact Hfd0. }
    iApply (UkShEcho.wp_kshr_exec_at_cwd_holds
              (UserFd.ustd (ukn_fd N) ld ∗ Cr)
              N Hcc h5 k3 FsImg.ROOTINO
              ((2 + (UkShDiag.ush_Dg + n))%nat)
              with "Hcode Hrun Hcwd Hdepx").
    rewrite Hrk3. iIntros (h6) "Hcwd [Hstd Hcr] Hrun".
    (* ---- 0xda: "exec cat failed" -- PAID ---- *)
    set (k4 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                 (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)).
    assert (Hs1_k4 : uint (k4 !!! Regidx s1_idx) = t).
    { rewrite /k4 (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne k3 (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_ne k1 (Regidx a1_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs1_k. apply uint_moi. unfold Z64. lia. }
    replace (2 + (UkShDiag.ush_Dg + n))%nat
      with (UkShDiag.ush_Dg + (2 + n))%nat by lia.
    iApply (wp_kshd_execfail_cat N Cr Cd ld h6 k4 (2 + n)
              (UArg (s0 + Z.of_nat a) 3%nat (fun j : nat => g (a + j)%nat))
              Hfd2 ltac:(rewrite Hs1_k4; exact Ht8) eq_refl
              ltac:(intros j Hj; cbn [ua_bytes];
                    exact (proj1 (proj2 Hbytes) j
                             ltac:(rewrite cmd_cat_len; exact Hj)))
              with "Hxl Hcode Hro [] [] Hstd Hcr [] Hrun").
    { rewrite Hs1_k4. cbn [ua_ptr]. iExact "Hw0". }
    { rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplitR; [ iPureIntro; exact Hxr | iExact "Hxs" ]. }
    { iIntros "_ Hc". rewrite <- Hpeq. iApply ("Hcd" with "Hc"). }
  Qed.

End UkShCatArm.

(* ===================================================================== *)
(* S5  THE ANTI-VACUITY WITNESS, AND THE LANE'S FINDING                   *)
(*                                                                        *)
(* [UCatPipe.pcat_image_entry] -- design section 5.3's landed (E) half,   *)
(* and the lemma this lane was told to plug its supply into -- takes      *)
(*                                                                        *)
(*     line_ok ws  ->  ...  ->  length ws = 1%nat  ->  ...                *)
(*                                                                        *)
(* and [EchoDisc.line_ok] contains [2 <= length ws] (it must: echo prints *)
(* nothing at argc 1, durable-notes' degenerate-member rule).  So the     *)
(* premise set is contradictory, the entry is VACUOUSLY true and no       *)
(* caller can ever apply it.  One line says so, and it is what a          *)
(* premise-threading lane cannot tell from a satisfiable one.             *)
(* ===================================================================== *)
Lemma cat_line_premises_absurd (ws : list (list (bv 8))) :
  line_ok ws -> length ws = 1%nat -> False.
Proof using .
  intros Hok H1. pose proof (line_ok_ge2 ws Hok). lia.
Qed.

(* ...and the same sentence at the OTHER conjunct, so that a repair that
   only relaxes the count is seen to be insufficient: an admissible line's
   first word is "echo", and cat's is "cat". *)
Lemma cat_line_head_absurd (ws : list (list (bv 8))) :
  line_ok ws -> ws !! 0%nat = Some cmd_cat -> False.
Proof using .
  intros Hok Hhd.
  pose proof (line_ok_head ws Hok) as He. rewrite Hhd in He.
  vm_compute in He. discriminate He.
Qed.
