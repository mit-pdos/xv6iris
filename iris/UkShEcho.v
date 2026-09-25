(* ===================================================================== *)
(* UkShEcho.v -- E4 SH-ECHO, THE u-TIER HALF: sh's forked child at the    *)
(* ONE command the disciplined line spells, and the PINNED exec supply    *)
(* its EXEC arm runs on.                                                  *)
(*                                                                        *)
(* WHY A SECOND RUNCMD.  [UkShRun.wp_kshr_runcmd] is proved by induction  *)
(* over an ARBITRARY [ushcmd], so its EXEC arm needs an exec bundle at an  *)
(* ARBITRARY argv -- which is exactly what no pin can supply, and why it   *)
(* takes [UkRun.uxsup_at], the generic (tainted) supply, at every key.     *)
(* Under the discipline sh's buffer holds ONE line ([UConsLine.           *)
(* ush_line_is ws]: an ADMISSIBLE line), so the command is ONE value and  *)
(* the arm can be respecialised at it.  This file states that value and    *)
(* the specialised arm; [UShEcho.v] PAYS the supply out of the echo        *)
(* application's claim that /echo is [ElfUser.echo_elf].                   *)
(*                                                                        *)
(* THE SPLIT IS INIT'S, one level down.  [UkInit.init_exec_sup] is the     *)
(* u-tier DEFINITION of init's pinned supply (a wand from init's own       *)
(* persistent image facts to [UkRun.udepw_at] at ONE working directory)    *)
(* and [UInitSh.init_exec_sup_of_sh_slot] is its payment above the         *)
(* kernel's instance.  [sh_exec_sup_echo] below is the first half at sh,   *)
(* and [UShEcho.sh_exec_sup_of_echo_slot] the second.                      *)
(*                                                                        *)
(* PHASE 1.  Everything a phase-2 proof will have to produce is STATED     *)
(* here, in the vocabulary the walks already speak, and the closed facts   *)
(* about the literal line are PROVED (that is what keeps the statements    *)
(* from being about nothing).  Nothing is [Admitted] and nothing is a      *)
(* placeholder premise: the four obligations below are [Prop]s whose       *)
(* bodies are the lemma statements, on [UConsLine.v]'s mould.              *)
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
Require Import Xv6Cameras.     (* [uartGhostG]: the position pair's cameras *)
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UkRunExecRef.  (* [udepw_at_refR] / [wp_uk_ecall_exec_at_cwd_refR]: the exec refund at the supplier's shape (step 4) *)
Require Import UkRunMem.   (* [uoff_c8]: the c.ld offset the 0xce load names *)
Require Import FdSlots UserFd UserCwd UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import LineWords.        (* [wl_line] / [wl_toks] / [wl_off]      *)
Require Import UkShWords.        (* the lexer at an ARBITRARY word list *)
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShDiagAt.        (* the exec-failed diagnostic at any command name *)
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShMain.
Require Import UkShFork.
Require Import UConsLine.        (* [ush_line_is ws]: the buffer's LINE    *)
Require Import EchoDisc.         (* [line_ok] / [cmd_echo] / [sb] / [nlb]  *)
Require Import ExecWords.        (* [exec_ok]: [line_ok] without the command *)
Require Import FsImg.            (* [ROOTINO] -- the cwd the pin resolves at *)
Require Import UexecSG.          (* [uexecSG] / [uprogSG]: the deposit class *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.

(* a failing tactic in a whole-function WP looks like a hang: Rocq prints
   the entire goal, and a [urun]-altitude goal is enormous (durable-notes,
   "The dev loop"). *)
Set Printing Depth 40.

(* ===================================================================== *)
(* S1  THE LINE'S COMMAND.                                                *)
(*                                                                        *)
(* THE PARSE IS FUNCTIONAL, and it always was: [UkShParseCmd.             *)
(* wp_kshp_parser] takes the token list as a PREMISE                      *)
(* ([UkShParse.ushp_tokens len f 0 toks]) and returns the node at THAT     *)
(* list ([ushp_tree s0 p (UshpExec toks)]), so there is no determinacy     *)
(* lemma to prove about the parser -- the caller names the tokens.  What   *)
(* the disciplined branch owes is therefore that the line LEXES: it        *)
(* carries no symbol byte and its maximal non-blank runs are the token     *)
(* list.  That is [ush_line_tokens] below.                                 *)
(*                                                                        *)
(* AND THAT IS NOT A PROPERTY OF ANY PARTICULAR SEVENTEEN BYTES.  Every    *)
(* reading here takes the WORD LIST [ws] the discipline admitted           *)
(* ([EchoDisc.line_ok]): the line is [LineWords.wl_line ws],               *)
(* [UkShWords.v] proves the lexing for an ARBITRARY list of words joined   *)
(* by single spaces and closed by a newline, and what is left here is the  *)
(* INSTANCE -- no closed computation over a literal survives.              *)
(* ===================================================================== *)

(* THE TOKEN LIST AND THE TWO BOUNDARY ACCESSORS ARE THE WORD LIST'S.
   The line is [LineWords.wl_line ws], so the tokens sh's lexer finds are
   [wl_toks] of those words, argument [i] starts where the join puts word
   [i], and it is as long as that word.  Nothing below reads a number off
   a line. *)
Definition echo_toks (ws : list (list (bv 8))) : list (nat * nat) :=
  wl_toks ws.

Definition echo_off (ws : list (list (bv 8))) (i : nat) : nat :=
  wl_off 0%nat ws i.

Definition echo_alen (ws : list (list (bv 8))) (i : nat) : nat :=
  length (ws !!! i).

(* the one fact about an admissible line's words the lexer's caller needs
   and the general statement cannot give it: there are fewer of them than
   sh's MAXARGS -- which is [EchoDisc.line_ok]'s third conjunct *)
Lemma echo_toks_lt10_x (ws : list (list (bv 8))) :
  exec_ok ws -> (length (echo_toks ws) < 10)%nat.
Proof. intro Hok. rewrite /echo_toks wl_toks_length. exact (exec_ok_lt10 ws Hok). Qed.

Lemma echo_toks_lt10 (ws : list (list (bv 8))) :
  line_ok ws -> (length (echo_toks ws) < 10)%nat.
Proof.
  intro Hok__.
  exact (echo_toks_lt10_x ws (line_ok_exec_ok _ Hok__)).
Qed.

(* AN ARGUMENT'S BYTES ARE INSIDE THE LINE -- [LineWords.wl_off_lt_line] at
   these words.  A caller that used to bound [echo_off i + j] by case
   analysis over three literal offsets gets it from this. *)
Lemma echo_off_lt_x (ws : list (list (bv 8))) (i j : nat) :
  exec_ok ws -> (i < length ws)%nat -> (j <= echo_alen ws i)%nat ->
  (echo_off ws i + j < length (wl_line ws))%nat.
Proof.
  intros Hok Hi Hj. rewrite /echo_off.
  exact (wl_off_lt_line ws i _ j (exec_ok_at ws i Hok Hi) Hj).
Qed.

Lemma echo_off_lt (ws : list (list (bv 8))) (i j : nat) :
  line_ok ws -> (i < length ws)%nat -> (j <= echo_alen ws i)%nat ->
  (echo_off ws i + j < length (wl_line ws))%nat.
Proof.
  intro Hok__.
  exact (echo_off_lt_x ws i j (line_ok_exec_ok _ Hok__)).
Qed.

(* ...AND THE TWO NUMBERS THAT ARE NOT ABOUT THE ARGUMENTS.  The first
   word starts at the line's base, which is true of every line
   ([LineWords.wl_off_0]); the COMMAND NAME is four bytes, which stays
   four whatever the arguments are, because the program run is /echo
   ([EchoDisc.line_ok_head_len]).  The offsets and lengths of the
   arguments themselves are gone: nothing above reads one any more. *)
Lemma echo_off_0 (ws : list (list (bv 8))) : echo_off ws 0%nat = 0%nat.
Proof. by rewrite /echo_off wl_off_0. Qed.

Lemma echo_alen_0 (ws : list (list (bv 8))) :
  line_ok ws -> echo_alen ws 0%nat = 4%nat.
Proof. exact (line_ok_head_len ws). Qed.

Lemma echo_toks_lookup_x (ws : list (list (bv 8))) (i : nat) :
  exec_ok ws -> (i < length ws)%nat ->
  echo_toks ws !! i = Some (echo_off ws i, (echo_off ws i + echo_alen ws i)%nat).
Proof.
  intros Hok Hi. rewrite /echo_toks /echo_off /echo_alen /wl_toks.
  exact (wl_toks_at_lookup ws 0%nat i _ (exec_ok_at ws i Hok Hi)).
Qed.

Lemma echo_toks_lookup (ws : list (list (bv 8))) (i : nat) :
  line_ok ws -> (i < length ws)%nat ->
  echo_toks ws !! i = Some (echo_off ws i, (echo_off ws i + echo_alen ws i)%nat).
Proof.
  intro Hok__.
  exact (echo_toks_lookup_x ws i (line_ok_exec_ok _ Hok__)).
Qed.

(* THE COMMAND NAME IS THE LINE'S FIRST FOUR BYTES, which is what the
   "exec %s failed" diagnostic prints back ([UkShDiag]'s [cmd_echo]). *)
(* ...AT ANY COMMAND: the line's first bytes are its first word's. *)
Lemma echo_line_word0 (ws : list (list (bv 8))) (j : nat) :
  exec_ok ws -> (j < length (ws !!! 0%nat))%nat ->
  wl_line ws !!! j = (ws !!! 0%nat) !!! j.
Proof.
  intros Hok Hj.
  pose proof (wl_line_word ws 0%nat (ws !!! 0%nat) j
                (exec_ok_at ws 0%nat Hok (exec_ok_pos ws Hok)) Hj) as Hw.
  replace (wl_off 0%nat ws 0%nat + j)%nat with j in Hw
    by (rewrite wl_off_0; lia).
  exact Hw.
Qed.

Lemma echo_line_cmd_byte (ws : list (list (bv 8))) (j : nat) :
  line_ok ws -> (j < 4)%nat -> wl_line ws !!! j = cmd_echo !!! j.
Proof.
  intros Hok Hj.
  assert (Hlen : (j < length cmd_echo)%nat) by (vm_compute in Hj |- *; lia).
  pose proof (wl_line_word ws 0%nat cmd_echo j (line_ok_head ws Hok) Hlen) as Hw.
  rewrite wl_off_0 Nat.add_0_l in Hw. exact Hw.
Qed.

(* ---- the line lexes: [UkShWords.v]'s two general lemmas, instantiated - *)
(* [ush_echo_tokens] used to live in [UConsLine.v] at the literal line and
   be answered by [vm_compute].  It is this, at the words, and its proof
   is two applications of the general tokenization. *)
Definition ush_line_tokens (ws : list (list (bv 8))) : Prop :=
  ushp_no_symbols (length (wl_line ws)) (fun j : nat => wl_line ws !!! j)
  /\ ushp_tokens (length (wl_line ws)) (fun j : nat => wl_line ws !!! j) 0%nat
       (wl_toks ws)
  /\ (length (wl_toks ws) < 10)%nat.

Lemma ush_line_tokens_holds_x (ws : list (list (bv 8))) :
  exec_ok ws -> ush_line_tokens ws.
Proof.
  intro Hok. pose proof (exec_ok_wf ws Hok) as Hwf.
  split_and!.
  - exact (wl_no_symbols ws (fun j : nat => wl_line ws !!! j)
             (length (wl_line ws)) Hwf eq_refl (fun j _ => eq_refl)).
  - exact (wl_tokens ws (fun j : nat => wl_line ws !!! j)
             (length (wl_line ws)) Hwf eq_refl (fun j _ => eq_refl)).
  - rewrite wl_toks_length. exact (exec_ok_lt10 ws Hok).
Qed.

Lemma ush_line_tokens_holds (ws : list (list (bv 8))) :
  line_ok ws -> ush_line_tokens ws.
Proof.
  intro Hok__.
  exact (ush_line_tokens_holds_x ws (line_ok_exec_ok _ Hok__)).
Qed.

(* ---- the determinacy the DISCIPLINED buffer needs -------------------- *)
(* [ush_line_tokens] is about [wl_line ws] read through
   [fun j => wl_line ws !!! j]; the command loop hands its body the line
   through [fun j => f (k + j)].  [UConsLine.ush_line_is ws] says the two
   agree pointwise below [len], and [ushp_no_symbols] / [ushp_tokens] read
   their bytes only there -- so this is a TRANSPORT and not a second
   computation.  It is [UConsLine.ush_line_lexable] with the token list
   NAMED, which is what the specialised arm needs and the existential form
   cannot give. *)
(* ---- THE LINE, AT ANY EXEC'ABLE WORD LIST ----------------------------- *)
(* [UConsLine.ush_line_is] with [ExecWords.exec_ok] for [EchoDisc.line_ok]:
   the buffer holds the join of [ws], whatever command [ws] names.  The
   lexer's transports below, the exec arm and the child's walk spend nothing
   else of the line; the [line_ok] statements are their instances. *)
Definition ush_xline_is (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) : Prop :=
  exec_ok ws
  /\ len = length (wl_line ws)
  /\ forall j : nat, (j < len)%nat -> f (k + j)%nat = wl_line ws !!! j.

Lemma ush_xline_is_of_line (ws : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) :
  UConsLine.ush_line_is ws f k len -> ush_xline_is ws f k len.
Proof.
  intros (Hok & Hlen & Hf). exact (conj (line_ok_exec_ok ws Hok) (conj Hlen Hf)).
Qed.

Definition ush_line_toks_x : Prop :=
  forall (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat),
    ush_xline_is ws f k len ->
    len = length (wl_line ws)
    /\ ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ ushp_tokens len (fun j : nat => f (k + j)%nat) 0%nat (echo_toks ws).

(* ---- the transport, which is all the determinacy costs --------------- *)
(* The four [ushp_*_ext] lemmas this used to carry say only that the lexer
   reads [f] inside its window and nowhere else -- nothing about echo, and
   nothing about any particular line -- so they live in [UkShWords.v] now,
   beside the general tokenization they exist to move. *)

(* ...and the determinacy itself: ONE transport of the lexing above. *)
Lemma ush_line_toks_x_holds : ush_line_toks_x.
Proof.
  intros ws f k len (Hok & Hlen & Hf).
  split; [ exact Hlen | ].
  subst len.
  destruct (ush_line_tokens_holds_x ws Hok) as (Hns & Htk & _).
  assert (Hext : forall j : nat, (j < length (wl_line ws))%nat ->
            wl_line ws !!! j = f (k + j)%nat)
    by (intros j Hj; symmetry; exact (Hf j Hj)).
  split.
  - exact (ushp_no_symbols_ext (length (wl_line ws)) _ _ Hext Hns).
  - exact (ushp_tokens_ext (length (wl_line ws)) _ _ Hext 0%nat
             (echo_toks ws) Htk).
Qed.

Definition ush_line_toks : Prop :=
  forall (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is ws f k len ->
    len = length (wl_line ws)
    /\ ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ ushp_tokens len (fun j : nat => f (k + j)%nat) 0%nat (echo_toks ws).

(* ---- the transport, which is all the determinacy costs --------------- *)
(* The four [ushp_*_ext] lemmas this used to carry say only that the lexer
   reads [f] inside its window and nowhere else -- nothing about echo, and
   nothing about any particular line -- so they live in [UkShWords.v] now,
   beside the general tokenization they exist to move. *)

(* ...and the determinacy itself: ONE transport of the lexing above. *)
Lemma ush_line_toks_holds : ush_line_toks.
Proof.
  intros ws f k len Hl.
  exact (ush_line_toks_x_holds ws f k len (ush_xline_is_of_line ws f k len Hl)).
Qed.

(* ---- the command, as a VALUE ---------------------------------------- *)
(* [UkShMain.ush_cmd_of_ushp] converts the parser's node into the runner's
   tree at [UExec (UkShMain.ush_args s0 g toks)], where [g] is the line
   AFTER [nulterminate]'s cut ([ushp_nulfold toks (ushp_ext len f)]).  At
   [toks := echo_toks ws] that value is one [UserHeap.uarg] per word of
   the line, and this is it. *)
Definition echo_cmd (ws : list (list (bv 8))) (s0 : Z) (g : nat -> bv 8)
    : ushcmd :=
  UExec (UkShMain.ush_args s0 g (echo_toks ws)).

Lemma echo_cmd_simple (ws : list (list (bv 8))) (s0 : Z) (g : nat -> bv 8) :
  ush_simple (echo_cmd ws s0 g).
Proof. exact I. Qed.

Lemma echo_cmd_ht (ws : list (list (bv 8))) (s0 : Z) (g : nat -> bv 8) :
  ush_ht (echo_cmd ws s0 g) = 1%nat.
Proof. reflexivity. Qed.

Lemma echo_cmd_args_length (ws : list (list (bv 8))) (s0 : Z)
    (g : nat -> bv 8) :
  length (UkShMain.ush_args s0 g (echo_toks ws)) = length ws.
Proof.
  rewrite UkShMain.ush_args_length /echo_toks. exact (wl_toks_length ws).
Qed.

Lemma echo_cmd_args_lookup_x (ws : list (list (bv 8))) (s0 : Z)
    (g : nat -> bv 8) (i : nat) :
  exec_ok ws -> (i < length ws)%nat ->
  UkShMain.ush_args s0 g (echo_toks ws) !! i
  = Some (UArg (s0 + Z.of_nat (echo_off ws i)) (echo_alen ws i)
            (fun j : nat => g (echo_off ws i + j)%nat)).
Proof.
  intros Hok Hi.
  rewrite (UkShMain.ush_args_lookup s0 g (echo_toks ws) i
             (echo_off ws i, (echo_off ws i + echo_alen ws i)%nat)
             (echo_toks_lookup_x ws i Hok Hi)).
  cbn [fst snd].
  replace (echo_off ws i + echo_alen ws i - echo_off ws i)%nat
    with (echo_alen ws i) by lia.
  reflexivity.
Qed.

Lemma echo_cmd_args_lookup (ws : list (list (bv 8))) (s0 : Z)
    (g : nat -> bv 8) (i : nat) :
  line_ok ws -> (i < length ws)%nat ->
  UkShMain.ush_args s0 g (echo_toks ws) !! i
  = Some (UArg (s0 + Z.of_nat (echo_off ws i)) (echo_alen ws i)
            (fun j : nat => g (echo_off ws i + j)%nat)).
Proof.
  intro Hok__.
  exact (echo_cmd_args_lookup_x ws s0 g i (line_ok_exec_ok _ Hok__)).
Qed.

(* ---- the argv BYTES, as a pure premise ------------------------------- *)
(* What the exec at the bottom of the arm needs of the line is not the
   whole of [ush_line_is] but one string per word and their NULs:
   [nulterminate] has cut the line at each token's end, so the byte
   function the tree is built over spells word [i] followed by a NUL at
   the offset the join puts it.  Stated over the CUT function [g] (the
   tree's own), because that is the one the node's [ustr]s are indexed
   by. *)
Definition echo_argv_bytes (ws : list (list (bv 8))) (g : nat -> bv 8)
    : Prop :=
  (forall (i j : nat), (i < length ws)%nat -> (j < echo_alen ws i)%nat ->
     g (echo_off ws i + j)%nat = wl_line ws !!! (echo_off ws i + j)%nat)
  /\ (forall i : nat, (i < length ws)%nat ->
        g (echo_off ws i + echo_alen ws i)%nat = ubyte0).

(* ...and it holds of the disciplined line's cut.  [ushp_nulfold] writes a
   NUL at each token's END and leaves every other index alone, and every
   word's end is outside every token -- so the strings are the line's own
   bytes and the terminators are the cut's. *)
Definition echo_argv_bytes_of_line_x : Prop :=
  forall (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat),
    ush_xline_is ws f k len ->
    echo_argv_bytes ws
      (ushp_nulfold (echo_toks ws)
         (ushp_ext len (fun j : nat => f (k + j)%nat))).

(* ...AND THE CUT IS NOT A PROPERTY OF ANY PARTICULAR OFFSETS EITHER.  It
   used to be three stores at 4, 10 and 16, discharged by [reflexivity] at
   each.  [UkShWords.wl_cut_in] / [wl_cut_end] say the same thing at an
   arbitrary word list -- inside word [i] the cut is transparent, at its
   END it is the terminator -- so this is two applications and the
   arithmetic that keeps every index inside [ushp_ext]'s window. *)
Lemma echo_argv_bytes_of_line_x_holds : echo_argv_bytes_of_line_x.
Proof.
  intros ws f k len (Hok & Hlen & Hf).
  split.
  - intros i j Hi Hj.
    pose proof (exec_ok_at ws i Hok Hi) as Hw.
    assert (Hlt : (wl_off 0%nat ws i + j < len)%nat).
    { rewrite Hlen.
      exact (wl_off_lt_line ws i _ j Hw (Nat.lt_le_incl _ _ Hj)). }
    rewrite /echo_off /echo_toks
      (wl_cut_in ws (fun x : nat => f (k + x)%nat) len i _ j Hw Hj Hlt).
    exact (Hf _ Hlt).
  - intros i Hi.
    pose proof (exec_ok_at ws i Hok Hi) as Hw.
    rewrite /echo_off /echo_alen /echo_toks.
    exact (wl_cut_end ws (fun x : nat => f (k + x)%nat) len i _ Hw).
Qed.

Definition echo_argv_bytes_of_line : Prop :=
  forall (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is ws f k len ->
    echo_argv_bytes ws
      (ushp_nulfold (echo_toks ws)
         (ushp_ext len (fun j : nat => f (k + j)%nat))).

(* ...AND THE CUT IS NOT A PROPERTY OF ANY PARTICULAR OFFSETS EITHER.  It
   used to be three stores at 4, 10 and 16, discharged by [reflexivity] at
   each.  [UkShWords.wl_cut_in] / [wl_cut_end] say the same thing at an
   arbitrary word list -- inside word [i] the cut is transparent, at its
   END it is the terminator -- so this is two applications and the
   arithmetic that keeps every index inside [ushp_ext]'s window. *)
Lemma echo_argv_bytes_of_line_holds : echo_argv_bytes_of_line.
Proof.
  intros ws f k len Hl.
  exact (echo_argv_bytes_of_line_x_holds ws f k len
           (ush_xline_is_of_line ws f k len Hl)).
Qed.
Section UkShEcho.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* the position pair's cameras -- [UkSh.ush_pstate]'s fourth conjunct *)
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* the numbers a verified program admits (lane SUPPLY-SPLIT); a SECTION
     hypothesis exactly as in [UkShRun]/[UkShFork], so no statement below
     names it *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  THE NODE, ADDRESSED.  Three accessors so that no consumer of the     *)
  (*  tree has to fight [UkShMain.ush_args]'s [map] again: argument [i]'s  *)
  (*  pointer word, its string, and the NULL cap.  Everything is           *)
  (*  [DfracDiscarded], so every one of them is free to take.              *)
  (* =================================================================== *)
  Lemma echo_cmd_str_x (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) (i : nat) :
    exec_ok ws -> (i < length ws)%nat ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    ⌜ 0 < s0 + Z.of_nat (echo_off ws i) < 2 ^ 38 ⌝ ∗
    ustr gd DfracDiscarded (s0 + Z.of_nat (echo_off ws i)) (echo_alen ws i)
      (fun j : nat => g (echo_off ws i + j)%nat).
  Proof using .
    intros Hok Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & _ & #Hs)".
    iDestruct (big_sepL_lookup _ (UkShMain.ush_args s0 g (echo_toks ws)) i _
                 (echo_cmd_args_lookup_x ws s0 g i Hok Hi) with "Hs") as "#Hx".
    rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
    iDestruct "Hx" as "[%Hr #Hstr]".
    iSplit; [ iPureIntro; exact Hr | iExact "Hstr" ].
  Qed.

  Lemma echo_cmd_str (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) (i : nat) :
    line_ok ws -> (i < length ws)%nat ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    ⌜ 0 < s0 + Z.of_nat (echo_off ws i) < 2 ^ 38 ⌝ ∗
    ustr gd DfracDiscarded (s0 + Z.of_nat (echo_off ws i)) (echo_alen ws i)
      (fun j : nat => g (echo_off ws i + j)%nat).
  Proof using .
    intro Hok__.
    exact (echo_cmd_str_x ws gd t s0 g i (line_ok_exec_ok _ Hok__)).
  Qed.

  Lemma echo_cmd_word_x (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) (i : nat) :
    exec_ok ws -> (i < length ws)%nat ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat i)
      (mword_of_int (s0 + Z.of_nat (echo_off ws i))).
  Proof using .
    intros Hok Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(#Hv & _ & _)".
    iDestruct (uargv_acc gd (t + 8) (UkShMain.ush_args s0 g (echo_toks ws)) i _
                 (echo_cmd_args_lookup_x ws s0 g i Hok Hi) with "Hv")
      as "[[#Hw _] _]".
    cbn [ua_ptr]. iExact "Hw".
  Qed.

  Lemma echo_cmd_word (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) (i : nat) :
    line_ok ws -> (i < length ws)%nat ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat i)
      (mword_of_int (s0 + Z.of_nat (echo_off ws i))).
  Proof using .
    intro Hok__.
    exact (echo_cmd_word_x ws gd t s0 g i (line_ok_exec_ok _ Hok__)).
  Qed.

  Lemma echo_cmd_cap (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat (length ws))
      (mword_of_int 0).
  Proof using .
    iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & #Hn & _)".
    rewrite /ush_ptr echo_cmd_args_length. iExact "Hn".
  Qed.

  Lemma echo_cmd_addr (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd ws s0 g) -∗ ⌜ 0 < t < 2 ^ 38 /\ t mod 8 = 0 ⌝.
  Proof using . iIntros "#Hc". iApply (ush_cmd_addr with "Hc"). Qed.

  (* argv[0], in the two shapes runcmd's EXEC arm reads it: the POINTER
     SLOT the [c.ld a0,8(s1)] at 0xce loads, and the STRING the diagnostic
     tail prints.  [UkShRun.ush_argv0] is the generic form; at [echo_cmd]
     the [match] on the vector is already decided. *)
  Lemma echo_cmd_argv0_x (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) :
    exec_ok ws ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    ush_ptr gd (t + 8) (s0 + Z.of_nat (echo_off ws 0%nat))
    ∗ ush_str gd (UArg (s0 + Z.of_nat (echo_off ws 0%nat)) (echo_alen ws 0%nat)
                    (fun j : nat => g (echo_off ws 0%nat + j)%nat)).
  Proof using .
    intro Hok. iIntros "#Hc". iSplit.
    - iDestruct (echo_cmd_word_x ws gd t s0 g 0%nat Hok
                   ltac:(exact (exec_ok_pos ws Hok)) with "Hc") as "#Hw".
      assert (E : t + 8 + 8 * Z.of_nat 0%nat = t + 8) by lia.
      iEval (rewrite E) in "Hw".
      rewrite /ush_ptr. iExact "Hw".
    - iDestruct (echo_cmd_str_x ws gd t s0 g 0%nat Hok
                   ltac:(exact (exec_ok_pos ws Hok)) with "Hc")
        as "[%Hr #Hs]".
      rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplit; [ iPureIntro; exact Hr | iExact "Hs" ].
  Qed.

  Lemma echo_cmd_argv0 (ws : list (list (bv 8))) (gd : gname) (t s0 : Z)
      (g : nat -> bv 8) :
    line_ok ws ->
    ush_cmd gd t (echo_cmd ws s0 g) -∗
    ush_ptr gd (t + 8) (s0 + Z.of_nat (echo_off ws 0%nat))
    ∗ ush_str gd (UArg (s0 + Z.of_nat (echo_off ws 0%nat)) (echo_alen ws 0%nat)
                    (fun j : nat => g (echo_off ws 0%nat + j)%nat)).
  Proof using .
    intro Hok__.
    exact (echo_cmd_argv0_x ws gd t s0 g (line_ok_exec_ok _ Hok__)).
  Qed.

  (* =================================================================== *)
  (* S2  THE PINNED EXEC SUPPLY, at sh's own key.                         *)
  (*                                                                      *)
  (* [UkRun.uxsup_at] is the exec bundle at EVERY key; a PINNED bundle is  *)
  (* about a PATH, and a relative path names a file only against the       *)
  (* directory it is resolved from -- so what a pinned supplier can pay is *)
  (* [UkRun.udepw_at] at ONE cwd, and the leaf that takes it is            *)
  (* [UkRunSys.wp_uk_ecall_exec_at_cwd] ([UkInit.wp_kinit_exec] is the     *)
  (* landed call site).  This is init's [init_exec_sup_pos] at sh.         *)
  (*                                                                      *)
  (* WHAT IT IS LENT AND WHAT IT READS.  [udepw_at] hands the supplier the *)
  (* key's two authorities and takes them back: the bundle owes            *)
  (* [SpecSysExec.exec_path_of M pv pl] and                                *)
  (* [SpecSysExec.exec_args_of M av na alen afun], both readings of the    *)
  (* image [M] at the key, and the node is what answers them -- the argv   *)
  (* words at [t+8], the NULL cap, and the three [ustr]s, all              *)
  (* [DfracDiscarded] and so all readable off the lent [UserHeap.uheap].   *)
  (*                                                                      *)
  (* THE CHILD'S PAYLOAD IS TRIVIAL.  The process that execs is the one sh *)
  (* FORKED, and [UkFork.wp_uk_ecall_fork_any]'s child arm gives the       *)
  (* equation ([UkRun.ukn_triv]); so [Q := fun _ => True] throughout and   *)
  (* the taint arm's generic slot is [UexecExecMint.uslot_mint_all] at it. *)
  (* =================================================================== *)
  (* AT THE CHILD'S PAID PAYLOAD (lane IO-LEAF, step 4): the process that
     execs is the one sh FORKED, and its payload is the one sh CHOSE at the
     fork ([UkShFork.ushf_wq] -- the credential after echo's block, or the
     block still owed) -- so [Q] is a parameter, and so is what the child
     was LENT ([Cr], the block credential the paid entry is built on).
     [UShEcho.sh_exec_sup_of_echo_slot] is the one discharge. *)
  Definition sh_exec_sup_echo (ws : list (list (bv 8))) (Q : Z -> iProp Σ)
      (Cr : iProp Σ) : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64)
          (s0 t : Z) (g : nat -> bv 8) (ld : list fdstate),
          ⌜ ukn_pay N' = Q ⌝ -∗
          (* ...AND THE EXEC'ING RECORD HOLDS NO OFFSET HALF (lane
             OFF-HAND-4, S2).  echo's entry is minted at [ukn_held = empty]
             and [ExecEntry.image_entry_at] no longer relays the key's
             all-parked row, so the SUPPLIER says it about the table it
             execs with -- read off its own run
             ([UkRun.urun_rows_parked]). *)
          (* argv[0]'s string, which is the PATH exec resolves... *)
          ⌜ m !!! Regidx a0_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          (* ...and [&argv[0]], which is the VECTOR it reads *)
          ⌜ m !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64) ⌝ -∗
          ⌜ echo_argv_bytes ws g ⌝ -∗
          (* ...AND THE CHILD'S fd 1 IS THE CONSOLE (step 4): echo's paid
             entry writes on it, and the fact is about the TABLE the exec
             channel carries verbatim -- so the ledger fragment goes in
             here, where the deposit meets the table's authority *)
          ⌜ UkSh.ush_fd1p ld ⌝ -∗
          UserFd.ustd (ukn_fd N') ld -∗
          ush_cmd (ukn_d N') t (echo_cmd ws s0 g) -∗
          Cr -∗
          (* AT THE REFUND THE SUPPLIER NAMES ([UkRunExecRef.udepw_at_refR]):
             a failed exec hands the ledger fragment and the lend back
             whole, which is what the diagnostic's exit pays with *)
          udepw_at_refR N' m pc FsImg.ROOTINO
            (UserFd.ustd (ukn_fd N') ld ∗ Cr)))%I.

  Global Instance sh_exec_sup_echo_persistent ws Q Cr :
    Persistent (sh_exec_sup_echo ws Q Cr).
  Proof using . rewrite /sh_exec_sup_echo. apply _. Qed.

  (* ===================================================================== *)
  (* THE SAME SUPPLY AT AN ABSTRACT fd-1 ROW (lane SH-CHILD-2).             *)
  (*                                                                       *)
  (* The only thing the arm below does with fd 1 is pass the row to the     *)
  (* supply, and the redirect child's fd 1 is a FILE                        *)
  (* ([FdOpen false true (FdInode i γo om)]), not the console.  So the row  *)
  (* is a parameter; echo's is the instance at [UkSh.ush_fd1p].             *)
  (*                                                                       *)
  (* A COPY AND NOT AN ALIAS, deliberately: [UShEchoPay.                    *)
  (* sh_exec_sup_echo_wq_holds] (lane LINK-GEN-3's file) UNFOLDS            *)
  (* [sh_exec_sup_echo] and introduces its box, so the landed definition    *)
  (* has to keep a body of its own.  The two are convertible at             *)
  (* [Fd1 := UkSh.ush_fd1p] and [sh_exec_sup_echo_at_fd1p] is that step.    *)
  (* ===================================================================== *)
  Definition sh_exec_sup_echo_at (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8))) (Q : Z -> iProp Σ)
      (Cr : iProp Σ) : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64)
          (s0 t : Z) (g : nat -> bv 8) (ld : list fdstate),
          ⌜ ukn_pay N' = Q ⌝ -∗
          ⌜ m !!! Regidx a0_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          ⌜ m !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64) ⌝ -∗
          ⌜ echo_argv_bytes ws g ⌝ -∗
          ⌜ Fd1 ld ⌝ -∗
          UserFd.ustd (ukn_fd N') ld -∗
          ush_cmd (ukn_d N') t (echo_cmd ws s0 g) -∗
          Cr -∗
          udepw_at_refR N' m pc FsImg.ROOTINO
            (UserFd.ustd (ukn_fd N') ld ∗ Cr)))%I.

  (* NOT [apply _] (durable-notes, the fourth silent hang; [UkSh.
     ush_rest_l_persistent] is the same remedy): with the body transparent
     AND its fd-1 row a VARIABLE, the [Persistent] search walks the whole
     obligation -- [udepw_at_refR] and everything under it -- and does not
     return.  Name the instance the box deserves. *)
  Global Instance sh_exec_sup_echo_at_persistent Fd1 ws Q Cr :
    Persistent (sh_exec_sup_echo_at Fd1 ws Q Cr).
  Proof using .
    rewrite /sh_exec_sup_echo_at. apply bi.intuitionistically_persistent.
  Qed.

  (* BOTH UNFOLDED FIRST (durable-notes, the dev loop): at [Fd1 :=
     UkSh.ush_fd1p] the two bodies are the same text, so the match is
     syntactic.  Left to [iIntros "$"] on the FOLDED goal the proofmode
     unifies two [udepw_at_refR]-sized terms through their definitions,
     which is minutes. *)
  Lemma sh_exec_sup_echo_at_fd1p (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Cr : iProp Σ) :
    sh_exec_sup_echo ws Q Cr -∗ sh_exec_sup_echo_at UkSh.ush_fd1p ws Q Cr.
  Proof using .
    rewrite /sh_exec_sup_echo /sh_exec_sup_echo_at. iIntros "$".
  Qed.

  (* THE CWD-INDEXED EXEC STUB.  [UkShRun.wp_kshr_exec] takes the ∀-cwd
     deposit [UkRun.udepw]; a pinned supply cannot pay that (its bundle
     answers at ONE cwd), so the specialised arm needs sh's exec stub at
     the indexed deposit and the program's own half of its working
     directory beside it -- [UkInit.wp_kinit_exec] is the same lemma at
     init's three pcs.  Everything else is [wp_kshr_exec] verbatim: a
     successful exec never comes back, so the only continuation is -1. *)
  Definition wp_kshr_exec_at_cwd (R : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (c : Z) (avail : nat),
      ⊢ shk_code (ukn_t N) -∗
        urun N h m (mword_of_int ShSyms.exec) avail -∗
        UserCwd.ucwd (ukn_cwd N) c -∗
        udepw_at_refR N
          (<[Regidx (mword_of_int 17 : mword 5) := (mword_of_int 7 : mword 64)]> m)
          (mword_of_int 0xcc0) c R -∗
        (∀ h' : CpuId,
           UserCwd.ucwd (ukn_cwd N) c -∗
           (* ...AND THE REFUND (step 4), at the shape the supplier named
              ([UkRunExecRef.wp_uk_ecall_exec_at_cwd_refR]) *)
           R -∗
           urun N h'
             (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                (<[Regidx (mword_of_int 17 : mword 5)
                   := (mword_of_int 7 : mword 64)]> m))
             (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) avail -∗
           mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang).

  (* =================================================================== *)
  (* THE SPECIALISED EXEC ARM.                                            *)
  (*                                                                      *)
  (* [UkShDiag.wp_kshr_runcmd_final] at [c := echo_cmd s0 g], with the two *)
  (* GENERIC supplies replaced by the pinned one and [UserCwd.ucwd_any]    *)
  (* replaced by the root: [ush_simple (echo_cmd s0 g)] is [I] and         *)
  (* [ush_ht] is 1, so the LIST and BACK arms -- the only consumers of     *)
  (* [UkRun.uxsup] -- are not reached at all, which is why this statement  *)
  (* names no generic supply (S5's grep).                                  *)
  (*                                                                      *)
  (* THE CWD IS A PREMISE.  sh's process state carries                     *)
  (* [UserCwd.ucwd_any] ([UkSh.ush_pstate]), which pins no inum; what this *)
  (* arm needs is [ucwd (ukn_cwd N) ROOTINO], and the fact that sh never   *)
  (* leaves the root is SH-OPEN's ([uvis_cwd W = ROOTINO] at sh's entry,   *)
  (* on its own branch).  Taken as a premise here, and the seam is named   *)
  (* in the report.                                                        *)
  (* =================================================================== *)
  (* AT THE PAID PAYLOAD (step 4): the record is CONSTANT-paid at [Q]
     ([UkRun.ukn_const], sh's choice is status-independent) and holds what
     it was lent; a failed exec's diagnostic exits on the refund. *)
  (* ...AND THE DIAGNOSTIC IS PAID (M4b(2)): a child whose exec FAILED
     writes "exec echo failed" on its fd 2 from the refund ([Cr], the
     block credential it was lent) and exits on what the diagnostic's
     bytes leave ([Cd], the block written up to its prompt).  The free law
     [UkSh.sh_deps] is no longer a premise: nothing on this walk spends it. *)
  Definition wp_kshr_exec_echo (ws : list (list (bv 8))) (Q : Z -> iProp Σ)
      (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      line_ok ws ->
      ukn_pay N = Q ->
      (* ...and the record holds no offset half (lane OFF-HAND-4, S2): the
         exec supply below relays it to echo's entry *)
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      echo_argv_bytes ws g ->
      UkSh.ush_fd1p ld ->
      UkSh.ush_fd2p ld ->
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo ws Q Cr -∗
        (* the diagnostic's law, and what its end pays at the exit *)
        UkShDiag.ush_execfail_law Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (echo_cmd ws s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        Cr -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  (* ...AND THE SAME ARM AT AN ABSTRACT fd-1 ROW (lane SH-CHILD-2), which
     is what the REDIRECT child runs: its fd 1 is the file the open
     returned, and the only place the row is read is the supply. *)
  (* THE EXEC ARM AT ANY EXEC'ABLE WORD LIST (2026-09-21).  The arm execs
     [argv[0]] whatever it is; the ONE place it read the command was the
     failed-exec diagnostic, which prints the name back.  So the general arm
     takes the alternative's bytes around the name
     ([UkShDiagAt.ush_execfail_bytes]) and the law at that alternative, and
     echo's is its instance at [alt_execfail]. *)
  Definition wp_kshr_exec_x_at (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8))) (dg : list (bv 8)) (Q : Z -> iProp Σ)
      (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      exec_ok ws ->
      UkShDiagAt.ush_execfail_bytes dg (ws !!! 0%nat) ->
      ukn_pay N = Q ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      echo_argv_bytes ws g ->
      Fd1 ld ->
      UkSh.ush_fd2p ld ->
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo_at Fd1 ws Q Cr -∗
        UkShDiag.ush_execfail_law_at dg (13 + length (ws !!! 0%nat))%nat
          Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (echo_cmd ws s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        Cr -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  Definition wp_kshr_exec_echo_at (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8))) (Q : Z -> iProp Σ)
      (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      line_ok ws ->
      ukn_pay N = Q ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      echo_argv_bytes ws g ->
      Fd1 ld ->
      UkSh.ush_fd2p ld ->
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo_at Fd1 ws Q Cr -∗
        UkShDiag.ush_execfail_law Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (echo_cmd ws s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        Cr -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  (* BOTH SEALED FOR TYPECLASS RESOLUTION (lane SH-CHILD-2; LINK-GEN-6's
     fourth hang shape).  A [Global Instance] whose head is one of these
     applied to a VARIABLE sends every later [Persistent]/[FromModal]
     search down their bodies -- [udepw_at_refR]-sized -- and the opening
     [iIntros] of the walk below wedges.  [local], so the seal does not
     follow the names out of this file. *)
  #[local] Typeclasses Opaque sh_exec_sup_echo_at.
  #[local] Typeclasses Opaque wp_kshr_exec_echo_at.
  #[local] Typeclasses Opaque wp_kshr_exec_x_at.

  Lemma wp_kshr_exec_at_cwd_holds (R : iProp Σ) : wp_kshr_exec_at_cwd R.
  Proof using .
    intros N Hc h m c avail.
    iIntros "#Hcode Hrun Hcwd Hsbx Hcont".
    assert (Hexec : ShSyms.exec = 0xcbe)
      by (destruct shk_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    rewrite Hexec.
    iApply (wp_uk_cli N h m (mword_of_int 0xcbe)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cbe with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 7 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xcbe : mword 64) 2
                 = mword_of_int 0xcc0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    iApply (wp_uk_ecall_exec_at_cwd_refR N h1 m1 (mword_of_int 0xcc0) avail c R
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hcwd Hsbx").
    { iApply (uis_shk_cc0 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xcc0 : mword 64) 4
                 = mword_of_int 0xcc4)
      by (apply bv_eq; vm_compute; reflexivity).
    (* the failed exec's refund goes on to the continuation (step 4) *)
    rewrite E1. iIntros (h2) "Hcwd Hpay Hrun".
    set (m2 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 7 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcc4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cc4 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hcwd Hpay Hrun").
  Qed.

  (* ---- the specialised EXEC arm, PROVED ------------------------------- *)
  Lemma wp_kshr_exec_x_at_holds (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8))) (dg : list (bv 8))
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshr_exec_x_at Fd1 ws dg Q Cr Cd.
  Proof using .
    intros N Hcc h m t szv s0 g ld n Hok Hdgb Hpeq Ha0 Hbytes Hfd1 Hfd2.
    destruct Hdgb as (Hc2 & Hdglk & Hw1 & Harg & Hw2).
    (* THE BUNDLE-INTRO HANG (durable-notes, "iIntros #H on a bundle of
       wands"): [iIntros "#H"] on a bundle of [UkRun.udepw_law]s sends the
       [Persistent] search down [udepw]'s wand chain and it does not return
       AT THIS FILE'S ALTITUDE.  [UkSh.sh_deps] used to be introduced
       linearly for that reason and is GONE from this walk (M4b(2): the
       diagnostic goes through the links); [sh_exec_sup_echo] is still
       introduced linearly and its box stripped by an explicit unfold. *)
    iIntros "#Hcode Hexs #Hxl #Hcd #Hjt #Htree Hsz Hstd Hcwd Hch Hcr Hrun".
    rewrite /sh_exec_sup_echo_at. iDestruct "Hexs" as "#Hexs".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iDestruct (echo_cmd_addr with "Htree") as %[Htr Ht8].
    iDestruct (echo_cmd_argv0_x ws _ _ _ _ Hok with "Htree") as "[#Hw0 #Hstr]".
    iDestruct "Hstr" as "[%Hxr #Hxs]".
    cbn [ua_ptr ua_len ua_bytes] in Hxr.
    (* ---- runcmd's prologue and the jump table ---- *)
    iApply (wp_kshr_entry N (echo_cmd ws s0 g) h m t
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
              (t + 8) (mword_of_int (s0 + Z.of_nat (echo_off ws 0%nat)))
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
                      (mword_of_int (s0 + Z.of_nat (echo_off ws 0%nat))
                       : mword 64)]> m1).
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
                                   (mword_of_int
                                      (s0 + Z.of_nat (echo_off ws 0%nat))
                                    : mword 64));
                    rewrite (moi_eq_zero (s0 + Z.of_nat (echo_off ws 0%nat))
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
              (mword_of_int 3048 : mword 21) (2 + (UkShDiag.ush_Dg + n))
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
                   = (mword_of_int (s0 + Z.of_nat (echo_off ws 0%nat))
                      : mword 64)).
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
    (* THE DEPOSIT, BUILT FIRST AND FULLY EXPLICITLY.  Leaving the key an
       evar for [iApply] to solve makes the proofmode unify against
       [UkRun.udepw_at]'s whole ∀-chain, which does not terminate at this
       altitude (durable-notes, "A compile that never finishes"). *)
    iAssert (udepw_at_refR N
               (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
               (mword_of_int 0xcc0) FsImg.ROOTINO
               (UserFd.ustd (ukn_fd N) ld ∗ Cr))
      with "[Hstd Hcr]" as "Hdepx".
    { iApply ("Hexs" $! N
                (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                (mword_of_int 0xcc0) s0 t g ld
                with "[%] [%] [%] [%] [%] Hstd Htree Hcr").
      - exact Hpeq.
      - (* [echo_off 0] IS 0; the supply names the token's base, the load
           named its offset from the node, and the two are the same [Z]. *)
        assert (Hoff0 : s0 + Z.of_nat (echo_off ws 0%nat) = s0)
          by (rewrite (echo_off_0 ws); lia).
        rewrite <- Hoff0. exact Hka0.
      - exact Hka1.
      - exact Hbytes.
      - exact Hfd1. }
    (* the budget is a [nat] and the cwd a [Z]; [wp_kshr_exec_at_cwd] is a
       [Definition ... : Prop], so its argument scopes are not visible at
       elaboration and the [%nat] has to be written. *)
    iApply (wp_kshr_exec_at_cwd_holds (UserFd.ustd (ukn_fd N) ld ∗ Cr)
              N Hcc h5 k3 FsImg.ROOTINO
              ((2 + (UkShDiag.ush_Dg + n))%nat)
              with "Hcode Hrun Hcwd Hdepx").
    rewrite Hrk3. iIntros (h6) "Hcwd [Hstd Hcr] Hrun".
    (* ---- 0xda: "exec %s failed" -- PAID (M4b(2)): the diagnostic's
       bytes go out on the refund, and the exit on what they leave ---- *)
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
    iApply (UkShDiagAt.wp_kshd_execfail_paid_at N dg (ws !!! 0%nat) Cr Cd
              ld h6 k4 (2 + n)
              (UArg (s0 + Z.of_nat (echo_off ws 0%nat)) (echo_alen ws 0%nat)
                 (fun j : nat => g (echo_off ws 0%nat + j)%nat))
              Hfd2 ltac:(rewrite Hs1_k4; exact Ht8) Hc2 eq_refl
              ltac:(intros j Hj; cbn [ua_bytes];
                    rewrite (proj1 Hbytes 0%nat j
                               ltac:(exact (exec_ok_pos ws Hok)) Hj);
                    rewrite (echo_off_0 ws) Nat.add_0_l;
                    exact (echo_line_word0 ws j Hok Hj))
              Hdglk Hw1 Harg Hw2
              with "Hxl Hcode Hro [] [] Hstd Hcr [] Hrun").
    { rewrite Hs1_k4. cbn [ua_ptr]. iExact "Hw0". }
    { rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplitR; [ iPureIntro; exact Hxr | iExact "Hxs" ]. }
    { iIntros "_ Hc". rewrite <- Hpeq. iApply ("Hcd" with "Hc"). }
  Qed.

  (* ECHO'S BYTES: the landed diagnostic's alternative around its name *)
  Lemma echo_execfail_bytes : UkShDiagAt.ush_execfail_bytes alt_execfail cmd_echo.
  Proof using .
    rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
    - vm_compute. lia.
    - intros p Hp.
      assert (Hl : (p < length alt_execfail)%nat) by (vm_compute in Hp |- *; lia).
      exact (list_lookup_lookup_total_lt alt_execfail p Hl).
    - intros p Hp.
      apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
               (fun q : nat => alt_execfail !!! q) 0%nat 5%nat);
        [ vm_compute; reflexivity | lia ].
    - intros j Hj.
      assert (Hj4 : (j < 4)%nat) by (vm_compute in Hj; lia).
      destruct j as [| [| [| [| j]]]]; try lia; vm_compute; reflexivity.
    - intros p Hp.
      apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
               (fun q : nat => alt_execfail !!! (q + 2)%nat) 7%nat 8%nat);
        [ vm_compute; reflexivity | lia ].
  Qed.

  Lemma wp_kshr_exec_echo_at_holds (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshr_exec_echo_at Fd1 ws Q Cr Cd.
  (* THE GENERAL ARM, at echo's alternative.  BY CONVERSION ([exact], not the
     proofmode -- see [wp_kshr_exec_echo_holds]): with the head word read as
     [cmd_echo] the law's index [13 + 4] computes to the landed 17. *)
  Proof using .
    intros N Hcc h m t szv s0 g ld n Hok Hpeq Ha0 Hbytes Hfd1 Hfd2.
    pose proof (list_lookup_total_correct ws 0%nat cmd_echo
                  (line_ok_head ws Hok)) as Hhd.
    pose proof (wp_kshr_exec_x_at_holds Fd1 ws alt_execfail Q Cr Cd
                  N Hcc h m t szv s0 g ld n (line_ok_exec_ok ws Hok)
                  ltac:(rewrite Hhd; exact echo_execfail_bytes)
                  Hpeq Ha0 Hbytes Hfd1 Hfd2) as Hx.
    rewrite Hhd in Hx. exact Hx.
  Qed.

  (* ...and the landed arm is that one at the console row. *)
  Lemma wp_kshr_exec_echo_holds (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshr_exec_echo ws Q Cr Cd.
  (* BY CONVERSION, not by [iApply]: the landed arm's statement IS the
     general one at [Fd1 := UkSh.ush_fd1p], delta-beta.  Elaborating the
     application through the proofmode instead costs tens of minutes on
     this file. *)
  Proof using .
    exact (wp_kshr_exec_echo_at_holds UkSh.ush_fd1p ws Q Cr Cd).
  Qed.

  (* =================================================================== *)
  (* THE DISPATCH, in [UkShMain.wp_kshm_child]'s place.                   *)
  (*                                                                      *)
  (* [wp_kshm_child_alloc] is already parametric in the token list, so the *)
  (* specialisation is at [toks := echo_toks ws]; what CHANGES is the      *)
  (* supply                                                                *)
  (* it hands the runner (pinned, not [UkRun.uxsup]) and the cwd.  The     *)
  (* two premises the generic lemma takes about the line                   *)
  (* ([ushp_no_symbols], [ushp_tokens]) are replaced by the ONE fact the   *)
  (* disciplined branch has -- [UConsLine.ush_line_is] -- through          *)
  (* [ush_line_toks] above.                                                *)
  (*                                                                      *)
  (* THE TAINTED BRANCH IS THE GENERIC ONE and does not appear here:       *)
  (* under the taint sh's line is unknown, the parse is whatever it is,    *)
  (* and [UkShMain.wp_kshm_child_alloc] runs on [UkRun.uxsup] exactly as   *)
  (* it does today.  The disjunction is [UConsLine.ush_rest_line]'s, and   *)
  (* the case split belongs to the body that holds it (SH-LINE 2b).        *)
  (* =================================================================== *)
  (* THE CHILD'S WALK AT ANY EXEC'ABLE LINE (2026-09-21), AND AT ANY ROW
     PREDICATE the supply asks of the child's table ([Fd1], as the arm's:
     echo's entry reads row 1, cat's rows 0-2): parse, then the exec arm.  Nothing in it reads the command but the failed-exec
     diagnostic ([wp_kshr_exec_x_at]); echo's walk is its instance. *)
  Definition wp_kshm_child_x (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8)))
      (dg : list (bv 8)) (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N)
           (h : CpuId) (m : regfile) (dw dv : dfrac)
           (s0 : Z) (len : nat) (f : nat -> bv 8) (sz : Z)
           (ld : list fdstate) (n : nat),
      ukn_pay N = Q ->
      (* ...and the record holds no offset half -- [wp_kshr_exec_echo] *)
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      ush_xline_is ws f 0%nat len ->
      UkShDiagAt.ush_execfail_bytes dg (ws !!! 0%nat) ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      8344 <= sz ->
      UserPtTree.pgroundup sz = sz ->
      usz_ok (sz + 65536) ->
      Fd1 ld ->
      UkSh.ush_fd2p ld ->
      (* NO FREE WRITE LAW (M4b(2)): the paid child's walk spends it
         nowhere *)
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo_at Fd1 ws Q Cr -∗
        (* what the lend pays where the parser's walk DIES (the null store
           at [memset]) -- and the diagnostic's law and what its end pays
           where the exec FAILED (M4b(2)) *)
        □ (Cr -∗ Q (-1)) -∗
        UkShDiag.ush_execfail_law_at dg (13 + length (ws !!! 0%nat))%nat
          Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        shp_code (ukn_t N) -∗ shp_rodata (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
        ustr (ukn_d N) (DfracOwn 1) s0 len f -∗
        ustr (ukn_d N) dw ushp_whitespace 5 ushp_ws_f -∗
        ustr (ukn_d N) dv ushp_symbols 7 ushp_sym_f -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        UkShMalloc.ushm_fresh N sz -∗
        Cr -∗
        urun N h m (mword_of_int 0x9c0)
          (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  Definition wp_kshm_child_echo (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N)
           (h : CpuId) (m : regfile) (dw dv : dfrac)
           (s0 : Z) (len : nat) (f : nat -> bv 8) (sz : Z)
           (ld : list fdstate) (n : nat),
      ukn_pay N = Q ->
      (* ...and the record holds no offset half -- [wp_kshr_exec_echo] *)
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      UConsLine.ush_line_is ws f 0%nat len ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      8344 <= sz ->
      UserPtTree.pgroundup sz = sz ->
      usz_ok (sz + 65536) ->
      UkSh.ush_fd1p ld ->
      UkSh.ush_fd2p ld ->
      (* NO FREE WRITE LAW (M4b(2)): the paid child's walk spends it
         nowhere *)
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo ws Q Cr -∗
        (* what the lend pays where the parser's walk DIES (the null store
           at [memset]) -- and the diagnostic's law and what its end pays
           where the exec FAILED (M4b(2)) *)
        □ (Cr -∗ Q (-1)) -∗
        UkShDiag.ush_execfail_law Cr Cd -∗
        □ (Cd -∗ Q (-1)) -∗
        shp_code (ukn_t N) -∗ shp_rodata (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
        ustr (ukn_d N) (DfracOwn 1) s0 len f -∗
        ustr (ukn_d N) dw ushp_whitespace 5 ushp_ws_f -∗
        ustr (ukn_d N) dv ushp_symbols 7 ushp_sym_f -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        UkShMalloc.ushm_fresh N sz -∗
        Cr -∗
        urun N h m (mword_of_int 0x9c0)
          (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
        mWP (Loop : expr riscv_lang).

  Lemma wp_kshm_child_x_holds (Fd1 : list fdstate -> Prop)
      (ws : list (list (bv 8)))
      (dg : list (bv 8)) (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshm_child_x Fd1 ws dg Q Cr Cd.
  Proof.
    intros N Hc h m dw dv s0 len f sz ld n
      Hpeq Hs1 Hline Hdgb Hs0 Hs64 Hs38 Hszlo Hszal Hszok Hfd1 Hfd2.
    (* the line the discipline admits, as the parser's own premises *)
    pose proof (proj1 Hline) as Hok.
    destruct (ush_line_toks_x_holds ws f 0%nat len Hline) as (_ & Hns0 & Htoks0).
    assert (Hns : ushp_no_symbols len f) by exact Hns0.
    assert (Htoks : ushp_tokens len f 0%nat (echo_toks ws)) by exact Htoks0.
    pose proof (echo_toks_lt10_x ws Hok) as Htlen.
    assert (Hbytes : echo_argv_bytes ws
              (ushp_nulfold (echo_toks ws) (ushp_ext len f)))
      by exact (echo_argv_bytes_of_line_x_holds ws f 0%nat len Hline).
    (* the pinned supply LINEARLY, as in [wp_kshr_exec_echo_holds]: it is
       spent exactly once, at the arm below, and introducing it with [#]
       does not return here.  No [UkSh.sh_deps] anywhere on this walk
       (M4b(2)). *)
    iIntros "#Hcode Hexs #Hcq #Hxl #Hcd #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd
             Hcwd Hch HM Hcr Hrun".
    (* the line's own bytes are non-NUL, which is what makes each token a
       string once the cut lands *)
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
    (* ---- 0x9c0  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx))
              (60 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_shk_9c0 with "Hcode"). }
    assert (E9c0 : add_vec_int (mword_of_int 0x9c0 : mword 64) 2
                   = mword_of_int 0x9c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9c0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
    { rewrite /m1 (upd_eq m (Regidx a0_idx) _).
      rewrite Hs1. apply bv_eq. rewrite add_vec_unsigned.
      unfold bv_wrap. cbn [bv_unsigned]. rewrite Z.add_0_l.
      rewrite Z.mod_small; [ reflexivity | ].
      pose proof (bv_unsigned_in_range _ (mword_of_int s0 : mword 64)) as Hr.
      assert (Hm : bv_modulus (MachineWord.Z_idx 64) = 18446744073709551616%Z)
        by (vm_compute; reflexivity).
      rewrite Hm in Hr. exact Hr. }
    assert (Hs1_1 : m1 !!! Regidx s1_idx = (mword_of_int s0 : mword 64))
      by (rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x9c2  jal ra,parsecmd ---- *)
    iApply (wp_uk_jal N h1 m1 (mword_of_int 0x9c2)
              (mword_of_int 2096812 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.parsecmd) (mword_of_int 0x9c6)
              (60 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9c6 : mword 64)]> m1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      by (rewrite /m2 (upd_ne m1 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_1).
    assert (Hra_2 : ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))
                    = (mword_of_int 0x9c6 : mword 64))
      by (rewrite /m2 (upd_eq m1 (Regidx (mword_of_int 1 : mword 5)) _);
          apply bv_eq; vm_compute; reflexivity).
    (* ---- parsecmd ---- *)
    (* the exit payload goes down the parser's walk (lane IO-LEAF, M3c):
       [malloc] can return NULL and the store through it kills this
       process.  This walk still has it for free. *)
    (* the exit resource down the parser's walk is the LEND (step 4): the
       law [Hcq] pays the exit where the walk dies, and the lend comes back
       on the arm where the allocation succeeded, for the exec below *)
    iAssert (□ (Cr -∗ ukn_pay N (-1)))%I as "#Hpxw".
    { iIntros "!> Hc". rewrite Hpeq. iApply ("Hcq" with "Hc"). }
    (* the parser takes the BOUNDED capability (lane SH-MALLOC-3) and the
       allocator's adapter proves the unbounded one; 168 <= 65504 *)
    iApply (UkShParseCmd.wp_kshp_parser N (UkShMalloc.ushm_fresh N sz)
              (usz (ukn_s N) (sz + 65536))
              (UkShParse.ushp_malloc_ty_le_mono N 65504 168 _ _ ltac:(lia)
                 (UkShParse.ushp_malloc_ty_le_top N _ _
                    (UkShMalloc.ushm_malloc_ok_holds N Hpsok_free sz
                       Hszlo Hszal Hszok)))
              h2 m2 dw dv s0 len f (echo_toks ws)
              (8 + (UkShDiag.ush_Dg + n))
              Ha0_2 Hns Htoks Htlen Hs0 Hs64
              with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (p) "%Hparses Hnode Hline %Hcut Hws Hsy".
    iIntros (h3 m3) "%Hcs3 %Ha0_3 Hsz Hcr Hrun".
    rewrite Hra_2.
    (* ---- 0x9c6  jal ra,runcmd ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
              (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
              (60 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9ca : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int p : mword 64))
      by (rewrite /m4 (upd_ne m3 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_3).
    (* ---- THE SEAM: the node the parser built is the tree runcmd walks ---- *)
    iMod (UkShMain.ush_cmd_of_ushp N h4 m4 (mword_of_int ShSyms.runcmd)
            (60 + (8 + (UkShDiag.ush_Dg + n))) s0 p len f (echo_toks ws)
            Htoks Hns Hnn0 Hlen31 Hs0 Hs38
            with "Hrun Hnode Hline") as "(Hrun & #Htree)".
    (* ---- THE PINNED EXEC ARM, at the ONE command the line spells ---- *)
    (* [echo_cmd] is a [UExec], so [ush_ht] is 1 and the budget is the
       generic arm's at [c := echo_cmd s0 g]; the LIST and BACK arms -- the
       only consumers of [UkRun.uxsup] -- are not reached, which is why no
       generic supply appears anywhere in this walk. *)
    replace (60 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (60 + n))))%nat by lia.
    iApply (wp_kshr_exec_x_at_holds Fd1 ws dg Q Cr Cd N _ h4 m4 p
              (sz + 65536) s0
              (ushp_nulfold (echo_toks ws) (ushp_ext len f)) ld ((60 + n)%nat)
              Hok Hdgb Hpeq Ha0_4 Hbytes Hfd1 Hfd2
              with "Hcode Hexs Hxl Hcd Hjt Htree Hsz Hstd Hcwd Hch Hcr Hrun").
  Qed.

  Lemma wp_kshm_child_echo_holds (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshm_child_echo ws Q Cr Cd.
  (* THE GENERAL WALK, at echo's alternative -- by conversion, as the arm. *)
  Proof.
    intros N Hc h m dw dv s0 len f sz ld n
      Hpeq Hs1 Hline Hs0 Hs64 Hs38 Hszlo Hszal Hszok Hfd1 Hfd2.
    pose proof (proj1 Hline) as Hok.
    pose proof (list_lookup_total_correct ws 0%nat cmd_echo
                  (line_ok_head ws Hok)) as Hhd.
    pose proof (wp_kshm_child_x_holds UkSh.ush_fd1p ws alt_execfail Q Cr Cd
                  N Hc h m dw dv s0 len f sz ld n
                  Hpeq Hs1 (ush_xline_is_of_line ws f 0%nat len Hline)
                  ltac:(rewrite Hhd; exact echo_execfail_bytes)
                  Hs0 Hs64 Hs38 Hszlo Hszal Hszok Hfd1 Hfd2) as Hx.
    rewrite Hhd in Hx. exact Hx.
  Qed.

  (* =================================================================== *)
  (* S3b THE BODY'S CHILD LAW, DISCHARGED (lane IO-LEAF, step 4).         *)
  (*                                                                      *)
  (* [UkShFork.ushf_child_law] is the dispatch above at the payload sh's   *)
  (* fork chose -- [ushf_wq I], the credential after echo's block or the   *)
  (* block still owed -- and the lend [Wc I 3], for every boundary [I].    *)
  (* The line the child runs is the LAST body of that boundary             *)
  (* ([LineWords.last_ws I]), which is what [UkSh.ush_posw] ties together. *)
  (* The exec supply at that payload is the one thing it needs, and it is  *)
  (* the application's to give ([UShEcho.sh_exec_sup_of_echo_slot]).       *)
  (* =================================================================== *)
  (* GUARDED BY THE LINE'S ADMISSIBILITY (project echo-any-line): the
     supply is about the line the boundary's last body parses to, and
     every reading the entry makes of it -- the argument count, the
     command name's length, the stack room -- is a reading of an
     ADMISSIBLE line.  The guard costs the fork nothing: the line it
     lends the child came out of [gets], which delivers [line_ok]
     ([UkSh.ush_line_is]'s first conjunct). *)
  (* ...AND THE GUARD IS A PARAMETER (the PROGRAM STREAM).  [line_ok] is
     ECHO's reading of "this input's line is one I supply for", and it is
     the whole reading only because that era has ONE line shape.  The file
     era has three, and its supply is about the [LEcho] ones alone -- at an
     [LEchoF] input the child writes to the FILE and the console block is
     the prompt, so the lend does not open into echo's stage at all.  So
     the era says which inputs its supply is about, and echo's instance is
     the landed one.  What the CONSUMER must then prove is [D I] at the
     input it applies the law at, and [UkShFork.ushf_child_law_at]'s box
     carries exactly the two facts that need ([line_ok ws] out of the line
     and [FileDisc.fbody_ok] out of the slot). *)
  Definition sh_exec_sup_echo_wq_at (D : list (bv 8) -> Prop)
      (Wc : list (bv 8) -> nat -> iProp Σ) : iProp Σ :=
    (□ (∀ I : list (bv 8),
          ⌜D I⌝ -∗
          sh_exec_sup_echo (last_ws I) (fun _ : Z => UkShFork.ushf_wq Wc I)
            (Wc I 3%nat)))%I.

  Definition sh_exec_sup_echo_wq (Wc : list (bv 8) -> nat -> iProp Σ)
      : iProp Σ :=
    sh_exec_sup_echo_wq_at (fun I => line_ok (last_ws I)) Wc.

  Global Instance sh_exec_sup_echo_wq_at_persistent D Wc :
    Persistent (sh_exec_sup_echo_wq_at D Wc).
  Proof using .
    rewrite /sh_exec_sup_echo_wq_at. apply bi.intuitionistically_persistent.
  Qed.

  Global Instance sh_exec_sup_echo_wq_persistent Wc :
    Persistent (sh_exec_sup_echo_wq Wc).
  Proof using . rewrite /sh_exec_sup_echo_wq. apply _. Qed.

  (* ...and the diagnostic's law at the same two ends (M4b(2)): from the
     block owed to the block written up to its prompt, at every boundary.
     THE DIAGNOSTIC IS A PARAMETER (lane LINK-GEN-4), as it already is one
     level down ([UkShDiag.ush_execfail_law_at dg n]).  An era whose
     exec-failed alternative depends on the LINE -- the file's
     [FileHooks.fexfb], which is [alt_execcat] at an [LCat] line --
     cannot answer the constant form at every input, and the producer
     ([UShPanic.ush_execfail_law_hold_at]) delivers it at [lk_exfb L I]
     anyway.  So the carrier takes the bytes and their index as functions
     of the input, and echo's is this at the constants. *)
  Definition ush_execfail_law_wq_at (dg : list (bv 8) -> list (bv 8))
      (nn : list (bv 8) -> nat) (Wc : list (bv 8) -> nat -> iProp Σ)
      : iProp Σ :=
    (□ (∀ I : list (bv 8),
          UkShDiag.ush_execfail_law_at (dg I) (nn I)
            (Wc I 3%nat) (Wc I 0%nat)))%I.

  Definition ush_execfail_law_wq (Wc : list (bv 8) -> nat -> iProp Σ)
      : iProp Σ :=
    ush_execfail_law_wq_at (fun _ => alt_execfail) (fun _ => 17%nat) Wc.

  Global Instance ush_execfail_law_wq_at_persistent dg nn Wc :
    Persistent (ush_execfail_law_wq_at dg nn Wc).
  Proof using . rewrite /ush_execfail_law_wq_at. apply _. Qed.
  Global Instance ush_execfail_law_wq_persistent Wc :
    Persistent (ush_execfail_law_wq Wc).
  Proof using . rewrite /ush_execfail_law_wq. apply _. Qed.

  (* ...AND THE WEAKENING, [UkSh.ush_tag_law_of_at]'s pattern: an era whose
     exec-failed bytes ARE the constants answers the landed carrier.  This
     is the ONE step a second application still owes at an ECHO line, and
     [UkShFork.ushf_child_law_at]'s own [Lp] is what should imply it --
     see the lane's findings. *)
  Lemma ush_execfail_law_wq_of_at (dg : list (bv 8) -> list (bv 8))
      (nn : list (bv 8) -> nat) (Wc : list (bv 8) -> nat -> iProp Σ) :
    (forall I : list (bv 8), dg I = alt_execfail) ->
    (forall I : list (bv 8), nn I = 17%nat) ->
    ush_execfail_law_wq_at dg nn Wc -∗ ush_execfail_law_wq Wc.
  Proof using .
    intros Hdg Hnn. iIntros "#Hx".
    rewrite /ush_execfail_law_wq /ush_execfail_law_wq_at.
    iIntros "!>" (I). rewrite <- (Hdg I), <- (Hnn I). iApply ("Hx" $! I).
  Qed.

  (* ...AND THE DIAGNOSTIC'S LAW UNDER THE SAME GUARD (lane HOLD-POS).
     [ush_execfail_law_wq_at] quantifies over EVERY input, and at a
     position-keyed family that is not a statement an era can meet: the
     file era's exit at position 0 ties the deed to the alternative the
     child FILED, and at an [echo ... > f] input the exec-failed
     alternative ([RFExec]) truncates `f` while the lend's deed is still at
     the round's PRE-state -- so [Wc I 0] is unreachable there, and the law
     was never spent there either ([ushf_child_law_holds_at] reads it only
     at an input the era admits).  The guard is the child law's own [D]. *)
  Definition ush_execfail_law_wq_at_D (D : list (bv 8) -> Prop)
      (dg : list (bv 8) -> list (bv 8))
      (nn : list (bv 8) -> nat) (Wc : list (bv 8) -> nat -> iProp Σ)
      : iProp Σ :=
    (□ (∀ I : list (bv 8),
          ⌜D I⌝ -∗
          UkShDiag.ush_execfail_law_at (dg I) (nn I)
            (Wc I 3%nat) (Wc I 0%nat)))%I.

  Global Instance ush_execfail_law_wq_at_D_persistent D dg nn Wc :
    Persistent (ush_execfail_law_wq_at_D D dg nn Wc).
  Proof using . rewrite /ush_execfail_law_wq_at_D. apply _. Qed.

  (* the unguarded carrier answers the guarded one *)
  Lemma ush_execfail_law_wq_at_D_of (D : list (bv 8) -> Prop)
      (dg : list (bv 8) -> list (bv 8))
      (nn : list (bv 8) -> nat) (Wc : list (bv 8) -> nat -> iProp Σ) :
    ush_execfail_law_wq_at dg nn Wc -∗ ush_execfail_law_wq_at_D D dg nn Wc.
  Proof using .
    iIntros "#Hx". rewrite /ush_execfail_law_wq_at /ush_execfail_law_wq_at_D.
    iIntros "!>" (I) "_". iApply ("Hx" $! I).
  Qed.

  (* ...AT THE ERA'S OWN GUARD AND ITS OWN DIAGNOSTIC (the PROGRAM
     STREAM).  Both parameters are answered by ONE fact about the input --
     [D I] -- and the two facts that prove it are in the law's own box: the
     line the fork lends is [line_ok] ([ush_line_is]'s first conjunct) and
     the slot the loop left says the input's last body PARSES
     ([UkSh.ush_posw]'s third conjunct).  At the file era that is
     [FileDisc.fbody_ok_echo], i.e. "the era filed an [LEcho] line here",
     from which both the stage and [FileHooks.fexfb]'s value follow. *)
  Lemma ushf_child_law_holds_at_D (D : list (bv 8) -> Prop)
      (dg : list (bv 8) -> list (bv 8)) (nn : list (bv 8) -> nat)
      (Wc : list (bv 8) -> nat -> iProp Σ) :
    (forall (I : list (bv 8)) (ws : list (list (bv 8))),
       line_ok ws -> ws = last_ws I ->
       FileDisc.fline_ok (UkSh.ush_lastbody I) -> D I) ->
    (forall I : list (bv 8),
       D I -> dg I = alt_execfail /\ nn I = 17%nat) ->
    ush_execfail_law_wq_at_D D dg nn Wc -∗
    sh_exec_sup_echo_wq_at D Wc -∗ UkShFork.ushf_child_law Wc.
  Proof using Hpsok_free.
    intros HD Hdg. iIntros "#Hxl #Hsup".
    rewrite /UkShFork.ushf_child_law /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv s0 len ws g sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfbk %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok %Hrows
       #Hcode #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd Hcwd Hch _ HM Hcr Hrun".
    (* the two rows design app-pipe SS4.3w bought (purchase 2) are FREE for
       this prover: the echo child's walk does not read its own pid, and
       the set it takes is [UserChildren.uch_any]. *)
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch".
    pose proof (HD I ws (proj1 Hline) Hlws Hfbk) as HDI.
    destruct (Hdg I HDI) as [Hdg1 Hdg2].
    subst ws.
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iApply (wp_kshm_child_echo_holds (last_ws I)
              (fun _ : Z => UkShFork.ushf_wq Wc I)
              (Wc I 3%nat) (Wc I 0%nat) N' Hc h m dw dv s0 len g sz ld n
              Hpeq Hs1 Hline Hs0 Hs64 Hs38 Hszlo Hszal Hszok
              (proj1 (proj2 Hrows)) (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hline Hws Hsy Hstd Hcwd Hch
                    HM Hcr Hrun").
    - iApply ("Hsup" $! I). iPureIntro. exact HDI.
    - (* a child that died at the null store exits on the block it was
         lent *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iLeft. iExact "Hc".
    - (* THE DIAGNOSTIC, AT THE ERA'S CARRIER READ AT THIS INPUT *)
      rewrite /UkShDiag.ush_execfail_law.
      rewrite <- Hdg1. rewrite <- Hdg2.
      iApply ("Hxl" $! I). iPureIntro. exact HDI.
    - (* a failed exec's child exits on the block written up to its prompt *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iRight. iExact "Hc".
  Qed.

  (* ...and the landed statement, through the guarded one.  ITS GUARD IS
     [FileDisc.fline_ok] AND NOT [fbody_ok] (lane ULINE-LPIPE): "the input's
     last body is in [FileDisc.parse_line]'s range" is the FILE era's
     reading of [UkSh.ush_posw]'s third conjunct, and the conjunct is what
     [ushf_child_law_holds_at_D] takes -- an era whose lines the file parser
     refuses (the pipeline application's, whose body carries a bar) can
     supply the weaker one and never the stronger.  Weakening a PREMISE
     makes this lemma stronger, so no caller loses anything: the echo era's
     ([ushf_child_law_holds] below) ignores the argument and the file era's
     ([UShRound.file_D_of_line]) spends it through
     [FileDisc.fline_ok_echo]. *)
  Lemma ushf_child_law_holds_at (D : list (bv 8) -> Prop)
      (dg : list (bv 8) -> list (bv 8)) (nn : list (bv 8) -> nat)
      (Wc : list (bv 8) -> nat -> iProp Σ) :
    (forall (I : list (bv 8)) (ws : list (list (bv 8))),
       line_ok ws -> ws = last_ws I ->
       FileDisc.fline_ok (UkSh.ush_lastbody I) -> D I) ->
    (forall I : list (bv 8),
       D I -> dg I = alt_execfail /\ nn I = 17%nat) ->
    ush_execfail_law_wq_at dg nn Wc -∗
    sh_exec_sup_echo_wq_at D Wc -∗ UkShFork.ushf_child_law Wc.
  Proof using Hpsok_free.
    intros HD Hdg. iIntros "#Hxl #Hsup".
    iApply (ushf_child_law_holds_at_D D dg nn Wc HD Hdg with "[] Hsup").
    iApply (ush_execfail_law_wq_at_D_of D dg nn Wc with "Hxl").
  Qed.

  (* the landed name: the echo era's guard is [line_ok] and its diagnostic
     is the constant one *)
  Lemma ushf_child_law_holds (Wc : list (bv 8) -> nat -> iProp Σ) :
    ush_execfail_law_wq Wc -∗
    sh_exec_sup_echo_wq Wc -∗ UkShFork.ushf_child_law Wc.
  Proof.
    iIntros "#Hxl #Hsup".
    iApply (ushf_child_law_holds_at (fun I => line_ok (last_ws I))
              (fun _ => alt_execfail) (fun _ => 17%nat) Wc
              ltac:(intros I ws Hok Heq _; subst ws; exact Hok)
              ltac:(intros I _; split; reflexivity)
              with "Hxl Hsup").
  Qed.

  (* =================================================================== *)
  (* S4  THE PARENT.                                                      *)
  (*                                                                      *)
  (* For [echo_cmd] the parent's round is the LANDED one:                  *)
  (* [UkShFork.wp_kshf_fork]'s parent arm reaps with [wait((int * )0)] --  *)
  (* [UkShRun.wp_kshr_wait], whose answer [ret] is UNCONSTRAINED and whose *)
  (* only moving resource is the index-free [UserChildren.uch_any] -- and  *)
  (* re-enters the loop head with exactly what it carried in.  So the      *)
  (* round's invariant carries NOTHING about the child: not its payload    *)
  (* (the child runs at [fun _ => True]), not its exit status, not a byte  *)
  (* of what echo wrote.  The five conjuncts below ARE the invariant, and  *)
  (* the ONE thing E4 adds to it is the cwd index: the next round's child  *)
  (* must exec on the pin too, so [UserCwd.ucwd_any] in                    *)
  (* [UkSh.ush_pstate] becomes [ucwd (ukn_cwd N) ROOTINO] here.            *)
  (* =================================================================== *)
  (* [T] IS A PARAMETER (lane IO-LEAF, M5(3)): the fourth conjunct is the
     cursor AT A LINE BOUNDARY now, whose other arm is the taint. *)
  (* ...AND THE PID ROW BESIDE THE CHILDREN SET (step 4), and the cwd
     PINNED at the root in [UkSh.ush_pstate] itself now (SH-LINE R3(2)):
     the index below is kept for E4's round, and is the root. *)
  Definition ush_pstate_at (N : uk_names Σ) (gp : gname) (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ) (Wb : list (bv 8) -> iProp Σ)
      (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) (c : Z) : iProp Σ :=
    (UkSh.ush_std N l ∗ UserCwd.ucwd (ukn_cwd N) c
     (* the two identity conjuncts are PINNED now (lane EXEC-SEAM), as
        [UkSh.ush_pstate]'s are: no children at the head, not <init> *)
     ∗ UserChildren.uch (ukn_ch N) ∅
     ∗ UkSh.ush_pid N
     ∗ UkSh.ush_posb N gp T Wc Wb Pm l 0%nat)%I.

  Lemma ush_pstate_of_at (N : uk_names Σ) (gp : gname) (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ) (Wb : list (bv 8) -> iProp Σ)
      (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) :
    ush_pstate_at N gp T Wc Wb Pm l FsImg.ROOTINO -∗
    UkSh.ush_pstate N gp T Wc Wb Pm l.
  Proof using .
    rewrite /ush_pstate_at /UkSh.ush_pstate.
    iIntros "(Hstd & Hcwd & Hch & Hpid & Hpos)". iFrame "Hstd Hcwd Hch Hpid Hpos".
  Qed.

  (* WHAT CROSSES THE ROUND, named once: the loop head's own resources are
     [UkShLoop.ushl_head]'s and are not re-stated; these are the four the
     fork arm threads through both processes' entry and back out of the
     parent's ([UkShFork.wp_kshf_fork]). *)
  Definition ush_echo_round_carry (N : uk_names Σ) (gp : gname)
      (T : iProp Σ) (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ)
      (Pm : list (bv 8) -> iProp Σ) (l : list fdstate) (sz : Z)
      (f : nat -> bv 8) : iProp Σ :=
    (ush_pstate_at N gp T Wc Wb Pm l FsImg.ROOTINO
     ∗ UkShLoop.ushl_dat (ukn_d N) ∗ usz (ukn_s N) sz
     ∗ ubytes (ukn_d N) UkSh.sh_buf UkSh.sh_nbuf f)%I.

End UkShEcho.
