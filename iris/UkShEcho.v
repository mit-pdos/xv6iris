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
(* ush_line_is]: "echo hello world\n"), so the command is ONE value and    *)
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
Require Import FdSlots UserFd UserCwd UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShMain.
Require Import UkShFork.
Require Import UConsLine.        (* [ush_line_is]: the buffer IS [echo_line] *)
Require Import EchoDisc.         (* [echo_line], [sb], [nlb] *)
Require Import FsImg.            (* [ROOTINO] -- the cwd the pin resolves at *)
Require Import UsysMemOk.        (* [USYS_exec] *)
Require Import UexecSG.          (* [uexecSG] / [uprogSG]: the deposit class *)
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* S1  THE LINE'S COMMAND.                                                *)
(*                                                                        *)
(* THE PARSE IS FUNCTIONAL, and it always was: [UkShParseCmd.             *)
(* wp_kshp_parser] takes the token list as a PREMISE                      *)
(* ([UkShParse.ushp_tokens len f 0 toks]) and returns the node at THAT     *)
(* list ([ushp_tree s0 p (UshpExec toks)]), so there is no determinacy     *)
(* lemma to prove about the parser -- the caller names the tokens.  What   *)
(* the disciplined branch owes is therefore a CLOSED COMPUTATION: the     *)
(* seventeen bytes of [EchoDisc.echo_line] carry no symbol byte and their  *)
(* maximal non-blank runs are [(0,4)], [(5,10)] and [(11,16)].  That is    *)
(* [UConsLine.ush_echo_tokens], and it is proved below by [vm_compute].    *)
(* ===================================================================== *)

Definition echo_toks : list (nat * nat) := [(0, 4); (5, 10); (11, 16)]%nat.

Lemma echo_toks_lt10 : (length echo_toks < 10)%nat.
Proof. vm_compute. lia. Qed.

(* the token boundaries, as the two functions every statement below reads
   them through: argument [i] starts at [echo_off i] and is [echo_alen i]
   bytes long *)
Definition echo_off (i : nat) : nat :=
  match i with 0%nat => 0%nat | 1%nat => 5%nat | _ => 11%nat end.

Definition echo_alen (i : nat) : nat :=
  match i with 0%nat => 4%nat | _ => 5%nat end.

Lemma echo_toks_lookup (i : nat) :
  (i < 3)%nat ->
  echo_toks !! i = Some (echo_off i, (echo_off i + echo_alen i)%nat).
Proof.
  intro Hi. destruct i as [| [| [| i]]]; try reflexivity. exfalso. lia.
Qed.

(* ---- the closed computation: the literal line lexes ------------------ *)

(* [UkShParse.UshpTokCons] with the two scanned lengths NAMED, so a call
   site supplies them as closed numbers instead of leaving them to
   unification. *)
Local Lemma ushe_tok_step (len i k n : nat) (f : nat -> bv 8)
    (toks : list (nat * nat)) :
  ushp_skipws (len - i) i f = k ->
  ushp_toklen (len - (i + k)) (i + k) f = n ->
  (0 < n)%nat ->
  ushp_tokens len f (i + k + n)%nat toks ->
  ushp_tokens len f i ((i + k, i + k + n)%nat :: toks).
Proof.
  intros Hk Hn Hpos Ht.
  pose proof (UshpTokCons len f i toks) as C. cbv zeta in C.
  rewrite Hk Hn in C. exact (C Hpos Ht).
Qed.

Lemma ush_echo_tokens_holds : UConsLine.ush_echo_tokens.
Proof.
  rewrite /UConsLine.ush_echo_tokens echo_line_length.
  split_and!.
  - intros j Hj.
    do 17 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
  - change [(0, 4); (5, 10); (11, 16)]%nat
      with [(0 + 0, 0 + 0 + 4); (4 + 1, 4 + 1 + 5); (10 + 1, 10 + 1 + 5)]%nat.
    apply (ushe_tok_step 17 0 0 4);
      [ vm_compute; reflexivity | vm_compute; reflexivity | lia | ].
    apply (ushe_tok_step 17 4 1 5);
      [ vm_compute; reflexivity | vm_compute; reflexivity | lia | ].
    apply (ushe_tok_step 17 10 1 5);
      [ vm_compute; reflexivity | vm_compute; reflexivity | lia | ].
    apply UshpTokNil. vm_compute. reflexivity.
  - simpl. lia.
Qed.

(* ---- the determinacy the DISCIPLINED buffer needs -------------------- *)
(* [ush_echo_tokens] is about [echo_line] read through
   [fun j => echo_line !!! j]; the command loop hands its body the line
   through [fun j => f (k + j)].  [UConsLine.ush_line_is] says the two
   agree pointwise below [len], and [ushp_no_symbols] / [ushp_tokens] read
   their bytes only there -- so this is a TRANSPORT and not a second
   computation.  It is [UConsLine.ush_line_lexable] with the token list
   NAMED, which is what the specialised arm needs and the existential form
   cannot give. *)
Definition ush_line_toks : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is f k len ->
    len = 17%nat
    /\ ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ ushp_tokens len (fun j : nat => f (k + j)%nat) 0%nat echo_toks.

(* ---- the transport, which is all the determinacy costs --------------- *)
(* [ushp_skipws] / [ushp_toklen] read [f] only inside the window they are
   given, and [ushp_tokens]' two constructors read it only through them --
   so pointwise equality below [len] carries a tokenization across.  Three
   plain inductions; nothing about echo. *)
Lemma ushp_skipws_ext (n : nat) :
  forall (i : nat) (f f' : nat -> bv 8),
    (forall j : nat, (i <= j < i + n)%nat -> f j = f' j) ->
    ushp_skipws n i f = ushp_skipws n i f'.
Proof.
  induction n as [| n IH ]; intros i f f' H; cbn; [ reflexivity | ].
  rewrite (H i ltac:(lia)).
  destruct (ushp_is_ws (f' i)); [ | reflexivity ].
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma ushp_toklen_ext (n : nat) :
  forall (i : nat) (f f' : nat -> bv 8),
    (forall j : nat, (i <= j < i + n)%nat -> f j = f' j) ->
    ushp_toklen n i f = ushp_toklen n i f'.
Proof.
  induction n as [| n IH ]; intros i f f' H; cbn; [ reflexivity | ].
  rewrite (H i ltac:(lia)).
  destruct (ushp_is_ws (f' i) || ushp_is_sym (f' i)); [ reflexivity | ].
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma ushp_no_symbols_ext (len : nat) (f f' : nat -> bv 8) :
  (forall j : nat, (j < len)%nat -> f j = f' j) ->
  ushp_no_symbols len f -> ushp_no_symbols len f'.
Proof.
  intros H Hns j Hj. rewrite <- (H j Hj). exact (Hns j Hj).
Qed.

Lemma ushp_tokens_ext (len : nat) (f f' : nat -> bv 8) :
  (forall j : nat, (j < len)%nat -> f j = f' j) ->
  forall (i : nat) (toks : list (nat * nat)),
    ushp_tokens len f i toks -> ushp_tokens len f' i toks.
Proof.
  intros Hff i toks Ht.
  assert (Hsk : forall a : nat,
            ushp_skipws (len - a) a f' = ushp_skipws (len - a) a f).
  { intro a. apply ushp_skipws_ext. intros j Hj. symmetry. apply Hff. lia. }
  assert (Htl : forall b : nat,
            ushp_toklen (len - b) b f' = ushp_toklen (len - b) b f).
  { intro b. apply ushp_toklen_ext. intros j Hj. symmetry. apply Hff. lia. }
  induction Ht as [ off Hnil | off toks0 k0 n0 Hpos Hrec IH ].
  - apply UshpTokNil. rewrite (Hsk off). exact Hnil.
  - apply (ushe_tok_step len off k0 n0 f').
    + exact (Hsk off).
    + exact (Htl (off + k0)%nat).
    + exact Hpos.
    + exact IH.
Qed.

(* ...and the determinacy itself: ONE transport of the closed computation. *)
Lemma ush_line_toks_holds : ush_line_toks.
Proof.
  intros f k len [Hlen Hf].
  rewrite echo_line_length in Hlen.
  split; [ exact Hlen | ].
  subst len.
  destruct ush_echo_tokens_holds as (Hns & Htk & _).
  rewrite echo_line_length in Hns, Htk.
  assert (Hext : forall j : nat, (j < 17)%nat ->
            echo_line !!! j = f (k + j)%nat)
    by (intros j Hj; symmetry; exact (Hf j Hj)).
  split.
  - exact (ushp_no_symbols_ext 17 _ _ Hext Hns).
  - exact (ushp_tokens_ext 17 _ _ Hext 0%nat echo_toks Htk).
Qed.

(* ---- the command, as a VALUE ---------------------------------------- *)
(* [UkShMain.ush_cmd_of_ushp] converts the parser's node into the runner's
   tree at [UExec (UkShMain.ush_args s0 g toks)], where [g] is the line
   AFTER [nulterminate]'s cut ([ushp_nulfold toks (ushp_ext len f)]).  At
   [toks := echo_toks] that value is three [UserHeap.uarg]s and nothing
   else, and this is it. *)
Definition echo_cmd (s0 : Z) (g : nat -> bv 8) : ushcmd :=
  UExec (UkShMain.ush_args s0 g echo_toks).

Lemma echo_cmd_simple (s0 : Z) (g : nat -> bv 8) : ush_simple (echo_cmd s0 g).
Proof. exact I. Qed.

Lemma echo_cmd_ht (s0 : Z) (g : nat -> bv 8) : ush_ht (echo_cmd s0 g) = 1%nat.
Proof. reflexivity. Qed.

Lemma echo_cmd_args_length (s0 : Z) (g : nat -> bv 8) :
  length (UkShMain.ush_args s0 g echo_toks) = 3%nat.
Proof. rewrite UkShMain.ush_args_length. reflexivity. Qed.

Lemma echo_cmd_args_lookup (s0 : Z) (g : nat -> bv 8) (i : nat) :
  (i < 3)%nat ->
  UkShMain.ush_args s0 g echo_toks !! i
  = Some (UArg (s0 + Z.of_nat (echo_off i)) (echo_alen i)
            (fun j : nat => g (echo_off i + j)%nat)).
Proof.
  intro Hi.
  rewrite (UkShMain.ush_args_lookup s0 g echo_toks i
             (echo_off i, (echo_off i + echo_alen i)%nat)
             (echo_toks_lookup i Hi)).
  cbn [fst snd].
  replace (echo_off i + echo_alen i - echo_off i)%nat with (echo_alen i)
    by lia.
  reflexivity.
Qed.

(* ---- the argv BYTES, as a pure premise ------------------------------- *)
(* What the exec at the bottom of the arm needs of the line is not the
   whole of [ush_line_is] but three strings and their NULs: [nulterminate]
   has cut the line at each token's end, so the byte function the tree is
   built over spells "echo\0", "hello\0", "world\0" at the three offsets.
   Stated over the CUT function [g] (the tree's own), because that is the
   one the node's [ustr]s are indexed by. *)
Definition echo_argv_bytes (g : nat -> bv 8) : Prop :=
  (forall (i j : nat), (i < 3)%nat -> (j < echo_alen i)%nat ->
     g (echo_off i + j)%nat = echo_line !!! (echo_off i + j)%nat)
  /\ (forall i : nat, (i < 3)%nat ->
        g (echo_off i + echo_alen i)%nat = ubyte0).

(* ...and it holds of the disciplined line's cut.  [ushp_nulfold] writes a
   NUL at each token's END and leaves every other index alone, and the
   three ends [4], [10], [16] are outside all three tokens -- so the
   strings are the line's own bytes and the terminators are the cut's. *)
Definition echo_argv_bytes_of_line : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is f k len ->
    echo_argv_bytes
      (ushp_nulfold echo_toks (ushp_ext len (fun j : nat => f (k + j)%nat))).

(* [nulterminate]'s cut at [echo_toks] is the three stores at 4, 10 and 16
   and nothing else, so every index inside a token is the line's own byte
   and every token's end is the terminator. *)
Local Lemma nulfold_echo_other (g : nat -> bv 8) (x : nat) :
  (x < 17)%nat -> x <> 4%nat -> x <> 10%nat -> x <> 16%nat ->
  ushp_nulfold echo_toks (ushp_ext 17 g) x = g x.
Proof.
  intros Hx H4 H10 H16.
  unfold echo_toks. cbn [ushp_nulfold snd].
  rewrite /ushp_setb /ushp_ext.
  rewrite (proj2 (Nat.eqb_neq x 16) H16).
  rewrite (proj2 (Nat.eqb_neq x 10) H10).
  rewrite (proj2 (Nat.eqb_neq x 4) H4).
  rewrite (bool_decide_eq_true_2 _ Hx).
  reflexivity.
Qed.

Local Lemma nulfold_echo_nul (g : nat -> bv 8) (x : nat) :
  (x = 4 \/ x = 10 \/ x = 16)%nat ->
  ushp_nulfold echo_toks (ushp_ext 17 g) x = ubyte0.
Proof.
  intros Hx. unfold echo_toks. cbn [ushp_nulfold snd].
  rewrite /ushp_setb.
  destruct Hx as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma echo_argv_bytes_of_line_holds : echo_argv_bytes_of_line.
Proof.
  intros f k len [Hlen Hf].
  rewrite echo_line_length in Hlen. subst len.
  split.
  - intros i j Hi Hj.
    assert (Hb : (echo_off i + j < 17)%nat /\ (echo_off i + j <> 4)%nat
                 /\ (echo_off i + j <> 10)%nat /\ (echo_off i + j <> 16)%nat)
      by (destruct i as [| [| i]]; cbn [echo_off echo_alen] in *; lia).
    destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4).
    rewrite (nulfold_echo_other _ _ Hb1 Hb2 Hb3 Hb4).
    exact (Hf _ Hb1).
  - intros i Hi. apply nulfold_echo_nul.
    destruct i as [| [| i]]; cbn [echo_off echo_alen]; auto.
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

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).

  (* =================================================================== *)
  (*  THE NODE, ADDRESSED.  Three accessors so that no consumer of the     *)
  (*  tree has to fight [UkShMain.ush_args]'s [map] again: argument [i]'s  *)
  (*  pointer word, its string, and the NULL cap.  Everything is           *)
  (*  [DfracDiscarded], so every one of them is free to take.              *)
  (* =================================================================== *)
  Lemma echo_cmd_str (gd : gname) (t s0 : Z) (g : nat -> bv 8) (i : nat) :
    (i < 3)%nat ->
    ush_cmd gd t (echo_cmd s0 g) -∗
    ⌜ 0 < s0 + Z.of_nat (echo_off i) < 2 ^ 38 ⌝ ∗
    ustr gd DfracDiscarded (s0 + Z.of_nat (echo_off i)) (echo_alen i)
      (fun j : nat => g (echo_off i + j)%nat).
  Proof.
    intro Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & _ & #Hs)".
    iDestruct (big_sepL_lookup _ (UkShMain.ush_args s0 g echo_toks) i _
                 (echo_cmd_args_lookup s0 g i Hi) with "Hs") as "#Hx".
    rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
    iDestruct "Hx" as "[%Hr #Hstr]".
    iSplit; [ iPureIntro; exact Hr | iExact "Hstr" ].
  Qed.

  Lemma echo_cmd_word (gd : gname) (t s0 : Z) (g : nat -> bv 8) (i : nat) :
    (i < 3)%nat ->
    ush_cmd gd t (echo_cmd s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat i)
      (mword_of_int (s0 + Z.of_nat (echo_off i))).
  Proof.
    intro Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(#Hv & _ & _)".
    iDestruct (uargv_acc gd (t + 8) (UkShMain.ush_args s0 g echo_toks) i _
                 (echo_cmd_args_lookup s0 g i Hi) with "Hv") as "[[#Hw _] _]".
    cbn [ua_ptr]. iExact "Hw".
  Qed.

  Lemma echo_cmd_cap (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat 3%nat) (mword_of_int 0).
  Proof.
    iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & #Hn & _)".
    rewrite /ush_ptr echo_cmd_args_length. iExact "Hn".
  Qed.

  Lemma echo_cmd_addr (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd s0 g) -∗ ⌜ 0 < t < 2 ^ 38 /\ t mod 8 = 0 ⌝.
  Proof. iIntros "#Hc". iApply (ush_cmd_addr with "Hc"). Qed.

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
  Definition sh_exec_sup_echo : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64)
          (s0 t : Z) (g : nat -> bv 8),
          ⌜ ukn_pay N' = (fun _ => True)%I ⌝ -∗
          (* argv[0]'s string, which is the PATH exec resolves... *)
          ⌜ m !!! Regidx a0_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          (* ...and [&argv[0]], which is the VECTOR it reads *)
          ⌜ m !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64) ⌝ -∗
          ⌜ echo_argv_bytes g ⌝ -∗
          ush_cmd (ukn_d N') t (echo_cmd s0 g) -∗
          udepw_at N' m pc USYS_exec FsImg.ROOTINO))%I.

  Global Instance sh_exec_sup_echo_persistent : Persistent sh_exec_sup_echo.
  Proof. rewrite /sh_exec_sup_echo. apply _. Qed.

  (* THE CWD-INDEXED EXEC STUB.  [UkShRun.wp_kshr_exec] takes the ∀-cwd
     deposit [UkRun.udepw]; a pinned supply cannot pay that (its bundle
     answers at ONE cwd), so the specialised arm needs sh's exec stub at
     the indexed deposit and the program's own half of its working
     directory beside it -- [UkInit.wp_kinit_exec] is the same lemma at
     init's three pcs.  Everything else is [wp_kshr_exec] verbatim: a
     successful exec never comes back, so the only continuation is -1. *)
  Definition wp_kshr_exec_at_cwd : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (c : Z) (avail : nat),
      ⊢ shk_code (ukn_t N) -∗
        urun N h m (mword_of_int ShSyms.exec) avail -∗
        UserCwd.ucwd (ukn_cwd N) c -∗
        udepw_at N
          (<[Regidx (mword_of_int 17 : mword 5) := (mword_of_int 7 : mword 64)]> m)
          (mword_of_int 0xcc0) USYS_exec c -∗
        (∀ h' : CpuId,
           UserCwd.ucwd (ukn_cwd N) c -∗
           urun N h'
             (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                (<[Regidx (mword_of_int 17 : mword 5)
                   := (mword_of_int 7 : mword 64)]> m))
             (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) avail -∗
           WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang).

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
  Definition wp_kshr_exec_echo : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      echo_argv_bytes g ->
      ⊢ UkSh.sh_deps -∗
        shk_code (ukn_t N) -∗
        sh_exec_sup_echo -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (echo_cmd s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        WP (Loop : expr riscv_lang).

  (* =================================================================== *)
  (* THE DISPATCH, in [UkShMain.wp_kshm_child]'s place.                   *)
  (*                                                                      *)
  (* [wp_kshm_child_alloc] is already parametric in the token list, so the *)
  (* specialisation is at [toks := echo_toks]; what CHANGES is the supply  *)
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
  Definition wp_kshm_child_echo : Prop :=
    forall (Hsbrk : forall (N' : uk_names Σ) (sz n : Z) (r : mword 64),
              UkShMalloc.ushm_sbrk_ans N' sz n r -∗
              ⌜ r = (mword_of_int sz : mword 64) ⌝ ∗
              UkShMalloc.ushm_sbrk_ans N' sz n r)
           (N : uk_names Σ) (Ht : ukn_triv N)
           (h : CpuId) (m : regfile) (dw dv : dfrac)
           (s0 : Z) (len : nat) (f : nat -> bv 8) (sz : Z)
           (ld : list fdstate) (n : nat),
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      UConsLine.ush_line_is f 0%nat len ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      8344 <= sz ->
      UserPtTree.pgroundup sz = sz ->
      usz_ok (sz + 65536) ->
      ⊢ UkSh.sh_deps -∗
        shk_code (ukn_t N) -∗
        sh_exec_sup_echo -∗
        shp_code (ukn_t N) -∗ shp_rodata (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
        ustr (ukn_d N) (DfracOwn 1) s0 len f -∗
        ustr (ukn_d N) dw ushp_whitespace 5 ushp_ws_f -∗
        ustr (ukn_d N) dv ushp_symbols 7 ushp_sym_f -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        UkShMalloc.ushm_fresh N sz -∗
        urun N h m (mword_of_int 0x9c0)
          (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
        WP (Loop : expr riscv_lang).

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
  Definition ush_pstate_at (N : uk_names Σ) (gp : gname) (l : list fdstate)
      (c : Z) : iProp Σ :=
    (UkSh.ush_std N l ∗ UserCwd.ucwd (ukn_cwd N) c
     ∗ UserChildren.uch_any (ukn_ch N) ∗ UkSh.ush_pos gp)%I.

  Lemma ush_pstate_of_at (N : uk_names Σ) (gp : gname) (l : list fdstate)
      (c : Z) :
    ush_pstate_at N gp l c -∗ UkSh.ush_pstate N gp l.
  Proof.
    rewrite /ush_pstate_at /UkSh.ush_pstate.
    iIntros "(Hstd & Hcwd & Hch & Hpos)". iFrame "Hstd Hch Hpos".
    iApply (UserCwd.ucwd_any_of with "Hcwd").
  Qed.

  (* WHAT CROSSES THE ROUND, named once: the loop head's own resources are
     [UkShLoop.ushl_head]'s and are not re-stated; these are the four the
     fork arm threads through both processes' entry and back out of the
     parent's ([UkShFork.wp_kshf_fork]). *)
  Definition ush_echo_round_carry (N : uk_names Σ) (gp : gname)
      (l : list fdstate) (sz : Z) (f : nat -> bv 8) : iProp Σ :=
    (ush_pstate_at N gp l FsImg.ROOTINO
     ∗ UkShLoop.ushl_dat (ukn_d N) ∗ usz (ukn_s N) sz
     ∗ ubytes (ukn_d N) UkSh.sh_buf UkSh.sh_nbuf f)%I.

End UkShEcho.
