(* ===================================================================== *)
(* RefParse.v -- THE REFERENCE PARSER: sh's recursive descent as pure     *)
(* functions over the line's bytes (design/user-once.md SS2, worklist A1). *)
(*                                                                        *)
(* user/sh.c's parser is                                                  *)
(*                                                                        *)
(*   parsecmd -> parseline -> parsepipe -> parseexec -> parseredirs       *)
(*            over peek / gettoken, then nulterminate,                    *)
(*                                                                        *)
(* and this file is that parser, function for function, as a computation *)
(* on a cursor into the line.  It is the ONE pure model every parser walk *)
(* is stated against: a walk of a C function says: the code computes what *)
(* the reference computes at this cursor, and a LINE SHAPE is an         *)
(* equation [ref_parsecmd len f = Some t] proved by computation on the    *)
(* line, never by a walk.  The three per-shape token models the landed    *)
(* tiers speak ([UkShParse.ushp_tokens] under [ushp_no_symbols],          *)
(* [UkShParseSym.ushs_toks] at the '>', [UkShPipeLex.ushq_pipe]) are its  *)
(* instances; the bridge lemmas live in RefParseBridge.v, above the files *)
(* that define them.                                                      *)
(*                                                                        *)
(* WHAT [None] MEANS.  Exactly where sh panics (syntax, too many args,      *)
(* missing file for redirection, leftovers) or where the walk  *)
(* reaches a function the catalog does not carry ([parseblock]).  The     *)
(* landed premise [ushp_no_symbols] is replaced by the equation; the      *)
(* panic arms are refuted from it.                                        *)
(*                                                                        *)
(* THE SCOPE is a separate predicate, [ushp_cat]: the constructors and    *)
(* redirect modes the catalog WALKS today (EXEC, REDIR at '>' only, PIPE). *)
(* The reference parses the whole grammar so that widening the catalog    *)
(* widens [ushp_cat] and nothing else.                                    *)
(*                                                                        *)
(* FUEL.  Every loop and recursion of sh's parser consumes at least one   *)
(* byte per turn, so the functions take a fuel that [ref_parsecmd] sets    *)
(* from the line's length; a fuel-monotonicity lemma per function is what  *)
(* the bridge file proves, and no consumer ever sees the fuel.             *)
(*                                                                        *)
(* Imports [UkShParse] for the lexer's two measures ([ushp_skipws],       *)
(* [ushp_toklen]), the byte classes and the tree type [ushp_cmd].  When    *)
(* the walks are re-stated over this file (A2), those ~600 pure lines move *)
(* here and [UkShParse] imports this file instead.                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List String.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.        (* [ubyte0] *)
Require Import StringBytes.     (* [string_bytes], for the demos *)
Require Import UkShParse.       (* the lexer measures, the byte classes, [ushp_cmd] *)
Local Open Scope Z_scope.
Import UkShParse.

(* ===================================================================== *)
(* §1 THE CURSOR, THE BYTE AT IT, AND THE TWO SCANS                       *)
(* ===================================================================== *)

(* The line is [len] body bytes [f 0 .. f (len-1)], none of them NUL, and
   the terminator behind them; [es = s0 + len].  A read at or past [len]
   is the NUL, which is what makes every [s < es &&] test of sh.c a test on
   the byte alone. *)
Definition ref_at (len : nat) (f : nat -> bv 8) (i : nat) : bv 8 :=
  if bool_decide (i < len)%nat then f i else ubyte0.

(* `while (s < es && strchr(whitespace, *s)) s++' *)
Definition ref_skip (len : nat) (f : nat -> bv 8) (i : nat) : nat :=
  (i + ushp_skipws (len - i) i f)%nat.

(* the default arm's scan: `while (s < es && !ws && !sym) s++' *)
Definition ref_tokend (len : nat) (f : nat -> bv 8) (i : nat) : nat :=
  (i + ushp_toklen (len - i) i f)%nat.

(* the byte values sh.c switches on *)
Definition rb_bar   : bv 8 := Z_to_bv 8 124.  (* '|' *)
Definition rb_lpar  : bv 8 := Z_to_bv 8 40.   (* '(' *)
Definition rb_rpar  : bv 8 := Z_to_bv 8 41.   (* ')' *)
Definition rb_semi  : bv 8 := Z_to_bv 8 59.   (* ';' *)
Definition rb_amp   : bv 8 := Z_to_bv 8 38.   (* '&' *)
Definition rb_lt    : bv 8 := Z_to_bv 8 60.   (* '<' *)
Definition rb_gt    : bv 8 := Z_to_bv 8 62.   (* '>' *)

(* gettoken's return codes: the symbol byte itself, 'a' for a word, '+'
   for ">>", 0 at the end of the line *)
Definition rt_word : Z := 97.   (* 'a' *)
Definition rt_app  : Z := 43.   (* '+' *)

(* ===================================================================== *)
(* §2 gettoken AND peek                                                   *)
(* ===================================================================== *)

(* [ref_gettoken len f i] -- sh.c's [gettoken(&s, es, &q, &eq)] at cursor
   [i]: (the token code, q, eq, the new cursor).  Total: gettoken never
   fails.  The trailing whitespace skip is part of it, as in the C. *)
Definition ref_gettoken (len : nat) (f : nat -> bv 8) (i : nat)
  : Z * nat * nat * nat :=
  let s := ref_skip len f i in
  let b := ref_at len f s in
  let '(ret, e) :=
    if bool_decide (b = ubyte0) then (0, s)
    else if bool_decide (b = rb_gt) then
      (if bool_decide (ref_at len f (S s) = rb_gt) then (rt_app, S (S s))
       else (bv_unsigned rb_gt, S s))
    else if ushp_is_sym b then (bv_unsigned b, S s)
    else (rt_word, ref_tokend len f s) in
  (ret, s, e, ref_skip len f e).

(* [ref_peek len f i toks] -- sh.c's [peek(&s, es, toks)]: skip blanks,
   then: the byte is non-NUL and in [toks]; the cursor moves to the
   skipped position whatever the answer. *)
Definition ref_peek (len : nat) (f : nat -> bv 8) (i : nat)
    (toks : list (bv 8)) : bool * nat :=
  let s := ref_skip len f i in
  let b := ref_at len f s in
  (negb (bool_decide (b = ubyte0)) && bool_decide (b ∈ toks), s).

(* ===================================================================== *)
(* §3 parseredirs, parseexec                                              *)
(* ===================================================================== *)

(* one redirect, as [redircmd] records it: the file name's two indices,
   the open mode and the descriptor it lands on.  kernel/fcntl.h:
   O_RDONLY 0, O_WRONLY 1, O_CREATE 0x200, O_TRUNC 0x400. *)
Record rredir := { rr_q : nat; rr_eq : nat; rr_mode : Z; rr_fd : Z }.

Definition rr_mode_gt  : Z := 1537.   (* O_WRONLY|O_CREATE|O_TRUNC, the '>'  *)
Definition rr_mode_app : Z := 513.    (* O_WRONLY|O_CREATE,         the '>>' *)

Definition rredir_of (tok : Z) (q eq : nat) : option rredir :=
  if bool_decide (tok = bv_unsigned rb_lt) then Some {| rr_q := q; rr_eq := eq; rr_mode := 0; rr_fd := 0 |}
  else if bool_decide (tok = bv_unsigned rb_gt) then Some {| rr_q := q; rr_eq := eq; rr_mode := rr_mode_gt; rr_fd := 1 |}
  else if bool_decide (tok = rt_app) then Some {| rr_q := q; rr_eq := eq; rr_mode := rr_mode_app; rr_fd := 1 |}
  else None.

(* [redircmd] wraps the tree built SO FAR, so the redirects apply
   outward in the order consumed *)
Definition ref_wrap (t : ushp_cmd) (rs : list rredir) : ushp_cmd :=
  fold_left (fun t r => UshpRedir t (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)) rs t.

(* `while (peek(ps, es, <>)) { tok = gettoken(..0,0); if (gettoken(..&q,&eq)
   != 'a') panic(missing file for redirection); switch (tok) ... }' --
   answering the redirects consumed (appended to [acc]) and the cursor *)
Fixpoint ref_redirs (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
    (acc : list rredir) : option (list rredir * nat) :=
  match n with
  | O => None
  | S n' =>
      let '(hit, s) := ref_peek len f i [rb_lt; rb_gt] in
      if hit then
        let '(tok, _, _, s1) := ref_gettoken len f s in
        let '(t2, q, eq, s2) := ref_gettoken len f s1 in
        if bool_decide (t2 = rt_word) then
          match rredir_of tok q eq with
          | Some r => ref_redirs len f n' s2 (acc ++ [r])
          | None => None
          end
        else None
      else Some (acc, s)
  end.

(* parseexec's argument loop:
     while (!peek(ps, es, |)&;)) {
       if ((tok = gettoken(ps, es, &q, &eq)) == 0) break;
       if (tok != 'a') panic(syntax);
       argv[argc] = q; eargv[argc] = eq; argc++;
       if (argc >= MAXARGS) panic(too many args);
       ret = parseredirs(ret, ps, es);
     }
   answering (the tokens, the redirects so far, the cursor) *)
Fixpoint ref_args (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
    (toks : list (nat * nat)) (rs : list rredir)
  : option (list (nat * nat) * list rredir * nat) :=
  match n with
  | O => None
  | S n' =>
      let '(stop, s) := ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi] in
      if stop then Some (toks, rs, s)
      else
        let '(tok, q, eq, s1) := ref_gettoken len f s in
        if bool_decide (tok = 0) then Some (toks, rs, s1)
        else if negb (bool_decide (tok = rt_word)) then None
        else
          let toks' := toks ++ [(q, eq)] in
          if bool_decide (10 <= length toks')%nat then None
          else
            match ref_redirs len f n' s1 rs with
            | Some (rs', s2) => ref_args len f n' s2 toks' rs'
            | None => None
            end
  end.

(* parseexec: `if (peek(ps, es, LPAREN)) return parseblock(ps, es);' is out
   of the catalog -- [None]; else the exec node, its leading redirects,
   the argument loop, and the wrap *)
Definition ref_parseexec (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
  : option (ushp_cmd * nat) :=
  let '(blk, s) := ref_peek len f i [rb_lpar] in
  if blk then None
  else
    match ref_redirs len f n s [] with
    | Some (rs, s1) =>
        match ref_args len f n s1 [] rs with
        | Some (toks, rs', s2) => Some (ref_wrap (UshpExec toks) rs', s2)
        | None => None
        end
    | None => None
    end.

(* ===================================================================== *)
(* §4 parsepipe, parseline, parsecmd                                      *)
(* ===================================================================== *)

(* parsepipe: `cmd = parseexec(); if (peek(ps, es, |)) { gettoken();
   cmd = pipecmd(cmd, parsepipe()); }' *)
Fixpoint ref_parsepipe (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
  : option (ushp_cmd * nat) :=
  match n with
  | O => None
  | S n' =>
      match ref_parseexec len f n' i with
      | Some (t, s) =>
          let '(bar, s1) := ref_peek len f s [rb_bar] in
          if bar then
            let '(_, _, _, s2) := ref_gettoken len f s1 in
            match ref_parsepipe len f n' s2 with
            | Some (r, s3) => Some (UshpPipe t r, s3)
            | None => None
            end
          else Some (t, s1)
      | None => None
      end
  end.

(* parseline's `while (peek(ps, es, &)) { gettoken(); cmd = backcmd(cmd); }' *)
Fixpoint ref_backs (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
    (t : ushp_cmd) : ushp_cmd * nat :=
  match n with
  | O => (t, i)
  | S n' =>
      let '(amp, s) := ref_peek len f i [rb_amp] in
      if amp then
        let '(_, _, _, s1) := ref_gettoken len f s in
        ref_backs len f n' s1 (UshpBack t)
      else (t, s)
  end.

(* parseline: `cmd = parsepipe(); while (peek &) ...; if (peek(ps, es,
   ;)) { gettoken(); cmd = listcmd(cmd, parseline()); }' *)
Fixpoint ref_parseline (len : nat) (f : nat -> bv 8) (n : nat) (i : nat)
  : option (ushp_cmd * nat) :=
  match n with
  | O => None
  | S n' =>
      match ref_parsepipe len f n' i with
      | Some (t, s) =>
          let '(t1, s1) := ref_backs len f n' s t in
          let '(semi, s2) := ref_peek len f s1 [rb_semi] in
          if semi then
            let '(_, _, _, s3) := ref_gettoken len f s2 in
            match ref_parseline len f n' s3 with
            | Some (r, s4) => Some (UshpList t1 r, s4)
            | None => None
            end
          else Some (t1, s2)
      | None => None
      end
  end.

(* Every turn of every loop and every recursive call consumes a byte, and
   the nesting parseline > parsepipe > parseexec > (redirs | args) is four
   deep, so four fuels per byte plus a margin is always enough.  The bridge
   file proves the monotonicity that makes the exact number irrelevant. *)
Definition ref_fuel (len : nat) : nat := (4 * len + 8)%nat.

(* parsecmd: `es = s + strlen(s); cmd = parseline(&s, es); peek(&s, es, EMPTY);
   if (s != es) { fprintf(2, "leftovers: %s\n", s); panic(syntax); }
   nulterminate(cmd);' -- the NUL cut is [ref_nulcut] below, a fact about
   the tree; this answers the tree. *)
Definition ref_parsecmd (len : nat) (f : nat -> bv 8) : option ushp_cmd :=
  match ref_parseline len f (ref_fuel len) 0%nat with
  | Some (t, s) =>
      let '(_, s1) := ref_peek len f s [] in
      if bool_decide (s1 = len) then Some t else None
  | None => None
  end.

(* ===================================================================== *)
(* §5 nulterminate, THE SCOPE, THE MEASURES                               *)
(* ===================================================================== *)

(* the indices nulterminate zeroes: each argument's end, each redirect
   file name's end -- in the order the recursion visits them *)
Fixpoint ref_nulcut (t : ushp_cmd) : list nat :=
  match t with
  | UshpExec toks => map snd toks
  | UshpRedir c _ eq _ _ => ref_nulcut c ++ [eq]
  | UshpPipe l r => ref_nulcut l ++ ref_nulcut r
  | UshpList l r => ref_nulcut l ++ ref_nulcut r
  | UshpBack c => ref_nulcut c
  end.

(* the catalog's scope: EXEC; REDIR only as `> file' onto fd 1; PIPE.
   LIST and BACK are parsed by the reference and walked by nothing. *)
Fixpoint ushp_cat (t : ushp_cmd) : Prop :=
  match t with
  | UshpExec _ => True
  | UshpRedir c _ _ mode fd => ushp_cat c /\ mode = rr_mode_gt /\ fd = 1
  | UshpPipe l r => ushp_cat l /\ ushp_cat r
  | UshpList _ _ => False
  | UshpBack _ => False
  end.

Global Instance ushp_cat_dec t : Decision (ushp_cat t).
Proof. induction t; cbn; apply _. Defined.

(* the tree's height -- the depth of the runcmd call chain -- as
   [UkShRun.ush_ht] measures it on the runner's side *)
Fixpoint ushp_ht (t : ushp_cmd) : nat :=
  match t with
  | UshpExec _ => 1
  | UshpRedir c _ _ _ _ => S (ushp_ht c)
  | UshpPipe l r => S (Nat.max (ushp_ht l) (ushp_ht r))
  | UshpList l r => S (Nat.max (ushp_ht l) (ushp_ht r))
  | UshpBack c => S (ushp_ht c)
  end.

(* the nodes -- one [malloc] each, which is what a walk chains from the
   allocator *)
Fixpoint ushp_nodes (t : ushp_cmd) : nat :=
  match t with
  | UshpExec _ => 1
  | UshpRedir c _ _ _ _ => S (ushp_nodes c)
  | UshpPipe l r => S (ushp_nodes l + ushp_nodes r)
  | UshpList l r => S (ushp_nodes l + ushp_nodes r)
  | UshpBack c => S (ushp_nodes c)
  end.

(* ===================================================================== *)
(* §6 ANTI-VACUITY: the three line shapes, computed                        *)
(* ===================================================================== *)

Definition rp_bytes (s : string) : nat -> bv 8 :=
  fun i => default ubyte0 (string_bytes s !! i).
Definition rp_len (s : string) : nat := String.length s.
Definition rp_parse (s : string) : option ushp_cmd :=
  ref_parsecmd (rp_len s) (rp_bytes s).

(* the echo line: one EXEC node whose argv are the words *)
Lemma rp_demo_echo :
  rp_parse "echo hello world
" = Some (UshpExec [(0, 4); (5, 10); (11, 16)]%nat).
Proof. vm_compute. reflexivity. Qed.

(* the redirect line: a REDIR onto fd 1 at O_WRONLY|O_CREATE|O_TRUNC over
   the EXEC of the words; the file name is (17, 18) *)
Lemma rp_demo_redir :
  rp_parse "echo hello world > f
" = Some (UshpRedir (UshpExec [(0, 4); (5, 10); (11, 16)]%nat) 19%nat 20%nat 1537 1).
Proof. vm_compute. reflexivity. Qed.

(* the pipe line: a PIPE of two EXEC nodes *)
Lemma rp_demo_pipe :
  rp_parse "echo hello world | cat
" = Some (UshpPipe (UshpExec [(0, 4); (5, 10); (11, 16)]%nat) (UshpExec [(19, 22)]%nat)).
Proof. vm_compute. reflexivity. Qed.

(* ...and the reference REFUSES what sh refuses: leftovers, a block, a
   missing redirect target, too many arguments *)
Lemma rp_demo_block : rp_parse "(echo hi)
" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma rp_demo_missing : rp_parse "echo hi >
" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma rp_demo_toomany : rp_parse "a b c d e f g h i j
" = None.
Proof. vm_compute. reflexivity. Qed.
Lemma rp_demo_leftover : rp_parse "echo hi )
" = None.
Proof. vm_compute. reflexivity. Qed.

(* the scope predicate on the three demos *)
Lemma rp_demo_cat :
  (forall t, rp_parse "echo hello world
" = Some t -> ushp_cat t)
  /\ (forall t, rp_parse "echo hello world > f
" = Some t -> ushp_cat t)
  /\ (forall t, rp_parse "echo hello world | cat
" = Some t -> ushp_cat t).
Proof.
  rewrite rp_demo_echo, rp_demo_redir, rp_demo_pipe.
  split; [ | split ]; intros t Ht; injection Ht as <-; cbn; auto.
Qed.
