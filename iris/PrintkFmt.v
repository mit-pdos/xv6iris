(* PrintkFmt.v -- the PURE model of printk's format string: which varargs a
   format string consumes, and in what order.  No Iris, no WP -- this is the
   vocabulary SpecPrintk.v states printk's precondition in, and the recursion
   ProofPrintk.v runs its loop induction on.

   printk reads its format string one character at a time and, at a '%', looks
   at up to three more characters (c0, c1, c2) to pick an arm:

       %d  %ld  %lld  %u  %lu  %llu  %x  %lx  %llx  %p  %c   -> one vararg
       %s                                                    -> one char* vararg
       %%                                                    -> no vararg
       %<anything else>                                      -> no vararg

   Each arm then advances the index past the characters it recognized, and the
   loop continues.  [pk_dir] is that classification -- the vararg an arm
   consumes plus how many characters BEYOND c0 it eats -- and [pk_kinds] runs it
   over a whole format string to produce the list of varargs, in order.

   Two modelling points worth stating, because both are load-bearing in the WP:

   - The C code reads c1 only when c0 is non-NUL, and c2 only when c1 is
     non-NUL, so it never reads past the terminator.  [pk_kinds] mirrors that by
     matching on how much string is actually left, and passes the NUL character
     for the ones that would be off the end -- which is exactly the [c1 = c2 = 0]
     the code assigns.
   - The whole model assumes the format string contains no embedded NUL
     ([nonul]).  That is not a restriction on real format strings, but it must
     be said: [a ↦ₛ{dq} s] resides |s|+1 bytes, and if [s] itself contained a
     NUL the C string at [a] would be a strict PREFIX of [s] -- so the loop
     would stop somewhere [pk_kinds s] knows nothing about. *)
From Stdlib Require Import ZArith List Bool Ascii String Lia.
Import ListNotations.
Local Open Scope string_scope.

(* Which kind of vararg an arm consumes: an integer-ish one (read and printed
   by value: %d/%u/%x/%p/%c and their long forms), or a [char *] (dereferenced
   and walked: %s). *)
Inductive pk_kind := PkNum | PkStr.

Definition pk_nul : ascii := Ascii.ascii_of_nat 0.

(* printk's arm selection, as a function of the three characters after '%':
   the vararg the arm consumes (if any), and how many characters BEYOND c0 the
   arm recognizes (0, 1 or 2).  The arms are pairwise disjoint on (c0,c1,c2) --
   an [l] followed by [d] cannot also be an [l] followed by [l] -- so this is a
   faithful reading of the if/else chain regardless of its order. *)
Definition pk_dir (c0 c1 c2 : ascii) : option pk_kind * nat :=
  if Ascii.eqb c0 "d" then (Some PkNum, 0)
  else if Ascii.eqb c0 "u" then (Some PkNum, 0)
  else if Ascii.eqb c0 "x" then (Some PkNum, 0)
  else if Ascii.eqb c0 "p" then (Some PkNum, 0)
  else if Ascii.eqb c0 "c" then (Some PkNum, 0)
  else if Ascii.eqb c0 "s" then (Some PkStr, 0)
  else if Ascii.eqb c0 "l" then
    (if Ascii.eqb c1 "d" then (Some PkNum, 1)
     else if Ascii.eqb c1 "u" then (Some PkNum, 1)
     else if Ascii.eqb c1 "x" then (Some PkNum, 1)
     else if Ascii.eqb c1 "l" then
       (if Ascii.eqb c2 "d" then (Some PkNum, 2)
        else if Ascii.eqb c2 "u" then (Some PkNum, 2)
        else if Ascii.eqb c2 "x" then (Some PkNum, 2)
        else (None, 0))
     else (None, 0))
  else (None, 0).

(* The j-th character of [f], and [pk_nul] at or past its end -- exactly the
   argument [pk_dir] is applied to when the format string runs out, so the
   machine's three lookahead bytes are [pk_ch f (i+1..i+3)] whether or not the
   string is long enough to hold them. *)
Fixpoint pk_ch (f : string) (j : nat) : ascii :=
  match f, j with
  | EmptyString, _ => pk_nul
  | String c _, O => c
  | String _ r, S j' => pk_ch r j'
  end.

Definition pk_cons (o : option pk_kind) (ks : list pk_kind) : list pk_kind :=
  match o with None => ks | Some k => k :: ks end.

(* The varargs a format string consumes, in order.  Every recursive call is on
   a syntactic tail of the string, so this is a plain structural fixpoint. *)
Fixpoint pk_kinds (f : string) : list pk_kind :=
  match f with
  | EmptyString => []
  | String c r =>
    if negb (Ascii.eqb c "%") then pk_kinds r
    else
      match r with
      | EmptyString => []                       (* c0 = 0: the loop breaks *)
      | String c0 r1 =>
        match r1 with
        | EmptyString =>                        (* c1 = c2 = 0 *)
            pk_cons (fst (pk_dir c0 pk_nul pk_nul)) []
        | String c1 r2 =>
          match r2 with
          | EmptyString =>                      (* c2 = 0 *)
            let d := pk_dir c0 c1 pk_nul in
            pk_cons (fst d) (match snd d with O => pk_kinds r1 | _ => pk_kinds r2 end)
          | String c2 r3 =>
            let d := pk_dir c0 c1 c2 in
            pk_cons (fst d) (match snd d with
                             | O => pk_kinds r1
                             | S O => pk_kinds r2
                             | _ => pk_kinds r3
                             end)
          end
        end
      end
  end.

(* no embedded NUL -- see the header *)
Fixpoint nonul (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => negb (Ascii.eqb c pk_nul) && nonul r
  end.

(* ---------------------------------------------------------------------- *)
(* [pk_kinds] AT A POSITION: what the format loop has left to do.          *)
(*                                                                        *)
(* [pk_kinds] recurses on the string; the loop walks an INDEX.  The bridge *)
(* is [str_drop], and the step lemma below is what the loop invariant is    *)
(* maintained by: one turn of the loop rewrites [pk_kinds (str_drop p f)]   *)
(* in terms of the three characters the dispatch just read.                *)
(* ---------------------------------------------------------------------- *)
Fixpoint str_drop (i : nat) (f : string) : string :=
  match i, f with
  | O, _ => f
  | S _, EmptyString => EmptyString
  | S i', String _ r => str_drop i' r
  end.

Lemma str_drop_0 (f : string) : str_drop 0 f = f.
Proof. reflexivity. Qed.

Lemma str_drop_S (i : nat) (c : ascii) (f : string) :
  str_drop (S i) (String c f) = str_drop i f.
Proof. reflexivity. Qed.

Lemma str_drop_len (f : string) (i : nat) :
  String.length (str_drop i f) = (String.length f - i)%nat.
Proof.
  revert i. induction f as [|c f IH]; intros [|i]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma pk_ch_drop (f : string) (i j : nat) : pk_ch (str_drop i f) j = pk_ch f (i + j).
Proof.
  revert j f. induction i as [|i IH]; intros j f; [reflexivity | ].
  destruct f as [|c f]; [destruct j; reflexivity | ]. cbn. apply IH.
Qed.

Lemma nonul_drop (f : string) (i : nat) : nonul f = true -> nonul (str_drop i f) = true.
Proof.
  revert f. induction i as [|i IH]; intros f H; [exact H | ].
  destruct f as [|c f]; [reflexivity | ]. cbn in H.
  apply andb_prop in H as [_ H]. apply IH. exact H.
Qed.

(* how far past c0 a directive can reach, and what a missing character does *)
Lemma pk_dir_snd_le (c0 c1 c2 : ascii) : (snd (pk_dir c0 c1 c2) <= 2)%nat.
Proof.
  unfold pk_dir.
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia.
Qed.

Lemma pk_dir_nul1 (c0 c2 : ascii) : snd (pk_dir c0 pk_nul c2) = 0%nat.
Proof.
  unfold pk_dir.
  repeat (match goal with |- context [if Ascii.eqb c0 ?d then _ else _] => destruct (Ascii.eqb c0 d) end);
    cbn; reflexivity.
Qed.

Lemma pk_dir_nul2 (c0 c1 : ascii) : (snd (pk_dir c0 c1 pk_nul) <= 1)%nat.
Proof.
  unfold pk_dir.
  (* the THIRD character is the terminator, so the two-character forms are out;
     reduce those tests first, or the blind case split asks for [2 <= 1]. *)
  replace (Ascii.eqb pk_nul "d") with false by (vm_compute; reflexivity).
  replace (Ascii.eqb pk_nul "u") with false by (vm_compute; reflexivity).
  replace (Ascii.eqb pk_nul "x") with false by (vm_compute; reflexivity).
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia.
Qed.

(* ONE turn of the format loop, as an equation on [pk_kinds]. *)
Lemma pk_kinds_step (f : string) (p : nat) :
  nonul f = true -> (p < String.length f)%nat ->
  pk_kinds (str_drop p f) =
    if negb (Ascii.eqb (pk_ch f p) "%") then pk_kinds (str_drop (S p) f)
    else if Ascii.eqb (pk_ch f (S p)) pk_nul then []
    else let d := pk_dir (pk_ch f (S p)) (pk_ch f (S (S p))) (pk_ch f (S (S (S p)))) in
         pk_cons (fst d) (pk_kinds (str_drop (S (S p) + snd d) f)).
Proof.
  revert p. induction f as [|c f IH]; intros p Hn Hp; [cbn in Hp; lia | ].
  destruct p as [|p]; [ | cbn in Hn; apply andb_prop in Hn as [_ Hn];
                          cbn in Hp; apply (IH p Hn ltac:(lia)) ].
  cbn [pk_ch str_drop Nat.add].
  cbn [nonul] in Hn. apply andb_prop in Hn as [Hc Hn].
  destruct (negb (Ascii.eqb c "%")) eqn:Hpct.
  { cbn [pk_kinds]. rewrite Hpct. reflexivity. }
  cbn [pk_kinds]. rewrite Hpct.
  destruct f as [|c0 r1]; [reflexivity | ].
  cbn [pk_ch] in *. cbn [nonul] in Hn. apply andb_prop in Hn as [Hc0 Hn].
  replace (Ascii.eqb c0 pk_nul) with false
    by (symmetry; apply negb_true_iff in Hc0; exact Hc0).
  destruct r1 as [|c1 r2].
  - cbn [pk_ch str_drop]. rewrite pk_dir_nul1. reflexivity.
  - cbn [pk_ch] in *. destruct r2 as [|c2 r3].
    + cbn [pk_ch str_drop].
      pose proof (pk_dir_nul2 c0 c1) as Hle.
      destruct (snd (pk_dir c0 c1 pk_nul)) as [|[|n]] eqn:Hs; [reflexivity | reflexivity | lia].
    + cbn [pk_ch str_drop].
      pose proof (pk_dir_snd_le c0 c1 c2) as Hle.
      destruct (snd (pk_dir c0 c1 c2)) as [|[|[|n]]] eqn:Hs;
        [reflexivity | reflexivity | reflexivity | lia].
Qed.

(* sanity: the shapes the kernel actually prints *)
Example pk_kinds_panic : pk_kinds "panic: " = [].
Proof. reflexivity. Qed.
Example pk_kinds_s : pk_kinds "%s
" = [PkStr].
Proof. reflexivity. Qed.
Example pk_kinds_mixed : pk_kinds "pid %d name %s state %lx%%" = [PkNum; PkStr; PkNum].
Proof. reflexivity. Qed.
Example pk_kinds_dangling : pk_kinds "abc%" = [].
Proof. reflexivity. Qed.
Example pk_kinds_unknown : pk_kinds "%q%llq" = [].
Proof. reflexivity. Qed.
