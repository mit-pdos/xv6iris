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
From Stdlib Require Import ZArith List Bool Ascii String.
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
