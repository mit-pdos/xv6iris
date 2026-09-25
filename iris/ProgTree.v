(* ===================================================================== *)
(* ProgTree.v -- a user program's EXTERNALLY VISIBLE behaviour as an       *)
(* INTERACTION TREE, and a pure interpreter that runs such trees against   *)
(* a console, files and pipes.                                            *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md (PROPOSAL).  This file is  *)
(* the pure half of that proposal, built first so that the specs can be    *)
(* READ and RUN before anything in the logic depends on them:             *)
(*                                                                        *)
(*   - [ev] is the vocabulary of what a process does that the world can    *)
(*     see: open, close, read, write, exit.  A syscall the world cannot    *)
(*     see (sbrk, the argument copies of exec, ...) is not an event.       *)
(*   - [itree R] is the ordinary interaction tree (Xia et al., POPL 2020), *)
(*     defined here in twenty lines because the switch has no itree        *)
(*     library and nothing below needs bisimulation: a program is a tree   *)
(*     that never returns ([proc := itree Empty_set]), and the theorems     *)
(*     about it are about its INTERPRETATIONS.                            *)
(*   - [echo_tree] and [cat_tree] are the two programs' specs: a function   *)
(*     from argv to the tree.  Each is at SYSCALL GRANULARITY -- one        *)
(*     [EWrite] per [write] the C makes, so xv6's [fprintf] (one write per  *)
(*     byte, user/printf.c [putc]) is a run of one-byte writes -- because   *)
(*     the granularity is observable when two processes share the console. *)
(*   - [run] interprets ONE process against a world under a deterministic  *)
(*     schedule, with fuel; [run_pipe] runs a two-process pipeline left     *)
(*     child first.  Both exist for the demos at the end (every line shape  *)
(*     the union application states, computed by [vm_compute]) and as the  *)
(*     pure reading the line model's continuations should be derived from. *)
(*     The general statement quantifies over schedules; the sequential one  *)
(*     is a valid schedule for every pipeline whose left output fits the    *)
(*     pipe (PIPESIZE = 512), which the line discipline guarantees.         *)
(*                                                                        *)
(* NOTHING IMPORTS THIS FILE.  It sits beside [LineWords] and above         *)
(* [StringBytes] only.                                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list gmap bitvector.definitions.
Require Import StringBytes LineWords.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition bytes := list (bv 8).
Definition sb (s : string) : bytes := string_bytes s.

(* ===================================================================== *)
(*  1.  EVENTS                                                            *)
(* ===================================================================== *)

(* what a read answers: the kernel's -1, or the bytes it delivered ([] is
   end of file) *)
Inductive rd_ans := RdErr | RdBytes (bs : bytes).

(* FIRST-ORDER events with an answer-type function, rather than the itree
   library's type-indexed [E : Type -> Type]: a node [Vis e k] then
   injects to [e = e'] and, since [ev] has decidable equality, to
   [k = k'] WITHOUT an axiom ([Eqdep_dec.inj_pair2_eq_dec]) -- which is
   what lets a payer invert [conforms] at a node. *)
Inductive ev :=
  | EOpen  (path : bytes) (omode : Z)               (* answers the descriptor, or -1 *)
  | EClose (fd : Z)
  | ERead  (fd : Z) (n : nat)                       (* at most [n] bytes *)
  | EWrite (fd : Z) (bs : bytes)                    (* the count written, or -1 *)
  | EExit  (status : Z).

Global Instance ev_eq_dec : EqDecision ev.
Proof. solve_decision. Defined.

Definition ans (e : ev) : Type :=
  match e with
  | EOpen _ _ => Z
  | EClose _ => Z
  | ERead _ _ => rd_ans
  | EWrite _ _ => Z
  | EExit _ => Empty_set
  end.

(* ===================================================================== *)
(*  2.  THE TREE                                                          *)
(* ===================================================================== *)

CoInductive itree (R : Type) : Type :=
  | Ret (r : R)
  | Tau (t : itree R)
  | Vis (e : ev) (k : ans e -> itree R).
Arguments Ret {R}.
Arguments Tau {R}.
Arguments Vis {R}.

Definition trigger (e : ev) : itree (ans e) := Vis e (fun x => Ret x).

CoFixpoint bind {R S : Type} (t : itree R) (f : R -> itree S) : itree S :=
  match t with
  | Ret r => f r
  | Tau t' => Tau (bind t' f)
  | Vis e k => Vis e (fun x => bind (k x) f)
  end.

Notation "x <- t ;; f" := (bind t (fun x => f))
  (at level 62, t at next level, right associativity).
Notation "t ;;; f" := (bind t (fun _ => f))
  (at level 62, right associativity).

(* the loop: [step] answers [inl] (again, at this state) or [inr] (done) *)
CoFixpoint iter_ {I R : Type} (step : I -> itree (I + R)) (t : itree (I + R))
    : itree R :=
  match t with
  | Ret (inl i) => Tau (iter_ step (step i))
  | Ret (inr r) => Ret r
  | Tau t' => Tau (iter_ step t')
  | Vis e k => Vis e (fun x => iter_ step (k x))
  end.
Definition iter {I R : Type} (step : I -> itree (I + R)) (i : I) : itree R :=
  iter_ step (step i).

(* a process never returns: its tree ends only in [EExit] *)
Definition proc := itree Empty_set.
Definition exit_ {R : Type} (status : Z) : itree R :=
  Vis (EExit status) (fun v : ans (EExit status) => match v with end).

(* the [observe] of the itree library: forces one step of a cofixpoint *)
Definition force {R : Type} (t : itree R) : itree R :=
  match t with Ret r => Ret r | Tau t' => Tau t' | Vis e k => Vis e k end.
Lemma force_eq {R : Type} (t : itree R) : t = force t.
Proof. destruct t; reflexivity. Qed.

(* ===================================================================== *)
(*  3.  THE PROGRAMS                                                      *)
(* ===================================================================== *)

(* THE TWO PROGRAMS ARE WRITTEN WITH THE CONSTRUCTORS, NOT WITH [bind]:
   every tree takes the tree that FOLLOWS it as an argument, so a payer
   reading a node sees the next node by one unfolding ([force_eq]) and
   never has to reassociate a [bind] -- an equation between two
   cofixpoints, which is not provable as an equality.  [bind] and [iter]
   stay for what is built from them by hand. *)

(* [fprintf]: one write per byte (user/printf.c, [putc]), then [rest] *)
Fixpoint write_bytes (fd : Z) (bs : bytes) (rest : proc) : proc :=
  match bs with
  | [] => rest
  | b :: r => Vis (EWrite fd [b]) (fun _ => write_bytes fd r rest)
  end.

(* --- echo -------------------------------------------------------------
     for (i = 1; i < argc; i++) {
       write(1, argv[i], strlen(argv[i]));
       write(1, i + 1 < argc ? SPACE : NEWLINE, 1);
     }
     exit(0);
   The return of [write] is ignored. *)
Fixpoint echo_words (ws : list bytes) (rest : proc) : proc :=
  match ws with
  | [] => rest
  | [w] => Vis (EWrite 1 w) (fun _ => Vis (EWrite 1 [wl_nl]) (fun _ => rest))
  | w :: r => Vis (EWrite 1 w) (fun _ => Vis (EWrite 1 [wl_sp]) (fun _ => echo_words r rest))
  end.

Definition echo_tree (argv : list bytes) : proc :=
  echo_words (drop 1 argv) (exit_ 0).

(* --- cat --------------------------------------------------------------
     cat(fd):  while ((n = read(fd, buf, 512)) > 0)
                 if (write(1, buf, n) != n) { fprintf(2, cat: write error); exit(1); }
               if (n < 0) { fprintf(2, cat: read error); exit(1); }
     main:     if (argc <= 1) { cat(0); exit(0); }
               for (i = 1; i < argc; i++) {
                 if ((fd = open(argv[i], O_RDONLY)) < 0) {
                   fprintf(2, cat: cannot open %s, argv[i]); exit(1); }
                 cat(fd); close(fd); }
               exit(0);                                                   *)
Definition cat_bufsz : nat := 512.
Definition cat_dg_read : bytes := sb "cat: read error" ++ [wl_nl].
Definition cat_dg_write : bytes := sb "cat: write error" ++ [wl_nl].
Definition cat_dg_open (p : bytes) : bytes := sb "cat: cannot open " ++ p ++ [wl_nl].

(* one turn of cat(fd): the read, then the branch its count selects *)
CoFixpoint cat_loop (fd : Z) (rest : proc) : proc :=
  Vis (ERead fd cat_bufsz) (fun a =>
    match a with
    | RdErr => write_bytes 2 cat_dg_read (exit_ 1)
    | RdBytes [] => rest
    | RdBytes bs =>
        Vis (EWrite 1 bs) (fun r =>
          if decide (r = Z.of_nat (length bs)) then Tau (cat_loop fd rest)
          else write_bytes 2 cat_dg_write (exit_ 1))
    end).

Fixpoint cat_files (paths : list bytes) (rest : proc) : proc :=
  match paths with
  | [] => rest
  | p :: r =>
      Vis (EOpen p 0) (fun fd =>
        if decide (fd < 0) then write_bytes 2 (cat_dg_open p) (exit_ 1)
        else cat_loop fd (Vis (EClose fd) (fun _ => cat_files r rest)))
  end.

Definition cat_tree (argv : list bytes) : proc :=
  match drop 1 argv with
  | [] => cat_loop 0 (exit_ 0)
  | paths => cat_files paths (exit_ 0)
  end.

(* Both trees look only at [drop 1 argv] (the command name is argv[0]), so
   a key's argument reading and a line's words that agree from argv[1] on
   name the same tree. *)
Lemma echo_tree_tail (a b : list bytes) :
  drop 1 a = drop 1 b -> echo_tree a = echo_tree b.
Proof. intros H. unfold echo_tree. rewrite H. reflexivity. Qed.

Lemma cat_tree_tail (a b : list bytes) :
  drop 1 a = drop 1 b -> cat_tree a = cat_tree b.
Proof. intros H. unfold cat_tree. rewrite H. reflexivity. Qed.

(* ===================================================================== *)
(*  4.  A WORLD, AND ONE PROCESS RUN AGAINST IT                           *)
(*                                                                        *)
(*  The endpoints a descriptor can name.  The shell's job at a line is to  *)
(*  build the table ([fdt]) -- that IS a line shape -- and nothing in a    *)
(*  program's tree depends on which endpoint a number names.               *)
(* ===================================================================== *)

Record pipe_st := MkPipe {
  p_buf : bytes;        (* written, not yet read *)
  p_wopen : bool;       (* a writer still holds the write end *)
}.

Inductive endpoint :=
  | EpCons
  | EpFile (name : bytes) (off : nat)
  | EpPipeW (p : nat)
  | EpPipeR (p : nat).

Record world := MkW {
  w_cin : bytes;                       (* what the console has to deliver *)
  w_cons : bytes;                      (* what the console has shown *)
  w_files : list (bytes * bytes);      (* name, content *)
  w_pipes : list (nat * pipe_st);
}.

Definition fdt := list (Z * endpoint).

Definition assoc_get {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    : option V :=
  match list_find (fun kv => kv.1 = k) l with
  | Some (_, kv) => Some kv.2
  | None => None
  end.
Definition assoc_set {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    (v : V) : list (K * V) :=
  (k, v) :: filter (fun kv => kv.1 <> k) l.
Definition assoc_del {K V : Type} `{EqDecision K} (l : list (K * V)) (k : K)
    : list (K * V) :=
  filter (fun kv => kv.1 <> k) l.

Definition file_get (w : world) (n : bytes) : option bytes := assoc_get (w_files w) n.
Definition file_set (w : world) (n : bytes) (c : bytes) : world :=
  MkW (w_cin w) (w_cons w) (assoc_set (w_files w) n c) (w_pipes w).
Definition pipe_get (w : world) (p : nat) : option pipe_st := assoc_get (w_pipes w) p.
Definition pipe_set (w : world) (p : nat) (s : pipe_st) : world :=
  MkW (w_cin w) (w_cons w) (w_files w) (assoc_set (w_pipes w) p s).
Definition cons_put (w : world) (bs : bytes) : world :=
  MkW (w_cin w) (w_cons w ++ bs) (w_files w) (w_pipes w).
Definition cons_take (w : world) (n : nat) : world * bytes :=
  (MkW (drop n (w_cin w)) (w_cons w) (w_files w) (w_pipes w), take n (w_cin w)).

(* the lowest descriptor not in the table (xv6's [fdalloc]) *)
Fixpoint lowest_free (t : fdt) (fd : Z) (fuel : nat) : Z :=
  match fuel with
  | O => fd
  | S f => match assoc_get t fd with None => fd | Some _ => lowest_free t (fd + 1) f end
  end.

(* O_CREATE = 0x200, O_TRUNC = 0x400 (kernel/fcntl.h) *)
Definition om_create (m : Z) : bool := bool_decide (Z.land m 0x200 <> 0).
Definition om_trunc  (m : Z) : bool := bool_decide (Z.land m 0x400 <> 0).

(* THE KERNEL'S ANSWER TO ONE EVENT, deterministically: the GOOD
   answers.  Where the kernel may answer otherwise (a present file whose
   [filealloc] fails, a pipe write whose reader has gone), the real
   theorem quantifies over the answer; the interpreter picks one. *)
Definition step_open (w : world) (t : fdt) (path : bytes) (m : Z)
    : world * fdt * Z :=
  match file_get w path, om_create m with
  | None, false => (w, t, -1)
  | None, true =>
      let fd := lowest_free t 0 16 in
      (file_set w path [], assoc_set t fd (EpFile path 0), fd)
  | Some c, _ =>
      let fd := lowest_free t 0 16 in
      let w' := if om_trunc m then file_set w path [] else w in
      (w', assoc_set t fd (EpFile path 0), fd)
  end.

Definition step_close (w : world) (t : fdt) (fd : Z) : world * fdt * Z :=
  match assoc_get t fd with
  | None => (w, t, -1)
  | Some (EpPipeW p) =>
      (* the last writer closing is what makes the reader's EOF; one writer
         per pipe end in every line here *)
      let w' := match pipe_get w p with
                | Some s => pipe_set w p (MkPipe (p_buf s) false)
                | None => w
                end in
      (w', assoc_del t fd, 0)
  | Some _ => (w, assoc_del t fd, 0)
  end.

(* what a process's exit does to the world: its descriptors close *)
Fixpoint close_all (w : world) (t : fdt) (fds : list Z) : world :=
  match fds with
  | [] => w
  | fd :: r => close_all (step_close w t fd).1.1 t r
  end.
Definition step_exit (w : world) (t : fdt) : world :=
  close_all w t (map fst t).

Definition step_read (w : world) (t : fdt) (fd : Z) (n : nat)
    : world * fdt * rd_ans :=
  match assoc_get t fd with
  | None => (w, t, RdErr)
  | Some EpCons => let '(w', bs) := cons_take w n in (w', t, RdBytes bs)
  | Some (EpFile name off) =>
      match file_get w name with
      | None => (w, t, RdErr)
      | Some c =>
          let bs := take n (drop off c) in
          (w, assoc_set t fd (EpFile name (off + length bs)), RdBytes bs)
      end
  | Some (EpPipeW _) => (w, t, RdErr)
  | Some (EpPipeR p) =>
      match pipe_get w p with
      | None => (w, t, RdErr)
      | Some s =>
          let bs := take n (p_buf s) in
          (pipe_set w p (MkPipe (drop n (p_buf s)) (p_wopen s)), t, RdBytes bs)
          (* an empty buffer with the writer open would BLOCK; under the
             left-first schedule it never happens *)
      end
  end.

Definition step_write (w : world) (t : fdt) (fd : Z) (bs : bytes)
    : world * fdt * Z :=
  match assoc_get t fd with
  | None => (w, t, -1)
  | Some EpCons => (cons_put w bs, t, Z.of_nat (length bs))
  | Some (EpFile name off) =>
      match file_get w name with
      | None => (w, t, -1)
      | Some c =>
          (* xv6 has no O_APPEND: the write lands at the descriptor's offset *)
          let c' := take off c ++ bs ++ drop (off + length bs) c in
          (file_set w name c', assoc_set t fd (EpFile name (off + length bs)),
           Z.of_nat (length bs))
      end
  | Some (EpPipeW p) =>
      match pipe_get w p with
      | None => (w, t, -1)
      | Some s => (pipe_set w p (MkPipe (p_buf s ++ bs) (p_wopen s)), t,
                   Z.of_nat (length bs))
      end
  | Some (EpPipeR _) => (w, t, -1)
  end.

Inductive outcome := Exited (status : Z) | OutOfFuel.

(* ONE PROCESS, to its exit *)
Fixpoint run (fuel : nat) (w : world) (t : fdt) (p : proc) : world * outcome :=
  match fuel with
  | O => (w, OutOfFuel)
  | S fuel' =>
      match force p with
      | Ret v => match v with end
      | Tau p' => run fuel' w t p'
      | Vis e k =>
          match e as e return (ans e -> proc) -> world * outcome with
          | EOpen path m => fun k =>
              let '(w', t', r) := step_open w t path m in run fuel' w' t' (k r)
          | EClose fd => fun k =>
              let '(w', t', r) := step_close w t fd in run fuel' w' t' (k r)
          | ERead fd n => fun k =>
              let '(w', t', a) := step_read w t fd n in run fuel' w' t' (k a)
          | EWrite fd bs => fun k =>
              let '(w', t', r) := step_write w t fd bs in run fuel' w' t' (k r)
          | EExit s => fun _ => (step_exit w t, Exited s)
          end k
      end
  end.

(* ===================================================================== *)
(*  5.  THE LINE SHAPES, as the shell provisions them                     *)
(* ===================================================================== *)

(* enough steps for every demo; a [nat] literal above 5000 warns *)
Definition fuel : nat := 100 * 100.

Definition std_console : fdt := [(0, EpCons); (1, EpCons); (2, EpCons)].

(* `cmd args`: the console on 0, 1, 2 *)
Definition line_plain (w : world) (p : proc) : world * outcome :=
  run fuel w std_console p.

(* `cmd args > f`: sh does close(1); open(f, O_WRONLY|O_CREATE|O_TRUNC) *)
Definition line_redirect (w : world) (f : bytes) (p : proc) : world * outcome :=
  let '(w', t', _) := step_open w (assoc_del std_console 1) f (0x1 + 0x200 + 0x400) in
  run fuel w' t' p.

(* `l | r`: sh does pipe(); the left child close(1); dup(w); the right
   close(0); dup(r); each closes both pipe ends it did not dup.  The left
   child runs first -- a valid schedule when its output fits the pipe. *)
Definition line_pipe (w : world) (l r : proc) : world * outcome :=
  let pid := 0%nat in
  let w0 := pipe_set w pid (MkPipe [] true) in
  let tl := assoc_set std_console 1 (EpPipeW pid) in
  let tr := assoc_set std_console 0 (EpPipeR pid) in
  let '(w1, _) := run fuel w0 tl l in
  run fuel w1 tr r.

(* ===================================================================== *)
(*  6.  DEMOS: what each line shows on the console, by computation        *)
(* ===================================================================== *)

Definition w0 : world := MkW [] [] [] [].
Definition argv_echo (ws : list string) : list bytes := sb "echo" :: map sb ws.
Definition argv_cat (ws : list string) : list bytes := sb "cat" :: map sb ws.

(* echo foo bar *)
Example demo_echo :
  (line_plain w0 (echo_tree (argv_echo ["foo"; "bar"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* ...and it is exactly the line model's block for the good alternative *)
Example demo_echo_is_wl_line :
  (line_plain w0 (echo_tree (argv_echo ["foo"; "bar"]))).1.(w_cons)
  = wl_line (drop 1 (argv_echo ["foo"; "bar"])).
Proof. vm_compute. reflexivity. Qed.

(* echo foo bar > f : nothing on the console; f holds the line *)
Definition after_redirect : world :=
  (line_redirect w0 (sb "f") (echo_tree (argv_echo ["foo"; "bar"]))).1.
Example demo_redirect_cons : w_cons after_redirect = [].
Proof. vm_compute. reflexivity. Qed.
Example demo_redirect_file : file_get after_redirect (sb "f") = Some (sb "foo bar" ++ [wl_nl]).
Proof. vm_compute. reflexivity. Qed.

(* cat f, after the redirect: the line comes back *)
Example demo_cat_f :
  (line_plain after_redirect (cat_tree (argv_cat ["f"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat g, absent: the diagnostic on fd 2 = the console, status 1 *)
Example demo_cat_absent :
  let '(w, o) := line_plain after_redirect (cat_tree (argv_cat ["g"])) in
  w_cons w = sb "cat: cannot open g" ++ [wl_nl] /\ o = Exited 1.
Proof. vm_compute. split; reflexivity. Qed.

(* cat f g: the content, THEN the diagnostic -- the order across fd 1 and
   fd 2 is the tree's, which a per-descriptor stream spec cannot say *)
Example demo_cat_f_then_absent :
  (line_plain after_redirect (cat_tree (argv_cat ["f"; "g"]))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl] ++ sb "cat: cannot open g" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* echo foo | cat *)
Example demo_pipe :
  (line_pipe w0 (echo_tree (argv_echo ["foo"])) (cat_tree (argv_cat []))).1.(w_cons)
  = sb "foo" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat f | cat *)
Example demo_cat_pipe_cat :
  (line_pipe after_redirect (cat_tree (argv_cat ["f"])) (cat_tree (argv_cat []))).1.(w_cons)
  = sb "foo bar" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* cat f > g, then cat g: the file copied through the held offset *)
Example demo_cat_redirect :
  let w1 := (line_redirect after_redirect (sb "g") (cat_tree (argv_cat ["f"]))).1 in
  w_cons w1 = [] /\ file_get w1 (sb "g") = Some (sb "foo bar" ++ [wl_nl]).
Proof. vm_compute. split; reflexivity. Qed.

(* chunking: a file longer than cat's buffer is copied in two reads and
   two writes, and the stream is still the content *)
Definition long_content : bytes := replicate 700 (Z_to_bv 8 97).
Definition w_long : world := file_set w0 (sb "big") long_content.
Example demo_cat_long :
  (line_plain w_long (cat_tree (argv_cat ["big"]))).1.(w_cons) = long_content.
Proof. vm_compute. reflexivity. Qed.

(* cat with no argument reads the console's input to end of file *)
Example demo_cat_stdin :
  let w := MkW (sb "typed" ++ [wl_nl]) [] [] [] in
  (line_plain w (cat_tree (argv_cat []))).1.(w_cons) = sb "typed" ++ [wl_nl].
Proof. vm_compute. reflexivity. Qed.

(* A NEGATIVE ONE: the interpreter is not a constant function of its input *)
Example demo_negative :
  (line_plain w0 (echo_tree (argv_echo ["foo"]))).1.(w_cons)
  <> (line_plain w0 (echo_tree (argv_echo ["bar"]))).1.(w_cons).
Proof. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  7.  THE ONE-STEP EQUATIONS                                            *)
(*                                                                        *)
(*  A cofixpoint is equal to its one-step unfolding ([force_eq]), and that *)
(*  is all the reasoning the trees ever need: a payer at a node reads the  *)
(*  node, never compares two trees.  Where a continuation is compared      *)
(*  pointwise the step is functional extensionality, which the tree        *)
(*  already assumes.                                                       *)
(* ===================================================================== *)
From Stdlib Require Import FunctionalExtensionality.

Lemma bind_ret {R S : Type} (r : R) (f : R -> itree S) : bind (Ret r) f = f r.
Proof. rewrite (force_eq (bind _ _)), (force_eq (f r)). reflexivity. Qed.
Lemma bind_tau {R S : Type} (t : itree R) (f : R -> itree S) :
  bind (Tau t) f = Tau (bind t f).
Proof. rewrite (force_eq (bind _ _)). reflexivity. Qed.
Lemma bind_vis {R S : Type} (e : ev) (k : ans e -> itree R) (f : R -> itree S) :
  bind (Vis e k) f = Vis e (fun x => bind (k x) f).
Proof. rewrite (force_eq (bind _ _)). reflexivity. Qed.
Lemma trigger_bind {S : Type} (e : ev) (f : ans e -> itree S) :
  bind (trigger e) f = Vis e f.
Proof.
  unfold trigger. rewrite bind_vis. f_equal. apply functional_extensionality.
  intros x. apply bind_ret.
Qed.
Lemma iter__ret_inl {I R : Type} (step : I -> itree (I + R)) (i : I) :
  iter_ step (Ret (inl i)) = Tau (iter step i).
Proof. rewrite (force_eq (iter_ _ _)). reflexivity. Qed.
Lemma iter__ret_inr {I R : Type} (step : I -> itree (I + R)) (r : R) :
  iter_ step (Ret (inr r)) = Ret r.
Proof. rewrite (force_eq (iter_ _ _)). reflexivity. Qed.
Lemma iter__tau {I R : Type} (step : I -> itree (I + R)) (t : itree (I + R)) :
  iter_ step (Tau t) = Tau (iter_ step t).
Proof. rewrite (force_eq (iter_ _ _)). reflexivity. Qed.
Lemma iter__vis {I R : Type} (step : I -> itree (I + R)) (e : ev)
    (k : ans e -> itree (I + R)) :
  iter_ step (Vis e k) = Vis e (fun x => iter_ step (k x)).
Proof. rewrite (force_eq (iter_ _ _)). reflexivity. Qed.
Lemma exit_bind {R S : Type} (s : Z) (f : R -> itree S) :
  bind (exit_ s) f = exit_ s.
Proof.
  unfold exit_. rewrite bind_vis. f_equal. apply functional_extensionality.
  intros v. destruct v.
Qed.
Lemma cat_loop_unfold (fd : Z) (rest : proc) :
  cat_loop fd rest
  = Vis (ERead fd cat_bufsz) (fun a =>
      match a with
      | RdErr => write_bytes 2 cat_dg_read (exit_ 1)
      | RdBytes [] => rest
      | RdBytes bs =>
          Vis (EWrite 1 bs) (fun r =>
            if decide (r = Z.of_nat (length bs)) then Tau (cat_loop fd rest)
            else write_bytes 2 cat_dg_write (exit_ 1))
      end).
Proof. etransitivity; [apply force_eq |]. reflexivity. Qed.

(* ===================================================================== *)
(*  8.  CONFORMANCE: a tree against an environment of endpoints           *)
(*                                                                        *)
(*  What a line shape provisions, abstractly: descriptors bound to        *)
(*  DEVICES, each device an endpoint spec -- an input stream, or an       *)
(*  output owed as a SET of alternatives (the console: which one is       *)
(*  decided at the first byte, as the line model's block-first link does; *)
(*  a file or a pipe: one alternative).  [conforms E t] says every path   *)
(*  of [t] writes a prefix of an alternative IT CHOOSES (after which that *)
(*  one's rest is all that is owed), reads any chunking of its input, is  *)
(*  ready for either answer of an open (the kernel may refuse a present   *)
(*  file), and exits only with every output fully written.  It is the PURE half of a handler: the logic's half    *)
(*  funds the holes of a conforming tree from the endpoints' resources,   *)
(*  once, by coinduction.                                                 *)
(* ===================================================================== *)

(* A FILTER (claude-notes/design/grep-pipes.md SS1): what a stage owes on
   its output, as a function of what it has read.  [flt_out R] is the
   output owed after reading [R]; [flt_new R c] is what a chunk [c] read
   after [R] adds to it (for a line filter, the lines [c] completes).
   [flt_app] says the two agree along the input, [flt_nil] that nothing is
   owed before the first byte.  cat is the identity, [flt_id], whose
   [flt_new] is the chunk itself -- so its device's read rule is the
   copy's [p ++ c] definitionally.  (Named [pfilter], not [filter]: a
   Record named [filter] here would shadow stdpp's list filter in every
   file that imports this one.) *)
Record pfilter := MkFilter {
  flt_out : bytes -> bytes;
  flt_new : bytes -> bytes -> bytes;
  flt_app : forall R c, flt_out (R ++ c) = flt_out R ++ flt_new R c;
  flt_nil : flt_out [] = [] }.

Definition flt_id : pfilter :=
  MkFilter (fun R => R) (fun _ c => c) (fun _ _ => eq_refl) eq_refl.

Inductive dspec :=
  | DOut (alts : list bytes)      (* what is still owed, one of these *)
  | DOutH (alts : list bytes)     (* ...at a device that may HALT: a pipe whose
                                     reader may go; a write then answers -1 *)
  | DOutM (chunks : list bytes)   (* ...at a device where a write may MISS: a
                                     file at a full disk answers -1 and the
                                     process goes on, the chunk not landed.
                                     Owed as CHUNKS, each write the next one
                                     whole: the file application records a
                                     file as the chunks of a line that landed *)
  | DHalt                         (* halted: every write answers -1 *)
  | DIn (S : bytes)               (* what is still to be read *)
  | DInE (S : bytes)              (* ...at a device that may END EARLY: a pipe
                                     whose writer may close before the line
                                     is in; a read then answers end of file *)
  | DInEnd                        (* ended: every read answers end of file *)
  (* THE FILTER DEVICE (design SS3.4f, generalised by grep-pipes.md SS1):
     a filter at a pipe's end -- cat, grep -- and ONE device number bound
     to both its descriptors, the pipe's read end on 0 and the sink on 1.
     [F] is the filter, [R] the input read so far, [S] the input still to
     come, [pending] the output owed and not yet written; [h] says whether
     the sink may halt (a pipe's write end) or not (the console).  A read
     of a chunk [c] of [S] adds [flt_new F R c] to [pending], or ends the
     input; a write drains a prefix of [pending]; the device is drained
     when [pending] is empty at the end of the input. *)
  | DCopy (F : pfilter) (h : bool) (R S : bytes) (pending : bytes)
  | DCopyEnd (F : pfilter) (h : bool) (pending : bytes)   (* the writer closed: reads answer end of file *)
  (* the sink's reader went: writes answer -1.  The filter may go on
     READING (grep reads to the end of its input whatever became of its
     output): [Some S] is the input still to come, [None] its end *)
  | DCopyHalt (oS : option bytes)
  (* THE PRODUCER'S DEVICE (union.md C9d'): a producer that may FAIL
     BEFORE its output -- [cat f], whose open may be refused -- writes its
     output on [prod_out] (a pipe's write end: the reader may go) and its
     diagnostics on [prod_err] (the console), and ONE device number is
     bound to both, as the copy device is to cat's input and output.  The
     output owes one of [outs]; the diagnostics owe one of [ds], or --
     while nothing is on the output yet -- one of the FAILURE REPORTS
     [xs], which leaves the output owing nothing ([] must be among
     [outs]).  The first byte on either descriptor retires [xs]: a report
     after output, or output after a report, is not the producer's.  The
     pairing is what the round's deposit needs: a failure report spends
     the output's untouched write permit, which the output then no longer
     holds. *)
  | DProd (outs : list bytes) (xs : list bytes) (ds : list bytes)
  | DProdHalt (ds : list bytes).  (* the output's reader went: output writes answer -1 *)

(* THE COPY DEVICE IS A FILTER'S (found by the pipeline instance, lane
   copyinst): its input is the standard input and its output the standard
   output.  The two descriptors are two kernel objects (a pipe's read end
   and the sink), so a read is a conformance event only at [copy_in] and a
   write only at [copy_out]; the instance cannot pay a read at the sink. *)
Definition copy_in : Z := 0.
Definition copy_out : Z := 1.

(* the producer device's two descriptors: its output, its diagnostics *)
Definition prod_out : Z := 1.
Definition prod_err : Z := 2.

Record penv := MkEnv {
  pe_fd : gmap Z nat;             (* descriptor -> device *)
  pe_dev : nat -> dspec;
  pe_files : bytes -> option bytes;
  pe_paths : list bytes;          (* the paths the environment DESCRIBES: an
                                     open of any other path is outside it *)
}.

Definition env_dev (E : penv) (fd : Z) : option dspec :=
  match pe_fd E !! fd with Some d => Some (pe_dev E d) | None => None end.
Definition env_set_dev (E : penv) (d : nat) (s : dspec) : penv :=
  MkEnv (pe_fd E) (fun d' => if decide (d' = d) then s else pe_dev E d') (pe_files E) (pe_paths E).
Definition env_bind (E : penv) (fd : Z) (d : nat) : penv :=
  MkEnv (<[fd := d]> (pe_fd E)) (pe_dev E) (pe_files E) (pe_paths E).
Definition env_unbind (E : penv) (fd : Z) : penv :=
  MkEnv (delete fd (pe_fd E)) (pe_dev E) (pe_files E) (pe_paths E).

(* an open mode that creates (O_CREATE, kernel/fcntl.h) *)
Definition mode_create (m : Z) : Prop := Z.land m 0x200 <> 0.
Definition env_fresh (E : penv) (d : nat) : Prop :=
  forall fd, pe_fd E !! fd <> Some d.

(* a read's answer: a chunk of at most [n], empty only at end of file *)
Definition chunk_ok (n : nat) (S c S' : bytes) : Prop :=
  S = c ++ S' /\ (length c <= n)%nat /\ (c = [] -> S = []).

(* an output device with nothing left to owe *)
Definition drained (x : dspec) : Prop :=
  match x with
  | DOut alts => [] ∈ alts
  | DOutH alts => [] ∈ alts
  | DOutM chunks => chunks = []
  (* a copy device is drained only at its END (lane copyinst): the exit
     payoff of a pipe's reader is the end-of-file shot, which an open
     device does not hold; cat reads until 0 and never exits open.  A
     halted one is drained (cat exits right after its sink halts) *)
  | DCopy _ _ _ _ _ => False
  | DCopyEnd _ _ pending => pending = []
  (* the producer device: the output and the diagnostics both done *)
  | DProd outs _ ds => [] ∈ outs /\ [] ∈ ds
  | DProdHalt ds => [] ∈ ds
  | _ => True
  end.

(* THE LAST CLOSE OF A DEVICE (the close gap, lane closegap): a descriptor
   is the last one naming its device when no other descriptor does, and
   the last close of a COPY device or of a HALTABLE output (a pipe's write
   end) asks the device DRAINED.  The pipeline's instance pays the reader's
   or the writer's exit payoff at that close (the end-of-file shot and
   equal cursors at a copy device, the line's end or the reader's shot at
   a write end), which an undrained device does not hold; cat and echo
   never close such a device early.  The other kinds are free: the file
   application closes an INPUT before it is read to its end. *)
Definition fd_last (fdm : gmap Z nat) (fd : Z) (d : nat) : Prop :=
  forall fd', fd' <> fd -> fdm !! fd' <> Some d.

Definition drained_at_close (x : dspec) : Prop :=
  match x with
  | DOutH _ | DHalt | DCopy _ _ _ _ _ | DCopyEnd _ _ _ | DCopyHalt _
  | DProd _ _ _ | DProdHalt _ => drained x
  | _ => True
  end.

(* ONE step of conformance, as a function of the relation: the greatest
   fixpoint below needs no injectivity of [Vis] to be unfolded, so a payer
   reads a node by [destruct t; simpl]. *)
Definition cf_step (R : penv -> proc -> Prop) (E : penv) (t : proc) : Prop :=
  match t with
  | Ret v => match v with end
  | Tau t' => R E t'
  | Vis e k =>
      match e as e return (ans e -> proc) -> Prop with
      | EWrite fd bs => fun k =>
          exists d, pe_fd E !! fd = Some d /\
          ((bs = [] /\ R E (k 0) /\ R E (k (-1)))
           \/ (bs <> [] /\ exists alts a, pe_dev E d = DOut alts
              /\ a ∈ alts /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DOut [drop (length bs) a])) (k (Z.of_nat (length bs))))
           \/ (bs <> [] /\ exists alts a, pe_dev E d = DOutH alts
              /\ a ∈ alts /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DOutH [drop (length bs) a])) (k (Z.of_nat (length bs)))
              /\ R (env_set_dev E d DHalt) (k (-1)))
           \/ (bs <> [] /\ exists rest, pe_dev E d = DOutM (bs :: rest)
              /\ R (env_set_dev E d (DOutM rest)) (k (Z.of_nat (length bs)))
              /\ R (env_set_dev E d (DOutM rest)) (k (-1)))
           \/ (bs <> [] /\ Z.of_nat (length bs) < 2 ^ 31 /\ pe_dev E d = DHalt /\ R E (k (-1)))
           \/ (bs <> [] /\ fd = copy_out /\ exists F h Rr S p, pe_dev E d = DCopy F h Rr S p /\ bs `prefix_of` p
              /\ R (env_set_dev E d (DCopy F h Rr S (drop (length bs) p))) (k (Z.of_nat (length bs)))
              /\ (h = true -> R (env_set_dev E d (DCopyHalt (Some S))) (k (-1))))
           \/ (bs <> [] /\ fd = copy_out /\ exists F h p, pe_dev E d = DCopyEnd F h p /\ bs `prefix_of` p
              /\ R (env_set_dev E d (DCopyEnd F h (drop (length bs) p))) (k (Z.of_nat (length bs)))
              /\ (h = true -> R (env_set_dev E d (DCopyHalt None)) (k (-1))))
           \/ (bs <> [] /\ Z.of_nat (length bs) < 2 ^ 31 /\ fd = copy_out
               /\ exists oS, pe_dev E d = DCopyHalt oS /\ R E (k (-1)))
           \/ (bs <> [] /\ fd = prod_out /\ exists outs xs ds a, pe_dev E d = DProd outs xs ds
              /\ a ∈ outs /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DProd [drop (length bs) a] [] ds)) (k (Z.of_nat (length bs)))
              /\ R (env_set_dev E d (DProdHalt ds)) (k (-1)))
           \/ (bs <> [] /\ Z.of_nat (length bs) < 2 ^ 31 /\ fd = prod_out
               /\ exists ds, pe_dev E d = DProdHalt ds /\ R E (k (-1)))
           \/ (bs <> [] /\ fd = prod_err /\ exists outs xs ds a, pe_dev E d = DProd outs xs ds
              /\ a ∈ ds /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DProd outs [] [drop (length bs) a])) (k (Z.of_nat (length bs))))
           \/ (bs <> [] /\ fd = prod_err /\ exists outs xs ds a, pe_dev E d = DProd outs xs ds
              /\ [] ∈ outs /\ a ∈ xs /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DProd [[]] [] [drop (length bs) a])) (k (Z.of_nat (length bs))))
           \/ (bs <> [] /\ fd = prod_err /\ exists ds a, pe_dev E d = DProdHalt ds
              /\ a ∈ ds /\ bs `prefix_of` a
              /\ R (env_set_dev E d (DProdHalt [drop (length bs) a])) (k (Z.of_nat (length bs)))))
      | ERead fd n => fun k =>
          exists d, pe_fd E !! fd = Some d /\ (0 < n)%nat /\
          ((exists S, pe_dev E d = DIn S
              /\ forall c S', chunk_ok n S c S' -> R (env_set_dev E d (DIn S')) (k (RdBytes c)))
           \/ (exists S, pe_dev E d = DInE S
              /\ (forall c S', chunk_ok n S c S' -> R (env_set_dev E d (DInE S')) (k (RdBytes c)))
              /\ R (env_set_dev E d DInEnd) (k (RdBytes [])))
           \/ (pe_dev E d = DInEnd /\ R E (k (RdBytes [])))
           \/ (fd = copy_in /\ exists F h Rr S p, pe_dev E d = DCopy F h Rr S p
              /\ (forall c S', chunk_ok n S c S' -> c <> [] ->
                    R (env_set_dev E d (DCopy F h (Rr ++ c) S' (p ++ flt_new F Rr c))) (k (RdBytes c)))
              /\ R (env_set_dev E d (DCopyEnd F h p)) (k (RdBytes [])))
           \/ (fd = copy_in /\ exists F h p, pe_dev E d = DCopyEnd F h p /\ R E (k (RdBytes [])))
           \/ (fd = copy_in /\ exists S, pe_dev E d = DCopyHalt (Some S)
              /\ (forall c S', chunk_ok n S c S' -> c <> [] ->
                    R (env_set_dev E d (DCopyHalt (Some S'))) (k (RdBytes c)))
              /\ R (env_set_dev E d (DCopyHalt None)) (k (RdBytes [])))
           \/ (fd = copy_in /\ pe_dev E d = DCopyHalt None /\ R E (k (RdBytes []))))
      | EOpen p m => fun k =>
          p ∈ pe_paths E /\
          ((m = 0 /\ exists content, pe_files E p = Some content
             (* the kernel hands back a descriptor the process did not hold *)
             /\ (forall fd d, 0 <= fd -> pe_fd E !! fd = None -> env_fresh E d ->
                   R (env_set_dev (env_bind E fd d) d (DIn content)) (k fd))
             /\ R E (k (-1)))
          \/ (~ mode_create m /\ pe_files E p = None /\ R E (k (-1))))
      | EClose fd => fun k =>
          exists d, pe_fd E !! fd = Some d
          /\ (fd_last (pe_fd E) fd d -> drained_at_close (pe_dev E d))
          /\ R (env_unbind E fd) (k 0)
      | EExit s => fun _ => forall d, drained (pe_dev E d)
      end k
  end.

CoInductive conforms : penv -> proc -> Prop :=
  | cf_tau E t :
      conforms E t -> conforms E (Tau t)
  (* a write CHOOSES the alternative it is a prefix of (the console files
     one at its first byte, and the proof knows which from its branch, as
     the landed payers do); what is owed is then that one's rest *)
  (* a zero-length write: 0 or -1, at the kernel's whim, nothing moves *)
  | cf_write_nil E fd d k :
      pe_fd E !! fd = Some d ->
      conforms E (k 0) -> conforms E (k (-1)) ->
      conforms E (Vis (EWrite fd []) k)
  | cf_write E fd d alts a bs k :
      bs <> [] ->
      pe_fd E !! fd = Some d -> pe_dev E d = DOut alts ->
      a ∈ alts -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DOut [drop (length bs) a])) (k (Z.of_nat (length bs))) ->
      conforms E (Vis (EWrite fd bs) k)
  (* ...at a haltable device the tree is ready for both answers *)
  | cf_write_h E fd d alts a bs k :
      bs <> [] ->
      pe_fd E !! fd = Some d -> pe_dev E d = DOutH alts ->
      a ∈ alts -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DOutH [drop (length bs) a])) (k (Z.of_nat (length bs))) ->
      conforms (env_set_dev E d DHalt) (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  (* ...at a device where a write may miss, the tree is ready for -1 and
     the device owes the rest either way *)
  | cf_write_m E fd d rest bs k :
      bs <> [] ->
      pe_fd E !! fd = Some d -> pe_dev E d = DOutM (bs :: rest) ->
      conforms (env_set_dev E d (DOutM rest)) (k (Z.of_nat (length bs))) ->
      conforms (env_set_dev E d (DOutM rest)) (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  (* at a HALTED device the answer is -1 only at a count the kernel reads
     as a positive C int: sys_write takes the count by argint, so a write
     of 2^31 bytes or more is read as the count modulo 2^32, signed --
     negative (filewrite answers -1 before the pipe, and the landed write
     contract admits 0 there), or 0 at a multiple of 2^32 (pipewrite's loop
     never runs and the answer is 0, halted or not).  The tree promises
     no such write at a halted device *)
  | cf_write_halt E fd d bs k :
      bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 ->
      pe_fd E !! fd = Some d -> pe_dev E d = DHalt ->
      conforms E (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  (* at the copy device a write drains a prefix of what was read; when the
     sink may halt ([h = true]) the tree is also ready for -1, after which
     the device is halted *)
  | cf_write_copy E fd d F h Rr S p bs k :
      bs <> [] -> fd = copy_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopy F h Rr S p ->
      bs `prefix_of` p ->
      conforms (env_set_dev E d (DCopy F h Rr S (drop (length bs) p))) (k (Z.of_nat (length bs))) ->
      (h = true -> conforms (env_set_dev E d (DCopyHalt (Some S))) (k (-1))) ->
      conforms E (Vis (EWrite fd bs) k)
  | cf_write_copy_end E fd d F h p bs k :
      bs <> [] -> fd = copy_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyEnd F h p ->
      bs `prefix_of` p ->
      conforms (env_set_dev E d (DCopyEnd F h (drop (length bs) p))) (k (Z.of_nat (length bs))) ->
      (h = true -> conforms (env_set_dev E d (DCopyHalt None)) (k (-1))) ->
      conforms E (Vis (EWrite fd bs) k)
  | cf_write_copy_halt E fd d oS bs k :
      bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fd = copy_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyHalt oS ->
      conforms E (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  (* at the PRODUCER device an output write takes a prefix of an owed
     output and retires the failure reports; the reader may go, after
     which every output write answers -1 *)
  | cf_write_prod E fd d outs xs ds a bs k :
      bs <> [] -> fd = prod_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DProd outs xs ds ->
      a ∈ outs -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DProd [drop (length bs) a] [] ds)) (k (Z.of_nat (length bs))) ->
      conforms (env_set_dev E d (DProdHalt ds)) (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  | cf_write_prod_halt E fd d ds bs k :
      bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fd = prod_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DProdHalt ds ->
      conforms E (k (-1)) ->
      conforms E (Vis (EWrite fd bs) k)
  (* ...a diagnostic write chooses one of [ds] (the reports retired), or
     -- the output still able to owe nothing -- a FAILURE REPORT, after
     which the output owes nothing *)
  | cf_write_prod_err E fd d outs xs ds a bs k :
      bs <> [] -> fd = prod_err ->
      pe_fd E !! fd = Some d -> pe_dev E d = DProd outs xs ds ->
      a ∈ ds -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DProd outs [] [drop (length bs) a])) (k (Z.of_nat (length bs))) ->
      conforms E (Vis (EWrite fd bs) k)
  | cf_write_prod_fail E fd d outs xs ds a bs k :
      bs <> [] -> fd = prod_err ->
      pe_fd E !! fd = Some d -> pe_dev E d = DProd outs xs ds ->
      [] ∈ outs -> a ∈ xs -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DProd [[]] [] [drop (length bs) a])) (k (Z.of_nat (length bs))) ->
      conforms E (Vis (EWrite fd bs) k)
  | cf_write_prod_halt_err E fd d ds a bs k :
      bs <> [] -> fd = prod_err ->
      pe_fd E !! fd = Some d -> pe_dev E d = DProdHalt ds ->
      a ∈ ds -> bs `prefix_of` a ->
      conforms (env_set_dev E d (DProdHalt [drop (length bs) a])) (k (Z.of_nat (length bs))) ->
      conforms E (Vis (EWrite fd bs) k)
  (* a read asks for at least one byte (a zero-length read answers 0
     whatever is owed) *)
  | cf_read E fd d S n k :
      (0 < n)%nat ->
      pe_fd E !! fd = Some d -> pe_dev E d = DIn S ->
      (forall c S', chunk_ok n S c S' ->
         conforms (env_set_dev E d (DIn S')) (k (RdBytes c))) ->
      conforms E (Vis (ERead fd n) k)
  (* ...at a device that may end early the tree is ready for end of file *)
  | cf_read_e E fd d S n k :
      (0 < n)%nat ->
      pe_fd E !! fd = Some d -> pe_dev E d = DInE S ->
      (forall c S', chunk_ok n S c S' ->
         conforms (env_set_dev E d (DInE S')) (k (RdBytes c))) ->
      conforms (env_set_dev E d DInEnd) (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  | cf_read_end E fd d n k :
      (0 < n)%nat ->
      pe_fd E !! fd = Some d -> pe_dev E d = DInEnd ->
      conforms E (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  (* at the filter device a read of a NONEMPTY chunk of the input (a pipe
     answers 0 only at its end) adds what the chunk owes to [pending], and
     (the writer may close first) the tree is ready for end of file *)
  | cf_read_copy E fd d F h Rr S p n k :
      (0 < n)%nat -> fd = copy_in ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopy F h Rr S p ->
      (forall c S', chunk_ok n S c S' -> c <> [] ->
         conforms (env_set_dev E d (DCopy F h (Rr ++ c) S' (p ++ flt_new F Rr c))) (k (RdBytes c))) ->
      conforms (env_set_dev E d (DCopyEnd F h p)) (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  | cf_read_copy_end E fd d F h p n k :
      (0 < n)%nat -> fd = copy_in ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyEnd F h p ->
      conforms E (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  (* ...and at a HALTED one the input goes on: a chunk, or end of file
     (grep reads to its end whatever became of its output; cat never
     reads there, it prints its diagnostic and exits) *)
  | cf_read_copy_halt E fd d S n k :
      (0 < n)%nat -> fd = copy_in ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyHalt (Some S) ->
      (forall c S', chunk_ok n S c S' -> c <> [] ->
         conforms (env_set_dev E d (DCopyHalt (Some S'))) (k (RdBytes c))) ->
      conforms (env_set_dev E d (DCopyHalt None)) (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  | cf_read_copy_halt_end E fd d n k :
      (0 < n)%nat -> fd = copy_in ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyHalt None ->
      conforms E (k (RdBytes [])) ->
      conforms E (Vis (ERead fd n) k)
  | cf_open_present E p content k :
      p ∈ pe_paths E ->
      pe_files E p = Some content ->
      (forall fd d, 0 <= fd -> pe_fd E !! fd = None -> env_fresh E d ->
         conforms (env_set_dev (env_bind E fd d) d (DIn content)) (k fd)) ->
      conforms E (k (-1)) ->
      conforms E (Vis (EOpen p 0) k)
  | cf_open_absent E p m k :
      p ∈ pe_paths E -> ~ mode_create m ->
      pe_files E p = None ->
      conforms E (k (-1)) ->
      conforms E (Vis (EOpen p m) k)
  (* ...the last descriptor of a copy device or a haltable output only
     once the device is drained *)
  | cf_close E fd d k :
      pe_fd E !! fd = Some d ->
      (fd_last (pe_fd E) fd d -> drained_at_close (pe_dev E d)) ->
      conforms (env_unbind E fd) (k 0) ->
      conforms E (Vis (EClose fd) k)
  | cf_exit E s k :
      (forall d, drained (pe_dev E d)) ->
      conforms E (Vis (EExit s) k).

(* ...read at a node WITHOUT inverting a dependent pair: dependent
   elimination substitutes the node into the goal, which [cf_step] then
   computes *)
Lemma conforms_unfold (E : penv) (t : proc) : conforms E t -> cf_step conforms E t.
Proof.
  intros H. destruct H; simpl.
  - exact H.
  - exists d. split; [assumption |]. left. auto.
  - exists d. split; [assumption |]. right. left. split; [assumption |]. exists alts, a. auto.
  - exists d. split; [assumption |]. right. right. left. split; [assumption |]. exists alts, a. auto.
  - exists d. split; [assumption |]. right. right. right. left. split; [assumption |]. exists rest. auto.
  - exists d. split; [assumption |]. do 4 right. left. auto.
  - exists d. split; [assumption |]. do 5 right. left. split; [assumption |].
    split; [assumption |]. exists F, h, Rr, S, p. auto.
  - exists d. split; [assumption |]. do 6 right. left. split; [assumption |].
    split; [assumption |]. exists F, h, p. auto.
  - exists d. split; [assumption |]. do 7 right. left. do 3 (split; [assumption |]).
    exists oS. auto.
  - exists d. split; [assumption |]. do 8 right. left. split; [assumption |].
    split; [assumption |]. exists outs, xs, ds, a. auto.
  - exists d. split; [assumption |]. do 9 right. left. do 3 (split; [assumption |]).
    exists ds. auto.
  - exists d. split; [assumption |]. do 10 right. left. split; [assumption |].
    split; [assumption |]. exists outs, xs, ds, a. auto.
  - exists d. split; [assumption |]. do 11 right. left. split; [assumption |].
    split; [assumption |]. exists outs, xs, ds, a. auto.
  - exists d. split; [assumption |]. do 12 right. split; [assumption |].
    split; [assumption |]. exists ds, a. auto.
  - exists d. split; [assumption |]. split; [assumption |]. left. exists S. auto.
  - exists d. split; [assumption |]. split; [assumption |]. right. left. exists S. auto.
  - exists d. split; [assumption |]. split; [assumption |]. do 2 right. left. auto.
  - exists d. split; [assumption |]. split; [assumption |]. do 3 right. left.
    split; [assumption |]. exists F, h, Rr, S, p. auto.
  - exists d. split; [assumption |]. split; [assumption |]. do 4 right. left.
    split; [assumption |]. exists F, h, p. auto.
  - exists d. split; [assumption |]. split; [assumption |]. do 5 right. left.
    split; [assumption |]. exists S. auto.
  - exists d. split; [assumption |]. split; [assumption |]. do 6 right. auto.
  - split; [assumption |]. left. split; [reflexivity |]. exists content. auto.
  - split; [assumption |]. right. auto.
  - exists d. auto.
  - exact H.
Qed.

(* a descriptor's device in a literal environment *)
Ltac fdlk := first [ apply lookup_insert | apply lookup_singleton
                   | by rewrite lookup_insert_ne; [| lia]
                   | by simplify_map_eq ].

(* ---- echo conforms to a console owing its line -------------------- *)

Lemma env_set_dev_dev (E : penv) (d : nat) (x : dspec) :
  pe_dev (env_set_dev E d x) d = x.
Proof. unfold env_set_dev. simpl. by rewrite decide_True. Qed.
Lemma env_set_dev_fd (E : penv) (d : nat) (x : dspec) (fd : Z) :
  pe_fd (env_set_dev E d x) = pe_fd E.
Proof. reflexivity. Qed.
Lemma env_set_dev_set_dev (E : penv) (d : nat) (x y : dspec) :
  env_set_dev (env_set_dev E d x) d y = env_set_dev E d y.
Proof.
  unfold env_set_dev. simpl. f_equal. apply functional_extensionality.
  intros d'. destruct (decide (d' = d)); reflexivity.
Qed.

(* a run of one-byte writes on an alternative the device owes: what is
   owed after it is that alternative's rest, in any set that has it *)
Lemma write_bytes_conforms (E : penv) (fd : Z) (d : nat) (bs S' : bytes)
    (alts : list bytes) (rest : proc) :
  pe_fd E !! fd = Some d -> pe_dev E d = DOut alts -> bs ++ S' ∈ alts ->
  (forall alts', S' ∈ alts' -> conforms (env_set_dev E d (DOut alts')) rest) ->
  conforms E (write_bytes fd bs rest).
Proof.
  revert E alts. induction bs as [| b bs IH]; intros E alts Hfd Hd Hin Hrest.
  - simpl in Hin. simpl.
    specialize (Hrest alts Hin).
    assert (env_set_dev E d (DOut alts) = E) as Heq.
    { destruct E as [f g files paths]. unfold env_set_dev. simpl in *. f_equal.
      apply functional_extensionality. intros d'.
      destruct (decide (d' = d)) as [-> | ]; [by rewrite Hd | reflexivity]. }
    by rewrite Heq in Hrest.
  - simpl.
    eapply cf_write with (d := d) (alts := alts) (a := b :: bs ++ S');
      [done | exact Hfd | exact Hd | exact Hin | by exists (bs ++ S') |].
    simpl.
    apply (IH (env_set_dev E d (DOut [bs ++ S'])) [bs ++ S']).
    + exact Hfd.
    + apply env_set_dev_dev.
    + by left.
    + intros alts' Hin'. rewrite env_set_dev_set_dev. exact (Hrest alts' Hin').
Qed.

(* the console device is 0 and fd 1 names it *)
Definition cons_env (owed : bytes) (files : bytes -> option bytes) : penv :=
  MkEnv {[1 := 0%nat]}
        (fun d => if decide (d = 0%nat) then DOut [owed] else DOut [[]]) files [].

Lemma cons_env_set (owed owed' : bytes) (files : bytes -> option bytes) :
  env_set_dev (cons_env owed files) 0 (DOut [owed']) = cons_env owed' files.
Proof.
  unfold env_set_dev, cons_env. f_equal. apply functional_extensionality.
  intros d. simpl. destruct (decide (d = 0%nat)); reflexivity.
Qed.

(* one word on the console: a chunk of the owed line, or nothing if the
   word is empty (a zero-length write, answered 0 or -1, the tree going on
   either way) *)
Lemma echo_word_conforms (w S' : bytes) files (rest : proc) :
  conforms (cons_env S' files) rest ->
  conforms (cons_env (w ++ S') files) (Vis (EWrite 1 w) (fun _ => rest)).
Proof.
  intros Hrest. destruct w as [| b w].
  - apply cf_write_nil with (d := 0%nat); [fdlk | exact Hrest | exact Hrest].
  - eapply cf_write with (d := 0%nat) (alts := [(b :: w) ++ S']) (a := (b :: w) ++ S');
      [done | fdlk | done | by left | by eexists |].
    rewrite drop_app_length, cons_env_set. exact Hrest.
Qed.

Lemma echo_words_conforms (ws : list bytes) (files : bytes -> option bytes)
    (rest : proc) :
  ws <> [] ->
  conforms (cons_env [] files) rest ->
  conforms (cons_env (wl_line ws) files) (echo_words ws rest).
Proof.
  revert rest. induction ws as [| w r IH]; intros rest Hne Hrest; [done |].
  destruct r as [| w' r'].
  - simpl. unfold wl_line. simpl. rewrite app_nil_r.
    apply echo_word_conforms.
    change [wl_nl] with ([wl_nl] ++ []).
    apply echo_word_conforms. exact Hrest.
  - simpl. unfold wl_line. rewrite wl_body_cons, wl_tail_cons.
    rewrite <- app_assoc.
    apply echo_word_conforms.
    apply (echo_word_conforms [wl_sp] (wl_body (w' :: r') ++ [wl_nl])).
    apply IH; [done | exact Hrest].
Qed.

Theorem echo_conforms (argv : list bytes) (files : bytes -> option bytes) :
  drop 1 argv <> [] ->
  conforms (cons_env (wl_line (drop 1 argv)) files) (echo_tree argv).
Proof.
  intros Hne. unfold echo_tree. apply echo_words_conforms; [exact Hne |].
  apply cf_exit. intros d. unfold drained. cbn [pe_dev cons_env].
  destruct (decide (d = 0%nat)); by left.
Qed.

(* ---- cat conforms to copying its input to its output ---------------- *)

(* the console is device 0 on descriptors 1 and 2; an input device [din]
   on descriptor [fdin]; every other device owes nothing *)
Definition cat_env (fdin : Z) (din : nat) (S_in : bytes) (alts : list bytes)
    (files : bytes -> option bytes) (paths : list bytes) : penv :=
  MkEnv (<[1 := 0%nat]> (<[2 := 0%nat]> {[fdin := din]}))
        (fun d => if decide (d = 0%nat) then DOut alts
                  else if decide (d = din) then DIn S_in else DOut [[]]) files paths.

(* ...and before any file is open *)
Definition cat_env0 (alts : list bytes) (files : bytes -> option bytes)
    (paths : list bytes) : penv :=
  MkEnv (<[1 := 0%nat]> {[2 := 0%nat]})
        (fun d => if decide (d = 0%nat) then DOut alts else DOut [[]]) files paths.

Lemma cat_env_in (fdin : Z) (din : nat) (S S' : bytes) (alts : list bytes) files paths :
  din <> 0%nat ->
  env_set_dev (cat_env fdin din S alts files paths) din (DIn S') = cat_env fdin din S' alts files paths.
Proof.
  intros Hd. unfold env_set_dev, cat_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = din)) as [-> | ]; [| reflexivity].
  rewrite decide_False; [| exact Hd]. first [ by rewrite decide_True | done ].
Qed.
Lemma cat_env_out (fdin : Z) (din : nat) (S : bytes) (alts alts' : list bytes) files paths :
  env_set_dev (cat_env fdin din S alts files paths) 0 (DOut alts') = cat_env fdin din S alts' files paths.
Proof.
  unfold env_set_dev, cat_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.
Lemma cat_env_exit (fdin : Z) (din : nat) (S : bytes) (alts : list bytes) files paths (st : Z) :
  [] ∈ alts -> conforms (cat_env fdin din S alts files paths) (exit_ st).
Proof.
  intros Hin. apply cf_exit. intros d. unfold drained. cbn [pe_dev cat_env cat_env0].
  destruct (decide (d = 0%nat)); [exact Hin |].
  destruct (decide (d = din)); [exact I | by left].
Qed.
Lemma cat_env0_exit (alts : list bytes) files paths (st : Z) :
  [] ∈ alts -> conforms (cat_env0 alts files paths) (exit_ st).
Proof.
  intros Hin. apply cf_exit. intros d. unfold drained. cbn [pe_dev cat_env cat_env0].
  destruct (decide (d = 0%nat)); [exact Hin | by left].
Qed.
Lemma cat_env0_out (alts alts' : list bytes) files paths :
  env_set_dev (cat_env0 alts files paths) 0 (DOut alts') = cat_env0 alts' files paths.
Proof.
  unfold env_set_dev, cat_env0. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

(* one call of cat(fdin): what the console owes after it is what it owed
   after the input, in every alternative that had it *)
Lemma cat_loop_conforms (fdin : Z) (din : nat) (S : bytes) (alts : list bytes)
    files paths (rest : proc) :
  din <> 0%nat -> fdin <> 1 -> fdin <> 2 -> S ∈ alts ->
  (forall alts', [] ∈ alts' -> conforms (cat_env fdin din [] alts' files paths) rest) ->
  conforms (cat_env fdin din S alts files paths) (cat_loop fdin rest).
Proof.
  intros Hd Hf1 Hf2. revert S alts. cofix CIH. intros S alts Hin Hrest.
  rewrite cat_loop_unfold.
  eapply cf_read with (d := din) (S := S).
  { unfold cat_bufsz. lia. }
  { cbv [cat_env pe_fd]. rewrite lookup_insert_ne; [| lia].
    rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
  { cbv [cat_env pe_fd pe_dev]. rewrite decide_False; [| exact Hd]. first [ by rewrite decide_True | done ]. }
  intros c S' (HS & Hlen & Hnil). rewrite cat_env_in; [| exact Hd].
  destruct c as [| b c'].
  - assert (S = []) as -> by exact (Hnil eq_refl).
    simpl in HS. destruct S'; [| discriminate HS].
    exact (Hrest alts Hin).
  - rewrite HS in Hin.
    eapply cf_write with (d := 0%nat) (alts := alts) (a := (b :: c') ++ S').
    { done. }
    { cbv [cat_env cat_env0 pe_fd]. apply lookup_insert. }
    { cbv [cat_env pe_fd pe_dev]. by rewrite decide_True. }
    { exact Hin. }
    { by eexists. }
    rewrite drop_app_length, cat_env_out. cbv beta.
    rewrite decide_True; [| reflexivity].
    apply cf_tau. apply CIH; [by left | exact Hrest].
Qed.

Theorem cat_stdin_conforms (S : bytes) files paths :
  conforms (cat_env 0 1 S [S] files paths) (cat_tree [sb "cat"]).
Proof.
  simpl. apply cat_loop_conforms; [done | done | done | by left |].
  intros alts' Hin. apply cat_env_exit. exact Hin.
Qed.

(* ---- cat f: the console owes the content OR the diagnostic ---------- *)

Lemma cat_env0_open (alts : list bytes) files paths (fd : Z) (d : nat) (content : bytes) :
  pe_fd (cat_env0 alts files paths) !! fd = None -> env_fresh (cat_env0 alts files paths) d ->
  env_set_dev (env_bind (cat_env0 alts files paths) fd d) d (DIn content)
  = cat_env fd d content alts files paths.
Proof.
  intros Hfd Hfr. cbv [cat_env0 pe_fd] in Hfd.
  assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
  { split; intros ->; simplify_map_eq. }
  assert (d <> 0%nat) as Hd0.
  { intros ->. apply (Hfr 1). cbv [cat_env0 pe_fd]. apply lookup_insert. }
  cbv [env_set_dev env_bind cat_env0 cat_env pe_fd pe_dev pe_files pe_paths]. f_equal.
  - apply map_eq. intros k.
    destruct (decide (k = fd)) as [-> |]; [by simplify_map_eq |].
    destruct (decide (k = 1)) as [-> |]; [by simplify_map_eq |].
    destruct (decide (k = 2)) as [-> |]; by simplify_map_eq.
  - apply functional_extensionality. intros d'.
    destruct (decide (d' = d)) as [-> | Hne].
    + rewrite decide_False; [| exact Hd0]. first [ reflexivity | by rewrite decide_True ].
    + destruct (decide (d' = 0%nat)); [reflexivity |].
      first [ reflexivity | by rewrite decide_False ].
Qed.

Theorem cat_file_conforms (f content : bytes) files :
  files f = Some content ->
  conforms (cat_env0 [content; cat_dg_open f] files [f]) (cat_tree [sb "cat"; f]).
Proof.
  intros Hf. simpl.
  eapply cf_open_present; [by left | exact Hf | |].
  - intros fd d Hfd Hnone Hfr. rewrite cat_env0_open; [| exact Hnone | exact Hfr].
    rewrite decide_False; [| lia].
    assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
    { cbv [cat_env0 pe_fd] in Hnone. split; intros ->; simplify_map_eq. }
    assert (d <> 0%nat) as Hd0.
    { intros ->. apply (Hfr 1). cbv [cat_env0 pe_fd]. apply lookup_insert. }
    apply cat_loop_conforms; [exact Hd0 | exact Hf1 | exact Hf2 | by left |].
    intros alts' Hin.
    eapply cf_close with (d := d).
    { cbv [cat_env pe_fd]. rewrite lookup_insert_ne; [| lia].
      rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
    { (* an input: the close owes nothing *)
      intros _. cbv [cat_env pe_dev]. repeat case_decide; exact I. }
    simpl. apply cf_exit. intros d'. unfold drained. cbv [env_unbind cat_env pe_dev].
    destruct (decide (d' = 0%nat)); [exact Hin |].
    destruct (decide (d' = d)); [exact I | by left].
  - cbv beta. rewrite decide_True; [| lia].
    eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := [content; cat_dg_open f]).
    { cbv [cat_env cat_env0 pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
    { reflexivity. }
    { rewrite app_nil_r. by right; left. }
    intros alts' Hin. rewrite cat_env0_out. apply cat_env0_exit. exact Hin.
Qed.

Theorem cat_file_absent_conforms (f : bytes) files :
  files f = None ->
  conforms (cat_env0 [cat_dg_open f] files [f]) (cat_tree [sb "cat"; f]).
Proof.
  intros Hf. simpl.
  eapply cf_open_absent; [by left | unfold mode_create; vm_compute; intros H; exact (H eq_refl) | exact Hf |].
  cbv beta. rewrite decide_True; [| lia].
  eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := [cat_dg_open f]).
  { cbv [cat_env cat_env0 pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
  { reflexivity. }
  { rewrite app_nil_r. by left. }
  intros alts' Hin. rewrite cat_env0_out. apply cat_env0_exit. exact Hin.
Qed.

(* ---- echo at a device that may halt (a pipe's write end) ------------- *)

Definition pipe_env (spec : dspec) (files : bytes -> option bytes) : penv :=
  MkEnv {[1 := 0%nat]}
        (fun d => if decide (d = 0%nat) then spec else DOut [[]]) files [].

Lemma pipe_env_set (spec spec' : dspec) files :
  env_set_dev (pipe_env spec files) 0 spec' = pipe_env spec' files.
Proof.
  unfold env_set_dev, pipe_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

Lemma pipe_env_exit (spec : dspec) files (st : Z) :
  drained spec ->
  conforms (pipe_env spec files) (exit_ st).
Proof.
  intros Hs. apply cf_exit. intros d. cbn [pe_dev pipe_env].
  destruct (decide (d = 0%nat)); [exact Hs | by left].
Qed.

(* once halted, echo's remaining writes all answer -1 and it exits -- each
   of them under 2^31 bytes (the halted rule's C int, [cf_write_halt]);
   the separators are one byte *)
Lemma wlen_one (b : bv 8) : Z.of_nat (length [b]) < 2 ^ 31.
Proof. vm_compute. reflexivity. Qed.

(* every word of a line is no longer than its body *)
Lemma wl_words_le (ws : list bytes) :
  Forall (fun w => (length w <= length (wl_body ws))%nat) ws.
Proof.
  induction ws as [| w r IH]; constructor.
  - rewrite wl_body_cons, length_app. lia.
  - assert (Ht : (length (wl_body r) <= length (wl_tail r))%nat).
    { destruct r as [| w' r']; [simpl; lia |]. rewrite wl_tail_cons. simpl. lia. }
    eapply List.Forall_impl; [| exact IH]. intros x Hx. cbv beta in *.
    rewrite wl_body_cons, length_app. lia.
Qed.

Lemma wl_words_short (ws : list bytes) :
  Z.of_nat (length (wl_line ws)) < 2 ^ 31 ->
  Forall (fun w => Z.of_nat (length w) < 2 ^ 31) ws.
Proof.
  intros HL. rewrite wl_line_length in HL.
  eapply List.Forall_impl; [| exact (wl_words_le ws)]. intros w Hw. cbv beta in *.
  change (2 ^ 31) with 2147483648 in *. lia.
Qed.

(* one word at a halted device: -1 (or, empty, 0 or -1) and on it goes *)
Lemma echo_word_halted (w : bytes) files (rest : proc) :
  Z.of_nat (length w) < 2 ^ 31 ->
  conforms (pipe_env DHalt files) rest ->
  conforms (pipe_env DHalt files) (Vis (EWrite 1 w) (fun _ => rest)).
Proof.
  intros Hw Hrest. destruct w as [| b w].
  - apply cf_write_nil with (d := 0%nat); [fdlk | exact Hrest | exact Hrest].
  - eapply cf_write_halt with (d := 0%nat); [done | exact Hw | fdlk | done | exact Hrest].
Qed.

Lemma echo_words_halted (ws : list bytes) files (rest : proc) :
  Forall (fun w => Z.of_nat (length w) < 2 ^ 31) ws ->
  conforms (pipe_env DHalt files) rest ->
  conforms (pipe_env DHalt files) (echo_words ws rest).
Proof.
  revert rest. induction ws as [| w r IH]; intros rest Hb Hrest; [exact Hrest |].
  inversion Hb as [| ? ? Hw Hr]; subst.
  destruct r as [| w' r']; simpl.
  - apply echo_word_halted; [exact Hw |].
    apply echo_word_halted; [apply wlen_one | exact Hrest].
  - apply echo_word_halted; [exact Hw |].
    apply echo_word_halted; [apply wlen_one |].
    apply IH; [exact Hr | exact Hrest].
Qed.

(* one word at a haltable device: the chunk (then the rest), or the halt
   (then the rest, halted); empty: 0 or -1, nothing moves *)
Lemma echo_word_conforms_h (w S' : bytes) files (rest : proc) :
  conforms (pipe_env (DOutH [S']) files) rest ->
  conforms (pipe_env DHalt files) rest ->
  conforms (pipe_env (DOutH [w ++ S']) files) (Vis (EWrite 1 w) (fun _ => rest)).
Proof.
  intros Hrest Hhalt. destruct w as [| b w].
  - apply cf_write_nil with (d := 0%nat); [fdlk | exact Hrest | exact Hrest].
  - eapply cf_write_h with (d := 0%nat) (alts := [(b :: w) ++ S']) (a := (b :: w) ++ S');
      [done | fdlk | done | by left | by eexists | |].
    + rewrite drop_app_length, pipe_env_set. exact Hrest.
    + rewrite pipe_env_set. exact Hhalt.
Qed.

Lemma echo_words_conforms_h (ws : list bytes) files (rest : proc) :
  ws <> [] ->
  Forall (fun w => Z.of_nat (length w) < 2 ^ 31) ws ->
  conforms (pipe_env (DOutH [[]]) files) rest ->
  conforms (pipe_env DHalt files) rest ->
  conforms (pipe_env (DOutH [wl_line ws]) files) (echo_words ws rest).
Proof.
  revert rest. induction ws as [| w r IH]; intros rest Hne Hb Hrest Hhalt; [done |].
  inversion Hb as [| ? ? Hw Hr]; subst.
  destruct r as [| w' r'].
  - simpl. unfold wl_line. simpl. rewrite app_nil_r.
    apply echo_word_conforms_h.
    + change [wl_nl] with ([wl_nl] ++ []).
      apply echo_word_conforms_h; [exact Hrest | exact Hhalt].
    + apply echo_word_halted; [apply wlen_one | exact Hhalt].
  - simpl. unfold wl_line. rewrite wl_body_cons, wl_tail_cons.
    rewrite <- app_assoc.
    apply echo_word_conforms_h.
    + apply (echo_word_conforms_h [wl_sp] (wl_body (w' :: r') ++ [wl_nl])).
      * apply IH; [done | exact Hr | exact Hrest | exact Hhalt].
      * apply (echo_words_halted (w' :: r') files rest); [exact Hr | exact Hhalt].
    + apply echo_word_halted; [apply wlen_one |].
      apply (echo_words_halted (w' :: r') files rest); [exact Hr | exact Hhalt].
Qed.

(* the line under 2^31 bytes: what a pipe's write end owes always is
   ([UkPipeDev.pipe_out]), and what keeps every write after a halt a
   positive C int *)
Theorem echo_pipe_conforms (argv : list bytes) files :
  drop 1 argv <> [] ->
  Z.of_nat (length (wl_line (drop 1 argv))) < 2 ^ 31 ->
  conforms (pipe_env (DOutH [wl_line (drop 1 argv)]) files) (echo_tree argv).
Proof.
  intros Hne HL. unfold echo_tree.
  apply echo_words_conforms_h; [exact Hne | exact (wl_words_short _ HL) | |].
  - apply pipe_env_exit. by left.
  - apply pipe_env_exit. exact I.
Qed.

(* ---- cat at the copy device (design SS3.4f) --------------------------- *)

(* descriptors 0 and 1 name the copy device (device 1); descriptor 2 a
   console (device 0) owing [alts]; every other device owes nothing *)
Definition copy_env (spec : dspec) (alts : list bytes)
    (files : bytes -> option bytes) (paths : list bytes) : penv :=
  MkEnv (<[0 := 1%nat]> (<[1 := 1%nat]> {[2 := 0%nat]}))
        (fun d => if decide (d = 0%nat) then DOut alts
                  else if decide (d = 1%nat) then spec else DOut [[]]) files paths.

Lemma copy_env_set (spec spec' : dspec) (alts : list bytes) files paths :
  env_set_dev (copy_env spec alts files paths) 1 spec' = copy_env spec' alts files paths.
Proof.
  unfold env_set_dev, copy_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 1%nat)) as [-> | Hne].
  - rewrite decide_False; [| lia]. first [ by rewrite decide_True | done ].
  - destruct (decide (d = 0%nat)); [reflexivity |]. first [ reflexivity | by rewrite decide_False ].
Qed.
Lemma copy_env_out (spec : dspec) (alts alts' : list bytes) files paths :
  env_set_dev (copy_env spec alts files paths) 0 (DOut alts') = copy_env spec alts' files paths.
Proof.
  unfold env_set_dev, copy_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.
Lemma copy_env_exit (spec : dspec) (alts : list bytes) files paths (st : Z) :
  [] ∈ alts -> drained spec -> conforms (copy_env spec alts files paths) (exit_ st).
Proof.
  intros Hin Hdr. apply cf_exit. intros d. cbn [pe_dev copy_env].
  destruct (decide (d = 0%nat)); [exact Hin |].
  destruct (decide (d = 1%nat)); [exact Hdr | by left].
Qed.

(* one call of cat(0) at the filter device at [flt_id]: each chunk read
   is written whole before the next read, so [pending] is empty at every
   read and at the exit, whatever was read so far ([R]), whether the input
   ran out or the writer closed first; a halted sink ([h = true]) sends cat
   to its diagnostic on descriptor 2, which the console must then owe *)
Lemma cat_copy_loop_conforms (h : bool) (R S : bytes) (alts : list bytes) files paths (rest : proc) :
  [] ∈ alts -> (h = true -> cat_dg_write ∈ alts) ->
  conforms (copy_env (DCopyEnd flt_id h []) alts files paths) rest ->
  conforms (copy_env (DCopy flt_id h R S []) alts files paths) (cat_loop 0 rest).
Proof.
  intros Hnil Hdg Hrest_end. revert R S. cofix CIH. intros R S.
  rewrite cat_loop_unfold.
  eapply cf_read_copy with (d := 1%nat) (F := flt_id) (h := h) (Rr := R) (S := S) (p := []).
  { unfold cat_bufsz. lia. }
  { reflexivity. }
  { cbv [copy_env pe_fd]. apply lookup_insert. }
  { cbv [copy_env pe_fd pe_dev]. rewrite decide_False; [| lia]. first [ by rewrite decide_True | done ]. }
  2: { rewrite copy_env_set. exact Hrest_end. }
  intros c S' (HS & Hlen & Hnil') Hne. rewrite copy_env_set.
  destruct c as [| b c']; [by destruct Hne |].
  eapply cf_write_copy with (d := 1%nat) (F := flt_id) (h := h) (Rr := R ++ b :: c') (S := S') (p := b :: c').
  { done. }
  { reflexivity. }
  { cbv [copy_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_insert. }
  { cbv [copy_env pe_fd pe_dev]. rewrite decide_False; [| lia]. first [ by rewrite decide_True | done ]. }
  { by exists []; rewrite app_nil_r. }
  - rewrite drop_all, copy_env_set. cbv beta.
    rewrite decide_True; [| reflexivity].
    apply cf_tau. apply CIH.
  - intros Hh. rewrite copy_env_set. cbv beta.
    rewrite decide_False; [| lia].
    eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := alts).
    { cbv [copy_env pe_fd]. do 2 (rewrite lookup_insert_ne; [| lia]). apply lookup_singleton. }
    { cbv [copy_env pe_fd pe_dev]. by rewrite decide_True. }
    { rewrite app_nil_r. exact (Hdg Hh). }
    intros alts' Hin'. rewrite copy_env_out. apply copy_env_exit; [exact Hin' | exact I].
Qed.

(* cat with no argument at the filter device: [cat_stdin_conforms]
   re-proved at [DCopy flt_id h [] L []] (the pipeline's cat: pipe in,
   pipe or console out, nothing read yet); the console on descriptor 2
   owes nothing, and, when the sink may halt, the write diagnostic as an
   alternative *)
Theorem cat_copy_conforms (h : bool) (L : bytes) (alts : list bytes) files paths :
  [] ∈ alts -> (h = true -> cat_dg_write ∈ alts) ->
  conforms (copy_env (DCopy flt_id h [] L []) alts files paths) (cat_tree [sb "cat"]).
Proof.
  intros Hnil Hdg. simpl. apply cat_copy_loop_conforms; [exact Hnil | exact Hdg |].
  apply copy_env_exit; [exact Hnil | exact eq_refl].
Qed.

(* ===================================================================== *)
(*  9.  THE DESCRIPTOR DISCIPLINE UNDER ANY ANSWER                        *)
(*                                                                        *)
(*  What a payer at the TAINT needs of a tree: along EVERY path, whatever  *)
(*  the kernel answered, it closes only descriptors it holds and reads at  *)
(*  least one byte.  Conformance says this along the paths it covers; the  *)
(*  taint arm of a law continues at an answer conformance did not cover,   *)
(*  and the free handler there has exactly the process's handles and the   *)
(*  free leaves, which is what these two clauses are.                      *)
(* ===================================================================== *)

Definition sf_step (R : gset Z -> proc -> Prop) (held : gset Z) (t : proc) : Prop :=
  match t with
  | Ret v => match v with end
  | Tau t' => R held t'
  | Vis e k =>
      match e as e return (ans e -> proc) -> Prop with
      | EWrite fd bs => fun k => forall x, R held (k x)
      | ERead fd n => fun k => (0 < n)%nat /\ forall x, R held (k x)
      | EOpen p m => fun k =>
          (forall fd, 0 <= fd -> R ({[fd]} ∪ held) (k fd)) /\ R held (k (-1))
      | EClose fd => fun k => fd ∈ held /\ forall x, R (held ∖ {[fd]}) (k x)
      | EExit s => fun _ => True
      end k
  end.

CoInductive safe_fds : gset Z -> proc -> Prop :=
  | sf_tau held t : safe_fds held t -> safe_fds held (Tau t)
  | sf_write held fd bs k :
      (forall x, safe_fds held (k x)) -> safe_fds held (Vis (EWrite fd bs) k)
  | sf_read held fd n k :
      (0 < n)%nat -> (forall x, safe_fds held (k x)) -> safe_fds held (Vis (ERead fd n) k)
  | sf_open held p m k :
      (forall fd, 0 <= fd -> safe_fds ({[fd]} ∪ held) (k fd)) ->
      safe_fds held (k (-1)) ->
      safe_fds held (Vis (EOpen p m) k)
  | sf_close held fd k :
      fd ∈ held -> (forall x, safe_fds (held ∖ {[fd]}) (k x)) ->
      safe_fds held (Vis (EClose fd) k)
  | sf_exit held s k : safe_fds held (Vis (EExit s) k).

Lemma safe_fds_unfold (held : gset Z) (t : proc) :
  safe_fds held t -> sf_step safe_fds held t.
Proof. intros H. destruct H; simpl; auto. Qed.

(* echo only writes and exits *)
Lemma echo_words_safe (ws : list bytes) (rest : proc) (held : gset Z) :
  safe_fds held rest -> safe_fds held (echo_words ws rest).
Proof.
  revert rest. induction ws as [| w r IH]; intros rest Hrest; [exact Hrest |].
  destruct r as [| w' r']; simpl.
  - apply sf_write. intros _. apply sf_write. intros _. exact Hrest.
  - apply sf_write. intros _. apply sf_write. intros _. apply IH. exact Hrest.
Qed.

Theorem echo_tree_safe (argv : list bytes) (held : gset Z) :
  safe_fds held (echo_tree argv).
Proof. unfold echo_tree. apply echo_words_safe. apply sf_exit. Qed.

(* cat reads 512 bytes at a time, closes what it opened *)
Lemma write_bytes_safe (fd : Z) (bs : bytes) (rest : proc) (held : gset Z) :
  safe_fds held rest -> safe_fds held (write_bytes fd bs rest).
Proof.
  induction bs as [| b bs IH]; intros Hrest; [exact Hrest |].
  simpl. apply sf_write. intros _. apply IH. exact Hrest.
Qed.

Lemma cat_loop_safe (fd : Z) (rest : proc) (held : gset Z) :
  safe_fds held rest -> safe_fds held (cat_loop fd rest).
Proof.
  intros Hrest. revert fd rest held Hrest. cofix CIH. intros fd rest held Hrest.
  rewrite cat_loop_unfold. apply sf_read; [unfold cat_bufsz; lia |].
  intros [| bs].
  - apply (write_bytes_safe 2 cat_dg_read (exit_ 1)). apply sf_exit.
  - destruct bs as [| b bs]; [exact Hrest |].
    apply sf_write. intros r. destruct (decide (r = Z.of_nat (length (b :: bs)))).
    + apply sf_tau. exact (CIH fd rest held Hrest).
    + apply (write_bytes_safe 2 cat_dg_write (exit_ 1)). apply sf_exit.
Qed.

Lemma cat_files_safe (paths : list bytes) (held : gset Z) :
  safe_fds held (cat_files paths (exit_ 0)).
Proof.
  revert held. induction paths as [| p r IH]; intros held; simpl; [apply sf_exit |].
  apply sf_open.
  - intros fd Hfd. rewrite decide_False; [| lia].
    apply cat_loop_safe. apply sf_close; [set_solver |]. intros _. apply IH.
  - rewrite decide_True; [| lia]. apply (write_bytes_safe 2 (cat_dg_open p) (exit_ 1)). apply sf_exit.
Qed.

Theorem cat_tree_safe (argv : list bytes) (held : gset Z) :
  safe_fds held (cat_tree argv).
Proof.
  unfold cat_tree. destruct (drop 1 argv) as [| p r].
  - apply cat_loop_safe. apply sf_exit.
  - apply cat_files_safe.
Qed.
