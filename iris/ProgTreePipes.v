(* ===================================================================== *)
(* ProgTreePipes.v -- PIPELINES OF ANY LENGTH over the trees of           *)
(* [ProgTree] (design: claude-notes/design/pipes-general.md SS3.1, cut    *)
(* C1).  Pure and additive; nothing imports it yet.                       *)
(*                                                                        *)
(*   1. [line_pipes]: the left-first chain of n processes joined by n-1   *)
(*      pipes, generalising [ProgTree.line_pipe] (which is its n = 2       *)
(*      instance, [line_pipes_two]), and the demos of the three-, four-   *)
(*      stage lines and of [cat f] as the producer.                       *)
(*   2. [cat_file_pipe_conforms]: [cat f] with its standard output at a   *)
(*      pipe's write end ([DOutH]) and its standard error at the console, *)
(*      the twin of [ProgTree.cat_file_conforms] -- the producer [cat f]  *)
(*      of a pipeline.                                                    *)
(*   3. [reach_exit E t E']: the environments at an exit along a          *)
(*      conforming path, and the three programs' EXIT LEMMAS -- what a    *)
(*      stage's devices look like when it exits, which is what the        *)
(*      per-stage outcome model reads off the trees.                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String FunctionalExtensionality.
From stdpp Require Import list gmap bitvector.definitions.
Require Import StringBytes LineWords ProgTree.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE CHAIN OF n PROCESSES                                          *)
(* ===================================================================== *)

(* a stage's descriptor table before its output is bound: the console on
   0, 1, 2, or the previous pipe's read end on 0 *)
Definition in_tab (inp : option nat) : fdt :=
  match inp with
  | None => std_console
  | Some j => assoc_set std_console 0 (EpPipeR j)
  end.

(* stage [i] of the chain reads [inp]; every stage but the last writes
   pipe [i], made just before it runs; the stages run LEFT FIRST, each to
   its exit (so each writer has closed its end before its reader reads: a
   valid schedule whenever every stage's output fits a pipe, as in
   [line_pipe]).  The outcome is the last stage's. *)
Fixpoint pipes_go (w : world) (i : nat) (inp : option nat) (ps : list proc)
    : world * outcome :=
  match ps with
  | [] => (w, Exited 0)          (* no stage: nothing runs *)
  | [p] => run fuel w (in_tab inp) p
  | p :: ps' =>
      let w0 := pipe_set w i (MkPipe [] true) in
      let '(w1, _) := run fuel w0 (assoc_set (in_tab inp) 1 (EpPipeW i)) p in
      pipes_go w1 (S i) (Some i) ps'
  end.

(* `p0 | p1 | ... | pn`: pipe ids 0 .. n-1 *)
Definition line_pipes (w : world) (ps : list proc) : world * outcome :=
  pipes_go w 0 None ps.

Lemma line_pipes_one (w : world) (p : proc) :
  line_pipes w [p] = line_plain w p.
Proof using. unfold line_pipes, line_plain. cbn [pipes_go in_tab]. reflexivity. Qed.

Lemma line_pipes_two (w : world) (l r : proc) :
  line_pipes w [l; r] = line_pipe w l r.
Proof using. unfold line_pipes, line_pipe. cbn [pipes_go in_tab]. reflexivity. Qed.

(* ---- demos --------------------------------------------------------- *)

Definition cat0 : proc := cat_tree (argv_cat []).

(* echo foo | cat | cat *)
Example demo_echo_cat_cat :
  let '(w, o) := line_pipes w0 [echo_tree (argv_echo ["foo"]); cat0; cat0] in
  w_cons w = sb "foo" ++ [wl_nl] /\ o = Exited 0.
Proof using. vm_compute. split; reflexivity. Qed.

(* echo foo bar | cat | cat | cat *)
Example demo_echo_cat3 :
  let '(w, o) := line_pipes w0 [echo_tree (argv_echo ["foo"; "bar"]); cat0; cat0; cat0] in
  w_cons w = sb "foo bar" ++ [wl_nl] /\ o = Exited 0.
Proof using. vm_compute. split; reflexivity. Qed.

(* cat f | cat, at the world where f holds the line *)
Example demo_catf_cat :
  let '(w, o) := line_pipes after_redirect [cat_tree (argv_cat ["f"]); cat0] in
  w_cons w = sb "foo bar" ++ [wl_nl] /\ o = Exited 0.
Proof using. vm_compute. split; reflexivity. Qed.

(* cat f | cat | cat *)
Example demo_catf_cat_cat :
  let '(w, o) := line_pipes after_redirect [cat_tree (argv_cat ["f"]); cat0; cat0] in
  w_cons w = sb "foo bar" ++ [wl_nl] /\ o = Exited 0.
Proof using. vm_compute. split; reflexivity. Qed.

(* chunking through three stages: 700 bytes, two reads and two writes at
   every cat *)
Example demo_catlong_cat_cat :
  (line_pipes w_long [cat_tree (argv_cat ["big"]); cat0; cat0]).1.(w_cons) = long_content.
Proof using. vm_compute. reflexivity. Qed.

(* the chain agrees with the two-process line it generalises *)
Example demo_pipes_is_pipe :
  line_pipes after_redirect [cat_tree (argv_cat ["f"]); cat0]
  = line_pipe after_redirect (cat_tree (argv_cat ["f"])) cat0.
Proof using. vm_compute. reflexivity. Qed.

(* NEGATIVE: cat nope | cat -- the producer's diagnostic reaches the
   console on its fd 2, nothing crosses the pipe, the last cat reads end
   of file and exits 0 *)
Example demo_neg_pipes :
  let '(w, o) := line_pipes after_redirect [cat_tree (argv_cat ["nope"]); cat0] in
  w_cons w = sb "cat: cannot open nope" ++ [wl_nl] /\ o = Exited 0.
Proof using. vm_compute. split; reflexivity. Qed.

(* ...and the chain is not blind to its producer *)
Example demo_neg_pipes_ne :
  (line_pipes w0 [echo_tree (argv_echo ["foo"]); cat0; cat0]).1.(w_cons)
  <> (line_pipes w0 [echo_tree (argv_echo ["bar"]); cat0; cat0]).1.(w_cons).
Proof using. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  2.  cat f AT A PIPE'S WRITE END                                       *)
(*                                                                        *)
(*  The producer [cat f] of a pipeline: descriptor 1 names the pipe's      *)
(*  write end (device 1, a haltable output), descriptor 2 the console      *)
(*  (device 0).  Unlike [ProgTree.cat_env0] the two are DIFFERENT devices. *)
(* ===================================================================== *)

Definition catf_env (out : dspec) (alts : list bytes) (files : bytes -> option bytes)
    (paths : list bytes) : penv :=
  MkEnv (<[1 := 1%nat]> {[2 := 0%nat]})
        (fun d => if decide (d = 0%nat) then DOut alts
                  else if decide (d = 1%nat) then out else DOut [[]]) files paths.

(* ...once f is open on [fdin], at input device [din] *)
Definition catf_loop_env (fdin : Z) (din : nat) (S : bytes) (out : dspec) (alts : list bytes)
    (files : bytes -> option bytes) (paths : list bytes) : penv :=
  MkEnv (<[1 := 1%nat]> (<[2 := 0%nat]> {[fdin := din]}))
        (fun d => if decide (d = 0%nat) then DOut alts
                  else if decide (d = 1%nat) then out
                  else if decide (d = din) then DIn S else DOut [[]]) files paths.

Lemma catf_env_cons (out : dspec) (alts alts' : list bytes) files paths :
  env_set_dev (catf_env out alts files paths) 0 (DOut alts') = catf_env out alts' files paths.
Proof using.
  unfold env_set_dev, catf_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

Lemma catf_loop_env_cons fdin din S (out : dspec) (alts alts' : list bytes) files paths :
  env_set_dev (catf_loop_env fdin din S out alts files paths) 0 (DOut alts')
  = catf_loop_env fdin din S out alts' files paths.
Proof using.
  unfold env_set_dev, catf_loop_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

Lemma catf_loop_env_out1 fdin din S (out out' : dspec) (alts : list bytes) files paths :
  env_set_dev (catf_loop_env fdin din S out alts files paths) 1 out'
  = catf_loop_env fdin din S out' alts files paths.
Proof using.
  unfold env_set_dev, catf_loop_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 1%nat)) as [-> | Hne].
  - rewrite decide_False; [| lia]. first [ by rewrite decide_True | done ].
  - destruct (decide (d = 0%nat)); [reflexivity |]. first [ reflexivity | by rewrite decide_False ].
Qed.

Lemma catf_loop_env_in fdin din S S' (out : dspec) (alts : list bytes) files paths :
  din <> 0%nat -> din <> 1%nat ->
  env_set_dev (catf_loop_env fdin din S out alts files paths) din (DIn S')
  = catf_loop_env fdin din S' out alts files paths.
Proof using.
  intros H0 H1. unfold env_set_dev, catf_loop_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = din)) as [-> | Hne].
  - rewrite decide_False; [| exact H0]. rewrite decide_False; [| exact H1].
    first [ by rewrite decide_True | done ].
  - destruct (decide (d = 0%nat)); [reflexivity |].
    destruct (decide (d = 1%nat)); [reflexivity |].
    first [ reflexivity | by rewrite decide_False ].
Qed.

Lemma catf_loop_env_din fdin din S (out : dspec) (alts : list bytes) files paths :
  din <> 0%nat -> din <> 1%nat ->
  pe_dev (catf_loop_env fdin din S out alts files paths) din = DIn S.
Proof using.
  intros H0 H1. cbv [catf_loop_env pe_dev]. rewrite decide_False; [| exact H0].
  rewrite decide_False; [| exact H1]. first [ by rewrite decide_True | done ].
Qed.

Lemma catf_loop_env_fdin fdin din S (out : dspec) (alts : list bytes) files paths :
  fdin <> 1 -> fdin <> 2 ->
  pe_fd (catf_loop_env fdin din S out alts files paths) !! fdin = Some din.
Proof using.
  intros H1 H2. cbv [catf_loop_env pe_fd]. rewrite lookup_insert_ne; [| lia].
  rewrite lookup_insert_ne; [| lia]. apply lookup_singleton.
Qed.

(* the open of f: a descriptor the process did not hold, at a device no
   descriptor names *)
Lemma catf_env_open (out : dspec) (alts : list bytes) files paths (fd : Z) (d : nat) (content : bytes) :
  pe_fd (catf_env out alts files paths) !! fd = None -> env_fresh (catf_env out alts files paths) d ->
  env_set_dev (env_bind (catf_env out alts files paths) fd d) d (DIn content)
  = catf_loop_env fd d content out alts files paths.
Proof using.
  intros Hfd Hfr. cbv [catf_env pe_fd] in Hfd.
  assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
  { split; intros ->; simplify_map_eq. }
  assert (d <> 0%nat) as Hd0.
  { intros ->. apply (Hfr 2). cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia].
    apply lookup_singleton. }
  assert (d <> 1%nat) as Hd1.
  { intros ->. apply (Hfr 1). cbv [catf_env pe_fd]. apply lookup_insert. }
  cbv [env_set_dev env_bind catf_env catf_loop_env pe_fd pe_dev pe_files pe_paths]. f_equal.
  - apply map_eq. intros k.
    destruct (decide (k = fd)) as [-> |]; [by simplify_map_eq |].
    destruct (decide (k = 1)) as [-> |]; [by simplify_map_eq |].
    destruct (decide (k = 2)) as [-> |]; by simplify_map_eq.
  - apply functional_extensionality. intros d'.
    destruct (decide (d' = d)) as [-> | Hne].
    + rewrite decide_False; [| exact Hd0]. rewrite decide_False; [| exact Hd1].
      first [ reflexivity | by rewrite decide_True ].
    + destruct (decide (d' = 0%nat)); [reflexivity |].
      destruct (decide (d' = 1%nat)); [reflexivity |].
      first [ reflexivity | by rewrite decide_False ].
Qed.

(* one call of cat(fdin) with the output at the pipe: each chunk read is
   owed next on the pipe; a halted pipe sends cat to its write diagnostic
   on the console *)
Lemma catf_loop_conforms (fdin : Z) (din : nat) (S : bytes) (outs alts : list bytes)
    files paths (rest : proc) :
  din <> 0%nat -> din <> 1%nat -> fdin <> 1 -> fdin <> 2 ->
  cat_dg_write ∈ alts -> S ∈ outs ->
  (forall outs', [] ∈ outs' -> conforms (catf_loop_env fdin din [] (DOutH outs') alts files paths) rest) ->
  conforms (catf_loop_env fdin din S (DOutH outs) alts files paths) (cat_loop fdin rest).
Proof using.
  intros Hd0 Hd1 Hf1 Hf2 Hdg. revert S outs. cofix CIH. intros S outs Hin Hrest.
  rewrite cat_loop_unfold.
  eapply cf_read with (d := din) (S := S).
  { unfold cat_bufsz. lia. }
  { apply catf_loop_env_fdin; assumption. }
  { apply catf_loop_env_din; assumption. }
  intros c S' (HS & Hlen & Hnil). rewrite catf_loop_env_in; [| exact Hd0 | exact Hd1].
  destruct c as [| b c'].
  - assert (S = []) as -> by exact (Hnil eq_refl).
    simpl in HS. destruct S'; [| discriminate HS].
    exact (Hrest outs Hin).
  - rewrite HS in Hin.
    eapply cf_write_h with (d := 1%nat) (alts := outs) (a := (b :: c') ++ S').
    { done. }
    { cbv [catf_loop_env pe_fd]. apply lookup_insert. }
    { cbv [catf_loop_env pe_fd pe_dev]. rewrite decide_False; [| lia].
      first [ by rewrite decide_True | done ]. }
    { exact Hin. }
    { by eexists. }
    + rewrite drop_app_length, catf_loop_env_out1. cbv beta.
      rewrite decide_True; [| reflexivity].
      apply cf_tau. apply CIH; [by left | exact Hrest].
    + rewrite catf_loop_env_out1. cbv beta.
      rewrite decide_False; [| lia].
      eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := alts).
      { cbv [catf_loop_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_insert. }
      { cbv [catf_loop_env pe_fd pe_dev]. by rewrite decide_True. }
      { rewrite app_nil_r. exact Hdg. }
      intros alts' Hin'. rewrite catf_loop_env_cons. apply cf_exit. intros d.
      cbn [pe_dev catf_loop_env].
      destruct (decide (d = 0%nat)); [exact Hin' |].
      destruct (decide (d = 1%nat)); [exact I |].
      destruct (decide (d = din)); [exact I | by left].
Qed.

(* THE GENERAL FORM: the pipe owes the content or nothing (the kernel may
   refuse the open of a present file: then nothing crosses the pipe), the
   console nothing, the open diagnostic or the write diagnostic *)
Theorem cat_file_pipe_conforms_gen (f c : bytes) (outs alts : list bytes) files :
  files f = Some c -> c ∈ outs -> [] ∈ outs ->
  [] ∈ alts -> cat_dg_open f ∈ alts -> cat_dg_write ∈ alts ->
  conforms (catf_env (DOutH outs) alts files [f]) (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf Hc Hon Han Hao Haw. simpl.
  eapply cf_open_present; [by left | exact Hf | |].
  - intros fd d Hfd Hnone Hfr. rewrite catf_env_open; [| exact Hnone | exact Hfr].
    rewrite decide_False; [| lia].
    assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
    { cbv [catf_env pe_fd] in Hnone. split; intros ->; simplify_map_eq. }
    assert (d <> 0%nat) as Hd0.
    { intros ->. apply (Hfr 2). cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia].
      apply lookup_singleton. }
    assert (d <> 1%nat) as Hd1.
    { intros ->. apply (Hfr 1). cbv [catf_env pe_fd]. apply lookup_insert. }
    apply catf_loop_conforms; [exact Hd0 | exact Hd1 | exact Hf1 | exact Hf2 | exact Haw | exact Hc |].
    intros outs' Hin.
    eapply cf_close with (d := d).
    { apply catf_loop_env_fdin; assumption. }
    { (* an input: the close owes nothing *)
      intros _. rewrite catf_loop_env_din; [exact I | exact Hd0 | exact Hd1]. }
    simpl. apply cf_exit. intros d'. cbv [env_unbind catf_loop_env pe_dev].
    destruct (decide (d' = 0%nat)); [exact Han |].
    destruct (decide (d' = 1%nat)); [exact Hin |].
    destruct (decide (d' = d)); [exact I | by left].
  - cbv beta. rewrite decide_True; [| lia].
    eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := alts).
    { cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
    { reflexivity. }
    { rewrite app_nil_r. exact Hao. }
    intros alts' Hin. rewrite catf_env_cons. apply cf_exit. intros d.
    cbn [pe_dev catf_env].
    destruct (decide (d = 0%nat)); [exact Hin |].
    destruct (decide (d = 1%nat)); [exact Hon | by left].
Qed.

(* the DOutH twin of [cat_file_conforms]: the pipe owes the content (or,
   the open refused, nothing), the console nothing or one of cat's two
   diagnostics *)
Theorem cat_file_pipe_conforms (f c : bytes) files :
  files f = Some c ->
  conforms (catf_env (DOutH [c; []]) [[]; cat_dg_open f; cat_dg_write] files [f])
           (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf. apply cat_file_pipe_conforms_gen with (c := c);
    [exact Hf | by left | by right; left | by left | by right; left | by right; right; left].
Qed.

Theorem cat_file_pipe_absent_conforms_gen (f : bytes) (outs alts : list bytes) files :
  files f = None -> [] ∈ outs -> cat_dg_open f ∈ alts ->
  conforms (catf_env (DOutH outs) alts files [f]) (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf Hon Hao. simpl.
  eapply cf_open_absent; [by left | unfold mode_create; vm_compute; intros H; exact (H eq_refl) | exact Hf |].
  cbv beta. rewrite decide_True; [| lia].
  eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := alts).
  { cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
  { reflexivity. }
  { rewrite app_nil_r. exact Hao. }
  intros alts' Hin. rewrite catf_env_cons. apply cf_exit. intros d.
  cbn [pe_dev catf_env].
  destruct (decide (d = 0%nat)); [exact Hin |].
  destruct (decide (d = 1%nat)); [exact Hon | by left].
Qed.

(* ...at the same console as the present file's *)
Theorem cat_file_pipe_absent_conforms (f : bytes) files :
  files f = None ->
  conforms (catf_env (DOutH [[]]) [[]; cat_dg_open f; cat_dg_write] files [f])
           (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf. apply cat_file_pipe_absent_conforms_gen; [exact Hf | by left | by right; left].
Qed.

(* ===================================================================== *)
(*  2b.  cat f AT THE PRODUCER DEVICE (union.md C9d')                     *)
(*                                                                        *)
(*  The same [cat f] with descriptors 1 AND 2 on ONE device, the          *)
(*  producer device [DProd outs xs ds]: the pipe owes one of [outs], the  *)
(*  console one of [ds] or -- nothing on the pipe yet -- the failure      *)
(*  report [cat: cannot open f] of [xs].  What the pairing buys the       *)
(*  instance: the report's first byte is where the round's deposit is     *)
(*  paid, out of the pipe's untouched write permit, and after it the      *)
(*  pipe owes nothing; the first byte on the pipe retires the report.     *)
(* ===================================================================== *)

Definition catp_env (x : dspec) (files : bytes -> option bytes) (paths : list bytes) : penv :=
  MkEnv (<[1 := 0%nat]> {[2 := 0%nat]})
        (fun d => if decide (d = 0%nat) then x else DOut [[]]) files paths.

(* ...once f is open on [fdin], at input device [din] *)
Definition catp_loop_env (fdin : Z) (din : nat) (S : bytes) (x : dspec)
    (files : bytes -> option bytes) (paths : list bytes) : penv :=
  MkEnv (<[1 := 0%nat]> (<[2 := 0%nat]> {[fdin := din]}))
        (fun d => if decide (d = 0%nat) then x
                  else if decide (d = din) then DIn S else DOut [[]]) files paths.

Lemma catp_env_set (x x' : dspec) files paths :
  env_set_dev (catp_env x files paths) 0 x' = catp_env x' files paths.
Proof using.
  unfold env_set_dev, catp_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

Lemma catp_loop_env_set fdin din S (x x' : dspec) files paths :
  env_set_dev (catp_loop_env fdin din S x files paths) 0 x'
  = catp_loop_env fdin din S x' files paths.
Proof using.
  unfold env_set_dev, catp_loop_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = 0%nat)); reflexivity.
Qed.

Lemma catp_loop_env_in fdin din S S' (x : dspec) files paths :
  din <> 0%nat ->
  env_set_dev (catp_loop_env fdin din S x files paths) din (DIn S')
  = catp_loop_env fdin din S' x files paths.
Proof using.
  intros H0. unfold env_set_dev, catp_loop_env. f_equal. apply functional_extensionality.
  intros d. cbn [pe_dev pe_fd]. destruct (decide (d = din)) as [-> | Hne].
  - rewrite decide_False; [| exact H0]. first [ by rewrite decide_True | done ].
  - destruct (decide (d = 0%nat)); [reflexivity |].
    first [ reflexivity | by rewrite decide_False ].
Qed.

Lemma catp_loop_env_din fdin din S (x : dspec) files paths :
  din <> 0%nat -> pe_dev (catp_loop_env fdin din S x files paths) din = DIn S.
Proof using.
  intros H0. cbv [catp_loop_env pe_dev]. rewrite decide_False; [| exact H0].
  first [ by rewrite decide_True | done ].
Qed.

Lemma catp_loop_env_fdin fdin din S (x : dspec) files paths :
  fdin <> 1 -> fdin <> 2 ->
  pe_fd (catp_loop_env fdin din S x files paths) !! fdin = Some din.
Proof using.
  intros H1 H2. cbv [catp_loop_env pe_fd]. rewrite lookup_insert_ne; [| lia].
  rewrite lookup_insert_ne; [| lia]. apply lookup_singleton.
Qed.

Lemma catp_loop_env_fd1 fdin din S (x : dspec) files paths :
  pe_fd (catp_loop_env fdin din S x files paths) !! prod_out = Some 0%nat.
Proof using. cbv [catp_loop_env pe_fd prod_out]. apply lookup_insert. Qed.

Lemma catp_loop_env_fd2 fdin din S (x : dspec) files paths :
  pe_fd (catp_loop_env fdin din S x files paths) !! prod_err = Some 0%nat.
Proof using.
  cbv [catp_loop_env pe_fd prod_err]. rewrite lookup_insert_ne; [| lia]. apply lookup_insert.
Qed.

Lemma catp_env_fd2 (x : dspec) files paths :
  pe_fd (catp_env x files paths) !! prod_err = Some 0%nat.
Proof using.
  cbv [catp_env pe_fd prod_err]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton.
Qed.

(* the open of f: a descriptor the process did not hold, at a device no
   descriptor names *)
Lemma catp_env_open (x : dspec) files paths (fd : Z) (d : nat) (content : bytes) :
  pe_fd (catp_env x files paths) !! fd = None -> env_fresh (catp_env x files paths) d ->
  env_set_dev (env_bind (catp_env x files paths) fd d) d (DIn content)
  = catp_loop_env fd d content x files paths.
Proof using.
  intros Hfd Hfr. cbv [catp_env pe_fd] in Hfd.
  assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
  { split; intros ->; simplify_map_eq. }
  assert (d <> 0%nat) as Hd0.
  { intros ->. apply (Hfr 1). cbv [catp_env pe_fd]. apply lookup_insert. }
  cbv [env_set_dev env_bind catp_env catp_loop_env pe_fd pe_dev pe_files pe_paths]. f_equal.
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

(* setting a device to what it already is changes nothing *)
Lemma catp_set_dev_id (E : penv) (d : nat) (x : dspec) :
  pe_dev E d = x -> env_set_dev E d x = E.
Proof using.
  intros Hd. destruct E as [f g files paths]. unfold env_set_dev. simpl in *. f_equal.
  apply functional_extensionality. intros d'.
  destruct (decide (d' = d)) as [-> |]; [by rewrite Hd | reflexivity].
Qed.

Lemma catp_dg_open_ne (p : bytes) : cat_dg_open p <> [].
Proof using.
  unfold cat_dg_open. intros H. apply app_eq_nil in H as [_ H].
  apply app_eq_nil in H as [_ H]. discriminate H.
Qed.

(* a run of one-byte diagnostic writes on a diagnostic the device owes:
   the reports are retired at the first byte *)
Lemma write_bytes_prod_conforms (E : penv) (d : nat) (bs S' : bytes)
    (outs xs ds : list bytes) (rest : proc) :
  pe_fd E !! prod_err = Some d -> pe_dev E d = DProd outs xs ds -> bs ++ S' ∈ ds ->
  (forall xs' ds', S' ∈ ds' -> conforms (env_set_dev E d (DProd outs xs' ds')) rest) ->
  conforms E (write_bytes prod_err bs rest).
Proof using.
  revert E xs ds. induction bs as [| b bs IH]; intros E xs ds Hfd Hd Hin Hrest.
  - simpl in Hin. simpl.
    specialize (Hrest xs ds Hin). by rewrite (catp_set_dev_id E d _ Hd) in Hrest.
  - simpl.
    eapply cf_write_prod_err with (d := d) (outs := outs) (xs := xs) (ds := ds)
      (a := b :: bs ++ S');
      [done | reflexivity | exact Hfd | exact Hd | exact Hin | by exists (bs ++ S') |].
    simpl.
    apply (IH (env_set_dev E d (DProd outs [] [bs ++ S'])) [] [bs ++ S']).
    + exact Hfd.
    + apply env_set_dev_dev.
    + by left.
    + intros xs' ds' Hin'. rewrite env_set_dev_set_dev. exact (Hrest xs' ds' Hin').
Qed.

(* ...a FAILURE REPORT: the first byte chooses it, the output then owes
   nothing *)
Lemma write_bytes_prod_fail_conforms (E : penv) (d : nat) (bs0 S' : bytes)
    (outs xs ds : list bytes) (rest : proc) :
  pe_fd E !! prod_err = Some d -> pe_dev E d = DProd outs xs ds ->
  bs0 <> [] -> [] ∈ outs -> bs0 ++ S' ∈ xs ->
  (forall xs' ds', S' ∈ ds' -> conforms (env_set_dev E d (DProd [[]] xs' ds')) rest) ->
  conforms E (write_bytes prod_err bs0 rest).
Proof using.
  intros Hfd Hd Hne Hon Hin Hrest.
  destruct bs0 as [| b bs]; [done |]. simpl.
  eapply cf_write_prod_fail with (d := d) (outs := outs) (xs := xs) (ds := ds)
    (a := b :: bs ++ S');
    [done | reflexivity | exact Hfd | exact Hd | exact Hon | exact Hin
    | by exists (bs ++ S') |].
  simpl.
  apply (write_bytes_prod_conforms (env_set_dev E d (DProd [[]] [] [bs ++ S'])) d bs S'
           [[]] [] [bs ++ S']).
  - exact Hfd.
  - apply env_set_dev_dev.
  - by left.
  - intros xs' ds' Hin'. rewrite env_set_dev_set_dev. exact (Hrest xs' ds' Hin').
Qed.

(* ...a diagnostic at the halted device *)
Lemma write_bytes_prodh_conforms (E : penv) (d : nat) (bs S' : bytes) (ds : list bytes)
    (rest : proc) :
  pe_fd E !! prod_err = Some d -> pe_dev E d = DProdHalt ds -> bs ++ S' ∈ ds ->
  (forall ds', S' ∈ ds' -> conforms (env_set_dev E d (DProdHalt ds')) rest) ->
  conforms E (write_bytes prod_err bs rest).
Proof using.
  revert E ds. induction bs as [| b bs IH]; intros E ds Hfd Hd Hin Hrest.
  - simpl in Hin. simpl.
    specialize (Hrest ds Hin). by rewrite (catp_set_dev_id E d _ Hd) in Hrest.
  - simpl.
    eapply cf_write_prod_halt_err with (d := d) (ds := ds) (a := b :: bs ++ S');
      [done | reflexivity | exact Hfd | exact Hd | exact Hin | by exists (bs ++ S') |].
    simpl.
    apply (IH (env_set_dev E d (DProdHalt [bs ++ S'])) [bs ++ S']).
    + exact Hfd.
    + apply env_set_dev_dev.
    + by left.
    + intros ds' Hin'. rewrite env_set_dev_set_dev. exact (Hrest ds' Hin').
Qed.

(* one call of cat(fdin) with the output at the producer device *)
Lemma catp_loop_conforms (fdin : Z) (din : nat) (S : bytes) (outs xs ds : list bytes)
    files paths (rest : proc) :
  din <> 0%nat -> fdin <> 1 -> fdin <> 2 ->
  cat_dg_write ∈ ds -> [] ∈ ds -> S ∈ outs ->
  (forall outs' xs', [] ∈ outs' ->
     conforms (catp_loop_env fdin din [] (DProd outs' xs' ds) files paths) rest) ->
  conforms (catp_loop_env fdin din S (DProd outs xs ds) files paths) (cat_loop fdin rest).
Proof using.
  intros Hd0 Hf1 Hf2 Hdg Hnil. revert S outs xs. cofix CIH. intros S outs xs Hin Hrest.
  rewrite cat_loop_unfold.
  eapply cf_read with (d := din) (S := S).
  { unfold cat_bufsz. lia. }
  { apply catp_loop_env_fdin; assumption. }
  { apply catp_loop_env_din; assumption. }
  intros c S' (HS & Hlen & Hnl). rewrite catp_loop_env_in; [| exact Hd0].
  destruct c as [| b c'].
  - assert (S = []) as -> by exact (Hnl eq_refl).
    simpl in HS. destruct S'; [| discriminate HS].
    exact (Hrest outs xs Hin).
  - rewrite HS in Hin.
    eapply cf_write_prod with (d := 0%nat) (outs := outs) (xs := xs) (ds := ds)
      (a := (b :: c') ++ S').
    { done. }
    { reflexivity. }
    { apply catp_loop_env_fd1. }
    { cbv [catp_loop_env pe_dev]. by rewrite decide_True. }
    { exact Hin. }
    { by eexists. }
    + rewrite drop_app_length, catp_loop_env_set. cbv beta.
      rewrite decide_True; [| reflexivity].
      apply cf_tau. apply CIH; [by left | exact Hrest].
    + rewrite catp_loop_env_set. cbv beta.
      rewrite decide_False; [| lia].
      apply (write_bytes_prodh_conforms _ 0%nat cat_dg_write [] ds);
        [apply catp_loop_env_fd2 | cbv [catp_loop_env pe_dev]; by rewrite decide_True
        | by rewrite app_nil_r |].
      intros ds' Hin'. rewrite catp_loop_env_set. apply cf_exit. intros d.
      cbn [pe_dev catp_loop_env].
      destruct (decide (d = 0%nat)); [exact Hin' |].
      destruct (decide (d = din)); [exact I | by left].
Qed.

(* THE GENERAL FORM: the output owes the content or nothing, the
   diagnostics nothing or the write error, or -- the open refused -- the
   open's report *)
Theorem cat_file_prod_conforms_gen (f c : bytes) (outs xs ds : list bytes) files :
  files f = Some c -> c ∈ outs -> [] ∈ outs -> cat_dg_open f ∈ xs ->
  [] ∈ ds -> cat_dg_write ∈ ds ->
  conforms (catp_env (DProd outs xs ds) files [f]) (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf Hc Hon Hao Hdn Hdw. simpl.
  eapply cf_open_present; [by left | exact Hf | |].
  - intros fd d Hfd Hnone Hfr. rewrite catp_env_open; [| exact Hnone | exact Hfr].
    rewrite decide_False; [| lia].
    assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
    { cbv [catp_env pe_fd] in Hnone. split; intros ->; simplify_map_eq. }
    assert (d <> 0%nat) as Hd0.
    { intros ->. apply (Hfr 1). cbv [catp_env pe_fd]. apply lookup_insert. }
    apply catp_loop_conforms; [exact Hd0 | exact Hf1 | exact Hf2 | exact Hdw | exact Hdn
                              | exact Hc |].
    intros outs' xs' Hin.
    eapply cf_close with (d := d).
    { apply catp_loop_env_fdin; assumption. }
    { (* an input: the close owes nothing *)
      intros _. rewrite catp_loop_env_din; [exact I | exact Hd0]. }
    simpl. apply cf_exit. intros d'. cbv [env_unbind catp_loop_env pe_dev].
    destruct (decide (d' = 0%nat)); [cbn [drained]; split; [exact Hin | exact Hdn] |].
    destruct (decide (d' = d)); [exact I | by left].
  - cbv beta. rewrite decide_True; [| lia].
    eapply (write_bytes_prod_fail_conforms _ 0%nat _ [] outs xs ds);
      [apply catp_env_fd2 | cbv [catp_env pe_dev]; by rewrite decide_True
      | apply catp_dg_open_ne | exact Hon | rewrite app_nil_r; exact Hao |].
    intros xs' ds' Hin. rewrite catp_env_set. apply cf_exit. intros d.
    cbn [pe_dev catp_env].
    destruct (decide (d = 0%nat)); [cbn [drained]; split; [by left | exact Hin] | by left].
Qed.

Theorem cat_file_prod_absent_conforms_gen (f : bytes) (outs xs ds : list bytes) files :
  files f = None -> [] ∈ outs -> cat_dg_open f ∈ xs ->
  conforms (catp_env (DProd outs xs ds) files [f]) (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf Hon Hao. simpl.
  eapply cf_open_absent; [by left | unfold mode_create; vm_compute; intros H; exact (H eq_refl) | exact Hf |].
  cbv beta. rewrite decide_True; [| lia].
  eapply (write_bytes_prod_fail_conforms _ 0%nat _ [] outs xs ds);
    [apply catp_env_fd2 | cbv [catp_env pe_dev]; by rewrite decide_True
    | apply catp_dg_open_ne | exact Hon | rewrite app_nil_r; exact Hao |].
  intros xs' ds' Hin. rewrite catp_env_set. apply cf_exit. intros d.
  cbn [pe_dev catp_env].
  destruct (decide (d = 0%nat)); [cbn [drained]; split; [by left | exact Hin] | by left].
Qed.

(* [cat_file_pipe_conforms] at the producer device: the pipe owes the
   content or nothing, the report is the open's, the diagnostics nothing
   or the write error *)
Theorem cat_file_prod_conforms (f c : bytes) files :
  files f = Some c ->
  conforms (catp_env (DProd [c; []] [cat_dg_open f] [[]; cat_dg_write]) files [f])
           (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf. apply cat_file_prod_conforms_gen with (c := c);
    [exact Hf | by left | by right; left | by left | by left | by right; left].
Qed.

(* ...and at an absent f, at the same device *)
Theorem cat_file_prod_absent_conforms (f : bytes) (outs : list bytes) files :
  files f = None -> [] ∈ outs ->
  conforms (catp_env (DProd outs [cat_dg_open f] [[]; cat_dg_write]) files [f])
           (cat_tree [sb "cat"; f]).
Proof using.
  intros Hf Hon. apply cat_file_prod_absent_conforms_gen; [exact Hf | exact Hon | by left].
Qed.

(* the descriptor discipline under any answer is [cat_tree_safe], which
   holds for every argv and every held set: nothing new to prove *)
Lemma cat_file_pipe_safe (f : bytes) (held : gset Z) :
  safe_fds held (cat_tree [sb "cat"; f]).
Proof using. apply cat_tree_safe. Qed.

(* ===================================================================== *)
(*  3.  THE EXITS OF A CONFORMING PATH                                    *)
(*                                                                        *)
(*  [reach_exit E t E']: along SOME path of [t] that conformance covers   *)
(*  from [E] -- the same transitions [conforms] takes, for every answer    *)
(*  and every alternative a write may choose -- an [EExit] is reached at   *)
(*  [E'].  One rule per successor of a [conforms] constructor (a rule     *)
(*  with two successors, a haltable write, gives two), with the same      *)
(*  side conditions, and the exit rule asks every device drained as       *)
(*  [cf_exit] does.  INDUCTIVE, because an exit is at the end of a FINITE *)
(*  path: an infinite path (cat reading forever) exits nowhere, and a     *)
(*  lemma about the exits says nothing about it.                          *)
(*                                                                        *)
(*  Nothing in the relation needs [conforms E t]; a path that is not      *)
(*  conforming simply has no rule.  The exit lemmas are proved by an      *)
(*  INVARIANT closed under one step ([re_step], the dual of [cf_step]: a  *)
(*  universal step where [cf_step] is existential in the alternative), so *)
(*  no proof ever inverts a [Vis] node.                                   *)
(* ===================================================================== *)

Inductive reach_exit : penv -> proc -> penv -> Prop :=
  | re_tau E t E' :
      reach_exit E t E' -> reach_exit E (Tau t) E'
  | re_write_nil E fd d k x E' :
      pe_fd E !! fd = Some d -> x = 0 \/ x = -1 ->
      reach_exit E (k x) E' -> reach_exit E (Vis (EWrite fd []) k) E'
  | re_write E fd d alts a bs k E' :
      bs <> [] -> pe_fd E !! fd = Some d -> pe_dev E d = DOut alts ->
      a ∈ alts -> bs `prefix_of` a ->
      reach_exit (env_set_dev E d (DOut [drop (length bs) a])) (k (Z.of_nat (length bs))) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_h E fd d alts a bs k E' :
      bs <> [] -> pe_fd E !! fd = Some d -> pe_dev E d = DOutH alts ->
      a ∈ alts -> bs `prefix_of` a ->
      reach_exit (env_set_dev E d (DOutH [drop (length bs) a])) (k (Z.of_nat (length bs))) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_h_halt E fd d alts a bs k E' :
      bs <> [] -> pe_fd E !! fd = Some d -> pe_dev E d = DOutH alts ->
      a ∈ alts -> bs `prefix_of` a ->
      reach_exit (env_set_dev E d DHalt) (k (-1)) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_m E fd d rest bs k x E' :
      bs <> [] -> pe_fd E !! fd = Some d -> pe_dev E d = DOutM (bs :: rest) ->
      x = Z.of_nat (length bs) \/ x = -1 ->
      reach_exit (env_set_dev E d (DOutM rest)) (k x) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_halt E fd d bs k E' :
      bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 ->
      pe_fd E !! fd = Some d -> pe_dev E d = DHalt ->
      reach_exit E (k (-1)) E' -> reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_copy E fd d h S p bs k E' :
      bs <> [] -> fd = copy_out -> pe_fd E !! fd = Some d -> pe_dev E d = DCopy h S p ->
      bs `prefix_of` p ->
      reach_exit (env_set_dev E d (DCopy h S (drop (length bs) p))) (k (Z.of_nat (length bs))) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_copy_h E fd d S p bs k E' :
      bs <> [] -> fd = copy_out -> pe_fd E !! fd = Some d -> pe_dev E d = DCopy true S p ->
      bs `prefix_of` p ->
      reach_exit (env_set_dev E d DCopyHalt) (k (-1)) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_copy_end E fd d h p bs k E' :
      bs <> [] -> fd = copy_out -> pe_fd E !! fd = Some d -> pe_dev E d = DCopyEnd h p ->
      bs `prefix_of` p ->
      reach_exit (env_set_dev E d (DCopyEnd h (drop (length bs) p))) (k (Z.of_nat (length bs))) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_copy_end_h E fd d p bs k E' :
      bs <> [] -> fd = copy_out -> pe_fd E !! fd = Some d -> pe_dev E d = DCopyEnd true p ->
      bs `prefix_of` p ->
      reach_exit (env_set_dev E d DCopyHalt) (k (-1)) E' ->
      reach_exit E (Vis (EWrite fd bs) k) E'
  | re_write_copy_halt E fd d bs k E' :
      bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fd = copy_out ->
      pe_fd E !! fd = Some d -> pe_dev E d = DCopyHalt ->
      reach_exit E (k (-1)) E' -> reach_exit E (Vis (EWrite fd bs) k) E'
  | re_read E fd d S n c S' k E' :
      (0 < n)%nat -> pe_fd E !! fd = Some d -> pe_dev E d = DIn S ->
      chunk_ok n S c S' ->
      reach_exit (env_set_dev E d (DIn S')) (k (RdBytes c)) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_e E fd d S n c S' k E' :
      (0 < n)%nat -> pe_fd E !! fd = Some d -> pe_dev E d = DInE S ->
      chunk_ok n S c S' ->
      reach_exit (env_set_dev E d (DInE S')) (k (RdBytes c)) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_e_end E fd d S n k E' :
      (0 < n)%nat -> pe_fd E !! fd = Some d -> pe_dev E d = DInE S ->
      reach_exit (env_set_dev E d DInEnd) (k (RdBytes [])) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_end E fd d n k E' :
      (0 < n)%nat -> pe_fd E !! fd = Some d -> pe_dev E d = DInEnd ->
      reach_exit E (k (RdBytes [])) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_copy E fd d h S p n c S' k E' :
      (0 < n)%nat -> fd = copy_in -> pe_fd E !! fd = Some d -> pe_dev E d = DCopy h S p ->
      chunk_ok n S c S' -> c <> [] ->
      reach_exit (env_set_dev E d (DCopy h S' (p ++ c))) (k (RdBytes c)) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_copy_eof E fd d h S p n k E' :
      (0 < n)%nat -> fd = copy_in -> pe_fd E !! fd = Some d -> pe_dev E d = DCopy h S p ->
      reach_exit (env_set_dev E d (DCopyEnd h p)) (k (RdBytes [])) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_read_copy_end E fd d h p n k E' :
      (0 < n)%nat -> fd = copy_in -> pe_fd E !! fd = Some d -> pe_dev E d = DCopyEnd h p ->
      reach_exit E (k (RdBytes [])) E' ->
      reach_exit E (Vis (ERead fd n) k) E'
  | re_open_present E p content fd d k E' :
      p ∈ pe_paths E -> pe_files E p = Some content ->
      0 <= fd -> pe_fd E !! fd = None -> env_fresh E d ->
      reach_exit (env_set_dev (env_bind E fd d) d (DIn content)) (k fd) E' ->
      reach_exit E (Vis (EOpen p 0) k) E'
  | re_open_refused E p content k E' :
      p ∈ pe_paths E -> pe_files E p = Some content ->
      reach_exit E (k (-1)) E' ->
      reach_exit E (Vis (EOpen p 0) k) E'
  | re_open_absent E p m k E' :
      p ∈ pe_paths E -> ~ mode_create m -> pe_files E p = None ->
      reach_exit E (k (-1)) E' ->
      reach_exit E (Vis (EOpen p m) k) E'
  | re_close E fd d k E' :
      pe_fd E !! fd = Some d ->
      (fd_last (pe_fd E) fd d -> drained_at_close (pe_dev E d)) ->
      reach_exit (env_unbind E fd) (k 0) E' ->
      reach_exit E (Vis (EClose fd) k) E'
  | re_exit E s k :
      (forall d, drained (pe_dev E d)) ->
      reach_exit E (Vis (EExit s) k) E.

(* every exit has every device drained *)
Lemma reach_exit_drained (E : penv) (t : proc) (E' : penv) :
  reach_exit E t E' -> forall d, drained (pe_dev E' d).
Proof using. induction 1; assumption. Qed.

(* ONE universal step: every successor [reach_exit] may take from [t] at
   [E] satisfies [R], and an exit satisfies [P] *)
Definition re_step (P : penv -> Prop) (R : penv -> proc -> Prop) (E : penv) (t : proc) : Prop :=
  match t with
  | Ret v => match v with end
  | Tau t' => R E t'
  | Vis e k =>
      match e as e return (ans e -> proc) -> Prop with
      | EWrite fd bs => fun k =>
          forall d, pe_fd E !! fd = Some d ->
          (bs = [] -> R E (k 0) /\ R E (k (-1)))
          /\ (forall alts a, bs <> [] -> pe_dev E d = DOut alts -> a ∈ alts -> bs `prefix_of` a ->
                R (env_set_dev E d (DOut [drop (length bs) a])) (k (Z.of_nat (length bs))))
          /\ (forall alts a, bs <> [] -> pe_dev E d = DOutH alts -> a ∈ alts -> bs `prefix_of` a ->
                R (env_set_dev E d (DOutH [drop (length bs) a])) (k (Z.of_nat (length bs)))
                /\ R (env_set_dev E d DHalt) (k (-1)))
          /\ (forall rest, bs <> [] -> pe_dev E d = DOutM (bs :: rest) ->
                R (env_set_dev E d (DOutM rest)) (k (Z.of_nat (length bs)))
                /\ R (env_set_dev E d (DOutM rest)) (k (-1)))
          /\ (bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> pe_dev E d = DHalt -> R E (k (-1)))
          /\ (forall h S p, bs <> [] -> fd = copy_out -> pe_dev E d = DCopy h S p -> bs `prefix_of` p ->
                R (env_set_dev E d (DCopy h S (drop (length bs) p))) (k (Z.of_nat (length bs)))
                /\ (h = true -> R (env_set_dev E d DCopyHalt) (k (-1))))
          /\ (forall h p, bs <> [] -> fd = copy_out -> pe_dev E d = DCopyEnd h p -> bs `prefix_of` p ->
                R (env_set_dev E d (DCopyEnd h (drop (length bs) p))) (k (Z.of_nat (length bs)))
                /\ (h = true -> R (env_set_dev E d DCopyHalt) (k (-1))))
          /\ (bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fd = copy_out -> pe_dev E d = DCopyHalt ->
                R E (k (-1)))
      | ERead fd n => fun k =>
          forall d, pe_fd E !! fd = Some d -> (0 < n)%nat ->
          (forall S c S', pe_dev E d = DIn S -> chunk_ok n S c S' ->
                R (env_set_dev E d (DIn S')) (k (RdBytes c)))
          /\ (forall S, pe_dev E d = DInE S ->
                (forall c S', chunk_ok n S c S' -> R (env_set_dev E d (DInE S')) (k (RdBytes c)))
                /\ R (env_set_dev E d DInEnd) (k (RdBytes [])))
          /\ (pe_dev E d = DInEnd -> R E (k (RdBytes [])))
          /\ (forall h S p, fd = copy_in -> pe_dev E d = DCopy h S p ->
                (forall c S', chunk_ok n S c S' -> c <> [] ->
                   R (env_set_dev E d (DCopy h S' (p ++ c))) (k (RdBytes c)))
                /\ R (env_set_dev E d (DCopyEnd h p)) (k (RdBytes [])))
          /\ (forall h p, fd = copy_in -> pe_dev E d = DCopyEnd h p -> R E (k (RdBytes [])))
      | EOpen p m => fun k =>
          p ∈ pe_paths E ->
          (forall content, m = 0 -> pe_files E p = Some content ->
             (forall fd d, 0 <= fd -> pe_fd E !! fd = None -> env_fresh E d ->
                R (env_set_dev (env_bind E fd d) d (DIn content)) (k fd))
             /\ R E (k (-1)))
          /\ (~ mode_create m -> pe_files E p = None -> R E (k (-1)))
      | EClose fd => fun k =>
          forall d, pe_fd E !! fd = Some d ->
          (fd_last (pe_fd E) fd d -> drained_at_close (pe_dev E d)) ->
          R (env_unbind E fd) (k 0)
      | EExit s => fun _ => (forall d, drained (pe_dev E d)) -> P E
      end k
  end.

(* THE INVARIANT PRINCIPLE: an invariant closed under [re_step] holds all
   along a path, and so [P] holds at its exit *)
Lemma reach_exit_inv (P : penv -> Prop) (I : penv -> proc -> Prop) :
  (forall E t, I E t -> re_step P I E t) ->
  forall E t E', reach_exit E t E' -> I E t -> P E'.
Proof using.
  intros Hcl E t E' Hr.
  induction Hr as
    [E t E' Hr IH
    | E fd d k x E' Hfd Hx Hr IH
    | E fd d alts a bs k E' Hne Hfd Hd Ha Hp Hr IH
    | E fd d alts a bs k E' Hne Hfd Hd Ha Hp Hr IH
    | E fd d alts a bs k E' Hne Hfd Hd Ha Hp Hr IH
    | E fd d rest bs k x E' Hne Hfd Hd Hx Hr IH
    | E fd d bs k E' Hne Hlt Hfd Hd Hr IH
    | E fd d h S p bs k E' Hne Hco Hfd Hd Hp Hr IH
    | E fd d S p bs k E' Hne Hco Hfd Hd Hp Hr IH
    | E fd d h p bs k E' Hne Hco Hfd Hd Hp Hr IH
    | E fd d p bs k E' Hne Hco Hfd Hd Hp Hr IH
    | E fd d bs k E' Hne Hlt Hco Hfd Hd Hr IH
    | E fd d S n c S' k E' Hn Hfd Hd Hc Hr IH
    | E fd d S n c S' k E' Hn Hfd Hd Hc Hr IH
    | E fd d S n k E' Hn Hfd Hd Hr IH
    | E fd d n k E' Hn Hfd Hd Hr IH
    | E fd d h S p n c S' k E' Hn Hci Hfd Hd Hc Hcne Hr IH
    | E fd d h S p n k E' Hn Hci Hfd Hd Hr IH
    | E fd d h p n k E' Hn Hci Hfd Hd Hr IH
    | E p content fd d k E' Hp Hf Hfd0 Hfd Hfr Hr IH
    | E p content k E' Hp Hf Hr IH
    | E p m k E' Hp Hm Hf Hr IH
    | E fd d k E' Hfd Hlast Hr IH
    | E s k Hdr ];
    intros HI; apply Hcl in HI; cbn [re_step] in HI.
  - exact (IH HI).
  - destruct (HI d Hfd) as [H _]. destruct (H eq_refl) as [H0 H1].
    destruct Hx as [-> | ->]; [exact (IH H0) | exact (IH H1)].
  - destruct (HI d Hfd) as (_ & H & _). exact (IH (H alts a Hne Hd Ha Hp)).
  - destruct (HI d Hfd) as (_ & _ & H & _). exact (IH (proj1 (H alts a Hne Hd Ha Hp))).
  - destruct (HI d Hfd) as (_ & _ & H & _). exact (IH (proj2 (H alts a Hne Hd Ha Hp))).
  - destruct (HI d Hfd) as (_ & _ & _ & H & _). destruct (H rest Hne Hd) as [H1 H2].
    destruct Hx as [-> | ->]; [exact (IH H1) | exact (IH H2)].
  - destruct (HI d Hfd) as (_ & _ & _ & _ & H & _). exact (IH (H Hne Hlt Hd)).
  - destruct (HI d Hfd) as (_ & _ & _ & _ & _ & H & _). exact (IH (proj1 (H h S p Hne Hco Hd Hp))).
  - destruct (HI d Hfd) as (_ & _ & _ & _ & _ & H & _). exact (IH (proj2 (H true S p Hne Hco Hd Hp) eq_refl)).
  - destruct (HI d Hfd) as (_ & _ & _ & _ & _ & _ & H & _). exact (IH (proj1 (H h p Hne Hco Hd Hp))).
  - destruct (HI d Hfd) as (_ & _ & _ & _ & _ & _ & H & _). exact (IH (proj2 (H true p Hne Hco Hd Hp) eq_refl)).
  - destruct (HI d Hfd) as (_ & _ & _ & _ & _ & _ & _ & H). exact (IH (H Hne Hlt Hco Hd)).
  - destruct (HI d Hfd Hn) as (H & _). exact (IH (H S c S' Hd Hc)).
  - destruct (HI d Hfd Hn) as (_ & H & _). exact (IH (proj1 (H S Hd) c S' Hc)).
  - destruct (HI d Hfd Hn) as (_ & H & _). exact (IH (proj2 (H S Hd))).
  - destruct (HI d Hfd Hn) as (_ & _ & H & _). exact (IH (H Hd)).
  - destruct (HI d Hfd Hn) as (_ & _ & _ & H & _). exact (IH (proj1 (H h S p Hci Hd) c S' Hc Hcne)).
  - destruct (HI d Hfd Hn) as (_ & _ & _ & H & _). exact (IH (proj2 (H h S p Hci Hd))).
  - destruct (HI d Hfd Hn) as (_ & _ & _ & _ & H). exact (IH (H h p Hci Hd)).
  - destruct (HI Hp) as [H _]. exact (IH (proj1 (H content eq_refl Hf) fd d Hfd0 Hfd Hfr)).
  - destruct (HI Hp) as [H _]. exact (IH (proj2 (H content eq_refl Hf))).
  - destruct (HI Hp) as [_ H]. exact (IH (H Hm Hf)).
  - exact (IH (HI d Hfd Hlast)).
  - exact (HI Hdr).
Qed.

(* ---- what a device wrote, read off what it still owes ---------------- *)

(* an output device that owed [alts] and has since taken the bytes [w]
   (in writes of any size) owes [A]: untouched, or the rest of the one
   alternative its first write chose *)
Definition dev_after (alts : list bytes) (w : bytes) (A : list bytes) : Prop :=
  (w = [] /\ A = alts)
  \/ (w <> [] /\ exists a, a ∈ alts /\ w `prefix_of` a /\ A = [drop (length w) a]).

Lemma dev_after_nil (alts : list bytes) : dev_after alts [] alts.
Proof using. by left. Qed.

Lemma dev_after_step (alts : list bytes) (w : bytes) (A : list bytes) (a bs : bytes) :
  dev_after alts w A -> a ∈ A -> bs `prefix_of` a -> bs <> [] ->
  dev_after alts (w ++ bs) [drop (length bs) a].
Proof using.
  intros [[-> ->] | (Hw & a0 & Ha0 & [z ->] & ->)] Ha [y ->] Hbs; right.
  - split; [exact Hbs |]. exists (bs ++ y).
    split; [exact Ha | split; [by exists y | reflexivity]].
  - apply elem_of_list_singleton in Ha. rewrite drop_app_length in Ha. subst z.
    split; [intros Hn; apply app_eq_nil in Hn as [-> _]; by apply Hw |].
    exists (w ++ bs ++ y). split; [exact Ha0 |].
    split; [by exists y; rewrite app_assoc |].
    rewrite app_assoc, !drop_app_length. reflexivity.
Qed.

(* at an exit the device is drained, so it took EXACTLY one alternative *)
Lemma dev_after_done (alts : list bytes) (w : bytes) (A : list bytes) :
  dev_after alts w A -> w <> [] -> [] ∈ A -> w ∈ alts /\ A = [[]].
Proof using.
  intros [[-> _] | (_ & a & Ha & [z ->] & ->)] Hw Hin; [exfalso; exact (Hw eq_refl) |].
  apply elem_of_list_singleton in Hin. rewrite drop_app_length in Hin. subst z.
  rewrite app_nil_r in Ha |- *. split; [exact Ha | by rewrite drop_all].
Qed.

Lemma cat_dg_write_ne : cat_dg_write <> [].
Proof using. unfold cat_dg_write. intros H. apply (f_equal (@length _)) in H.
  rewrite length_app in H. simpl in H. lia. Qed.
Lemma cat_dg_open_ne (p : bytes) : cat_dg_open p <> [].
Proof using. unfold cat_dg_open. intros H. apply (f_equal (@length _)) in H.
  rewrite !length_app in H. simpl in H. lia. Qed.

(* ---- a diagnostic on descriptor 2, byte by byte, at any environment
   family that keeps the console at device 0 ---------------------------- *)
Lemma diag_step (P : penv -> Prop) (I : penv -> proc -> Prop) (F : list bytes -> penv)
    (alts : list bytes) (dg w r : bytes) (A : list bytes) (s : Z) :
  (forall A, pe_fd (F A) !! 2 = Some 0%nat) ->
  (forall A, pe_dev (F A) 0 = DOut A) ->
  (forall A A', env_set_dev (F A) 0 (DOut A') = F A') ->
  (forall w' r' A', w' ++ r' = dg -> dev_after alts w' A' -> I (F A') (write_bytes 2 r' (exit_ s))) ->
  (forall A', dev_after alts dg A' -> (forall d, drained (pe_dev (F A') d)) -> P (F A')) ->
  w ++ r = dg -> dev_after alts w A ->
  re_step P I (F A) (write_bytes 2 r (exit_ s)).
Proof using.
  intros Hfd Hdev Hset HI HP Hwr Hw. destruct r as [| b r].
  - cbn [write_bytes exit_ re_step]. intros Hdr. rewrite app_nil_r in Hwr. subst w.
    exact (HP A Hw Hdr).
  - cbn [write_bytes re_step]. intros d Hd. rewrite Hfd in Hd. injection Hd as <-.
    rewrite Hdev.
    split; [intros; discriminate |].
    split.
    { intros alts0 a _ Heq Ha Hp. injection Heq as <-. rewrite Hset.
      apply (HI (w ++ [b])); [rewrite <- app_assoc; exact Hwr |].
      eapply dev_after_step; [exact Hw | exact Ha | exact Hp | done]. }
    repeat split; intros; discriminate.
Qed.

(* ---- echo at a pipe's write end ---------------------------------------- *)

Inductive ep_tree : proc -> Prop :=
  | et_words ws : ep_tree (echo_words ws (exit_ 0))
  | et_sep b ws : ep_tree (Vis (EWrite 1 [b]) (fun _ => echo_words ws (exit_ 0))).

Inductive ep_env (files : bytes -> option bytes) : penv -> Prop :=
  | epe_halt : ep_env files (pipe_env DHalt files)
  | epe_out o : ep_env files (pipe_env (DOutH [o]) files).

Inductive ep_st (files : bytes -> option bytes) (E : penv) (t : proc) : Prop :=
  | eps : ep_env files E -> ep_tree t -> ep_st files E t.

Lemma pipe_env_fd1 (spec : dspec) files : pe_fd (pipe_env spec files) !! 1 = Some 0%nat.
Proof using. cbv [pipe_env pe_fd]. apply lookup_singleton. Qed.
Lemma pipe_env_dev0 (spec : dspec) files : pe_dev (pipe_env spec files) 0 = spec.
Proof using. reflexivity. Qed.

Lemma ep_write_step (P : penv -> Prop) files (E : penv) (bs : bytes) (k : Z -> proc) :
  ep_env files E -> (forall x, ep_tree (k x)) ->
  re_step P (ep_st files) E (Vis (EWrite 1 bs) k).
Proof using.
  intros HE Hk. cbn [re_step]. intros d Hd.
  destruct HE as [| o]; rewrite pipe_env_fd1 in Hd; injection Hd as <-; rewrite pipe_env_dev0.
  - (* halted: every write answers -1 (or, empty, 0) *)
    split; [intros _; split; constructor; [constructor | apply Hk | constructor | apply Hk] |].
    split; [intros; discriminate |]. split; [intros; discriminate |].
    split; [intros; discriminate |].
    split; [intros; constructor; [constructor | apply Hk] |].
    repeat split; intros; discriminate.
  - split; [intros _; split; constructor; [constructor | apply Hk | constructor | apply Hk] |].
    split; [intros; discriminate |].
    split.
    { intros alts a _ _ _ _. rewrite !pipe_env_set.
      split; constructor; [constructor | apply Hk | constructor | apply Hk]. }
    repeat split; intros; discriminate.
Qed.

Definition echo_exit (files : bytes -> option bytes) (E' : penv) : Prop :=
  E' = pipe_env (DOutH [[]]) files \/ E' = pipe_env DHalt files.

Lemma ep_st_closed (files : bytes -> option bytes) (E : penv) (t : proc) :
  ep_st files E t -> re_step (echo_exit files) (ep_st files) E t.
Proof using.
  intros [HE Ht]. destruct Ht as [ws | b ws].
  - destruct ws as [| w [| w' r]].
    + cbn [echo_words exit_ re_step]. intros Hdr. specialize (Hdr 0%nat).
      unfold echo_exit. destruct HE as [| o]; [by right |]. left.
      rewrite pipe_env_dev0 in Hdr. change ([] ∈ [o]) in Hdr.
      apply elem_of_list_singleton in Hdr. subst o. reflexivity.
    + cbn [echo_words]. apply ep_write_step; [exact HE |]. intros _.
      exact (et_sep wl_nl []).
    + cbn [echo_words]. apply ep_write_step; [exact HE |]. intros _.
      exact (et_sep wl_sp (w' :: r)).
  - apply ep_write_step; [exact HE |]. intros _. apply et_words.
Qed.

(* echo at a pipe's write end owing [L] exits having written it all, or
   halted (the reader went first) *)
Theorem echo_pipe_exits (argv : list bytes) (L : bytes) files (E' : penv) :
  reach_exit (pipe_env (DOutH [L]) files) (echo_tree argv) E' ->
  E' = pipe_env (DOutH [[]]) files \/ E' = pipe_env DHalt files.
Proof using.
  intros Hr. apply (reach_exit_inv (echo_exit files) (ep_st files) (ep_st_closed files) _ _ _ Hr).
  exact (eps files _ _ (epe_out files L) (et_words (drop 1 argv))).
Qed.

(* ---- cat at the copy device ------------------------------------------- *)

Lemma copy_env_fd0 (spec : dspec) alts files paths :
  pe_fd (copy_env spec alts files paths) !! 0 = Some 1%nat.
Proof using. cbv [copy_env pe_fd]. apply lookup_insert. Qed.
Lemma copy_env_fd1 (spec : dspec) alts files paths :
  pe_fd (copy_env spec alts files paths) !! 1 = Some 1%nat.
Proof using. cbv [copy_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_insert. Qed.
Lemma copy_env_fd2 (spec : dspec) alts files paths :
  pe_fd (copy_env spec alts files paths) !! 2 = Some 0%nat.
Proof using.
  cbv [copy_env pe_fd]. do 2 (rewrite lookup_insert_ne; [| lia]). apply lookup_singleton.
Qed.
Lemma copy_env_dev0 (spec : dspec) alts files paths :
  pe_dev (copy_env spec alts files paths) 0 = DOut alts.
Proof using. reflexivity. Qed.
Lemma copy_env_dev1 (spec : dspec) alts files paths :
  pe_dev (copy_env spec alts files paths) 1 = spec.
Proof using. reflexivity. Qed.

Definition cc_wr_tree (bs : bytes) : proc :=
  Vis (EWrite 1 bs) (fun r =>
    if decide (r = Z.of_nat (length bs)) then Tau (cat_loop 0 (exit_ 0))
    else write_bytes 2 cat_dg_write (exit_ 1)).

Inductive cc_st (h : bool) (alts : list bytes) files paths : penv -> proc -> Prop :=
  | cc_loop S : cc_st h alts files paths (copy_env (DCopy h S []) alts files paths) (cat_loop 0 (exit_ 0))
  | cc_tau S : cc_st h alts files paths (copy_env (DCopy h S []) alts files paths) (Tau (cat_loop 0 (exit_ 0)))
  | cc_wr S bs : bs <> [] ->
      cc_st h alts files paths (copy_env (DCopy h S bs) alts files paths) (cc_wr_tree bs)
  | cc_end : cc_st h alts files paths (copy_env (DCopyEnd h []) alts files paths) (exit_ 0)
  | cc_dg w r A : h = true -> w ++ r = cat_dg_write -> dev_after alts w A ->
      cc_st h alts files paths (copy_env DCopyHalt A files paths) (write_bytes 2 r (exit_ 1)).

Definition copy_exit (h : bool) (alts : list bytes) files paths (E' : penv) : Prop :=
  E' = copy_env (DCopyEnd h []) alts files paths
  \/ (h = true /\ cat_dg_write ∈ alts /\ E' = copy_env DCopyHalt [[]] files paths).

Lemma cc_st_closed (h : bool) (alts : list bytes) files paths (E : penv) (t : proc) :
  cc_st h alts files paths E t -> re_step (copy_exit h alts files paths) (cc_st h alts files paths) E t.
Proof using.
  intros Hst. destruct Hst as [S | S | S bs Hbs | | w r A Hh Hwr Hw].
  - (* the read *)
    rewrite cat_loop_unfold. cbn [re_step]. intros d Hd _.
    rewrite copy_env_fd0 in Hd. injection Hd as <-. rewrite copy_env_dev1.
    split; [intros; discriminate |]. split; [intros; discriminate |].
    split; [intros; discriminate |]. split; [| intros; discriminate].
    intros h' S' p _ Heq. injection Heq as <- <- <-. split.
    + intros c S'' _ Hc. rewrite copy_env_set. destruct c as [| b c']; [done |].
      apply (cc_wr h alts files paths S'' (b :: c')). discriminate.
    + rewrite copy_env_set. apply cc_end.
  - cbn [re_step]. apply cc_loop.
  - (* the write of what was read *)
    unfold cc_wr_tree. cbn [re_step]. intros d Hd.
    rewrite copy_env_fd1 in Hd. injection Hd as <-. rewrite copy_env_dev1.
    split; [intros Hn; exfalso; exact (Hbs Hn) |].
    do 4 (split; [intros; discriminate |]).
    split; [| repeat split; intros; discriminate].
    intros h' S' p _ _ Heq _. injection Heq as <- <- <-. split.
    + rewrite drop_all, copy_env_set. rewrite decide_True; [| reflexivity]. apply cc_tau.
    + intros Hh. rewrite copy_env_set. rewrite decide_False; [| lia].
      apply (cc_dg h alts files paths [] cat_dg_write alts Hh); [reflexivity | apply dev_after_nil].
  - cbn [exit_ re_step]. intros _. unfold copy_exit. by left.
  - apply (diag_step _ _ (fun A => copy_env DCopyHalt A files paths) alts cat_dg_write w r A 1).
    + intros A'. apply copy_env_fd2.
    + intros A'. apply copy_env_dev0.
    + intros A' A''. apply copy_env_out.
    + intros w' r' A' Hwr' Hw'. exact (cc_dg h alts files paths w' r' A' Hh Hwr' Hw').
    + intros A' HA' Hdr. specialize (Hdr 0%nat). cbv beta in Hdr |- *.
      change (drained (DOut A')) in Hdr.
      destruct (dev_after_done _ _ _ HA' cat_dg_write_ne Hdr) as [Hin ->].
      unfold copy_exit. right. split; [exact Hh |]. split; [exact Hin | reflexivity].
    + exact Hwr.
    + exact Hw.
Qed.

(* cat at the copy device exits having read its input to the end and
   written all of it, the console untouched; or (the sink may halt) with
   the sink halted and exactly the write diagnostic on the console *)
Theorem cat_copy_exits (h : bool) (L : bytes) (alts : list bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy h L []) alts files paths) (cat_tree [sb "cat"]) E' ->
  E' = copy_env (DCopyEnd h []) alts files paths
  \/ (h = true /\ cat_dg_write ∈ alts /\ E' = copy_env DCopyHalt [[]] files paths).
Proof using.
  intros Hr.
  apply (reach_exit_inv (copy_exit h alts files paths) (cc_st h alts files paths)
           (cc_st_closed h alts files paths) _ _ _ Hr).
  exact (cc_loop h alts files paths L).
Qed.

(* ---- cat f at a pipe's write end --------------------------------------- *)

Definition catf_ok (fd : Z) (d : nat) : Prop :=
  fd <> 1 /\ fd <> 2 /\ d <> 0%nat /\ d <> 1%nat.

Definition catf_rest (fd : Z) : proc := Vis (EClose fd) (fun _ => cat_files [] (exit_ 0)).

Definition catf_wr_tree (fd : Z) (bs : bytes) : proc :=
  Vis (EWrite 1 bs) (fun r =>
    if decide (r = Z.of_nat (length bs)) then Tau (cat_loop fd (catf_rest fd))
    else write_bytes 2 cat_dg_write (exit_ 1)).

Inductive cf_st (f : bytes) (outs alts : list bytes) files : penv -> proc -> Prop :=
  | cfs_open :
      cf_st f outs alts files (catf_env (DOutH outs) alts files [f]) (cat_tree [sb "cat"; f])
  | cfs_loop fd d c w S A :
      files f = Some c -> w ++ S = c -> dev_after outs w A -> catf_ok fd d ->
      cf_st f outs alts files (catf_loop_env fd d S (DOutH A) alts files [f]) (cat_loop fd (catf_rest fd))
  | cfs_tau fd d c w S A :
      files f = Some c -> w ++ S = c -> dev_after outs w A -> catf_ok fd d ->
      cf_st f outs alts files (catf_loop_env fd d S (DOutH A) alts files [f])
        (Tau (cat_loop fd (catf_rest fd)))
  | cfs_wr fd d c w bs S A :
      files f = Some c -> w ++ bs ++ S = c -> bs <> [] -> dev_after outs w A -> catf_ok fd d ->
      cf_st f outs alts files (catf_loop_env fd d S (DOutH A) alts files [f]) (catf_wr_tree fd bs)
  | cfs_close fd d c A :
      files f = Some c -> dev_after outs c A -> catf_ok fd d ->
      cf_st f outs alts files (catf_loop_env fd d [] (DOutH A) alts files [f]) (catf_rest fd)
  | cfs_done fd d c A :
      files f = Some c -> dev_after outs c A ->
      cf_st f outs alts files (env_unbind (catf_loop_env fd d [] (DOutH A) alts files [f]) fd)
        (exit_ 0)
  | cfs_halt fd d S w r A :
      w ++ r = cat_dg_write -> dev_after alts w A ->
      cf_st f outs alts files (catf_loop_env fd d S DHalt A files [f]) (write_bytes 2 r (exit_ 1))
  | cfs_refused w r A :
      w ++ r = cat_dg_open f -> dev_after alts w A ->
      cf_st f outs alts files (catf_env (DOutH outs) A files [f]) (write_bytes 2 r (exit_ 1)).

Definition catf_exit (f : bytes) (outs alts : list bytes) files (E' : penv) : Prop :=
  (pe_dev E' 0 = DOut alts
     /\ exists c A, files f = Some c /\ pe_dev E' 1 = DOutH A /\ dev_after outs c A)
  \/ (pe_dev E' 1 = DHalt /\ cat_dg_write ∈ alts /\ pe_dev E' 0 = DOut [[]])
  \/ (pe_dev E' 1 = DOutH outs /\ cat_dg_open f ∈ alts /\ pe_dev E' 0 = DOut [[]]).

Lemma catf_loop_env_fd1 fdin din S (out : dspec) alts files paths :
  pe_fd (catf_loop_env fdin din S out alts files paths) !! 1 = Some 1%nat.
Proof using. cbv [catf_loop_env pe_fd]. apply lookup_insert. Qed.
Lemma catf_loop_env_fd2 fdin din S (out : dspec) alts files paths :
  pe_fd (catf_loop_env fdin din S out alts files paths) !! 2 = Some 0%nat.
Proof using. cbv [catf_loop_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_insert. Qed.
Lemma catf_loop_env_dev1 fdin din S (out : dspec) alts files paths :
  pe_dev (catf_loop_env fdin din S out alts files paths) 1 = out.
Proof using. reflexivity. Qed.
Lemma catf_env_fd2 (out : dspec) alts files paths :
  pe_fd (catf_env out alts files paths) !! 2 = Some 0%nat.
Proof using. cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. Qed.

Lemma cf_st_closed (f : bytes) (outs alts : list bytes) files (E : penv) (t : proc) :
  cf_st f outs alts files E t -> re_step (catf_exit f outs alts files) (cf_st f outs alts files) E t.
Proof using.
  intros Hst.
  destruct Hst as [| fd d c w S A Hf HwS Hw Hok | fd d c w S A Hf HwS Hw Hok
                  | fd d c w bs S A Hf HwS Hbs Hw Hok | fd d c A Hf Hw Hok | fd d c A Hf Hw
                  | fd d S w r A Hwr Hw | w r A Hwr Hw].
  - (* the open *)
    cbn [cat_tree drop cat_files re_step]. intros _. split.
    + intros content _ Hf. split.
      * intros fd d Hfd Hnone Hfr. rewrite catf_env_open; [| exact Hnone | exact Hfr].
        rewrite decide_False; [| lia].
        assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
        { cbv [catf_env pe_fd] in Hnone. split; intros ->; simplify_map_eq. }
        assert (d <> 0%nat) as Hd0.
        { intros ->. apply (Hfr 2). cbv [catf_env pe_fd]. rewrite lookup_insert_ne; [| lia].
          apply lookup_singleton. }
        assert (d <> 1%nat) as Hd1.
        { intros ->. apply (Hfr 1). cbv [catf_env pe_fd]. apply lookup_insert. }
        apply (cfs_loop f outs alts files fd d content [] content outs Hf eq_refl (dev_after_nil _)).
        exact (conj Hf1 (conj Hf2 (conj Hd0 Hd1))).
      * rewrite decide_True; [| lia].
        exact (cfs_refused f outs alts files [] (cat_dg_open f) alts eq_refl (dev_after_nil _)).
    + intros _ _. rewrite decide_True; [| lia].
      exact (cfs_refused f outs alts files [] (cat_dg_open f) alts eq_refl (dev_after_nil _)).
  - (* the read *)
    destruct Hok as (Hf1 & Hf2 & Hd0 & Hd1).
    rewrite cat_loop_unfold. cbn [re_step]. intros d' Hd' _.
    rewrite catf_loop_env_fdin in Hd'; [| exact Hf1 | exact Hf2]. injection Hd' as <-.
    rewrite catf_loop_env_din; [| exact Hd0 | exact Hd1].
    split; [| repeat split; intros; discriminate].
    intros S0 ch S' Heq (HS & _ & Hnil). injection Heq as <-.
    rewrite catf_loop_env_in; [| exact Hd0 | exact Hd1].
    destruct ch as [| b c'].
    + assert (S = []) as -> by exact (Hnil eq_refl).
      simpl in HS. subst S'. rewrite app_nil_r in HwS. subst w.
      apply (cfs_close f outs alts files fd d c A Hf Hw).
      exact (conj Hf1 (conj Hf2 (conj Hd0 Hd1))).
    + apply (cfs_wr f outs alts files fd d c w (b :: c') S' A Hf); [by rewrite <- HS | discriminate | exact Hw |].
      exact (conj Hf1 (conj Hf2 (conj Hd0 Hd1))).
  - cbn [re_step]. exact (cfs_loop f outs alts files fd d c w S A Hf HwS Hw Hok).
  - (* the write of the chunk *)
    unfold catf_wr_tree. cbn [re_step]. intros d' Hd'.
    rewrite catf_loop_env_fd1 in Hd'. injection Hd' as <-. rewrite catf_loop_env_dev1.
    split; [intros Hn; exfalso; exact (Hbs Hn) |].
    split; [intros; discriminate |].
    split; [| repeat split; intros; discriminate].
    intros alts0 a _ Heq Ha Hp. injection Heq as <-. rewrite !catf_loop_env_out1. split.
    + rewrite decide_True; [| reflexivity].
      apply (cfs_tau f outs alts files fd d c (w ++ bs) S); [exact Hf | by rewrite <- app_assoc | | exact Hok].
      eapply dev_after_step; [exact Hw | exact Ha | exact Hp | exact Hbs].
    + rewrite decide_False; [| lia].
      exact (cfs_halt f outs alts files fd d S [] cat_dg_write alts eq_refl (dev_after_nil _)).
  - (* the close of f *)
    destruct Hok as (Hf1 & Hf2 & Hd0 & Hd1).
    unfold catf_rest. cbn [re_step]. intros d' _ _.
    exact (cfs_done f outs alts files fd d c A Hf Hw).
  - (* the exit, having copied f whole *)
    cbn [exit_ re_step]. intros _. unfold catf_exit. left. split; [reflexivity |].
    exists c, A. split; [exact Hf |]. split; [reflexivity | exact Hw].
  - (* the write diagnostic, the pipe halted *)
    apply (diag_step _ _ (fun A => catf_loop_env fd d S DHalt A files [f]) alts cat_dg_write w r A 1).
    + intros A'. apply catf_loop_env_fd2.
    + intros A'. reflexivity.
    + intros A' A''. apply catf_loop_env_cons.
    + intros w' r' A' Hwr' Hw'. exact (cfs_halt f outs alts files fd d S w' r' A' Hwr' Hw').
    + intros A' HA' Hdr. specialize (Hdr 0%nat). cbv beta in Hdr |- *.
      change (drained (DOut A')) in Hdr. unfold catf_exit. right. left.
      destruct (dev_after_done _ _ _ HA' cat_dg_write_ne Hdr) as [Hin ->].
      split; [reflexivity |]. split; [exact Hin | reflexivity].
    + exact Hwr.
    + exact Hw.
  - (* the open diagnostic, nothing on the pipe *)
    apply (diag_step _ _ (fun A => catf_env (DOutH outs) A files [f]) alts (cat_dg_open f) w r A 1).
    + intros A'. apply catf_env_fd2.
    + intros A'. reflexivity.
    + intros A' A''. apply catf_env_cons.
    + intros w' r' A' Hwr' Hw'. exact (cfs_refused f outs alts files w' r' A' Hwr' Hw').
    + intros A' HA' Hdr. specialize (Hdr 0%nat). cbv beta in Hdr |- *.
      change (drained (DOut A')) in Hdr. unfold catf_exit. right. right.
      destruct (dev_after_done _ _ _ HA' (cat_dg_open_ne f) Hdr) as [Hin ->].
      split; [reflexivity |]. split; [exact Hin | reflexivity].
    + exact Hwr.
    + exact Hw.
Qed.

(* cat f at a pipe's write end exits in one of three ways: f read to its
   end and written whole down the pipe (the pipe's device has taken
   exactly f's content, [dev_after]), the console untouched; the pipe
   halted (its reader went) and exactly the write diagnostic on the
   console; or the open refused (absent, or the kernel's -1 on a present
   file), nothing on the pipe and exactly the open diagnostic on the
   console *)
Theorem cat_file_pipe_exits (f : bytes) (outs alts : list bytes) files (E' : penv) :
  reach_exit (catf_env (DOutH outs) alts files [f]) (cat_tree [sb "cat"; f]) E' ->
  (pe_dev E' 0 = DOut alts
     /\ exists c A, files f = Some c /\ pe_dev E' 1 = DOutH A /\ dev_after outs c A)
  \/ (pe_dev E' 1 = DHalt /\ cat_dg_write ∈ alts /\ pe_dev E' 0 = DOut [[]])
  \/ (pe_dev E' 1 = DOutH outs /\ cat_dg_open f ∈ alts /\ pe_dev E' 0 = DOut [[]]).
Proof using.
  intros Hr.
  exact (reach_exit_inv (catf_exit f outs alts files) (cf_st f outs alts files)
           (cf_st_closed f outs alts files) _ _ _ Hr (cfs_open f outs alts files)).
Qed.

(* ---- the relation is inhabited where it should be ------------------- *)

(* cat at the copy device reaches its good exit on a one-byte input, and
   its halt exit at a sink that may halt: the exit lemmas above are not
   about an empty relation *)
Example reach_copy_good (b : bv 8) (alts : list bytes) files paths :
  [] ∈ alts ->
  reach_exit (copy_env (DCopy false [b] []) alts files paths) (cat_tree [sb "cat"])
             (copy_env (DCopyEnd false []) alts files paths).
Proof using.
  intros Hnil. cbn [cat_tree drop]. rewrite cat_loop_unfold.
  eapply (re_read_copy _ 0 1%nat false [b] [] cat_bufsz [b] []);
    [unfold cat_bufsz; lia | reflexivity | apply copy_env_fd0 | reflexivity
    | split; [reflexivity | split; [unfold cat_bufsz; simpl; lia | intros Hn; exact Hn]] | discriminate |].
  rewrite copy_env_set. cbv beta iota.
  eapply (re_write_copy _ 1 1%nat false [] [b] [b]);
    [discriminate | reflexivity | apply copy_env_fd1 | reflexivity | exists []; reflexivity |].
  rewrite drop_all, copy_env_set. cbv beta. rewrite decide_True; [| reflexivity].
  apply re_tau. rewrite cat_loop_unfold.
  eapply (re_read_copy_eof _ 0 1%nat false [] [] cat_bufsz);
    [unfold cat_bufsz; lia | reflexivity | apply copy_env_fd0 | reflexivity |].
  rewrite copy_env_set. cbv beta iota.
  apply re_exit. intros d. cbn [pe_dev copy_env].
  destruct (decide (d = 0%nat)); [exact Hnil |].
  destruct (decide (d = 1%nat)); [reflexivity | by left].
Qed.

Example reach_copy_halt (b : bv 8) files paths :
  reach_exit (copy_env (DCopy true [b] []) [[]; cat_dg_write] files paths) (cat_tree [sb "cat"])
             (copy_env DCopyHalt [[]] files paths).
Proof using.
  cbn [cat_tree drop]. rewrite cat_loop_unfold.
  eapply (re_read_copy _ 0 1%nat true [b] [] cat_bufsz [b] []);
    [unfold cat_bufsz; lia | reflexivity | apply copy_env_fd0 | reflexivity
    | split; [reflexivity | split; [unfold cat_bufsz; simpl; lia | intros Hn; exact Hn]] | discriminate |].
  rewrite copy_env_set. cbv beta iota.
  eapply (re_write_copy_h _ 1 1%nat [] [b] [b]);
    [discriminate | reflexivity | apply copy_env_fd1 | reflexivity | exists []; reflexivity |].
  rewrite copy_env_set. cbv beta. rewrite decide_False; [| lia].
  (* the diagnostic, one byte at a time, each on the one alternative *)
  assert (forall w r, w ++ r = cat_dg_write -> w <> [] ->
            reach_exit (copy_env DCopyHalt [r] files paths) (write_bytes 2 r (exit_ 1))
                       (copy_env DCopyHalt [[]] files paths)) as Hrun.
  { intros w r. revert w. induction r as [| x r IH]; intros w Hwr Hw.
    - cbn [write_bytes exit_]. apply re_exit. intros d. cbn [pe_dev copy_env].
      destruct (decide (d = 0%nat)); [by left |].
      destruct (decide (d = 1%nat)); [exact I | by left].
    - cbn [write_bytes].
      eapply (re_write _ 2 0%nat [x :: r] (x :: r) [x]);
        [discriminate | apply copy_env_fd2 | reflexivity | by left | by exists r |].
      rewrite copy_env_out. cbn [length drop].
      apply (IH (w ++ [x])); [rewrite <- app_assoc; exact Hwr |].
      intros Hn. apply app_eq_nil in Hn as [_ Hn]. discriminate Hn. }
  unfold cat_dg_write. remember (sb "cat: write error" ++ [wl_nl]) as dg eqn:Hdg.
  destruct dg as [| x r]; [exfalso; apply (cat_dg_write_ne); unfold cat_dg_write; by rewrite <- Hdg |].
  cbn [write_bytes].
  eapply (re_write _ 2 0%nat [[]; x :: r] (x :: r) [x]);
    [discriminate | apply copy_env_fd2 | reflexivity | by right; left | by exists r |].
  rewrite copy_env_out. cbn [length drop].
  apply (Hrun [x] r); [unfold cat_dg_write; by rewrite <- Hdg | discriminate].
Qed.
