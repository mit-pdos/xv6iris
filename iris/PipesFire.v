(* ===================================================================== *)
(* PipesFire.v -- THE N-STAGE ROUND'S COMMITS, ADMITTED BY THE MODEL     *)
(* (design claude-notes/design/pipes-general.md SS2.2, SS3.2; cut C7;    *)
(* producer-generic in cut C9c', union.md S6; over the stage list in cut *)
(* G7, grep-pipes.md SS4).                                                *)
(*                                                                        *)
(* Pure.  The family ([PipeBothN]) reads the committed sources with every *)
(* uncommitted writer SILENT and asks that vector to be a complete run    *)
(* ([PipeBothNPure.runS]); a commit is admitted iff the vector with the   *)
(* committer's source is still one, or a committed writer's deposit       *)
(* refutes the committer's ([EXf]).  This file is that question at the    *)
(* pipeline [p | F1 | .. | Fn] of the filter stages [fs] ([cat] or [grep  *)
(* w]), for EITHER producer [p] (echo, or [cat f] at the content function *)
(* [fc]), read off the VALUES:                                            *)
(*                                                                        *)
(*   [real] / [realT]  a vector is a run / a terminal vector iff its      *)
(*                     values are what the stages may print and the one  *)
(*                     data demand -- the last stage's content -- is met  *)
(*                     by the stages above it ([run_real] / [real_run],   *)
(*                     [terms_realT] / [realT_terms]);                    *)
(*   [fire_nt] / [fire_t1] / [fire_t2]  every commit the round's          *)
(*                     processes make keeps the vector real (or           *)
(*                     terminal), or meets a committed writer [EXf]       *)
(*                     names.                                            *)
(*                                                                        *)
(* The exclusions [EXf] are design SS2.2's: content against a FAILED      *)
(* stage -- an exec failure, or the [cat f] producer's refused open, both *)
(* of which leave the stage's output pipe untouched ([fail_src]) -- (the  *)
(* flow chain), a node's panic against the writers it never forked (the  *)
(* one-shots) -- and every source no process of the round commits        *)
(* ([gsrc]), whose deposit is unpayable.                                  *)
(*                                                                        *)
(* THE FILTERS (grep-pipes SS4).  Every content of the union is one line  *)
(* ([GrepFilt.oneline]), and on one line a filter is a GATE: what it owes *)
(* of a prefix [D] of the line is [D] or nothing ([PipesDisc.fapp_pass]). *)
(* So the last stage's content, if any, is the line itself or (behind a   *)
(* halted cat, the loose corner) a prefix of it, and it came down the     *)
(* chain through filters that each pass it.  A stage's exec diagnostic is *)
(* its program's ([dg_st]); only a CAT halts with [cat: write error]      *)
(* ([halts_at]); the content writer commits the line only where every     *)
(* filter passes it ([fire_src]'s [passes]).                              *)
(*                                                                        *)
(* THE CAT PRODUCER (union.md S3/S6).  [cat f] prints [cat: cannot open   *)
(* f] when its open is refused (never writing: [WrNone], paired with an   *)
(* end of file at the empty prefix), and [cat: write error] when its      *)
(* reader went -- the ruled corner (B) at the producer itself, so a       *)
(* halted [cat f] may sit beside any printed prefix already at TWO        *)
(* stages.  It halts only where its file holds content ([prod_halts]).    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import ProgTree ProgTreePipes PipesPair PipesDisc.
Require Import PipeBothNPure.
Require GrepFilt.
From stdpp Require Import list.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  0.  THE WRITERS, THE DIAGNOSTICS, THE EXCLUSIONS                      *)
(* ===================================================================== *)

Lemma wids_from_elem (k n : nat) (w : wid) :
  w ∈ wids_from k n <->
  match w with WSh j | WLeft j => k <= j < k + n | WLast => True end.
Proof using.
  revert k. induction n as [| n IH]; intros k; cbn [wids_from].
  - rewrite elem_of_list_singleton. destruct w; split; try lia; try done.
  - rewrite !elem_of_cons, IH. destruct w as [j | j |]; split.
    + intros [Hq | [Hq | Hq]]; [injection Hq as ->; lia | discriminate | lia].
    + intros Hj. destruct (decide (j = k)) as [-> | Hne]; [by left | right; right; lia].
    + intros [Hq | [Hq | Hq]]; [discriminate | injection Hq as ->; lia | lia].
    + intros Hj. destruct (decide (j = k)) as [-> | Hne]; [by right; left | right; right; lia].
    + intros _. done.
    + intros _. by right; right.
Qed.

Lemma wids_elem (n : nat) (w : wid) :
  w ∈ wids n <-> match w with WSh j | WLeft j => j < n | WLast => True end.
Proof using. unfold wids. rewrite wids_from_elem. destruct w; lia || done. Qed.

(* ---- THE STAGES' FILTERS: stage [j] (1 <= j <= length fs) runs the
        [j]-th filter of the line; [PipeBothNPure.lfilt] at the line's
        list is this, by its definition ---- *)
Definition sfilt (fs : list filt) (j : nat) : filt := nth (j - 1) fs FCat.

Lemma lfilt_sfilt (l : pline') (j : nat) : lfilt l j = sfilt (lfilts l) j.
Proof using. reflexivity. Qed.

(* the filters of stages [j .. j + m], as a list *)
Definition subf (F : nat -> filt) (j m : nat) : list filt := map F (seq j (S m)).

Lemma subf_0 (F : nat -> filt) (j : nat) : subf F j 0 = [F j].
Proof using. reflexivity. Qed.

Lemma subf_S (F : nat -> filt) (j m : nat) : subf F j (S m) = F j :: subf F (S j) m.
Proof using. reflexivity. Qed.

Lemma map_lookup_opt {A B : Type} (f : A -> B) (l : list A) (k : nat) :
  map f l !! k = f <$> (l !! k).
Proof using.
  revert k. induction l as [| x l IH]; intros [| k]; [done | done | done |].
  exact (IH k).
Qed.

Lemma subf_fs (fs : list filt) : fs <> [] -> fs = subf (sfilt fs) 1 (length fs - 1).
Proof using.
  intros Hne. apply list_eq. intros i. unfold subf.
  rewrite map_lookup_opt.
  assert (Hl : length fs <> 0) by (destruct fs; [done | cbn; lia]).
  destruct (decide (i < length fs)) as [Hi | Hi].
  - rewrite lookup_seq_lt; [| lia]. cbn [fmap option_fmap option_map].
    destruct (lookup_lt_is_Some_2 fs i Hi) as [x Hx]. rewrite Hx. f_equal.
    unfold sfilt. replace (1 + i - 1) with i by lia. symmetry. exact (nth_lookup_Some _ _ _ _ Hx).
  - rewrite (lookup_ge_None_2 fs i); [| lia]. rewrite lookup_seq_ge; [reflexivity | lia].
Qed.

(* EVERY FILTER PASSES THE LINE, stage by stage *)
Lemma passes_sfilt (fs : list filt) (L : bytes) :
  passes fs L <-> forall i, 1 <= i <= length fs -> fapp (sfilt fs i) L = L.
Proof using.
  unfold passes. rewrite Forall_lookup. split.
  - intros H i Hi. destruct (lookup_lt_is_Some_2 fs (i - 1) ltac:(lia)) as [x Hx].
    unfold sfilt. rewrite (nth_lookup_Some _ _ _ _ Hx). exact (H _ _ Hx).
  - intros H i x Hx. pose proof (lookup_lt_Some _ _ _ Hx) as Hlt.
    pose proof (H (S i) ltac:(lia)) as Hp. unfold sfilt in Hp.
    replace (S i - 1) with i in Hp by lia. rewrite (nth_lookup_Some _ _ _ _ Hx) in Hp. exact Hp.
Qed.

(* sh's [exec %s failed] at stage [k]: argv[0] is the producer's command
   at stage 0 ([PipesDisc.st_dg_exec]) and the stage's program below it *)
Definition dg_st (p : producer) (fs : list filt) (k : nat) : list (bv 8) :=
  match k with O => st_dg_exec (SProd p) | S _ => filt_dg_exec (sfilt fs k) end.

(* the last stage's *)
Definition ldg (fs : list filt) : list (bv 8) := filt_dg_exec (sfilt fs (length fs)).

(* the producer's OTHER failure that writes nothing: [cat f]'s refused
   open ([cat.c]'s [cannot open]); echo has none *)
Definition prod_open (p : producer) : option (list (bv 8)) :=
  match p with PrEcho _ => None | PrCatF f => Some (cat_dg_open f) end.

(* the producer may halt with [cat: write error]: a cat whose file has a
   content ([PipesDisc.so_catf_halt]'s premise) *)
Definition prod_halts (fc : bytes -> option bytes) (p : producer) : Prop :=
  match p with PrEcho _ => False | PrCatF f => is_Some (fc f) end.

Global Instance prod_halts_dec fc p : Decision (prod_halts fc p).
Proof using. destruct p; cbn [prod_halts]; apply _. Defined.

Lemma prod_halts_cat fc p : prod_halts fc p -> prod_cat p = true.
Proof using. destruct p; cbn [prod_halts prod_cat]; [intros [] | reflexivity]. Qed.

(* WHO MAY HALT with [cat: write error]: the [cat f] producer where its
   file holds content, and a middle CAT (a grep's halt prints nothing) *)
Definition halts_at (fc : bytes -> option bytes) (p : producer) (fs : list filt) (k : nat) : Prop :=
  match k with O => prod_halts fc p | S _ => sfilt fs k = FCat end.

Global Instance halts_at_dec fc p fs k : Decision (halts_at fc p fs k).
Proof using. destruct k; cbn [halts_at]; apply _. Defined.

(* A FAILED STAGE: its exec failed, or (the producer) its open was
   refused.  Either way it never touched its output pipe. *)
Definition fail_src (p : producer) (fs : list filt) (k : nat) (s : list (bv 8)) : Prop :=
  s = dg_st p fs k \/ (k = 0 /\ prod_open p = Some s).

Global Instance fail_src_dec p fs k s : Decision (fail_src p fs k s).
Proof using. unfold fail_src. apply _. Defined.

Lemma filt_dg_exec_ne (F : filt) : filt_dg_exec F <> [].
Proof using. destruct F; vm_compute; discriminate. Qed.

Lemma filt_dg_exec_ne_write (F : filt) : filt_dg_exec F <> cat_dg_write.
Proof using. destruct F; vm_compute; discriminate. Qed.

Lemma dg_st_ne (p : producer) (fs : list filt) (k : nat) : dg_st p fs k <> [].
Proof using. destruct k as [| k]; [destruct p; vm_compute; discriminate | apply filt_dg_exec_ne]. Qed.

Lemma dg_st_ne_write (p : producer) (fs : list filt) (k : nat) : dg_st p fs k <> cat_dg_write.
Proof using.
  destruct k as [| k]; [destruct p; vm_compute; discriminate | apply filt_dg_exec_ne_write].
Qed.

Lemma cat_dg_open_ne (f : bytes) : cat_dg_open f <> [].
Proof using. unfold cat_dg_open. intros Hq. apply app_eq_nil in Hq as [Hq _]. discriminate Hq. Qed.

Lemma cat_dg_open_ne_write (f : bytes) : cat_dg_open f <> cat_dg_write.
Proof using.
  intros Hq. apply (f_equal (fun l : list (bv 8) => l !! 5)) in Hq.
  vm_compute in Hq. discriminate Hq.
Qed.

Lemma fail_src_ne (p : producer) (fs : list filt) (k : nat) (s : list (bv 8)) :
  fail_src p fs k s -> s <> [].
Proof using.
  intros [-> | [_ Ho]]; [exact (dg_st_ne p fs k) |].
  destruct p as [ws | f]; cbn [prod_open] in Ho; [discriminate Ho |].
  injection Ho as <-. exact (cat_dg_open_ne f).
Qed.

Lemma fail_src_ne_write (p : producer) (fs : list filt) (k : nat) (s : list (bv 8)) :
  fail_src p fs k s -> s <> cat_dg_write.
Proof using.
  intros [-> | [_ Ho]]; [exact (dg_st_ne_write p fs k) |].
  destruct p as [ws | f]; cbn [prod_open] in Ho; [discriminate Ho |].
  injection Ho as <-. exact (cat_dg_open_ne_write f).
Qed.

(* below the producer a failed stage is exactly the exec failure of its
   program *)
Lemma fail_src_S (p : producer) (fs : list filt) (k : nat) (s : list (bv 8)) :
  fail_src p fs (S k) s <-> s = filt_dg_exec (sfilt fs (S k)).
Proof using. unfold fail_src. cbn [dg_st]. split; [intros [H | [H _]]; [exact H | discriminate H] | by left]. Qed.

Lemma dg_pipe_ne_fork : dg_pipe_b <> alt_forkc.
Proof using. vm_compute. discriminate. Qed.

Lemma dg_pipe_b_len : length dg_pipe_b = 5.
Proof using. vm_compute. reflexivity. Qed.

Lemma alt_forkc_len : length alt_forkc = 7.
Proof using. vm_compute. reflexivity. Qed.

Lemma dg_execL_ne_R : dg_execL <> dg_execR.
Proof using. vm_compute. discriminate. Qed.

Definition panic_src (s : list (bv 8)) : Prop := s = dg_pipe_b \/ s = alt_forkc.

(* THE COMMITS the round's processes make, source by writer: a node's two
   panics; a stage's failure, or a cat's write error (the producer's only
   where it can halt, a grep never); the last stage's content -- the line,
   where every filter of the line passes it -- or its exec failure *)
Definition fire_src (fc : bytes -> option bytes) (p : producer) (fs : list filt)
    (L : list (bv 8)) (w : wid) (s : list (bv 8)) : Prop :=
  match w with
  | WSh _ => panic_src s
  | WLeft k => fail_src p fs k s \/ (halts_at fc p fs k /\ s = cat_dg_write)
  | WLast => (s = L /\ L <> [] /\ passes fs L) \/ s = ldg fs
  end.

Global Instance fire_src_dec fc p fs L w s : Decision (fire_src fc p fs L w s).
Proof using. destruct w; unfold fire_src, panic_src, passes; apply _. Defined.

(* a source no process of the round commits *)
Definition gsrc (fc : bytes -> option bytes) (p : producer) (fs : list filt) (L : list (bv 8))
    (w : wid) (s : list (bv 8)) : Prop :=
  s <> [] /\ ~ fire_src fc p fs L w s.

(* THE EXCLUSIONS a commit of source [s] by writer [w] spends (design
   SS2.2): every committed writer [w'] at [s'] whose deposit refutes this
   one's.  [nc] is the number of filter stages, [L] the line's content. *)
Definition EXf (fc : bytes -> option bytes) (p : producer) (fs : list filt) (nc : nat)
    (L : list (bv 8)) (w : wid) (s : list (bv 8)) (w' : wid) (s' : list (bv 8)) : Prop :=
  gsrc fc p fs L w' s'
  \/ match w with
     | WSh k =>
         (exists j, w' = WSh j /\ (j < nc)%nat /\ j <> k /\ panic_src s')
         \/ (exists j, w' = WLeft j /\ (j < nc)%nat
               /\ (if bool_decide (s = dg_pipe_b) then (k <= j)%nat else (k < j)%nat)
               /\ s' <> [])
         \/ (w' = WLast /\ s' <> [])
     | WLeft k =>
         (exists j, w' = WSh j /\ (j < nc)%nat
               /\ (((j <= k)%nat /\ s' = dg_pipe_b) \/ ((j < k)%nat /\ s' = alt_forkc)))
         \/ (fail_src p fs k s /\ w' = WLast /\ s' = L /\ L <> [] /\ L <> ldg fs)
     | WLast =>
         (exists j, w' = WSh j /\ (j < nc)%nat /\ panic_src s')
         \/ (s = L /\ L <> [] /\ L <> ldg fs
             /\ exists j, w' = WLeft j /\ (j < nc)%nat /\ fail_src p fs j s')
     end.

(* ---- a middle stage's outcomes, at any filter ---- *)
Lemma stage_out_mid_f_inv fc L F so :
  stage_out fc L (SMid F) so ->
  so = MkSO (filt_dg_exec F) (Some RdGone) (Some WrNone) \/ so = MkSO [] (Some RdGone) (Some WrNone)
  \/ (exists D, D `prefix_of` L /\ so = MkSO [] (Some (RdEof D)) (Some (WrAll (fapp F D))))
  \/ (F = FCat /\ exists D, D `prefix_of` L /\ so = MkSO cat_dg_write (Some RdGone) (Some (WrHalt D)))
  \/ (exists w D W, F = FGrep w /\ D `prefix_of` L /\ so = MkSO [] (Some (RdEof D)) (Some (WrHalt W))).
Proof using.
  intros H. remember (SMid F) as st eqn:Hst.
  destruct H as [st' | st' | | | | | | F' D HD | D HD | w D W HD HW |]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right; left. exists D. split; [exact HD | reflexivity].
  - injection Hst as <-. right; right; right; left. split; [reflexivity |]. exists D. split; [exact HD | reflexivity].
  - injection Hst as <-. right; right; right; right. exists w, D, W. split_and!; [reflexivity | exact HD | reflexivity].
Qed.

(* ===================================================================== *)
(*  1.  THE PIPELINE'S RUNS, READ OFF THE VALUES                          *)
(* ===================================================================== *)

Section real.
  Context (fc : bytes -> option bytes) (p : producer) (fs : list filt).
  Local Notation L := (prod_content fc p).
  Local Notation n := (length fs).
  Local Notation F := (sfilt fs).

  (* what each stage may print on the console *)
  Definition aP (s : bytes) : Prop :=
    s = [] \/ fail_src p fs 0 s \/ (prod_halts fc p /\ s = cat_dg_write).
  Definition aM (G : filt) (s : bytes) : Prop :=
    s = [] \/ s = filt_dg_exec G \/ (G = FCat /\ s = cat_dg_write).
  Definition aT (G : filt) (s : bytes) : Prop :=
    s = filt_dg_exec G \/ exists D, D `prefix_of` L /\ s = fapp G D.
  Definition aS (j : nat) (s : bytes) : Prop := match j with O => aP s | S _ => aM (F j) s end.

  (* THE ONE DATA DEMAND: the last stage's content [D] came down the
     chain -- from a cat that halted (the ruled corner: a middle cat, or
     the [cat f] producer), with only silent stages below it each passing
     [D], or from the producer itself through silent stages each passing
     the line *)
  Definition upok (v : wid -> bytes) (D : bytes) : Prop :=
    (exists i, i < n /\ v (WLeft i) = cat_dg_write
               /\ (forall i', i < i' < n -> v (WLeft i') = [])
               /\ (forall j, i < j <= n -> fapp (F j) D = D))
    \/ ((forall i, i < n -> v (WLeft i) = []) /\ D = L /\ passes fs L).

  (* node [k]'s pipe(2) failed *)
  Definition realP (v : wid -> bytes) (k : nat) : Prop :=
    k < n /\ v (WSh k) = dg_pipe_b /\ (forall j, j < n -> j <> k -> v (WSh j) = [])
    /\ (forall j, k <= j < n -> v (WLeft j) = []) /\ v WLast = []
    /\ (forall j, j < k -> aS j (v (WLeft j))).

  (* the round ran *)
  Definition realN (v : wid -> bytes) : Prop :=
    (forall j, j < n -> v (WSh j) = []) /\ (forall j, j < n -> aS j (v (WLeft j)))
    /\ aT (F n) (v WLast)
    /\ (forall D, v WLast = D -> D <> [] -> D <> ldg fs -> upok v D).

  Definition real (v : wid -> bytes) : Prop := (exists k, realP v k) \/ realN v.

  (* node [k]'s fork failed: the TERMINAL vector *)
  Definition realT (v : wid -> bytes) (k : nat) : Prop :=
    k < n /\ v (WSh k) = alt_forkc /\ (forall j, j <> k -> v (WSh j) = [])
    /\ (forall j, k < j -> v (WLeft j) = []) /\ v WLast = []
    /\ (forall j, j <= k -> aS j (v (WLeft j))).

  (* ---- the stages' outcomes, chosen ---- *)
  Definition so_prod (s : bytes) : st_out :=
    if decide (s = cat_dg_write) then MkSO cat_dg_write None (Some (WrHalt []))
    else MkSO s None (Some WrNone).
  Definition so_mid (s : bytes) : st_out :=
    if decide (s = cat_dg_write) then MkSO cat_dg_write (Some RdGone) (Some (WrHalt []))
    else MkSO s (Some RdGone) (Some WrNone).
  Definition so_copy (G : filt) (D : bytes) : st_out :=
    MkSO [] (Some (RdEof D)) (Some (WrAll (fapp G D))).
  Definition so_lastd (G : filt) (s : bytes) : st_out :=
    if decide (s = filt_dg_exec G) then MkSO (filt_dg_exec G) (Some RdGone) None
    else if decide (s = []) then MkSO [] (Some RdGone) None
    else MkSO s (Some (RdEof s)) None.

  Lemma so_prod_ok s : aP s -> stage_out fc L (SProd p) (so_prod s).
  Proof using.
    unfold so_prod. intros [-> | [[-> | [_ Ho]] | [Hh ->]]].
    - rewrite decide_False; [exact (so_silent fc L (SProd p)) | vm_compute; discriminate].
    - rewrite decide_False; [exact (so_exec fc L (SProd p)) | exact (dg_st_ne_write p fs 0)].
    - destruct p as [ws | f]; cbn [prod_open] in Ho; [discriminate Ho |]. injection Ho as <-.
      rewrite decide_False; [exact (so_catf_open fc _ f) | exact (cat_dg_open_ne_write f)].
    - rewrite decide_True; [| reflexivity].
      destruct p as [ws | f]; cbn [prod_halts] in Hh; [destruct Hh |].
      destruct Hh as [c Hc].
      apply (so_catf_halt fc _ f []); [cbn [prod_content]; rewrite Hc; reflexivity | apply prefix_nil].
  Qed.

  Lemma so_prod_cons s : so_cons (so_prod s) = s.
  Proof using. unfold so_prod. case_decide as Hw; [by subst s | reflexivity]. Qed.

  (* the producer wrote the whole line (echo's words, or f's content) *)
  Lemma so_whole_ok : L <> [] -> stage_out fc L (SProd p) (MkSO [] None (Some (WrAll L))).
  Proof using.
    destruct p as [ws | f]; cbn [prod_content].
    - intros _. exact (so_echo fc _ ws eq_refl).
    - destruct (fc f) as [c |] eqn:Hf; cbn [default]; intros Hne;
        [exact (so_catf fc c f Hf) | by destruct Hne].
  Qed.

  Lemma so_mid_ok G s : aM G s -> stage_out fc L (SMid G) (so_mid s).
  Proof using.
    intros Hs. unfold so_mid. case_decide as Hw.
    - subst s. destruct Hs as [Hq | [Hq | [-> _]]].
      + exfalso. revert Hq. vm_compute. discriminate.
      + by destruct (filt_dg_exec_ne_write G (eq_sym Hq)).
      + exact (so_mid_halt fc L [] (prefix_nil _)).
    - destruct Hs as [-> | [-> | [_ ->]]]; [| | by destruct Hw].
      + exact (so_silent fc L (SMid G)).
      + exact (so_exec fc L (SMid G)).
  Qed.

  Lemma so_mid_cons s : so_cons (so_mid s) = s.
  Proof using. unfold so_mid. case_decide as Hw; [by subst s | reflexivity]. Qed.

  Lemma so_mid_rd s : rd_of (so_mid s) = RdGone.
  Proof using. unfold so_mid. case_decide; reflexivity. Qed.

  (* a stage that printed a nonempty prefix [s] of the line read it and
     passed it *)
  Lemma so_lastd_ok G s :
    GrepFilt.oneline L -> aT G s -> stage_out fc L (SLast G) (so_lastd G s).
  Proof using.
    intros HL Hs. unfold so_lastd. case_decide as He; [exact (so_exec fc L (SLast G)) |].
    case_decide as Hz; [exact (so_silent fc L (SLast G)) |].
    destruct Hs as [Hs | (D & HD & ->)]; [by destruct He |].
    destruct (fapp_pass G L D HL HD Hz) as [HfD _]. rewrite HfD.
    pose proof (so_last_f fc L G D HD) as Hso. rewrite HfD in Hso. exact Hso.
  Qed.

  Lemma so_lastd_cons G s : so_cons (so_lastd G s) = s.
  Proof using.
    unfold so_lastd. case_decide as He; [by subst s |]. case_decide as Hz; [by subst s |].
    reflexivity.
  Qed.

  Lemma so_copy_ok G D : D `prefix_of` L -> stage_out fc L (SMid G) (so_copy G D).
  Proof using. intros HD. exact (so_mid_f fc L G D HD). Qed.

  (* a content the last stage printed through its filter is a prefix of
     the line it passes *)
  Lemma aT_content G D :
    GrepFilt.oneline L -> aT G D -> D <> [] -> D <> filt_dg_exec G ->
    D `prefix_of` L /\ fapp G D = D.
  Proof using.
    intros HL [Hq | (D' & HD' & ->)] Hne Hnx; [by destruct (Hnx Hq) |].
    destruct (fapp_pass G L D' HL HD' Hne) as [HfD _]. rewrite HfD. split; [exact HD' | exact HfD].
  Qed.
End real.

(* a gone reader pairs with every writer *)
Lemma pipe_pairB_gone (L : bytes) (wc : bool) (w : wr_out) : pipe_pairB L wc w RdGone.
Proof using. destruct w; exact I. Qed.

(* ---- building the suffix from an outcome per stage ---- *)
Section build.
  Context (fc : bytes -> option bytes) (p : producer) (F : nat -> filt).
  Local Notation L := (prod_content fc p).

  Lemma rep_S2 {A : Type} (x : A) (m : nat) :
    replicate (2 * S m) x = x :: replicate (2 * m + 1) x.
  Proof using. replace (2 * S m) with (S (2 * m + 1)) by lia. reflexivity. Qed.

  Lemma wids_from_nil (src : wid -> bytes) (k m : nat) :
    (forall j, k <= j < k + m -> src (WSh j) = [] /\ src (WLeft j) = []) -> src WLast = [] ->
    src <$> wids_from k m = replicate (2 * m + 1) [].
  Proof using.
    revert k. induction m as [| m IH]; intros k Hs Hl; cbn [wids_from].
    - rewrite fmap_cons, fmap_nil, Hl. reflexivity.
    - destruct (Hs k ltac:(lia)) as [H1 H2]. rewrite !fmap_cons, H1, H2.
      rewrite (IH (S k)); [| intros j Hj; apply Hs; lia | exact Hl].
      replace (2 * S m + 1) with (S (S (2 * m + 1))) by lia. reflexivity.
  Qed.

  Lemma sfx_build (v : wid -> bytes) (so : nat -> st_out) (m : nat) :
    forall (j : nat) (win : wr_out) (wc : bool),
    (forall i, j <= i < j + m ->
       v (WSh i) = [] /\ stage_out fc L (SMid (F i)) (so i) /\ so_cons (so i) = v (WLeft i)) ->
    stage_out fc L (SLast (F (j + m))) (so (j + m)) -> so_cons (so (j + m)) = v WLast ->
    pipe_pairB L wc win (rd_of (so j)) ->
    (forall i, j <= i < j + m -> pipe_pairB L (filt_is_cat (F i)) (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (subf F j m) win wc (v <$> wids_from j m).
  Proof using.
    induction m as [| m IH]; intros j win wc Hst Hl Hlc Hp Hps.
    - rewrite Nat.add_0_r in Hl, Hlc. cbn [wids_from]. rewrite fmap_cons, fmap_nil, subf_0.
      rewrite <- Hlc. exact (srv_last fc L (F j) win wc (so j) Hl Hp).
    - cbn [wids_from]. rewrite !fmap_cons, subf_S.
      destruct (Hst j ltac:(lia)) as (Hsh & Hso & Hc). rewrite Hsh, <- Hc.
      apply (srv_node fc L (F j) (F (S j)) (map F (seq (S (S j)) m)) win wc (so j) _ Hso Hp).
      change (F (S j) :: map F (seq (S (S j)) m)) with (subf F (S j) m).
      apply (IH (S j) (wr_of (so j)) (filt_is_cat (F j))).
      + intros i Hi. apply Hst. lia.
      + replace (S j + m) with (j + S m) by lia. exact Hl.
      + replace (S j + m) with (j + S m) by lia. exact Hlc.
      + exact (Hps j ltac:(lia)).
      + intros i Hi. apply Hps. lia.
  Qed.

  (* ...and with node [j + d]'s pipe(2) failing *)
  Lemma sfx_build_pf (v : wid -> bytes) (so : nat -> st_out) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool),
    d < S m ->
    (forall i, j <= i < j + d ->
       v (WSh i) = [] /\ stage_out fc L (SMid (F i)) (so i) /\ so_cons (so i) = v (WLeft i)) ->
    v (WSh (j + d)) = dg_pipe_b ->
    (forall i, j + d < i < j + S m -> v (WSh i) = []) ->
    (forall i, j + d <= i < j + S m -> v (WLeft i) = []) -> v WLast = [] ->
    (0 < d -> pipe_pairB L wc win (rd_of (so j))) ->
    (forall i, j <= i -> S i < j + d -> pipe_pairB L (filt_is_cat (F i)) (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (subf F j (S m)) win wc (v <$> wids_from j (S m)).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Hst Hpf Hsh Hlf Hlast Hp Hps.
    - rewrite Nat.add_0_r in Hpf, Hsh, Hlf. cbn [wids_from]. rewrite !fmap_cons.
      rewrite Hpf, (Hlf j ltac:(lia)).
      assert (Hrest : v <$> wids_from (S j) m = replicate (2 * m + 1) []).
      { apply (wids_from_nil v (S j) m); [| exact Hlast].
        intros i Hi. split; [apply Hsh | apply Hlf]; lia. }
      rewrite Hrest.
      rewrite <- rep_S2.
      pose proof (srv_pipe_fail fc L (F j) (F (S j)) (map F (seq (S (S j)) m)) win wc) as Hpf'.
      cbn [length] in Hpf'. rewrite length_map, length_seq in Hpf'.
      exact Hpf'.
    - destruct m as [| m]; [lia |].
      cbn [wids_from]. rewrite !fmap_cons.
      destruct (Hst j ltac:(lia)) as (Hsj & Hso & Hc). rewrite Hsj, <- Hc.
      apply (srv_node fc L (F j) (F (S j)) (map F (seq (S (S j)) (S m))) win wc (so j) _ Hso (Hp ltac:(lia))).
      change (F (S j) :: map F (seq (S (S j)) (S m))) with (subf F (S j) (S m)).
      apply (IH (S j) m (wr_of (so j)) (filt_is_cat (F j)) ltac:(lia)).
      + intros i Hi. apply Hst. lia.
      + replace (S j + d) with (j + S d) by lia. exact Hpf.
      + intros i Hi. apply Hsh. lia.
      + intros i Hi. apply Hlf. lia.
      + exact Hlast.
      + intros Hd0. apply Hps; lia.
      + intros i Hi1 Hi2. apply Hps; lia.
  Qed.
End build.

(* ---- the runs' shapes, one constructor at a time ---- *)
Section inv.
  Context (fc : bytes -> option bytes) (L : bytes) (F : nat -> filt).

  Lemma sfx_runV_1_inv j win wc vs :
    sfx_runV fc L (subf F j 0) win wc vs ->
    exists so, vs = [so_cons so] /\ stage_out fc L (SLast (F j)) so /\ pipe_pairB L wc win (rd_of so).
  Proof using.
    intros H. remember (subf F j 0) as mm eqn:Hmm. rewrite subf_0 in Hmm.
    destruct H as [G win' wc' so Hso Hp | G G' gs win' wc' | G G' gs win' wc' so vs' Hso Hp Hr];
      [| discriminate Hmm | discriminate Hmm].
    injection Hmm as ->. exists so. done.
  Qed.

  Lemma sfx_runV_SS_inv j m win wc a b vs :
    sfx_runV fc L (subf F j (S m)) win wc (a :: b :: vs) ->
    (a = dg_pipe_b /\ b :: vs = replicate (2 * S m) [])
    \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc L (SMid (F j)) so
                  /\ pipe_pairB L wc win (rd_of so)
                  /\ sfx_runV fc L (subf F (S j) m) (wr_of so) (filt_is_cat (F j)) vs.
  Proof using.
    intros H. remember (subf F j (S m)) as mm eqn:Hmm. remember (a :: b :: vs) as l eqn:Hl.
    unfold subf in Hmm. cbn [seq map] in Hmm.
    destruct H as [G win' wc' so Hso Hp | G G' gs win' wc' | G G' gs win' wc' so vs' Hso Hp Hr].
    - discriminate Hmm.
    - injection Hmm as -> -> ->. cbn [length] in Hl. rewrite length_map, length_seq in Hl.
      left. split; congruence.
    - injection Hmm as -> -> ->. injection Hl as Ha Hb Hvs. subst. right. exists so.
      split_and!; [reflexivity | reflexivity | exact Hso | exact Hp | exact Hr].
  Qed.

  Lemma replicate_nil_elem (vs : list bytes) (k : nat) (x : bytes) :
    vs = replicate k [] -> x ∈ vs -> x = [].
  Proof using. intros -> Hx. by apply elem_of_replicate in Hx as [-> _]. Qed.
End inv.

Section real2.
  Context (fc : bytes -> option bytes) (p : producer) (fs : list filt).
  Hypothesis HL1 : GrepFilt.oneline (prod_content fc p).
  Local Notation L := (prod_content fc p).
  Local Notation F := (sfilt fs).
  Local Notation aT := (aT fc p).

  (* the suffix from stage [j], [m] middle stages above the last *)
  Definition sreal (v : wid -> bytes) (j m : nat) (win : wr_out) (wc : bool) : Prop :=
    (exists k, j <= k < j + m /\ v (WSh k) = dg_pipe_b
       /\ (forall i, j <= i < k -> v (WSh i) = [] /\ aM (F i) (v (WLeft i)))
       /\ (forall i, k < i < j + m -> v (WSh i) = [])
       /\ (forall i, k <= i < j + m -> v (WLeft i) = []) /\ v WLast = [])
    \/ ((forall i, j <= i < j + m -> v (WSh i) = [] /\ aM (F i) (v (WLeft i))) /\ aT (F (j + m)) (v WLast)
        /\ (forall D, v WLast = D -> D <> [] -> D <> filt_dg_exec (F (j + m)) ->
              (exists i, j <= i < j + m /\ v (WLeft i) = cat_dg_write
                         /\ (forall i', i < i' < j + m -> v (WLeft i') = [])
                         /\ (forall i', i < i' <= j + m -> fapp (F i') D = D))
              \/ ((forall i, j <= i < j + m -> v (WLeft i) = [])
                  /\ (forall i', j <= i' <= j + m -> fapp (F i') D = D)
                  /\ pipe_pairB L wc win (RdEof D)))).

  Lemma fmap_wids_nil (v : wid -> bytes) (k m : nat) (x : wid) :
    (v <$> wids_from k m) = replicate (2 * m + 1) [] -> x ∈ wids_from k m -> v x = [].
  Proof using.
    intros Heq Hx. apply (replicate_nil_elem (v <$> wids_from k m) (2 * m + 1)); [exact Heq |].
    apply elem_of_list_fmap. by exists x.
  Qed.

  (* a middle stage's print, read at its filter *)
  Lemma mid_aM (G : filt) (so : st_out) :
    stage_out fc L (SMid G) so -> aM G (so_cons so).
  Proof using.
    intros Hso. unfold aM.
    destruct (stage_out_mid_f_inv fc L G so Hso)
      as [-> | [-> | [(D & _ & ->) | [(HG & D & _ & ->) | (w & D & W & _ & _ & ->)]]]]; cbn [so_cons].
    - right; left. reflexivity.
    - left. reflexivity.
    - left. reflexivity.
    - right; right. split; [exact HG | reflexivity].
    - left. reflexivity.
  Qed.

  Lemma sfx_inv (v : wid -> bytes) (m : nat) :
    forall (j : nat) (win : wr_out) (wc : bool),
    sfx_runV fc L (subf F j m) win wc (v <$> wids_from j m) -> sreal v j m win wc.
  Proof using HL1.
    induction m as [| m IH]; intros j win wc H.
    - cbn [wids_from] in H. rewrite fmap_cons, fmap_nil in H.
      destruct (sfx_runV_1_inv fc L F j win wc _ H) as (so & Heq & Hso & Hp).
      injection Heq as Hv. right. split; [intros i Hi; lia |]. rewrite Nat.add_0_r.
      destruct (stage_out_last_f_inv fc L (F j) so Hso) as [-> | [-> | (D & HD & ->)]];
        cbn [so_cons rd_of so_rd] in Hv, Hp; rewrite Hv.
      + split; [left; reflexivity | intros D -> _ HD; by destruct HD].
      + split; [right; exists []; split; [apply prefix_nil | rewrite fapp_nil; reflexivity] |].
        intros D -> HD; by destruct HD.
      + split; [right; exists D; split; [exact HD | reflexivity] |].
        intros D' <- Hne _. right.
        destruct (fapp_pass (F j) L D HL1 HD Hne) as [HfD _].
        split; [intros i Hi; lia |]. split.
        * intros i' Hi'. assert (i' = j) as -> by lia. rewrite HfD. exact HfD.
        * rewrite HfD. exact Hp.
    - cbn [wids_from] in H. rewrite !fmap_cons in H.
      destruct (sfx_runV_SS_inv fc L F j m win wc _ _ _ H)
        as [[Hsh Hrest] | (so & Hsh & Hl & Hso & Hp & Hr)].
      + (* node j's pipe(2) failed *)
        assert (Hall : forall x, x ∈ wids_from (S j) m -> v x = []).
        { intros x Hx. apply (fmap_wids_nil v (S j) m x); [| exact Hx].
          rewrite rep_S2 in Hrest. by injection Hrest as _ ->. }
        assert (Hlj : v (WLeft j) = []).
        { rewrite rep_S2 in Hrest. by injection Hrest as ->. }
        left. exists j. split; [lia |]. split; [exact Hsh |].
        split; [intros i Hi; lia |].
        split; [intros i Hi; apply Hall, wids_from_elem; lia |].
        split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne];
                  [exact Hlj | apply Hall, wids_from_elem; lia] |].
        apply Hall, wids_from_elem. done.
      + (* it forked: stage j, then the suffix below *)
        pose proof (IH (S j) (wr_of so) (filt_is_cat (F j)) Hr) as Hs.
        assert (Hj : v (WSh j) = [] /\ aM (F j) (v (WLeft j))).
        { split; [exact Hsh |]. rewrite Hl. exact (mid_aM (F j) so Hso). }
        destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
        * left. exists k. split; [lia |]. split; [exact Hpf |].
          split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne]; [exact Hj | apply Hab; lia] |].
          split; [intros i Hi; apply Hbl; lia |].
          split; [intros i Hi; apply Hlf; lia | exact Hlast].
        * right. split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne];
                          [exact Hj | apply Hab; lia] |].
          replace (j + S m) with (S j + m) by lia.
          split; [exact HT |].
          intros D HD Hne Hnx. destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib & Hif) | (Hall & Hfa & Hpp)].
          -- left. exists i. split; [lia |]. split; [exact Hic |]. split; [| exact Hif].
             intros i' Hi'. apply Hib. lia.
          -- destruct (stage_out_mid_f_inv fc L (F j) so Hso)
               as [Hso' | [Hso' | [(D0 & HD0 & Hso') | [(HG & D0 & HD0 & Hso') | (w & D0 & W & HG & HD0 & Hso')]]]];
               subst so; cbn [wr_of so_wr rd_of so_rd so_cons pipe_pairB pipe_pair] in *.
             ++ exfalso. apply Hne. exact Hpp.
             ++ exfalso. apply Hne. exact Hpp.
             ++ (* it copied: what it wrote whole is what it read *)
                right. subst D. rewrite Hpp in Hne, Hfa |- *.
                destruct (fapp_pass (F j) L D0 HL1 HD0 Hne) as [HfD _]. rewrite HfD in Hne, Hfa |- *.
                split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne']; [exact Hl | apply Hall; lia] |].
                split; [| exact Hp].
                intros i' Hi'. destruct (decide (i' = j)) as [-> | Hne']; [exact HfD | apply Hfa; lia].
             ++ (* a halted cat: the corner *)
                left. exists j. split; [lia |]. split; [exact Hl |].
                split; [intros i' Hi'; apply Hall; lia |].
                intros i' Hi'. apply Hfa. lia.
             ++ (* a halted grep pairs exactly, and a halt is no end of file *)
                exfalso. rewrite HG in Hpp. destruct Hpp as [Hq _]. cbn [filt_is_cat] in Hq.
                discriminate Hq.
  Qed.
End real2.

Lemma line_runV_SS_inv (fc : bytes -> option bytes) (p : producer) (fs : list filt) (a b : bytes)
    (vs : list bytes) :
  line_runV fc (LPipes p fs) (a :: b :: vs) ->
  (a = dg_pipe_b /\ b :: vs = replicate (2 * length fs) [])
  \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc (prod_content fc p) (SProd p) so
                /\ sfx_runV fc (prod_content fc p) fs (wr_of so) (prod_cat p) vs.
Proof using.
  intros H. remember (LPipes p fs) as l eqn:Hl. remember (a :: b :: vs) as ls eqn:Hls.
  destruct H as [ws' | ws' | ws' | p' fs' Hn' | p' fs' so vs' Hso Hr]; try discriminate Hl.
  - injection Hl as -> ->. left. split; congruence.
  - injection Hl as -> ->. injection Hls as Ha Hb Hvs. subst. right. exists so. done.
Qed.

Lemma aS_mid (fc : bytes -> option bytes) (p : producer) (fs : list filt) (i : nat) (s : bytes) :
  1 <= i -> aS fc p fs i s -> aM (sfilt fs i) s.
Proof using. intros Hi Hs. destruct i as [| i]; [lia | exact Hs]. Qed.

(* WHAT THE PRODUCER PRINTED, and what it did to its pipe *)
Lemma prod_aP (fc : bytes -> option bytes) (p : producer) (fs : list filt) (so : st_out) :
  stage_out fc (prod_content fc p) (SProd p) so -> aP fc p fs (so_cons so).
Proof using.
  intros Hso. unfold aP, fail_src. destruct p as [ws | f].
  - destruct (stage_out_echo_inv fc _ ws so Hso)
      as [-> | [-> | [(_ & ->) | (D & _ & _ & ->)]]]; cbn [so_cons dg_st st_dg_exec].
    + right; left; left. reflexivity.
    + left. reflexivity.
    + left. reflexivity.
    + left. reflexivity.
  - destruct (stage_out_catf_inv fc _ f so Hso)
      as [-> | [-> | [(_ & ->) | [(D & Hf & _ & ->) | ->]]]]; cbn [so_cons dg_st st_dg_exec].
    + right; left; left. reflexivity.
    + left. reflexivity.
    + left. reflexivity.
    + right; right. split; [exact (mk_is_Some _ _ Hf) | reflexivity].
    + right; left; right. split; reflexivity.
Qed.

(* the producer's write outcome against an end of file at a NONEMPTY
   prefix: it wrote the whole line silently, or it is a cat that halted *)
Lemma prod_pair_eof (fc : bytes -> option bytes) (p : producer) (so : st_out) (D : bytes) :
  stage_out fc (prod_content fc p) (SProd p) so -> D <> [] ->
  pipe_pairB (prod_content fc p) (prod_cat p) (wr_of so) (RdEof D) ->
  (so_cons so = [] /\ D = prod_content fc p) \/ so_cons so = cat_dg_write.
Proof using.
  intros Hso Hne Hp. destruct p as [ws | f].
  - destruct (stage_out_echo_inv fc _ ws so Hso)
      as [-> | [-> | [(_ & ->) | (D0 & _ & _ & ->)]]];
      cbn [so_cons wr_of so_wr pipe_pairB pipe_pair prod_cat] in Hp |- *.
    + by destruct (Hne Hp).
    + by destruct (Hne Hp).
    + left. split; [reflexivity | exact Hp].
    + destruct Hp as [Hf _]. discriminate Hf.
  - destruct (stage_out_catf_inv fc _ f so Hso)
      as [-> | [-> | [(_ & ->) | [(D0 & _ & _ & ->) | ->]]]];
      cbn [so_cons wr_of so_wr pipe_pairB pipe_pair prod_cat] in Hp |- *.
    + by destruct (Hne Hp).
    + by destruct (Hne Hp).
    + left. split; [reflexivity | exact Hp].
    + right. reflexivity.
    + by destruct (Hne Hp).
Qed.

(* a halted middle stage is a cat *)
Lemma aM_write (G : filt) : aM G cat_dg_write -> G = FCat.
Proof using.
  intros [Hq | [Hq | [HG _]]]; [revert Hq; vm_compute; discriminate | | exact HG].
  by destruct (filt_dg_exec_ne_write G (eq_sym Hq)).
Qed.


Section real3.
  Context (fc : bytes -> option bytes) (p : producer) (fs : list filt).
  Hypothesis Hn : fs <> [].
  Hypothesis HL1 : GrepFilt.oneline (prod_content fc p).
  Local Notation L := (prod_content fc p).
  Local Notation F := (sfilt fs).
  Local Notation lp := (LPipes p fs).

  Lemma len_S : exists m, length fs = S m.
  Proof using Hn. destruct fs as [| x l]; [done | by exists (length l)]. Qed.

  (* A RUN IS REAL *)
  Lemma run_real (v : wid -> bytes) : runN fc lp v -> real fc p fs v.
  Proof using Hn HL1.
    intros H. unfold runN in H. cbn [lcats] in H.
    destruct len_S as [m Hm]. rewrite Hm in H.
    unfold wids in H. cbn [wids_from] in H.
    rewrite !fmap_cons in H.
    destruct (line_runV_SS_inv fc p fs _ _ _ H)
      as [[Hsh Hrest] | (so & Hsh & Hl & Hso & Hr)].
    - (* the top node's pipe(2) failed *)
      rewrite Hm in Hrest.
      assert (Hrest' : v (WLeft 0) :: (v <$> wids_from 1 m) = [] :: replicate (2 * m + 1) [])
        by (rewrite Hrest; replace (2 * S m) with (S (2 * m + 1)) by lia; reflexivity).
      injection Hrest' as Hl0 Hall.
      assert (Hall' : forall x, x ∈ wids_from 1 m -> v x = []).
      { intros x Hx. exact (fmap_wids_nil v 1 m x Hall Hx). }
      left. exists 0. split; [lia |]. split; [exact Hsh |].
      split; [intros j Hj Hj0; apply Hall', wids_from_elem; lia |].
      split; [intros j Hj; destruct j as [| j]; [exact Hl0 | apply Hall', wids_from_elem; lia] |].
      split; [apply Hall', wids_from_elem; done | intros j Hj; lia].
    - rewrite (subf_fs fs Hn) in Hr. rewrite Hm in Hr. replace (S m - 1) with m in Hr by lia.
      pose proof (sfx_inv fc p fs HL1 v m 1 (wr_of so) (prod_cat p) Hr) as Hs.
      assert (H0 : aS fc p fs 0 (v (WLeft 0))) by (cbn [aS]; rewrite Hl; exact (prod_aP fc p fs so Hso)).
      unfold sreal in Hs.
      destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
      + left. exists k. split; [lia |]. split; [exact Hpf |].
        split; [intros j Hj Hjk; destruct j as [| j]; [exact Hsh |];
                destruct (decide (S j < k)) as [Hlt | Hge]; [apply Hab; lia | apply Hbl; lia] |].
        split; [intros j Hj; apply Hlf; lia |]. split; [exact Hlast |].
        intros j Hj. destruct j as [| j]; [exact H0 | cbn [aS]; apply Hab; lia].
      + right. split; [intros j Hj; destruct j as [| j]; [exact Hsh | apply Hab; lia] |].
        split; [intros j Hj; destruct j as [| j]; [exact H0 | cbn [aS]; apply Hab; lia] |].
        split; [rewrite Hm; exact HT |].
        intros D HD Hne Hnx. unfold ldg in Hnx. rewrite Hm in Hnx.
        destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib & Hif) | (Hall & Hfa & Hpp)].
        * left. exists i. split; [lia |]. split; [exact Hic |]. split; [intros i' Hi'; apply Hib; lia |].
          intros j Hj. apply Hif. lia.
        * destruct (prod_pair_eof fc p so D Hso Hne Hpp) as [[Hc HDL] | Hc]; rewrite <- Hl in Hc.
          -- right. split; [intros i Hi; destruct i as [| i]; [exact Hc | apply Hall; lia] |].
             split; [exact HDL |]. apply passes_sfilt. intros i Hi. rewrite <- HDL. apply Hfa. lia.
          -- left. exists 0. split; [lia |]. split; [exact Hc |].
             split; [intros i' Hi'; apply Hall; lia |]. intros j Hj. apply Hfa. lia.
  Qed.

  (* A REAL VECTOR IS A RUN *)
  Lemma real_run (v : wid -> bytes) : real fc p fs v -> runN fc lp v.
  Proof using Hn HL1.
    intros Hre. unfold runN. cbn [lcats].
    destruct len_S as [m Hm].
    pose proof (subf_fs fs Hn) as Hsub. rewrite Hm in Hsub. replace (S m - 1) with m in Hsub by lia.
    rewrite Hm. unfold wids. cbn [wids_from]. rewrite !fmap_cons.
    destruct Hre as [(k & Hk & Hpf & Hsh & Hlf & Hlast & Hab) | (Hsh & Hab & HT & Hch)].
    - destruct k as [| k'].
      + (* the top node's pipe(2) failed *)
        rewrite Hpf, (Hlf 0 ltac:(lia)).
        rewrite (wids_from_nil v 1 m); [| intros j Hj; split; [apply Hsh; lia | apply Hlf; lia] | exact Hlast].
        rewrite <- rep_S2. rewrite <- Hm.
        exact (lrv_pipe_fail fc p fs Hn).
      + (* node [S k']'s *)
        destruct m as [| m']; [lia |].
        rewrite (Hsh 0 ltac:(lia) ltac:(lia)).
        set (so := fun i : nat => so_mid (v (WLeft i))).
        pose proof (so_prod_ok fc p fs (v (WLeft 0)) (Hab 0 ltac:(lia))) as Hso0.
        rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
        apply (lrv_node fc p fs (so_prod (v (WLeft 0))) _ Hso0).
        rewrite Hsub.
        apply (sfx_build_pf fc p F v so k' 1 m' _ _ ltac:(lia)).
        * intros i Hi. split; [apply Hsh; lia |].
          split; [unfold so; apply (so_mid_ok fc p); exact (aS_mid fc p fs i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * replace (1 + k') with (S k') by lia. exact Hpf.
        * intros i Hi. apply Hsh; lia.
        * intros i Hi. apply Hlf; lia.
        * exact Hlast.
        * intros _. unfold so. rewrite so_mid_rd. apply pipe_pairB_gone.
        * intros i Hi1 Hi2. unfold so. rewrite so_mid_rd. apply pipe_pairB_gone.
    - (* THE ROUND RAN *)
      rewrite (Hsh 0 ltac:(lia)).
      pose proof (so_prod_ok fc p fs (v (WLeft 0)) (Hab 0 ltac:(lia))) as Hso0.
      assert (Hldg : ldg fs = filt_dg_exec (F (S m))) by (unfold ldg; rewrite Hm; reflexivity).
      rewrite Hm in HT.
      destruct (decide (v WLast = [] \/ v WLast = filt_dg_exec (F (S m)))) as [Hnd | Hd].
      + (* no data demand: every stage's outcome is its own, every reader gone *)
        set (so := fun i : nat => if decide (i = S m) then so_lastd (F (S m)) (v WLast) else so_mid (v (WLeft i))).
        rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
        apply (lrv_node fc p fs (so_prod (v (WLeft 0))) _ Hso0).
        rewrite Hsub.
        apply (sfx_build fc p F v so m 1 _ _).
        * intros i Hi. unfold so. rewrite decide_False by lia.
          split; [apply Hsh; lia |].
          split; [apply (so_mid_ok fc p); exact (aS_mid fc p fs i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * unfold so. rewrite decide_True by lia. replace (1 + m) with (S m) by lia.
          exact (so_lastd_ok fc p (F (S m)) _ HL1 HT).
        * unfold so. rewrite decide_True by lia. apply so_lastd_cons.
        * unfold so. destruct (decide (1 = S m)).
          -- unfold so_lastd. destruct Hnd as [Hq | Hq]; rewrite Hq; repeat case_decide; try congruence;
               try apply pipe_pairB_gone.
          -- rewrite so_mid_rd. apply pipe_pairB_gone.
        * intros i Hi. unfold so. destruct (decide (S i = S m)).
          -- unfold so_lastd. destruct Hnd as [Hq | Hq]; rewrite Hq; repeat case_decide; try congruence;
               try apply pipe_pairB_gone.
          -- rewrite so_mid_rd. apply pipe_pairB_gone.
      + (* THE CONTENT: it came down the chain *)
        assert (Hne : v WLast <> []) by tauto. assert (Hnx : v WLast <> filt_dg_exec (F (S m))) by tauto.
        set (D := v WLast).
        destruct (aT_content fc p (F (S m)) D HL1 HT Hne Hnx) as [HDL HfD].
        assert (Hlast : so_lastd (F (S m)) D = MkSO D (Some (RdEof D)) None).
        { unfold so_lastd. rewrite decide_False by exact Hnx. rewrite decide_False by exact Hne.
          reflexivity. }
        assert (Hlast_ok : stage_out fc L (SLast (F (S m))) (MkSO D (Some (RdEof D)) None)).
        { pose proof (so_last_f fc L (F (S m)) D HDL) as Hso. rewrite HfD in Hso. exact Hso. }
        destruct (Hch D eq_refl Hne ltac:(rewrite Hldg; exact Hnx))
          as [(i0 & Hi0 & Hic & Hib & Hif) | (Hall & HDe & Hpass)].
        * (* a cat halted -- a middle one, or the [cat f] producer -- and the
             stages below it passed what came *)
          set (so := fun i : nat =>
                       if decide (i = S m) then so_lastd (F (S m)) D
                       else if decide (i0 < i) then so_copy (F i) D else so_mid (v (WLeft i))).
          assert (Hbelow : forall i, i0 < i -> i <= S m -> rd_of (so i) = RdEof D).
          { intros i H1 H2. unfold so. destruct (decide (i = S m)) as [_ | Hsm].
            - rewrite Hlast. reflexivity.
            - rewrite decide_True by lia. reflexivity. }
          assert (Habove : forall i, i <= i0 -> i < S m -> rd_of (so i) = RdGone).
          { intros i H1 H2. unfold so. rewrite decide_False by lia. rewrite decide_False by lia.
            apply so_mid_rd. }
          assert (Hhalt : forall i, i = i0 -> 1 <= i -> wr_of (so i) = WrHalt []).
          { intros i -> H1. unfold so. rewrite decide_False by lia. rewrite decide_False by lia.
            unfold so_mid. rewrite Hic, decide_True by reflexivity. reflexivity. }
          assert (Hcopy : forall i, i0 < i -> i < S m -> wr_of (so i) = WrAll D).
          { intros i H1 H2. unfold so. rewrite decide_False by lia. rewrite decide_True by lia.
            cbn [so_copy wr_of so_wr]. rewrite (Hif i ltac:(lia)). reflexivity. }
          rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
          apply (lrv_node fc p fs (so_prod (v (WLeft 0))) _ Hso0).
          rewrite Hsub.
          apply (sfx_build fc p F v so m 1 _ _).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. destruct (decide (i0 < i)) as [Hlt | Hge].
             ++ split; [exact (so_copy_ok fc p (F i) D HDL) |]. cbn. symmetry. apply Hib. lia.
             ++ split; [apply (so_mid_ok fc p); exact (aS_mid fc p fs i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. replace (1 + m) with (S m) by lia.
             exact Hlast_ok.
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- (* the first reader *)
             destruct (decide (i0 = 0)) as [Hz | Hz].
             ++ rewrite (Hbelow 1 ltac:(lia) ltac:(lia)).
                assert (Hc0 : v (WLeft 0) = cat_dg_write) by (rewrite <- Hz; exact Hic).
                assert (Hcat : prod_cat p = true).
                { apply (prod_halts_cat fc p).
                  destruct (Hab 0 ltac:(lia)) as [Hq | [Hq | [Hh _]]].
                  - exfalso. rewrite Hc0 in Hq. revert Hq. vm_compute. discriminate.
                  - rewrite Hc0 in Hq. by destruct (fail_src_ne_write p fs 0 _ Hq).
                  - exact Hh. }
                rewrite Hcat. unfold so_prod. rewrite Hc0, decide_True by reflexivity.
                cbn [wr_of so_wr pipe_pairB]. split; [reflexivity | exact HDL].
             ++ rewrite (Habove 1 ltac:(lia) ltac:(lia)). apply pipe_pairB_gone.
          -- intros i Hi. destruct (decide (i < i0)) as [Hlt | Hge].
             ++ rewrite (Habove (S i) ltac:(lia) ltac:(lia)). apply pipe_pairB_gone.
             ++ rewrite (Hbelow (S i) ltac:(lia) ltac:(lia)).
                destruct (decide (i = i0)) as [Heq | Hne'].
                ** rewrite (Hhalt i Heq ltac:(lia)).
                   assert (Hcat : F i = FCat).
                   { apply aM_write. rewrite Heq, <- Hic. exact (aS_mid fc p fs i0 _ ltac:(lia) (Hab i0 ltac:(lia))). }
                   rewrite Hcat. cbn [pipe_pairB filt_is_cat].
                   split; [reflexivity | exact HDL].
                ** rewrite (Hcopy i ltac:(lia) ltac:(lia)). cbn [pipe_pairB pipe_pair].
                   reflexivity.
        * (* the producer wrote the line whole, every stage passed it *)
          set (so := fun i : nat => if decide (i = S m) then so_lastd (F (S m)) D else so_copy (F i) D).
          assert (HLne : L <> []).
          { intros HL. apply Hne. change (D = []). rewrite HDe, HL. reflexivity. }
          assert (Hwhole := so_whole_ok fc p HLne).
          assert (Hpf : forall i, 1 <= i <= S m -> fapp (F i) D = D).
          { intros i Hi. rewrite HDe. apply (proj1 (passes_sfilt fs L) Hpass). lia. }
          rewrite (Hall 0 ltac:(lia)).
          change (@nil (bv 8)) with (so_cons (MkSO [] None (Some (WrAll L)))) at 1.
          apply (lrv_node fc p fs (MkSO [] None (Some (WrAll L))) _ Hwhole).
          rewrite Hsub.
          apply (sfx_build fc p F v so m 1 (WrAll L) (prod_cat p)).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. split; [exact (so_copy_ok fc p (F i) D HDL) |].
             cbn. symmetry. apply Hall. lia.
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. replace (1 + m) with (S m) by lia.
             exact Hlast_ok.
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- unfold so. destruct (decide (1 = S m)).
             ++ rewrite Hlast. cbn. exact HDe.
             ++ cbn [so_copy rd_of so_rd pipe_pairB pipe_pair]. exact HDe.
          -- intros i Hi. unfold so. rewrite (decide_False (P := i = S m)) by lia.
             cbn [so_copy wr_of so_wr]. rewrite (Hpf i ltac:(lia)).
             destruct (decide (S i = S m)); [rewrite Hlast |]; cbn; reflexivity.
  Qed.
End real3.

(* ---- the terminal vectors ---- *)
Lemma sfx_term_nil fc L ms win wc W s : sfx_term fc L ms win wc W s -> W <> [].
Proof using. intros H. destruct H; discriminate. Qed.

Section term.
  Context (fc : bytes -> option bytes) (p : producer) (F : nat -> filt).
  Local Notation L := (prod_content fc p).

  Lemma sfx_term_build (v : wid -> bytes) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool),
    d < S m -> (forall i, j <= i <= j + d -> aM (F i) (v (WLeft i))) ->
    sfx_term fc L (subf F j (S m)) win wc ((v <$> (WLeft <$> seq j d)) ++ [dg_fork_b])
      (v (WLeft (j + d))).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Ha.
    - rewrite Nat.add_0_r. cbn [seq fmap list_fmap app].
      rewrite <- (so_mid_cons (v (WLeft j))).
      exact (stt_here fc L (F j) (F (S j)) (map F (seq (S (S j)) m)) win wc (so_mid (v (WLeft j)))
               (so_mid_ok fc p (F j) _ (Ha j ltac:(lia)))).
    - destruct m as [| m]; [lia |].
      cbn [seq]. rewrite !fmap_cons. cbn [app].
      rewrite <- (so_mid_cons (v (WLeft j))) at 1.
      apply (stt_next fc L (F j) (F (S j)) (map F (seq (S (S j)) (S m))) win wc (so_mid (v (WLeft j))) _ _
               (so_mid_ok fc p (F j) _ (Ha j ltac:(lia)))).
      + rewrite so_mid_rd. apply pipe_pairB_gone.
      + change (F (S j) :: map F (seq (S (S j)) (S m))) with (subf F (S j) (S m)).
        replace (j + S d) with (S j + d) by lia.
        apply (IH (S j) m); [lia |]. intros i Hi. apply Ha. lia.
  Qed.

  Lemma sfx_term_inv (v : wid -> bytes) (d : nat) :
    forall (j : nat) (ms : list filt) (win : wr_out) (wc : bool) (W : list bytes) (sv : bytes),
    (forall i, i < length ms -> nth i ms FCat = F (j + i)) -> sfx_term fc L ms win wc W sv ->
    W = (v <$> (WLeft <$> seq j d)) ++ [dg_fork_b] -> sv = v (WLeft (j + d)) ->
    forall i, j <= i <= j + d -> aM (F i) (v (WLeft i)).
  Proof using.
    induction d as [| d IH]; intros j ms win wc W sv Hms H HW Hsv i Hi.
    - rewrite Nat.add_0_r in Hsv. cbn [seq fmap list_fmap app] in HW.
      destruct H as [G G' ms' win' wc' so Hso | G G' ms' win' wc' so W' s' Hso Hp Hr].
      + assert (i = j) by lia. subst i.
        pose proof (Hms 0 ltac:(cbn [length]; lia)) as HG. cbn [nth] in HG. rewrite Nat.add_0_r in HG.
        rewrite <- Hsv, <- HG. exact (mid_aM fc p G so Hso).
      + exfalso. injection HW as _ HW'. destruct Hr; discriminate HW'.
    - cbn [seq] in HW. rewrite !fmap_cons in HW. cbn [app] in HW.
      destruct H as [G G' ms' win' wc' so Hso | G G' ms' win' wc' so W' s' Hso Hp Hr].
      + exfalso. injection HW as _ HW'. destruct (seq (S j) d); cbn in HW'; discriminate HW'.
      + injection HW as Hl0 HW'.
        pose proof (Hms 0 ltac:(cbn [length]; lia)) as HG. cbn [nth] in HG. rewrite Nat.add_0_r in HG.
        destruct (decide (i = j)) as [-> | Hne].
        * rewrite <- Hl0, <- HG. exact (mid_aM fc p G so Hso).
        * apply (IH (S j) (G' :: ms') (wr_of so) (filt_is_cat G) W' s'); [| exact Hr | exact HW' | | lia].
          -- intros i' Hi'.
             pose proof (Hms (S i') ltac:(cbn [length] in *; lia)) as Hq.
             change (nth (S i') (G :: G' :: ms') FCat) with (nth i' (G' :: ms') FCat) in Hq.
             rewrite Hq. f_equal. lia.
          -- rewrite Hsv. f_equal. f_equal. lia.
  Qed.
End term.

Section term2.
  Context (fc : bytes -> option bytes) (p : producer) (fs : list filt).
  Hypothesis Hn : fs <> [].
  Local Notation L := (prod_content fc p).
  Local Notation F := (sfilt fs).
  Local Notation lp := (LPipes p fs).

  Lemma waitedN_S (k : nat) : waitedN (S k) = WLeft 0 :: (WLeft <$> seq 1 k).
  Proof using. unfold waitedN. cbn [seq]. rewrite fmap_cons. reflexivity. Qed.

  (* the line's filters are the stage filters from stage 1 *)
  Lemma nth_sfilt (i : nat) : i < length fs -> nth i fs FCat = F (1 + i).
  Proof using. intros _. unfold sfilt. replace (1 + i - 1) with i by lia. reflexivity. Qed.

  Lemma realT_terms (v : wid -> bytes) (k : nat) : realT fc p fs v k -> termsN fc lp v.
  Proof using Hn.
    intros (Hk & Hf & Hsh & Hlf & Hlast & Hab). exists k.
    split; [cbn [lcats]; exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
    split; [exact Hlf |]. split; [exact Hlast |].
    destruct k as [| k'].
    - unfold waitedN. cbn [seq fmap list_fmap app].
      rewrite <- (so_prod_cons (v (WLeft 0))).
      exact (lt_here fc p fs (so_prod (v (WLeft 0))) Hn
               (so_prod_ok fc p fs _ (Hab 0 ltac:(lia)))).
    - rewrite waitedN_S, fmap_cons. cbn [app].
      rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
      apply (lt_next fc p fs (so_prod (v (WLeft 0))) _ _
               (so_prod_ok fc p fs _ (Hab 0 ltac:(lia)))).
      assert (Hm : exists m, length fs = S (S m)) by (exists (length fs - 2); lia).
      destruct Hm as [m Hm].
      rewrite (subf_fs fs Hn), Hm. replace (S (S m) - 1) with (S m) by lia.
      replace (S k') with (1 + k') by lia.
      apply (sfx_term_build fc p F v k' 1 m _ _); [lia |].
      intros i Hi. apply (aS_mid fc p fs i); [lia | apply Hab; lia].
  Qed.

  Lemma line_term_inv (v : wid -> bytes) (k : nat) (W : list bytes) (sv : bytes) :
    line_term fc lp W sv -> W = (v <$> waitedN k) ++ [dg_fork_b] -> sv = v (WLeft k) ->
    forall j, j <= k -> aS fc p fs j (v (WLeft j)).
  Proof using.
    intros H HW Hsv j Hj. remember lp as l eqn:Hl.
    destruct H as [p' n' so Hn' Hso | p' n' so W' s' Hso Hr];
      injection Hl as -> ->.
    - destruct k as [| k'].
      + assert (j = 0) by lia. subst j. cbn [aS]. rewrite <- Hsv. exact (prod_aP fc p fs so Hso).
      + exfalso. rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW.
        injection HW as _ HW'. destruct (seq 1 k'); cbn in HW'; discriminate HW'.
    - destruct k as [| k'].
      + exfalso. unfold waitedN in HW. cbn [seq fmap list_fmap app] in HW.
        injection HW as _ HW'. exact (sfx_term_nil _ _ _ _ _ _ _ Hr HW').
      + rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW. injection HW as Hl0 HW'.
        destruct j as [| j].
        * cbn [aS]. rewrite <- Hl0. exact (prod_aP fc p fs so Hso).
        * cbn [aS]. apply (sfx_term_inv fc p F v k' 1 fs _ _ W' s' nth_sfilt Hr HW');
            [| lia].
          by rewrite Hsv.
  Qed.

  Lemma terms_realT (v : wid -> bytes) : termsN fc lp v -> exists k, realT fc p fs v k.
  Proof using.
    intros (k & Hk & Hf & Hsh & Hlf & Hlast & Hlt). exists k.
    split; [cbn [lcats] in Hk; exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
    split; [exact Hlf |]. split; [exact Hlast |].
    exact (line_term_inv v k _ _ Hlt eq_refl eq_refl).
  Qed.
End term2.
(* ===================================================================== *)
(*  2.  EVERY COMMIT OF THE ROUND: ADMITTED, OR REFUTED                   *)
(* ===================================================================== *)

Definition vupd (v : wid -> bytes) (w : wid) (s : bytes) : wid -> bytes :=
  fun x => if decide (x = w) then s else v x.

Lemma vupd_self v w s : vupd v w s w = s.
Proof using. unfold vupd. by rewrite decide_True. Qed.
Lemma vupd_other v w s x : x <> w -> vupd v w s x = v x.
Proof using. intros Hx. unfold vupd. by rewrite decide_False. Qed.

(* a bounded search, and its last hit *)
Lemma range_dec (P : nat -> Prop) `{!forall i, Decision (P i)} (a b : nat) :
  (exists i, a <= i < b /\ P i) \/ (forall i, a <= i < b -> ~ P i).
Proof using.
  induction b as [| b IH]; [right; intros i Hi; lia |].
  destruct (decide (a <= b /\ P b)) as [[Hab Hb] | Hn]; [left; exists b; split; [lia | exact Hb] |].
  destruct IH as [(i & Hi & Hp) | Hno]; [left; exists i; split; [lia | exact Hp] |].
  right. intros i Hi Hp. destruct (decide (i = b)) as [-> | Hne].
  - apply Hn. split; [lia | exact Hp].
  - exact (Hno i ltac:(lia) Hp).
Qed.

Lemma range_max (P : nat -> Prop) `{!forall i, Decision (P i)} (a b : nat) :
  (exists i, a <= i < b /\ P i /\ forall i', i < i' < b -> ~ P i')
  \/ (forall i, a <= i < b -> ~ P i).
Proof using.
  induction b as [| b IH]; [right; intros i Hi; lia |].
  destruct (decide (a <= b /\ P b)) as [[Hab Hb] | Hn].
  - left. exists b. split; [lia |]. split; [exact Hb | intros i' Hi'; lia].
  - destruct IH as [(i & Hi & Hp & Hup) | Hno].
    + left. exists i. split; [lia |]. split; [exact Hp |]. intros i' Hi' Hp'.
      destruct (decide (i' = b)) as [-> | Hne]; [apply Hn; split; [lia | exact Hp'] |].
      exact (Hup i' ltac:(lia) Hp').
    + right. intros i Hi Hp. destruct (decide (i = b)) as [-> | Hne].
      * apply Hn. split; [lia | exact Hp].
      * exact (Hno i ltac:(lia) Hp).
Qed.

Lemma not_ne_nil (s : bytes) : ~ s <> [] -> s = [].
Proof using. intros H. destruct (decide (s = [])) as [He | He]; [exact He | by destruct (H He)]. Qed.

Section fire.
  Context (fc : bytes -> option bytes) (p : producer) (fs : list filt).
  Hypothesis Hn : fs <> [].
  Local Notation L := (prod_content fc p).
  Local Notation n := (length fs).
  Local Notation F := (sfilt fs).

  (* the conflicting committed writer *)
  Definition EXw (v : wid -> bytes) (w : wid) (s : bytes) : Prop :=
    exists w', v w' <> [] /\ EXf fc p fs n L w s w' (v w').

  Lemma fire_src_aS (k : nat) (s : bytes) : fire_src fc p fs L (WLeft k) s -> aS fc p fs k s.
  Proof using.
    intros [Hf | [Hk ->]]; destruct k as [| k]; cbn [aS halts_at] in *; unfold aP, aM.
    - right; left. exact Hf.
    - right; left. by apply fail_src_S in Hf.
    - right; right. split; [exact Hk | reflexivity].
    - right; right. split; [exact Hk | reflexivity].
  Qed.

  (* a failed stage's diagnostic, read at its stage: [aS] and not a halt *)
  Lemma aS_fail (k : nat) (s : bytes) :
    aS fc p fs k s -> s <> [] -> ~ fail_src p fs k s -> s = cat_dg_write.
  Proof using.
    destruct k as [| k]; cbn [aS]; unfold aP, aM.
    - intros [Hq | [Hq | [_ Hq]]] Hne Hnf; [by destruct Hne | by destruct Hnf | exact Hq].
    - intros [Hq | [Hq | [_ Hq]]] Hne Hnf; [by destruct Hne | | exact Hq].
      exfalso. apply Hnf. by apply fail_src_S.
  Qed.

  (* the last stage passes a line every filter passes *)
  Lemma passes_last : passes fs L -> fapp (F n) L = L.
  Proof using Hn.
    intros Hp. apply (proj1 (passes_sfilt fs L) Hp). destruct fs; [done | cbn; lia].
  Qed.

  (* A NON-TERMINAL COMMIT *)
  Lemma fire_nt (v : wid -> bytes) (w : wid) (s : bytes) :
    real fc p fs v -> v w = [] -> w ∈ wids n -> fire_src fc p fs L w s -> termw w s = false ->
    real fc p fs (vupd v w s) \/ EXw v w s.
  Proof using Hn.
    intros Hre Hw0 Hw Hf Ht. rewrite wids_elem in Hw.
    destruct w as [k | k |].
    - (* ---- sh node k's pipe panic ---- *)
      assert (Hs : s = dg_pipe_b).
      { destruct Hf as [-> | ->]; [reflexivity |]. cbn in Ht. rewrite bool_decide_true in Ht; done. }
      subst s.
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
        left. exists k0. split; [reflexivity |]. split; [exact Hk0 |].
        split; [intros ->; rewrite Hpf0 in Hw0; vm_compute in Hw0; discriminate Hw0 | by left].
      + destruct (range_dec (fun j => v (WLeft j) <> []) k n) as [(j & Hj & Hnz) | Hnone].
        * right. exists (WLeft j). split; [exact Hnz |]. right. right. left.
          exists j. split; [reflexivity |]. split; [lia |].
          rewrite bool_decide_true; [| reflexivity]. split; [lia | exact Hnz].
        * destruct (decide (v WLast = [])) as [Hl0 | Hl0].
          -- left. left. exists k. split; [exact Hw |]. split; [apply vupd_self |].
             split; [intros j Hj Hjk; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
             split; [intros j Hj; rewrite vupd_other; [exact (not_ne_nil _ (Hnone j Hj)) | congruence] |].
             split; [rewrite vupd_other; [exact Hl0 | congruence] |].
             intros j Hj. rewrite vupd_other; [apply Hab; lia | congruence].
          -- right. exists WLast. split; [exact Hl0 |]. right. right. right. split; [reflexivity | exact Hl0].
    - (* ---- stage k's failure, or a cat's write error ---- *)
      pose proof (fire_src_aS k s Hf) as HaS.
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + destruct (decide (k0 <= k)) as [Hle | Hgt].
        * right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
          left. exists k0. split; [reflexivity |]. split; [exact Hk0 |]. left. split; [exact Hle | reflexivity].
        * left. left. exists k0. split; [exact Hk0 |].
          split; [rewrite vupd_other; [exact Hpf0 | congruence] |].
          split; [intros j Hj Hjk; rewrite vupd_other; [exact (Hsh0 j Hj Hjk) | congruence] |].
          split; [intros j Hj; rewrite vupd_other; [exact (Hlf0 j Hj) | intros Hq; injection Hq; lia] |].
          split; [rewrite vupd_other; [exact Hlast0 | congruence] |].
          intros j Hj. destruct (decide (j = k)) as [-> | Hne].
          -- rewrite vupd_self. exact HaS.
          -- rewrite vupd_other; [exact (Hab0 j Hj) | congruence].
      + destruct Hf as [Hex | [Hk0 Hwr]].
        * (* THE FAILURE: nothing may have come down to the content writer *)
          destruct (decide (v WLast = [] \/ v WLast = ldg fs)) as [Hnd | Hd].
          -- left. right. split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
             split; [intros j Hj; destruct (decide (j = k)) as [-> | Hne];
                     [rewrite vupd_self; exact HaS | rewrite vupd_other; [exact (Hab j Hj) | congruence]] |].
             split; [rewrite vupd_other; [exact HT | congruence] |].
             intros D HD Hne Hnx. rewrite vupd_other in HD; [| congruence].
             exfalso. destruct Hnd as [Hq | Hq]; rewrite Hq in HD; subst D; [exact (Hne eq_refl) | exact (Hnx eq_refl)].
          -- right. exists WLast. split; [tauto |].
             destruct (decide (v WLast = L)) as [HL | HL].
             ++ right. right. split; [exact Hex |]. split; [reflexivity |].
                split; [exact HL |]. rewrite <- HL. tauto.
             ++ left. split; [tauto |]. intros [[Hq _] | Hq]; [exact (HL Hq) | tauto].
        * (* A WRITE ERROR: a halted cat is a source of the corner *)
          subst s. left. right.
          split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
          split; [intros j Hj; destruct (decide (j = k)) as [-> | Hne];
                  [rewrite vupd_self; exact HaS | rewrite vupd_other; [exact (Hab j Hj) | congruence]] |].
          split; [rewrite vupd_other; [exact HT | congruence] |].
          intros D HD Hne Hnx. rewrite vupd_other in HD; [| congruence].
          destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib & Hif) | (Hall & HDL & Hpass)].
          -- left. assert (Hik : i <> k) by (intros ->; rewrite Hic in Hw0; vm_compute in Hw0; discriminate).
             destruct (decide (k < i)) as [Hlt | Hge].
             ++ exists i. split; [exact Hi |]. split; [rewrite vupd_other; [exact Hic | congruence] |].
                split; [intros i' Hi'; rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia] |].
                exact Hif.
             ++ exists k. split; [lia |]. split; [apply vupd_self |].
                split; [intros i' Hi'; rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia] |].
                intros j Hj. apply Hif. lia.
          -- left. exists k. split; [lia |]. split; [apply vupd_self |].
             split; [intros i' Hi'; rewrite vupd_other; [apply Hall; lia | intros Hq; injection Hq; lia] |].
             intros j Hj. rewrite HDL. apply (proj1 (passes_sfilt fs L) Hpass). lia.
    - (* ---- the last stage: content, or its exec failure ---- *)
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
        left. exists k0. split; [reflexivity |]. split; [exact Hk0 | by left].
      + assert (Hrest : forall s', aT fc p (F n) s' ->
                  (forall D, s' = D -> D <> [] -> D <> ldg fs -> upok fc p fs (vupd v WLast s') D) ->
                  real fc p fs (vupd v WLast s')).
        { intros s' HT' Hch'. right.
          split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
          split; [intros j Hj; rewrite vupd_other; [exact (Hab j Hj) | congruence] |].
          split; [rewrite vupd_self; exact HT' |].
          intros D HD. rewrite vupd_self in HD. exact (Hch' D HD). }
        destruct (decide (s = ldg fs)) as [-> | Hsx].
        * left. apply Hrest; [left; reflexivity |]. intros D HD Hne Hnx. by destruct (Hnx (eq_sym HD)).
        * destruct Hf as [(HsL & HLne & Hpass) | Hsx']; [| by destruct (Hsx Hsx')]. subst s.
          assert (HTL : aT fc p (F n) L).
          { right. exists L. split; [reflexivity |]. symmetry. exact (passes_last Hpass). }
          destruct (range_max (fun i => v (WLeft i) <> []) 0 n) as [(i & Hi & Hnz & Hup) | Hnone].
          -- destruct (decide (fail_src p fs i (v (WLeft i)))) as [Hfl | Hnf].
             ++ (* the content against a failed stage *)
                right. exists (WLeft i). split; [exact Hnz |]. right. right.
                split; [reflexivity |]. split; [exact HLne |]. split; [exact Hsx |]. exists i.
                split; [reflexivity |]. split; [lia | exact Hfl].
             ++ (* a halted cat above silent stages: the corner *)
                pose proof (aS_fail i _ (Hab i ltac:(lia)) Hnz Hnf) as Hq.
                left. apply Hrest; [exact HTL |]. intros D HD Hne Hnx. subst D. left.
                exists i. split; [lia |]. split; [rewrite vupd_other; [exact Hq | congruence] |].
                split; [intros i' Hi'; rewrite vupd_other; [exact (not_ne_nil _ (Hup i' Hi')) | congruence] |].
                intros j Hj. apply (proj1 (passes_sfilt fs L) Hpass). lia.
          -- (* every stage silent: the producer wrote the line whole *)
             left. apply Hrest; [exact HTL |]. intros D HD Hne Hnx. subst D. right.
             split; [intros i Hi; rewrite vupd_other; [exact (not_ne_nil _ (Hnone i ltac:(lia))) | congruence] |].
             split; [reflexivity | exact Hpass].
  Qed.
  Lemma alt_forkc_ne_pipe : alt_forkc <> dg_pipe_b.
  Proof using. vm_compute. discriminate. Qed.

  (* THE TERMINAL COMMIT: node [k]'s fork failed on a run *)
  Lemma fire_t1 (v : wid -> bytes) (k : nat) :
    real fc p fs v -> (forall x, x ∉ wids n -> v x = []) -> v (WSh k) = [] -> k < n ->
    realT fc p fs (vupd v (WSh k) alt_forkc) k \/ EXw v (WSh k) alt_forkc.
  Proof using.
    intros Hre Hdom Hw0 Hk.
    assert (Hout : forall j, n <= j -> v (WSh j) = [] /\ v (WLeft j) = []).
    { intros j Hj. split; apply Hdom; rewrite wids_elem; lia. }
    destruct Hre as [(k0 & Hk0 & Hpf0 & _) | (Hsh & Hab & HT & Hch)].
    - right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
      left. exists k0. split; [reflexivity |]. split; [exact Hk0 |].
      split; [intros ->; rewrite Hpf0 in Hw0; vm_compute in Hw0; discriminate Hw0 | by left].
    - destruct (range_dec (fun j => v (WLeft j) <> []) (S k) n) as [(j & Hj & Hnz) | Hnone].
      + right. exists (WLeft j). split; [exact Hnz |]. right. right. left.
        exists j. split; [reflexivity |]. split; [lia |].
        rewrite bool_decide_false; [| exact alt_forkc_ne_pipe]. split; [lia | exact Hnz].
      + destruct (decide (v WLast = [])) as [Hl0 | Hl0].
        * left. split; [exact Hk |]. split; [apply vupd_self |].
          split.
          { intros j Hj. rewrite vupd_other; [| congruence].
            destruct (decide (j < n)); [exact (Hsh j ltac:(lia)) | exact (proj1 (Hout j ltac:(lia)))]. }
          split.
          { intros j Hj. rewrite vupd_other; [| congruence].
            destruct (decide (j < n));
              [exact (not_ne_nil _ (Hnone j ltac:(lia))) | exact (proj2 (Hout j ltac:(lia)))]. }
          split; [rewrite vupd_other; [exact Hl0 | congruence] |].
          intros j Hj. rewrite vupd_other; [exact (Hab j ltac:(lia)) | congruence].
        * right. exists WLast. split; [exact Hl0 |]. right. right. right. split; [reflexivity | exact Hl0].
  Qed.

  (* A COMMIT AFTER THE TERMINAL ONE: admitted by the terminal vector, or
     refuted by the failed fork's own deposit *)
  Lemma fire_t2 (v : wid -> bytes) (i : nat) (w : wid) (s : bytes) :
    realT fc p fs v i -> v w = [] -> w ∈ wids n -> fire_src fc p fs L w s ->
    realT fc p fs (vupd v w s) i \/ EXw v w s.
  Proof using.
    intros (Hi & Hf & Hsh & Hlf & Hlast & Hab) Hw0 Hw Hfs. rewrite wids_elem in Hw.
    destruct w as [k | k |].
    - right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
      exists i. split; [reflexivity |]. split; [exact Hi |].
      split; [intros ->; rewrite Hf in Hw0; vm_compute in Hw0; discriminate Hw0 | by right].
    - destruct (decide (k <= i)) as [Hle | Hgt].
      + left. split; [exact Hi |]. split; [rewrite vupd_other; [exact Hf | congruence] |].
        split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
        split; [intros j Hj; rewrite vupd_other; [exact (Hlf j Hj) | intros Hq; injection Hq; lia] |].
        split; [rewrite vupd_other; [exact Hlast | congruence] |].
        intros j Hj. destruct (decide (j = k)) as [-> | Hne].
        * rewrite vupd_self. exact (fire_src_aS k s Hfs).
        * rewrite vupd_other; [exact (Hab j Hj) | congruence].
      + right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
        exists i. split; [reflexivity |]. split; [exact Hi |]. right. split; [lia | reflexivity].
    - right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
      exists i. split; [reflexivity |]. split; [exact Hi | by right].
  Qed.

  (* every commit of the round has a source *)
  Lemma fire_src_ne (w : wid) (s : bytes) : fire_src fc p fs L w s -> s <> [].
  Proof using.
    destruct w as [k | k |]; cbn [fire_src]; unfold panic_src.
    - intros [-> | ->]; vm_compute; discriminate.
    - intros [Hf | [_ ->]]; [exact (fail_src_ne p fs k s Hf) | vm_compute; discriminate].
    - intros [(-> & HL & _) | ->]; [exact HL | apply filt_dg_exec_ne].
  Qed.
End fire.
