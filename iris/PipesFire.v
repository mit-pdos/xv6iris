(* ===================================================================== *)
(* PipesFire.v -- THE N-STAGE ROUND'S COMMITS, ADMITTED BY THE MODEL     *)
(* (design claude-notes/design/pipes-general.md SS2.2, SS3.2; cut C7;    *)
(* producer-generic in cut C9c', union.md S6).                            *)
(*                                                                        *)
(* Pure.  The family ([PipeBothN]) reads the committed sources with every *)
(* uncommitted writer SILENT and asks that vector to be a complete run    *)
(* ([PipeBothNPure.runS]); a commit is admitted iff the vector with the   *)
(* committer's source is still one, or a committed writer's deposit       *)
(* refutes the committer's ([EXf]).  This file is that question at the    *)
(* pipeline [p | cat | .. | cat] of [n] cats, for EITHER producer [p]     *)
(* (echo, or [cat f] at the content function [fc]), read off the VALUES: *)
(*                                                                        *)
(*   [real] / [realT]  a vector is a run / a terminal vector iff its      *)
(*                     values are what the stages may print and the one  *)
(*                     data demand -- the last cat's content -- is met by *)
(*                     the stages above it ([run_real] / [real_run],      *)
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

(* sh's [exec %s failed] at stage [k]: argv[0] is the producer's command
   at stage 0 ([PipesDisc.st_dg_exec]) and [cat] below it *)
Definition dg_st (p : producer) (k : nat) : list (bv 8) :=
  match k with O => st_dg_exec (SProd p) | S _ => dg_execR end.

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

(* A FAILED STAGE: its exec failed, or (the producer) its open was
   refused.  Either way it never touched its output pipe. *)
Definition fail_src (p : producer) (k : nat) (s : list (bv 8)) : Prop :=
  s = dg_st p k \/ (k = 0 /\ prod_open p = Some s).

Global Instance fail_src_dec p k s : Decision (fail_src p k s).
Proof using. unfold fail_src. apply _. Defined.

Lemma dg_st_ne (p : producer) (k : nat) : dg_st p k <> [].
Proof using. destruct k as [| k]; [destruct p |]; vm_compute; discriminate. Qed.

Lemma dg_st_ne_write (p : producer) (k : nat) : dg_st p k <> cat_dg_write.
Proof using. destruct k as [| k]; [destruct p |]; vm_compute; discriminate. Qed.

Lemma cat_dg_open_ne (f : bytes) : cat_dg_open f <> [].
Proof using. unfold cat_dg_open. intros Hq. apply app_eq_nil in Hq as [Hq _]. discriminate Hq. Qed.

Lemma cat_dg_open_ne_write (f : bytes) : cat_dg_open f <> cat_dg_write.
Proof using.
  intros Hq. apply (f_equal (fun l : list (bv 8) => l !! 5)) in Hq.
  vm_compute in Hq. discriminate Hq.
Qed.

Lemma fail_src_ne (p : producer) (k : nat) (s : list (bv 8)) : fail_src p k s -> s <> [].
Proof using.
  intros [-> | [_ Ho]]; [exact (dg_st_ne p k) |].
  destruct p as [ws | f]; cbn [prod_open] in Ho; [discriminate Ho |].
  injection Ho as <-. exact (cat_dg_open_ne f).
Qed.

Lemma fail_src_ne_write (p : producer) (k : nat) (s : list (bv 8)) :
  fail_src p k s -> s <> cat_dg_write.
Proof using.
  intros [-> | [_ Ho]]; [exact (dg_st_ne_write p k) |].
  destruct p as [ws | f]; cbn [prod_open] in Ho; [discriminate Ho |].
  injection Ho as <-. exact (cat_dg_open_ne_write f).
Qed.

(* below the producer a failed stage is exactly the exec failure *)
Lemma fail_src_S (p : producer) (k : nat) (s : list (bv 8)) :
  fail_src p (S k) s <-> s = dg_execR.
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
   where it can halt); the last cat's content, or its exec failure *)
Definition fire_src (fc : bytes -> option bytes) (p : producer) (L : list (bv 8)) (w : wid)
    (s : list (bv 8)) : Prop :=
  match w with
  | WSh _ => panic_src s
  | WLeft k => fail_src p k s \/ ((k <> 0 \/ prod_halts fc p) /\ s = cat_dg_write)
  | WLast => (s = L /\ L <> []) \/ s = dg_execR
  end.

Global Instance fire_src_dec fc p L w s : Decision (fire_src fc p L w s).
Proof using. destruct w; unfold fire_src, panic_src; apply _. Defined.

(* a source no process of the round commits *)
Definition gsrc (fc : bytes -> option bytes) (p : producer) (L : list (bv 8)) (w : wid)
    (s : list (bv 8)) : Prop :=
  s <> [] /\ ~ fire_src fc p L w s.

(* THE EXCLUSIONS a commit of source [s] by writer [w] spends (design
   SS2.2): every committed writer [w'] at [s'] whose deposit refutes this
   one's.  [nc] is the number of cats, [L] the line's content. *)
Definition EXf (fc : bytes -> option bytes) (p : producer) (nc : nat) (L : list (bv 8))
    (w : wid) (s : list (bv 8)) (w' : wid) (s' : list (bv 8)) : Prop :=
  gsrc fc p L w' s'
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
         \/ (fail_src p k s /\ w' = WLast /\ s' = L /\ L <> [] /\ L <> dg_execR)
     | WLast =>
         (exists j, w' = WSh j /\ (j < nc)%nat /\ panic_src s')
         \/ (s = L /\ L <> [] /\ L <> dg_execR
             /\ exists j, w' = WLeft j /\ (j < nc)%nat /\ fail_src p j s')
     end.

(* ===================================================================== *)
(*  1.  THE PIPELINE'S RUNS, READ OFF THE VALUES                          *)
(* ===================================================================== *)

Section real.
  Context (fc : bytes -> option bytes) (p : producer) (n : nat).
  Local Notation L := (prod_content fc p).

  (* what each stage may print on the console *)
  Definition aP (s : bytes) : Prop :=
    s = [] \/ fail_src p 0 s \/ (prod_halts fc p /\ s = cat_dg_write).
  Definition aM (s : bytes) : Prop := s = [] \/ s = dg_execR \/ s = cat_dg_write.
  Definition aT (s : bytes) : Prop := s = dg_execR \/ s `prefix_of` L.
  Definition aS (j : nat) (s : bytes) : Prop := match j with O => aP s | S _ => aM s end.

  (* THE ONE DATA DEMAND: the last cat's content [D] came down the chain --
     from a cat that halted (the ruled corner: a middle cat, or the [cat f]
     producer), with only silent stages below it, or from the producer
     itself through silent stages *)
  Definition upok (v : wid -> bytes) (D : bytes) : Prop :=
    (exists i, i < n /\ v (WLeft i) = cat_dg_write
               /\ forall i', i < i' < n -> v (WLeft i') = [])
    \/ ((forall i, i < n -> v (WLeft i) = []) /\ D = L).

  (* node [k]'s pipe(2) failed *)
  Definition realP (v : wid -> bytes) (k : nat) : Prop :=
    k < n /\ v (WSh k) = dg_pipe_b /\ (forall j, j < n -> j <> k -> v (WSh j) = [])
    /\ (forall j, k <= j < n -> v (WLeft j) = []) /\ v WLast = []
    /\ (forall j, j < k -> aS j (v (WLeft j))).

  (* the round ran *)
  Definition realN (v : wid -> bytes) : Prop :=
    (forall j, j < n -> v (WSh j) = []) /\ (forall j, j < n -> aS j (v (WLeft j)))
    /\ aT (v WLast)
    /\ (forall D, v WLast = D -> D <> [] -> D <> dg_execR -> upok v D).

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
  Definition so_copy (D : bytes) : st_out := MkSO [] (Some (RdEof D)) (Some (WrAll D)).
  Definition so_lastd (s : bytes) : st_out :=
    if decide (s = dg_execR) then MkSO dg_execR (Some RdGone) None
    else if decide (s = []) then MkSO [] (Some RdGone) None
    else MkSO s (Some (RdEof s)) None.

  Lemma so_prod_ok s : aP s -> stage_out fc L (SProd p) (so_prod s).
  Proof using.
    unfold so_prod. intros [-> | [[-> | [_ Ho]] | [Hh ->]]].
    - rewrite decide_False; [exact (so_silent fc L (SProd p)) | vm_compute; discriminate].
    - rewrite decide_False; [exact (so_exec fc L (SProd p)) | exact (dg_st_ne_write p 0)].
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

  Lemma so_mid_ok s : aM s -> stage_out fc L (SMid FCat) (so_mid s).
  Proof using.
    intros Hs. unfold so_mid. case_decide as Hw.
    - subst s. exact (so_mid_halt fc L [] (prefix_nil _)).
    - destruct Hs as [-> | [-> | ->]]; [| | by destruct Hw].
      + exact (so_silent fc L (SMid FCat)).
      + exact (so_exec fc L (SMid FCat)).
  Qed.

  Lemma so_mid_cons s : so_cons (so_mid s) = s.
  Proof using. unfold so_mid. case_decide as Hw; [by subst s | reflexivity]. Qed.

  Lemma so_mid_rd s : rd_of (so_mid s) = RdGone.
  Proof using. unfold so_mid. case_decide; reflexivity. Qed.

  Lemma so_lastd_ok s : aT s -> stage_out fc L (SLast FCat) (so_lastd s).
  Proof using.
    intros Hs. unfold so_lastd. case_decide as He; [subst s; exact (so_exec fc L (SLast FCat)) |].
    case_decide as Hz; [subst s; exact (so_silent fc L (SLast FCat)) |].
    destruct Hs as [Hs | Hs]; [by destruct He |]. exact (so_last fc L s Hs).
  Qed.

  Lemma so_lastd_cons s : so_cons (so_lastd s) = s.
  Proof using.
    unfold so_lastd. case_decide as He; [by subst s |]. case_decide as Hz; [by subst s |].
    reflexivity.
  Qed.

  Lemma so_copy_ok D : D `prefix_of` L -> stage_out fc L (SMid FCat) (so_copy D).
  Proof using. intros HD. exact (so_mid_copy fc L D HD). Qed.

End real.

(* a gone reader pairs with every writer *)
Lemma pipe_pairB_gone (L : bytes) (wc : bool) (w : wr_out) : pipe_pairB L wc w RdGone.
Proof using. destruct w; exact I. Qed.

(* ---- building the suffix from an outcome per stage ---- *)
Section build.
  Context (fc : bytes -> option bytes) (p : producer).
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
       v (WSh i) = [] /\ stage_out fc L (SMid FCat) (so i) /\ so_cons (so i) = v (WLeft i)) ->
    stage_out fc L (SLast FCat) (so (j + m)) -> so_cons (so (j + m)) = v WLast ->
    pipe_pairB L wc win (rd_of (so j)) ->
    (forall i, j <= i < j + m -> pipe_pairB L true (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (cats (S m)) win wc (v <$> wids_from j m).
  Proof using.
    induction m as [| m IH]; intros j win wc Hst Hl Hlc Hp Hps.
    - rewrite Nat.add_0_r in Hl, Hlc. cbn [wids_from]. rewrite fmap_cons, fmap_nil.
      rewrite <- Hlc. exact (srv_last fc L FCat win wc (so j) Hl Hp).
    - cbn [wids_from]. rewrite !fmap_cons.
      destruct (Hst j ltac:(lia)) as (Hsh & Hso & Hc). rewrite Hsh, <- Hc.
      apply (srv_node fc L FCat FCat (cats m) win wc (so j) _ Hso Hp).
      apply (IH (S j) (wr_of (so j)) true).
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
       v (WSh i) = [] /\ stage_out fc L (SMid FCat) (so i) /\ so_cons (so i) = v (WLeft i)) ->
    v (WSh (j + d)) = dg_pipe_b ->
    (forall i, j + d < i < j + S m -> v (WSh i) = []) ->
    (forall i, j + d <= i < j + S m -> v (WLeft i) = []) -> v WLast = [] ->
    (0 < d -> pipe_pairB L wc win (rd_of (so j))) ->
    (forall i, j <= i -> S i < j + d -> pipe_pairB L true (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (cats (S (S m))) win wc (v <$> wids_from j (S m)).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Hst Hpf Hsh Hlf Hlast Hp Hps.
    - rewrite Nat.add_0_r in Hpf, Hsh, Hlf. cbn [wids_from]. rewrite !fmap_cons.
      rewrite Hpf, (Hlf j ltac:(lia)).
      assert (Hrest : v <$> wids_from (S j) m = replicate (2 * m + 1) []).
      { apply (wids_from_nil v (S j) m); [| exact Hlast].
        intros i Hi. split; [apply Hsh | apply Hlf]; lia. }
      rewrite Hrest.
      rewrite <- rep_S2.
      pose proof (srv_pipe_fail fc L FCat FCat (cats m) win wc) as Hpf'.
      cbn [length] in Hpf'. rewrite FileDisc.cats_length in Hpf'. exact Hpf'.
    - destruct m as [| m]; [lia |].
      cbn [wids_from]. rewrite !fmap_cons.
      destruct (Hst j ltac:(lia)) as (Hsj & Hso & Hc). rewrite Hsj, <- Hc.
      apply (srv_node fc L FCat FCat (cats (S m)) win wc (so j) _ Hso (Hp ltac:(lia))).
      apply (IH (S j) m (wr_of (so j)) true ltac:(lia)).
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
  Context (fc : bytes -> option bytes) (L : bytes).

  Lemma sfx_runV_1_inv win wc vs :
    sfx_runV fc L (cats 1) win wc vs ->
    exists so, vs = [so_cons so] /\ stage_out fc L (SLast FCat) so /\ pipe_pairB L wc win (rd_of so).
  Proof using.
    intros H. remember (cats 1) as mm eqn:Hmm. unfold FileDisc.cats in Hmm. cbn [replicate] in Hmm.
    destruct H as [F win' wc' so Hso Hp | F F' fs win' wc' | F F' fs win' wc' so vs' Hso Hp Hr];
      [| injection Hmm as _ Hq; discriminate Hq | injection Hmm as _ Hq; discriminate Hq].
    injection Hmm as ->. exists so. done.
  Qed.

  Lemma sfx_runV_SS_inv m win wc a b vs :
    sfx_runV fc L (cats (S (S m))) win wc (a :: b :: vs) ->
    (a = dg_pipe_b /\ b :: vs = replicate (2 * S m) [])
    \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc L (SMid FCat) so
                  /\ pipe_pairB L wc win (rd_of so) /\ sfx_runV fc L (cats (S m)) (wr_of so) true vs.
  Proof using.
    intros H. remember (cats (S (S m))) as mm eqn:Hmm. remember (a :: b :: vs) as l eqn:Hl.
    unfold FileDisc.cats in Hmm. cbn [replicate] in Hmm.
    destruct H as [F win' wc' so Hso Hp | F F' fs win' wc' | F F' fs win' wc' so vs' Hso Hp Hr].
    - injection Hmm as _ Hq. discriminate Hq.
    - injection Hmm as -> -> ->. cbn [length] in Hl. rewrite length_replicate in Hl.
      left. split; congruence.
    - injection Hmm as -> -> ->. injection Hl as Ha Hb Hvs. subst. right. exists so.
      split_and!; [reflexivity | reflexivity | exact Hso | exact Hp | exact Hr].
  Qed.

  Lemma replicate_nil_elem (vs : list bytes) (k : nat) (x : bytes) :
    vs = replicate k [] -> x ∈ vs -> x = [].
  Proof using. intros -> Hx. by apply elem_of_replicate in Hx as [-> _]. Qed.
End inv.

Section real2.
  Context (fc : bytes -> option bytes) (p : producer).
  Local Notation L := (prod_content fc p).
  Local Notation aT := (aT fc p).

  (* the suffix from stage [j], [m] middle stages above the last *)
  Definition sreal (v : wid -> bytes) (j m : nat) (win : wr_out) (wc : bool) : Prop :=
    (exists k, j <= k < j + m /\ v (WSh k) = dg_pipe_b
       /\ (forall i, j <= i < k -> v (WSh i) = [] /\ aM (v (WLeft i)))
       /\ (forall i, k < i < j + m -> v (WSh i) = [])
       /\ (forall i, k <= i < j + m -> v (WLeft i) = []) /\ v WLast = [])
    \/ ((forall i, j <= i < j + m -> v (WSh i) = [] /\ aM (v (WLeft i))) /\ aT (v WLast)
        /\ (forall D, v WLast = D -> D <> [] -> D <> dg_execR ->
              (exists i, j <= i < j + m /\ v (WLeft i) = cat_dg_write
                         /\ forall i', i < i' < j + m -> v (WLeft i') = [])
              \/ ((forall i, j <= i < j + m -> v (WLeft i) = [])
                  /\ pipe_pairB L wc win (RdEof D)))).

  Lemma fmap_wids_nil (v : wid -> bytes) (k m : nat) (x : wid) :
    (v <$> wids_from k m) = replicate (2 * m + 1) [] -> x ∈ wids_from k m -> v x = [].
  Proof using.
    intros Heq Hx. apply (replicate_nil_elem (v <$> wids_from k m) (2 * m + 1)); [exact Heq |].
    apply elem_of_list_fmap. by exists x.
  Qed.

  Lemma sfx_inv (v : wid -> bytes) (m : nat) :
    forall (j : nat) (win : wr_out) (wc : bool),
    sfx_runV fc L (cats (S m)) win wc (v <$> wids_from j m) -> sreal v j m win wc.
  Proof using.
    induction m as [| m IH]; intros j win wc H.
    - cbn [wids_from] in H. rewrite fmap_cons, fmap_nil in H.
      destruct (sfx_runV_1_inv fc L win wc _ H) as (so & Heq & Hso & Hp).
      injection Heq as Hv. right. split; [intros i Hi; lia |].
      destruct (stage_out_last_inv fc L so Hso) as [-> | [-> | (D & HD & ->)]];
        cbn in Hv, Hp |- *; rewrite Hv.
      + split; [left; reflexivity | intros D -> _ HD; by destruct HD].
      + split; [right; apply prefix_nil | intros D -> HD; by destruct HD].
      + split; [right; exact HD |]. intros D' <- _ _. right.
        split; [intros i Hi; lia | exact Hp].
    - cbn [wids_from] in H. rewrite !fmap_cons in H.
      destruct (sfx_runV_SS_inv fc L m win wc _ _ _ H)
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
        pose proof (IH (S j) (wr_of so) true Hr) as Hs.
        assert (Hj : v (WSh j) = [] /\ aM (v (WLeft j))).
        { split; [exact Hsh |]. rewrite Hl.
          destruct (stage_out_mid_inv fc L so Hso)
            as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]]; cbn; unfold aM; tauto. }
        destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
        * left. exists k. split; [lia |]. split; [exact Hpf |].
          split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne]; [exact Hj | apply Hab; lia] |].
          split; [intros i Hi; apply Hbl; lia |].
          split; [intros i Hi; apply Hlf; lia | exact Hlast].
        * right. split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne];
                          [exact Hj | apply Hab; lia] |].
          split; [exact HT |].
          intros D HD Hne Hnx. destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & Hpp)].
          -- left. exists i. split; [lia |]. split; [exact Hic |].
             intros i' Hi'. apply Hib. lia.
          -- destruct (stage_out_mid_inv fc L so Hso)
               as [Hso' | [Hso' | [(D0 & HD0 & Hso') | (D0 & HD0 & Hso')]]]; subst so; cbn in *.
             ++ exfalso. apply Hne. exact Hpp.
             ++ exfalso. apply Hne. exact Hpp.
             ++ right. subst D0. split; [| exact Hp].
                intros i Hi. destruct (decide (i = j)) as [-> | Hne']; [exact Hl | apply Hall; lia].
             ++ left. exists j. split; [lia |]. split; [exact Hl |].
                intros i' Hi'. apply Hall. lia.
  Qed.
End real2.

Lemma line_runV_SS_inv (fc : bytes -> option bytes) (p : producer) (n : nat) (a b : bytes)
    (vs : list bytes) :
  line_runV fc (LPipes p (cats n)) (a :: b :: vs) ->
  (a = dg_pipe_b /\ b :: vs = replicate (2 * n) [])
  \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc (prod_content fc p) (SProd p) so
                /\ sfx_runV fc (prod_content fc p) (cats n) (wr_of so) (prod_cat p) vs.
Proof using.
  intros H. remember (LPipes p (cats n)) as l eqn:Hl. remember (a :: b :: vs) as ls eqn:Hls.
  destruct H as [ws' | ws' | ws' | p' fs' Hn' | p' fs' so vs' Hso Hr]; try discriminate Hl.
  - injection Hl as -> ->. rewrite FileDisc.cats_length in Hls. left. split; congruence.
  - injection Hl as -> ->. injection Hls as Ha Hb Hvs. subst. right. exists so. done.
Qed.

Lemma aS_mid (fc : bytes -> option bytes) (p : producer) (i : nat) (s : bytes) :
  1 <= i -> aS fc p i s -> aM s.
Proof using. intros Hi Hs. destruct i as [| i]; [lia | exact Hs]. Qed.

(* WHAT THE PRODUCER PRINTED, and what it did to its pipe *)
Lemma prod_aP (fc : bytes -> option bytes) (p : producer) (so : st_out) :
  stage_out fc (prod_content fc p) (SProd p) so -> aP fc p (so_cons so).
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

Section real3.
  Context (fc : bytes -> option bytes) (p : producer) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (prod_content fc p).
  Local Notation lp := (LPipes p (cats n)).

  (* A RUN IS REAL *)
  Lemma run_real (v : wid -> bytes) : runN fc lp v -> real fc p n v.
  Proof using Hn.
    intros H. unfold runN in H. rewrite lcats_cats in H.
    destruct n as [| m] eqn:Hnm; [lia |]. unfold wids in H. cbn [wids_from] in H.
    rewrite !fmap_cons in H.
    destruct (line_runV_SS_inv fc p (S m) _ _ _ H)
      as [[Hsh Hrest] | (so & Hsh & Hl & Hso & Hr)].
    - (* the top node's pipe(2) failed *)
      assert (Hrest' : v (WLeft 0) :: (v <$> wids_from 1 m) = [] :: replicate (2 * m + 1) [])
        by (rewrite Hrest; replace (2 * S m) with (S (2 * m + 1)) by lia; reflexivity).
      injection Hrest' as Hl0 Hall.
      assert (Hall' : forall x, x ∈ wids_from 1 m -> v x = []).
      { intros x Hx. exact (fmap_wids_nil v 1 m x Hall Hx). }
      left. exists 0. split; [lia |]. split; [exact Hsh |].
      split; [intros j Hj Hj0; apply Hall', wids_from_elem; lia |].
      split; [intros j Hj; destruct j as [| j]; [exact Hl0 | apply Hall', wids_from_elem; lia] |].
      split; [apply Hall', wids_from_elem; done | intros j Hj; lia].
    - pose proof (sfx_inv fc p v m 1 (wr_of so) (prod_cat p) Hr) as Hs.
      assert (H0 : aS fc p 0 (v (WLeft 0))) by (cbn [aS]; rewrite Hl; exact (prod_aP fc p so Hso)).
      destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
      + left. exists k. split; [lia |]. split; [exact Hpf |].
        split; [intros j Hj Hjk; destruct j as [| j]; [exact Hsh |];
                destruct (decide (S j < k)) as [Hlt | Hge]; [apply Hab; lia | apply Hbl; lia] |].
        split; [intros j Hj; apply Hlf; lia |]. split; [exact Hlast |].
        intros j Hj. destruct j as [| j]; [exact H0 | cbn [aS]; apply Hab; lia].
      + right. split; [intros j Hj; destruct j as [| j]; [exact Hsh | apply Hab; lia] |].
        split; [intros j Hj; destruct j as [| j]; [exact H0 | cbn [aS]; apply Hab; lia] |].
        split; [exact HT |].
        intros D HD Hne Hnx. destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & Hpp)].
        * left. exists i. split; [lia |]. split; [exact Hic |]. intros i' Hi'. apply Hib. lia.
        * destruct (prod_pair_eof fc p so D Hso Hne Hpp) as [[Hc HDL] | Hc]; rewrite <- Hl in Hc.
          -- right. split; [| exact HDL].
             intros i Hi. destruct i as [| i]; [exact Hc | apply Hall; lia].
          -- left. exists 0. split; [lia |]. split; [exact Hc |].
             intros i' Hi'. apply Hall. lia.
  Qed.

  (* A REAL VECTOR IS A RUN *)
  Lemma real_run (v : wid -> bytes) : real fc p n v -> runN fc lp v.
  Proof using Hn.
    intros Hre. unfold runN. rewrite lcats_cats. destruct n as [| m] eqn:Hnm; [lia |].
    unfold wids. cbn [wids_from]. rewrite !fmap_cons.
    destruct Hre as [(k & Hk & Hpf & Hsh & Hlf & Hlast & Hab) | (Hsh & Hab & HT & Hch)].
    - destruct k as [| k'].
      + (* the top node's pipe(2) failed *)
        rewrite Hpf, (Hlf 0 ltac:(lia)).
        rewrite (wids_from_nil v 1 m); [| intros j Hj; split; [apply Hsh; lia | apply Hlf; lia] | exact Hlast].
        rewrite <- rep_S2.
        pose proof (lrv_pipe_fail fc p (cats (S m)) (FileDisc.cats_ne (S m) Hn)) as Hpf'.
        rewrite FileDisc.cats_length in Hpf'. exact Hpf'.
      + (* node [S k']'s *)
        destruct m as [| m']; [lia |].
        rewrite (Hsh 0 ltac:(lia) ltac:(lia)).
        set (so := fun i : nat => so_mid (v (WLeft i))).
        pose proof (so_prod_ok fc p (v (WLeft 0)) (Hab 0 ltac:(lia))) as Hso0.
        rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
        apply (lrv_node fc p (cats (S (S m'))) (so_prod (v (WLeft 0))) _ Hso0).
        apply (sfx_build_pf fc p v so k' 1 m' _ _ ltac:(lia)).
        * intros i Hi. split; [apply Hsh; lia |].
          split; [unfold so; apply (so_mid_ok fc p); exact (aS_mid fc p i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * replace (1 + k') with (S k') by lia. exact Hpf.
        * intros i Hi. apply Hsh; lia.
        * intros i Hi. apply Hlf; lia.
        * exact Hlast.
        * intros _. unfold so. rewrite so_mid_rd. apply pipe_pairB_gone.
        * intros i Hi1 Hi2. unfold so. rewrite so_mid_rd. apply pipe_pairB_gone.
    - (* THE ROUND RAN *)
      rewrite (Hsh 0 ltac:(lia)).
      pose proof (so_prod_ok fc p (v (WLeft 0)) (Hab 0 ltac:(lia))) as Hso0.
      destruct (decide (v WLast = [] \/ v WLast = dg_execR)) as [Hnd | Hd].
      + (* no data demand: every stage's outcome is its own, every reader gone *)
        set (so := fun i : nat => if decide (i = S m) then so_lastd (v WLast) else so_mid (v (WLeft i))).
        rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
        apply (lrv_node fc p (cats (S m)) (so_prod (v (WLeft 0))) _ Hso0).
        apply (sfx_build fc p v so m 1 _ _).
        * intros i Hi. unfold so. rewrite decide_False by lia.
          split; [apply Hsh; lia |].
          split; [apply (so_mid_ok fc p); exact (aS_mid fc p i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * unfold so. rewrite decide_True by lia. exact (so_lastd_ok fc p _ HT).
        * unfold so. rewrite decide_True by lia. apply so_lastd_cons.
        * unfold so. destruct (decide (1 = S m)).
          -- unfold so_lastd. destruct Hnd as [-> | ->]; repeat case_decide; try congruence;
               apply pipe_pairB_gone.
          -- rewrite so_mid_rd. apply pipe_pairB_gone.
        * intros i Hi. unfold so. destruct (decide (S i = S m)).
          -- unfold so_lastd. destruct Hnd as [-> | ->]; repeat case_decide; try congruence;
               apply pipe_pairB_gone.
          -- rewrite so_mid_rd. apply pipe_pairB_gone.
      + (* THE CONTENT: it came down the chain *)
        assert (Hne : v WLast <> []) by tauto. assert (Hnx : v WLast <> dg_execR) by tauto.
        set (D := v WLast).
        assert (HDL : D `prefix_of` L) by (destruct HT as [HT | HT]; [by destruct Hnx | exact HT]).
        assert (Hlast : so_lastd D = MkSO D (Some (RdEof D)) None).
        { unfold so_lastd. rewrite decide_False by exact Hnx. rewrite decide_False by exact Hne.
          reflexivity. }
        destruct (Hch D eq_refl Hne Hnx) as [(i0 & Hi0 & Hic & Hib) | (Hall & HDe)].
        * (* a cat halted -- a middle one, or the [cat f] producer -- and the
             stages below it copied what came *)
          set (so := fun i : nat =>
                       if decide (i = S m) then so_lastd D
                       else if decide (i0 < i) then so_copy D else so_mid (v (WLeft i))).
          (* below the halted cat every reader saw the end of file at [D],
             above it every reader is gone *)
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
            reflexivity. }
          rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
          apply (lrv_node fc p (cats (S m)) (so_prod (v (WLeft 0))) _ Hso0).
          apply (sfx_build fc p v so m 1 _ _).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. destruct (decide (i0 < i)) as [Hlt | Hge].
             ++ split; [exact (so_copy_ok fc p D HDL) |]. cbn. symmetry. apply Hib. lia.
             ++ split; [apply (so_mid_ok fc p); exact (aS_mid fc p i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. exact (so_last fc L D HDL).
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- (* the first reader *)
             destruct (decide (i0 = 0)) as [Hz | Hz].
             ++ rewrite (Hbelow 1 ltac:(lia) ltac:(lia)).
                assert (Hc0 : v (WLeft 0) = cat_dg_write) by (rewrite <- Hz; exact Hic).
                assert (Hcat : prod_cat p = true).
                { apply (prod_halts_cat fc p).
                  destruct (Hab 0 ltac:(lia)) as [Hq | [Hq | [Hh _]]].
                  - exfalso. rewrite Hc0 in Hq. revert Hq. vm_compute. discriminate.
                  - rewrite Hc0 in Hq. by destruct (fail_src_ne_write p 0 _ Hq).
                  - exact Hh. }
                rewrite Hcat. unfold so_prod. rewrite Hc0, decide_True by reflexivity.
                cbn [wr_of so_wr pipe_pairB]. split; [reflexivity | exact HDL].
             ++ rewrite (Habove 1 ltac:(lia) ltac:(lia)). apply pipe_pairB_gone.
          -- intros i Hi. destruct (decide (i < i0)) as [Hlt | Hge].
             ++ rewrite (Habove (S i) ltac:(lia) ltac:(lia)). apply pipe_pairB_gone.
             ++ rewrite (Hbelow (S i) ltac:(lia) ltac:(lia)).
                destruct (decide (i = i0)) as [Heq | Hne'].
                ** rewrite (Hhalt i Heq ltac:(lia)). cbn [pipe_pairB].
                   split; [reflexivity | exact HDL].
                ** rewrite (Hcopy i ltac:(lia) ltac:(lia)). cbn [pipe_pairB pipe_pair].
                   reflexivity.
        * (* the producer wrote the line whole, every stage copied it *)
          set (so := fun i : nat => if decide (i = S m) then so_lastd D else so_copy D).
          assert (HLne : L <> []).
          { intros HL. apply Hne. change (D = []). rewrite HDe, HL. reflexivity. }
          assert (Hwhole := so_whole_ok fc p HLne).
          rewrite (Hall 0 ltac:(lia)).
          change (@nil (bv 8)) with (so_cons (MkSO [] None (Some (WrAll L)))) at 1.
          apply (lrv_node fc p (cats (S m)) (MkSO [] None (Some (WrAll L))) _ Hwhole).
          apply (sfx_build fc p v so m 1 (WrAll L) (prod_cat p)).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. split; [exact (so_copy_ok fc p D HDL) |].
             cbn. symmetry. apply Hall. lia.
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. exact (so_last fc L D HDL).
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- unfold so. destruct (decide (1 = S m)).
             ++ rewrite Hlast. cbn. exact HDe.
             ++ cbn. exact HDe.
          -- intros i Hi. unfold so. rewrite (decide_False (P := i = S m)) by lia.
             destruct (decide (S i = S m)); [rewrite Hlast |]; cbn; reflexivity.
  Qed.
End real3.

(* ---- the terminal vectors ---- *)
Section term.
  Context (fc : bytes -> option bytes) (p : producer).
  Local Notation L := (prod_content fc p).

  Lemma sfx_term_build (v : wid -> bytes) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool),
    d < S m -> (forall i, j <= i <= j + d -> aM (v (WLeft i))) ->
    sfx_term fc L (cats (S (S m))) win wc ((v <$> (WLeft <$> seq j d)) ++ [dg_fork_b])
      (v (WLeft (j + d))).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Ha.
    - rewrite Nat.add_0_r. cbn [seq fmap list_fmap app].
      rewrite <- (so_mid_cons (v (WLeft j))).
      exact (stt_here fc L FCat FCat (cats m) win wc (so_mid (v (WLeft j)))
               (so_mid_ok fc p _ (Ha j ltac:(lia)))).
    - destruct m as [| m]; [lia |].
      cbn [seq]. rewrite !fmap_cons. cbn [app].
      rewrite <- (so_mid_cons (v (WLeft j))) at 1.
      apply (stt_next fc L FCat FCat (cats (S m)) win wc (so_mid (v (WLeft j))) _ _
               (so_mid_ok fc p _ (Ha j ltac:(lia)))).
      + rewrite so_mid_rd. apply pipe_pairB_gone.
      + replace (j + S d) with (S j + d) by lia.
        apply (IH (S j) m); [lia |]. intros i Hi. apply Ha. lia.
  Qed.

  Lemma sfx_term_inv (v : wid -> bytes) (d : nat) :
    forall (j : nat) (m : list filt) (win : wr_out) (wc : bool) (W : list bytes) (sv : bytes),
    all_cats m = true -> sfx_term fc L m win wc W sv ->
    W = (v <$> (WLeft <$> seq j d)) ++ [dg_fork_b] -> sv = v (WLeft (j + d)) ->
    forall i, j <= i <= j + d -> aM (v (WLeft i)).
  Proof using.
    induction d as [| d IH]; intros j m win wc W sv Hc H HW Hsv i Hi.
    - rewrite Nat.add_0_r in Hsv. cbn [seq fmap list_fmap app] in HW.
      destruct H as [F F' m' win' wc' so Hso | F F' m' win' wc' so W' s' Hso Hp Hr];
        apply FileDisc.all_cats_cons in Hc as [-> Hc].
      + assert (i = j) by lia. subst i.
        destruct (stage_out_mid_inv fc L so Hso) as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]];
          cbn in Hsv; rewrite <- Hsv; unfold aM; tauto.
      + exfalso. injection HW as _ HW'. destruct Hr; discriminate HW'.
    - cbn [seq] in HW. rewrite !fmap_cons in HW. cbn [app] in HW.
      destruct H as [F F' m' win' wc' so Hso | F F' m' win' wc' so W' s' Hso Hp Hr];
        apply FileDisc.all_cats_cons in Hc as [-> Hc].
      + exfalso. injection HW as _ HW'. destruct (seq (S j) d); cbn in HW'; discriminate HW'.
      + injection HW as Hl0 HW'.
        destruct (decide (i = j)) as [-> | Hne].
        * rewrite <- Hl0.
          destruct (stage_out_mid_inv fc L so Hso) as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]];
            cbn; unfold aM; tauto.
        * apply (IH (S j) _ _ _ W' s' Hc Hr HW'); [| lia].
          rewrite Hsv. f_equal. f_equal. lia.
  Qed.
End term.

Section term2.
  Context (fc : bytes -> option bytes) (p : producer) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (prod_content fc p).
  Local Notation lp := (LPipes p (cats n)).

  Lemma waitedN_S (k : nat) : waitedN (S k) = WLeft 0 :: (WLeft <$> seq 1 k).
  Proof using. unfold waitedN. cbn [seq]. rewrite fmap_cons. reflexivity. Qed.

  Lemma realT_terms (v : wid -> bytes) (k : nat) : realT fc p n v k -> termsN fc lp v.
  Proof using Hn.
    intros (Hk & Hf & Hsh & Hlf & Hlast & Hab). exists k.
    split; [rewrite lcats_cats; exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
    split; [exact Hlf |]. split; [exact Hlast |].
    destruct k as [| k'].
    - unfold waitedN. cbn [seq fmap list_fmap app].
      rewrite <- (so_prod_cons (v (WLeft 0))).
      exact (lt_here fc p (cats n) (so_prod (v (WLeft 0))) (FileDisc.cats_ne n Hn)
               (so_prod_ok fc p _ (Hab 0 ltac:(lia)))).
    - rewrite waitedN_S, fmap_cons. cbn [app].
      rewrite <- (so_prod_cons (v (WLeft 0))) at 1.
      apply (lt_next fc p (cats n) (so_prod (v (WLeft 0))) _ _
               (so_prod_ok fc p _ (Hab 0 ltac:(lia)))).
      destruct n as [| [| m]]; [lia | lia |].
      replace (S k') with (1 + k') by lia.
      apply (sfx_term_build fc p v k' 1 m _ _); [lia |].
      intros i Hi. apply (aS_mid fc p i); [lia | apply Hab; lia].
  Qed.

  Lemma line_term_inv (v : wid -> bytes) (k : nat) (W : list bytes) (sv : bytes) :
    line_term fc lp W sv -> W = (v <$> waitedN k) ++ [dg_fork_b] -> sv = v (WLeft k) ->
    forall j, j <= k -> aS fc p j (v (WLeft j)).
  Proof using Hn.
    intros H HW Hsv j Hj. remember lp as l eqn:Hl.
    destruct H as [p' n' so Hn' Hso | p' n' so W' s' Hso Hr];
      injection Hl as Hp Hnn; subst p' n'; cbn [prod_content prod_cat] in *.
    - destruct k as [| k'].
      + assert (j = 0) by lia. subst j. cbn [aS]. rewrite <- Hsv. exact (prod_aP fc p so Hso).
      + exfalso. rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW.
        injection HW as _ HW'. destruct (seq 1 k'); cbn in HW'; discriminate HW'.
    - destruct k as [| k'].
      + exfalso. unfold waitedN in HW. cbn [seq fmap list_fmap app] in HW.
        injection HW as _ HW'. destruct Hr; discriminate HW'.
      + rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW. injection HW as Hl0 HW'.
        destruct j as [| j].
        * cbn [aS]. rewrite <- Hl0. exact (prod_aP fc p so Hso).
        * cbn [aS]. apply (sfx_term_inv fc p v k' 1 _ _ _ W' s' (FileDisc.all_cats_cats n) Hr HW');
            [| lia].
          by rewrite Hsv.
  Qed.

  Lemma terms_realT (v : wid -> bytes) : termsN fc lp v -> exists k, realT fc p n v k.
  Proof using Hn.
    intros (k & Hk & Hf & Hsh & Hlf & Hlast & Hlt). exists k.
    split; [rewrite lcats_cats in Hk; exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
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
  Context (fc : bytes -> option bytes) (p : producer) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (prod_content fc p).

  (* the conflicting committed writer *)
  Definition EXw (v : wid -> bytes) (w : wid) (s : bytes) : Prop :=
    exists w', v w' <> [] /\ EXf fc p n L w s w' (v w').

  Lemma fire_src_aS (k : nat) (s : bytes) : fire_src fc p L (WLeft k) s -> aS fc p k s.
  Proof using.
    intros [Hf | [Hk ->]]; destruct k as [| k]; cbn [aS]; unfold aP, aM.
    - right; left. exact Hf.
    - right; left. by apply fail_src_S in Hf.
    - destruct Hk as [Hk | Hh]; [exfalso; exact (Hk eq_refl) |]. right; right. split; [exact Hh | reflexivity].
    - right; right. reflexivity.
  Qed.

  (* a failed stage's diagnostic, read at its stage: [aS] and not a halt *)
  Lemma aS_fail (k : nat) (s : bytes) :
    aS fc p k s -> s <> [] -> ~ fail_src p k s -> s = cat_dg_write.
  Proof using.
    destruct k as [| k]; cbn [aS]; unfold aP, aM.
    - intros [Hq | [Hq | [_ Hq]]] Hne Hnf; [by destruct Hne | by destruct Hnf | exact Hq].
    - intros [Hq | [Hq | Hq]] Hne Hnf; [by destruct Hne | | exact Hq].
      exfalso. apply Hnf. by apply fail_src_S.
  Qed.

  (* A NON-TERMINAL COMMIT *)
  Lemma fire_nt (v : wid -> bytes) (w : wid) (s : bytes) :
    real fc p n v -> v w = [] -> w ∈ wids n -> fire_src fc p L w s -> termw w s = false ->
    real fc p n (vupd v w s) \/ EXw v w s.
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
          destruct (decide (v WLast = [] \/ v WLast = dg_execR)) as [Hnd | Hd].
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
          destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & HDL)].
          -- left. assert (Hik : i <> k) by (intros ->; rewrite Hic in Hw0; vm_compute in Hw0; discriminate).
             destruct (decide (k < i)) as [Hlt | Hge].
             ++ exists i. split; [exact Hi |]. split; [rewrite vupd_other; [exact Hic | congruence] |].
                intros i' Hi'. rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia].
             ++ exists k. split; [lia |]. split; [apply vupd_self |].
                intros i' Hi'. rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia].
          -- left. exists k. split; [lia |]. split; [apply vupd_self |].
             intros i' Hi'. rewrite vupd_other; [apply Hall; lia | intros Hq; injection Hq; lia].
    - (* ---- the last cat: content, or its exec failure ---- *)
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
        left. exists k0. split; [reflexivity |]. split; [exact Hk0 | by left].
      + assert (Hrest : forall s', s' = dg_execR \/ s' `prefix_of` L ->
                  (forall D, s' = D -> D <> [] -> D <> dg_execR -> upok fc p n (vupd v WLast s') D) ->
                  real fc p n (vupd v WLast s')).
        { intros s' HT' Hch'. right.
          split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
          split; [intros j Hj; rewrite vupd_other; [exact (Hab j Hj) | congruence] |].
          split; [rewrite vupd_self; exact HT' |].
          intros D HD. rewrite vupd_self in HD. exact (Hch' D HD). }
        destruct (decide (s = dg_execR)) as [-> | Hsx].
        * left. apply Hrest; [by left |]. intros D HD Hne Hnx. by destruct (Hnx (eq_sym HD)).
        * destruct Hf as [[HsL HLne] | Hsx']; [| by destruct (Hsx Hsx')]. subst s.
          destruct (range_max (fun i => v (WLeft i) <> []) 0 n) as [(i & Hi & Hnz & Hup) | Hnone].
          -- destruct (decide (fail_src p i (v (WLeft i)))) as [Hfl | Hnf].
             ++ (* the content against a failed stage *)
                right. exists (WLeft i). split; [exact Hnz |]. right. right.
                split; [reflexivity |]. split; [exact HLne |]. split; [exact Hsx |]. exists i.
                split; [reflexivity |]. split; [lia | exact Hfl].
             ++ (* a halted cat above silent stages: the corner *)
                pose proof (aS_fail i _ (Hab i ltac:(lia)) Hnz Hnf) as Hq.
                left. apply Hrest; [right; reflexivity |]. intros D HD Hne Hnx. left.
                exists i. split; [lia |]. split; [rewrite vupd_other; [exact Hq | congruence] |].
                intros i' Hi'. rewrite vupd_other; [exact (not_ne_nil _ (Hup i' Hi')) | congruence].
          -- (* every stage silent: the producer wrote the line whole *)
             left. apply Hrest; [right; reflexivity |]. intros D HD Hne Hnx. right.
             split; [intros i Hi; rewrite vupd_other; [exact (not_ne_nil _ (Hnone i ltac:(lia))) | congruence] |].
             by rewrite HD.
  Qed.
  Lemma alt_forkc_ne_pipe : alt_forkc <> dg_pipe_b.
  Proof using. vm_compute. discriminate. Qed.

  (* THE TERMINAL COMMIT: node [k]'s fork failed on a run *)
  Lemma fire_t1 (v : wid -> bytes) (k : nat) :
    real fc p n v -> (forall x, x ∉ wids n -> v x = []) -> v (WSh k) = [] -> k < n ->
    realT fc p n (vupd v (WSh k) alt_forkc) k \/ EXw v (WSh k) alt_forkc.
  Proof using.
    clear Hn. intros Hre Hdom Hw0 Hk.
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
    realT fc p n v i -> v w = [] -> w ∈ wids n -> fire_src fc p L w s ->
    realT fc p n (vupd v w s) i \/ EXw v w s.
  Proof using.
    clear Hn. intros (Hi & Hf & Hsh & Hlf & Hlast & Hab) Hw0 Hw Hfs. rewrite wids_elem in Hw.
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
  Lemma fire_src_ne (w : wid) (s : bytes) : fire_src fc p L w s -> s <> [].
  Proof using.
    destruct w as [k | k |]; cbn [fire_src]; unfold panic_src.
    - intros [-> | ->]; vm_compute; discriminate.
    - intros [Hf | [_ ->]]; [exact (fail_src_ne p k s Hf) | vm_compute; discriminate].
    - intros [[-> HL] | ->]; [exact HL | vm_compute; discriminate].
  Qed.
End fire.
