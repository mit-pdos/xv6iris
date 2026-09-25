(* ===================================================================== *)
(*  PipeHooks.v -- THE PIPELINE MODEL'S HOOKS, PURE (app-both M3b).      *)
(*                                                                       *)
(*  [PipeLinksLine]'s section S0, moved below [PipeOut] unchanged, as     *)
(*  [FileHooks] is the file's: the pipeline's claim is [GenOut.gcl] at    *)
(*  [pipe_lm] and needs [pipe_hooks] below the link families.  PURE       *)
(*  IMPORTS ONLY (durable-notes: a pure file must not load the link      *)
(*  tier's instances).                                                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import LineModelLinks.
From stdpp Require Import ssreflect.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE LINE, AND ITS ALTERNATIVES' OUTPUT                            *)
(* ===================================================================== *)

(* the line the last COMPLETE body of [I] parses to ([FileHooks.fline]) *)
Definition pline_at (I : list (bv 8)) : pline :=
  pline_of (bodies_of I !!! (nlines I - 1)%nat).

(* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
   guarded by ADMISSIBILITY alone (see the header). *)
(* THE GUARD GAINS [palt_isforkS = false] (lane PIPE-MODEL-3): the
   terminal fork-failure round's block is NEVER written through this
   layer -- it is written by TWO processes at the two cursors and its
   code is never filed -- and [PipeOut.pecl_step_write_blk], which files
   the code at the block's FIRST byte, must not be reachable at it.  The
   guard is where the claim's [cs_nofork] comes from: [pab_nofork]
   carries it out of the same lookup [pab_ok] reads. *)
Definition pab_gd (I : list (bv 8)) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a) /\ palt_isforkS (palt_of a) = false.

Global Instance pab_gd_dec I a : Decision (pab_gd I a).
Proof using. rewrite /pab_gd. apply _. Defined.

Definition pab (I : list (bv 8)) (a : nat) : list (bv 8) :=
  if decide (pab_gd I a)
  then pcont (pline_at I) (palt_of a) else [].

(* THE RECORD'S [lk_apr]: the alternative is admissible and does not
   reopen the prologue -- which is exactly when its output ends with the
   shell's prompt ([PipeDisc.pcont_shape], minus the [pline_ok] premise a
   WRITER does not hold; [pcont_prompt] below). *)
Definition papr (I : list (bv 8)) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a) /\ palt_panic (palt_of a) = false
  /\ palt_isforkS (palt_of a) = false.




(* ---- THE BLOCK'S LAST TWO BYTES ARE THE SHELL'S PROMPT.  [pcont_shape]
        says so under [pline_ok]; a writer holds no such thing, so the
        "ends with the prompt" half is read off the eight constructors
        instead -- every one of them is literally [_ ++ u_prompt]. ---- *)
Lemma pcont_prompt (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  exists u : list (bv 8), pcont l a = u ++ u_prompt.
Proof using.
  intros Hok Hp Hfk.
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont;
    [| | | | | | done |].
  - (* [PEcho k]: [k < 4] at an [LEcho] line, [k = 3] at an [LPipe] one --
       and the panic index is excluded, so [k < 3] either way. *)
    assert (Hk : (k < 3)%nat).
    { rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
      destruct l as [ws | ws]; cbn [palt_ok] in Hok; lia. }
    destruct k as [| [| [| k]]]; [| | | exfalso; lia].
    + exists (wl_line (drop 1 (pline_ws l))). exact (line_alts_of_0 _).
    + exists dg_execL. rewrite (line_alts_of_1 (pline_ws l)).
      by rewrite -alt_execL_echo /alt_execL.
    + exists []. rewrite (line_alts_of_2 (pline_ws l)). by rewrite app_nil_l.
  - exists (wl_line (drop 1 (pline_ws l))). reflexivity.
  - exists dg_execL. reflexivity.
  - exists dg_execR. reflexivity.
  - exists (pmerge sel dg_execL dg_execR). reflexivity.
  - exists (wl_line dg_pipe). reflexivity.
  - exists []. by rewrite app_nil_l.
Qed.

(* ...and what "ends with the prompt" buys, once, for the three readings
   the record asks for. *)
Lemma prompt_tail_facts (x u : list (bv 8)) :
  x = u ++ u_prompt ->
  (2 <= length x)%nat
  /\ x !! (length x - 2)%nat = Some (u_prompt !!! 0%nat)
  /\ x !! (length x - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  intros ->. rewrite length_app (_ : length u_prompt = 2%nat); [| by vm_compute].
  split_and!; [lia | | ].
  - rewrite lookup_app_r; [| lia].
    replace (length u + 2 - 2 - length u)%nat with 0%nat by lia.
    by vm_compute.
  - rewrite lookup_app_r; [| lia].
    replace (length u + 2 - 1 - length u)%nat with 1%nat by lia.
    by vm_compute.
Qed.




(* ---- THE THREE NAMED ALTERNATIVES ------------------------------------ *)

(* THE PANIC is the LITERAL 3 at BOTH line shapes -- the coordinator's
   ruling of 2026-09-18 ([PipeDisc.palt_ok_pipe_panic]) is exactly what
   makes [lk_pan] a constant here where the file's is per-line. *)
Lemma palt_of_3 : palt_of 3%nat = PEcho 3%nat.
Proof using. apply palt_of_lt4. lia. Qed.

Lemma ppan_panic : palt_panic (palt_of 3%nat) = true.
Proof using. rewrite palt_of_3. by vm_compute. Qed.

Lemma ppan_ok (l : pline) : palt_ok l (palt_of 3%nat).
Proof using.
  rewrite palt_of_3. destruct l as [ws | ws]; cbn [palt_ok]; lia.
Qed.

Lemma pcont_ppan (l : pline) : pcont l (palt_of 3%nat) = alt_panic.
Proof using. apply pcont_panic. exact ppan_panic. Qed.

Lemma ppan_nofork : palt_isforkS (palt_of 3%nat) = false.
Proof using. rewrite palt_of_3. reflexivity. Qed.


(* THE EXEC-FAILED CHILD'S alternative is PER-LINE and the design's
   "literally 1" is refuted at the statement: [palt_ok (LPipe ws)
   (PEcho 1)] is FALSE (only [PEcho 3] joins a pipeline line's [PEcho]
   arms).  What IS echo's verbatim are the BYTES, through
   [PipeDisc.alt_execL_echo]. *)
Definition pexf_of (l : pline) : nat :=
  match l with LEcho _ => 1%nat | LPipe _ => palt_code PExecL end.

Definition pexfb (l : pline) : list (bv 8) :=
  match l with LEcho _ => alt_execfail | LPipe _ => alt_execL end.

Lemma pexfb_execfail (l : pline) : pexfb l = alt_execfail.
Proof using. destruct l; [reflexivity | exact alt_execL_echo]. Qed.

Lemma pexf_of_dec (l : pline) :
  palt_of (pexf_of l) = match l with LEcho _ => PEcho 1%nat | LPipe _ => PExecL end.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - apply palt_of_lt4. lia.
  - exact (palt_of_code PExecL).
Qed.

Lemma pexf_of_ok (l : pline) : palt_ok l (palt_of (pexf_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PExecL). exact I.
Qed.

Lemma pexf_of_nopanic (l : pline) : palt_panic (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pcont_pexf (l : pline) : pcont l (palt_of (pexf_of l)) = pexfb l.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of pexfb].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). cbn [pcont pline_ws].
    exact (line_alts_of_1 ws).
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.

Lemma pexf_of_nofork (l : pline) : palt_isforkS (palt_of (pexf_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pexf_of].
  - rewrite (palt_of_lt4 1%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PExecL). reflexivity.
Qed.



(* THE ALTERNATIVE A ROUND TAKES WHEN NOBODY WROTE: the shell's own prompt
   IS the block's first byte.  [PEcho 2] at an echo line, [PSilent] at a
   pipeline one; both print [u_prompt]. *)
Definition pnoc_of (l : pline) : nat :=
  match l with LEcho _ => 2%nat | LPipe _ => palt_code PSilent end.

Lemma pnoc_of_dec (l : pline) :
  palt_of (pnoc_of l)
  = match l with LEcho _ => PEcho 2%nat | LPipe _ => PSilent end.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - apply palt_of_lt4. lia.
  - exact (palt_of_code PSilent).
Qed.

Lemma pnoc_of_ok (l : pline) : palt_ok l (palt_of (pnoc_of l)).
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [palt_ok]. lia.
  - rewrite (palt_of_code PSilent). exact I.
Qed.

Lemma pnoc_of_nopanic (l : pline) : palt_panic (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). by vm_compute.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pcont_pnoc (l : pline) : pcont l (palt_of (pnoc_of l)) = u_prompt.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). cbn [pcont pline_ws].
    reflexivity.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.

Lemma pnoc_of_nofork (l : pline) : palt_isforkS (palt_of (pnoc_of l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [pnoc_of].
  - rewrite (palt_of_lt4 2%nat ltac:(lia)). reflexivity.
  - rewrite (palt_of_code PSilent). reflexivity.
Qed.






(* ---- THE MODEL'S HOOKS ([LineModelLinks.lm_hooks] at the pipeline
        model): the panic is the literal 3, the exec failure and the
        silent alternative are per-line, state-freedom is [~ PForkS] (the
        arm written by two processes never goes through this layer), and
        what a WRITER knows of a continuation is [pcont_prompt] /
        [PipeOutPure.pcont_nonnil].  Everything section 0 said of [pab] /
        [papr] is then [LineModelLinks]'s lemma read back through the
        equations below. ---- *)
Lemma pfree_term (a : palt) : negb (palt_isforkS a) = true -> palt_isforkS a = false.
Proof using. destruct (palt_isforkS a); [discriminate | reflexivity]. Qed.

Lemma pfree_of_nofork (a : palt) : palt_isforkS a = false -> negb (palt_isforkS a) = true.
Proof using. intros ->. reflexivity. Qed.

Lemma pcont_nonnil_dec (l : pline) (a : palt) :
  palt_ok l a \/ a = palt_of 0%nat -> pcont l a <> [].
Proof using.
  rewrite (palt_of_lt4 0%nat ltac:(lia)). exact (pcont_nonnil l a).
Qed.

Definition pipe_hooks : lm_hooks pipe_lm :=
  MkLMH pipe_lm (fun a => negb (palt_isforkS a)) tt (fun _ => 3%nat) pexf_of pexfb
    pnoc_of (fun _ => palt_ok_dec)
    (fun _ _ _ _ _ => eq_refl) pfree_term (fun _ _ _ _ _ H => H)
    (fun _ => ppan_ok) (fun _ => pfree_of_nofork _ ppan_nofork) (fun _ => ppan_panic)
    (fun _ => pexf_of_ok) (fun l => pfree_of_nofork _ (pexf_of_nofork l)) pexf_of_nopanic
    (fun _ l => pcont_pexf l)
    (fun _ => pnoc_of_ok) (fun l => pfree_of_nofork _ (pnoc_of_nofork l)) pnoc_of_nopanic
    (fun _ l => pcont_pnoc l)
    (fun _ l a Hok Hp Ht => pcont_prompt l a Hok Hp Ht)
    (fun _ l a H => pcont_nonnil_dec l a H).

Lemma pline_at_lm (I : list (bv 8)) : pline_at I = lm_line_at pipe_lm I.
Proof using. reflexivity. Qed.

Lemma pab_lm (I : list (bv 8)) (a : nat) : pab I a = lm_ab pipe_lm pipe_hooks I a.
Proof using.
  rewrite /pab /lm_ab. case_decide as H1; case_decide as H2; [reflexivity | | | reflexivity].
  - exfalso. apply H2. split; [exact (proj1 H1) | exact (pfree_of_nofork _ (proj2 H1))].
  - exfalso. apply H1. split; [exact (proj1 H2) | exact (pfree_term _ (proj2 H2))].
Qed.

Lemma papr_lm (I : list (bv 8)) (a : nat) : papr I a <-> lm_apr pipe_lm pipe_hooks I a.
Proof using.
  split.
  - intros (H1 & H2 & H3). exact (conj H1 (conj (pfree_of_nofork _ H3) H2)).
  - intros (H1 & H2 & H3). exact (conj H1 (conj H3 (pfree_term _ H2))).
Qed.


(* ---- what section 0 said, as corollaries ---- *)
Lemma pab_ok (I : list (bv 8)) (a i : nat) (b : bv 8) :
  pab I a !! i = Some b -> palt_ok (pline_at I) (palt_of a).
Proof using.
  rewrite pab_lm. intros H. exact (proj1 (lm_ab_ok pipe_lm pipe_hooks I a i b H)).
Qed.

Lemma pab_nofork (I : list (bv 8)) (a i : nat) (b : bv 8) :
  pab I a !! i = Some b -> palt_isforkS (palt_of a) = false.
Proof using.
  rewrite pab_lm. intros H.
  exact (pfree_term _ (proj2 (lm_ab_ok pipe_lm pipe_hooks I a i b H))).
Qed.

Lemma pab_is (I : list (bv 8)) (a : nat) :
  pab_gd I a -> pab I a = pcont (pline_at I) (palt_of a).
Proof using.
  intros [H1 H2]. rewrite pab_lm.
  exact (lm_ab_is pipe_lm pipe_hooks I a H1 (pfree_of_nofork _ H2)).
Qed.

Lemma pab_len_ge2 (I : list (bv 8)) (a : nat) :
  papr I a -> (2 <= length (pab I a))%nat.
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_len_ge2 pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_dollar (I : list (bv 8)) (a : nat) :
  papr I a ->
  pab I a !! (length (pab I a) - 2)%nat = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_dollar pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_space (I : list (bv 8)) (a : nat) :
  papr I a ->
  pab I a !! (length (pab I a) - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite pab_lm. intros Hpr.
  exact (lm_ab_space pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma pab_pan (I : list (bv 8)) : pab I 3%nat = alt_panic.
Proof using.
  rewrite pab_lm. exact (lm_ab_pan pipe_lm pipe_lm_laws pipe_hooks I).
Qed.

Lemma pab_exf (I : list (bv 8)) :
  pab I (pexf_of (pline_at I)) = pexfb (pline_at I).
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_exf pipe_lm pipe_hooks).
Qed.

Lemma papr_exf (I : list (bv 8)) : papr I (pexf_of (pline_at I)).
Proof using.
  apply papr_lm. apply (lm_apr_exf pipe_lm pipe_hooks).
Qed.

Lemma pab_noc (I : list (bv 8)) : pab I (pnoc_of (pline_at I)) = u_prompt.
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_noc pipe_lm pipe_hooks).
Qed.

Lemma papr_noc (I : list (bv 8)) : papr I (pnoc_of (pline_at I)).
Proof using.
  apply papr_lm. apply (lm_apr_noc pipe_lm pipe_hooks).
Qed.

Lemma pab_noc_len (I : list (bv 8)) :
  (length (pab I (pnoc_of (pline_at I))) - 2)%nat = 0%nat.
Proof using.
  rewrite pab_lm pline_at_lm. apply (lm_ab_noc_len pipe_lm pipe_hooks).
Qed.


