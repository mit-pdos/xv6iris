(* ===================================================================== *)
(*  FileHooks.v -- THE FILE MODEL'S HOOKS, PURE (app-both M3b).          *)
(*                                                                       *)
(*  [FileLinksLine]'s section S0, moved below [FileOut] unchanged: the    *)
(*  line the input's last complete body parses to, the state-free         *)
(*  alternatives, the named alternatives (the fork panic, the exec        *)
(*  failure with its bytes; no silent round), the continuation's shape    *)
(*  lemmas, and [file_hooks : lm_hooks file_lm] with its equations.  The  *)
(*  generic claim ([GenOut.gcl]) needs the hooks, and the file's claim    *)
(*  sits below the link families that used to carry them.                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import LineModel.
Require Import LineModelLinks.
From stdpp Require Import ssreflect.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE LINE, ITS ALTERNATIVES' OUTPUT, AND STATE-FREEDOM             *)
(* ===================================================================== *)

(* the line the last COMPLETE body of [I] parses to *)
Definition fline (I : list (bv 8)) : uline :=
  uline_of (bodies_of I !!! (nlines I - 1)%nat).

(* ...and when that line is a redirect, its words are among the input's
   redirect lines -- which is what turns the read's witness
   ([flw]: every [echof_lines_in I] word list is in the claim's ledger)
   into the [ws ∈ ls] the open and the write credential ask for. *)
Lemma fline_echof_in (I : list (bv 8)) (ws : list (list (bv 8))) (N : list (bv 8)) :
  (0 < nlines I)%nat -> fline I = LEchoF ws N -> (N, ws) ∈ echof_lines_in I.
Proof using.
  intros Hp Hf. rewrite /echof_lines_in. apply elem_of_list_omap.
  exists (LEchoF ws N). split; [ | reflexivity ].
  rewrite /lines_of -Hf /fline. apply elem_of_list_fmap.
  eexists. split; [ reflexivity | ].
  apply elem_of_list_lookup. exists (nlines I - 1)%nat.
  apply list_lookup_lookup_total_lt. rewrite /nlines in Hp |- *. lia.
Qed.

(* the alternatives whose console output is a function of the LINE alone.
   [RCRan] is the only one that reads the file's state, and it is cat's
   own round. *)
Definition fstate_free (a : ralt) : bool :=
  match a with RCRan => false | _ => true end.

Lemma cont_state_free (s s' : fstate) (l : uline) (a : ralt) :
  fstate_free a = true -> cont s l a = cont s' l a.
Proof using. destruct a; cbn [fstate_free]; try discriminate; reflexivity. Qed.

(* THE RECORD'S [lk_ab]: the block alternative [a] owes at input [I],
   GUARDED so that a byte lookup alone says the alternative is admissible
   and state-free -- which is what makes the block-byte step premise-free. *)
Definition fab (I : list (bv 8)) (a : nat) : list (bv 8) :=
  if decide (ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true)
  then cont ∅ (fline I) (ralt_dec a) else [].

(* THE RECORD'S [lk_apr]: the alternative ends with the shell's prompt,
   i.e. it is admissible, state-free and does NOT reopen the prologue. *)
Definition fapr (I : list (bv 8)) (a : nat) : Prop :=
  ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true
  /\ ralt_panic (ralt_dec a) = false.




(* ---- THE SHELL'S OWN TWO ALTERNATIVES ARE PER-LINE.  This is lane
        LINK-GEN's [lk_pan]/[lk_exf] found to be the WRONG TYPE: at the
        echo application there is one line shape and the fork panic is
        the constant 3, but [FileDisc.ralt_ok] admits [RFFork] only at an
        [LEchoF] line, [RCFork] only at an [LCat] one and [REcho 3] only
        at an [LEcho] one.  The panic's BYTES are the same at all three
        ([alt_panic]); the exec-failed child's are NOT ([alt_execcat] at
        a cat line), because sh prints "exec %s failed" with the command
        name. ---- *)
Definition fpan_of (l : uline) : nat :=
  match l with
  | LEcho _ => 3%nat
  | LEchoF _ _ => ralt_enc RFFork
  | LCat _ => ralt_enc RCFork
  (* the DEAD arm: [FileDisc.ralt_ok] gives [LPipe] exactly [LCat]'s five,
     so all four of this file's per-line choices are [LCat]'s verbatim *)
  | LPipe _ _ => ralt_enc RCFork
  (* a [seccomp] line: the shell's own fork panic *)
  | LSecc _ => ralt_enc RCFork
  end.

Definition fexf_of (l : uline) : nat :=
  match l with
  | LEcho _ => 1%nat
  | LEchoF _ _ => ralt_enc RFExec
  | LCat _ => ralt_enc RCExec
  | LPipe _ _ => ralt_enc RCExec
  | LSecc _ => ralt_enc RSExec
  end.

(* ...and the bytes the exec-failed child prints, per line *)
Definition fexfb (l : uline) : list (bv 8) :=
  match l with
  | LEcho _ => alt_execfail
  | LEchoF _ _ => alt_execfail
  | LCat _ => alt_execcat
  | LPipe _ _ => alt_execcat
  | LSecc _ => alt_execsecc
  end.


(* ---- the block's LAST TWO BYTES are the shell's prompt, at every
        admissible, state-free, non-panic alternative.  [FileDisc.
        cont_shape] says so under [uline_ok], which a WRITER does not
        hold; this reads it off the twelve cases instead, four of which
        are literals. ---- *)



(* ===================================================================== *)
(*  THE STATE-AWARE BLOCK (PROGRAM-STREAM stretch 11, defect 3).           *)
(*                                                                       *)
(*  [fab] gives an alternative's bytes from the INPUT alone, and is [[]]  *)
(*  at the one alternative whose bytes are a function of the FILE --      *)
(*  [RCRan], "cat printed the contents".  So a block at [RCRan] had no    *)
(*  bytes here, [fapr] excluded it, and the line credential could not     *)
(*  hold a round in which cat printed a non-empty file.                   *)
(*                                                                       *)
(*  The model underneath was never the problem: [pending_at_f] speaks     *)
(*  [cont] at the round's own state, [fstate_upto cs s0 ...], and [fab]   *)
(*  reaches it only through [cont_state_free].  [fabs] is that reading    *)
(*  with the state kept: the era's boot state [s0] and the choice list    *)
(*  [cs] filed so far determine it.  [fab] is its instance at a           *)
(*  state-free alternative ([fabs_fab]), and the block lemmas below are   *)
(*  proved at [fabs]; their [fab] statements are corollaries.             *)
(* ===================================================================== *)
Definition fabs (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat)
  : list (bv 8) :=
  cont (fstate_upto cs s0 (bodies_of I) (nlines I - 1)%nat) (fline I)
    (ralt_dec a).

(* [fapr] without state-freedom: admissible, and not a panic *)
Definition faprs (I : list (bv 8)) (a : nat) : Prop :=
  ralt_ok (fline I) (ralt_dec a) /\ ralt_panic (ralt_dec a) = false.



(* every non-panic admissible alternative's block ENDS WITH THE PROMPT, at
   every state: the file's contents come BEFORE it *)





(* ---- the two PER-LINE alternatives, and the "nobody chose" one ---- *)
Lemma fpan_of_ok (l : uline) : ralt_ok l (ralt_dec (fpan_of l)).
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)) /ralt_ok. lia.
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma fpan_of_free (l : uline) : fstate_free (ralt_dec (fpan_of l)) = true.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fpan_of].
  - by rewrite (ralt_dec_lt4 3%nat ltac:(lia)).
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma fpan_of_panic (l : uline) : ralt_panic (ralt_dec (fpan_of l)) = true.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)). by vm_compute.
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.

Lemma cont_fpan (s : fstate) (l : uline) :
  cont s l (ralt_dec (fpan_of l)) = alt_panic.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fpan_of].
  - rewrite (ralt_dec_lt4 3%nat ltac:(lia)). cbn [cont uline_ws].
    exact (line_alts_of_3 ws).
  - by rewrite (ralt_dec_enc RFFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
  - by rewrite (ralt_dec_enc RCFork).
Qed.


Lemma fexf_of_ok (l : uline) : ralt_ok l (ralt_dec (fexf_of l)).
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fexf_of].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)) /ralt_ok. lia.
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RSExec).
Qed.

Lemma fexf_of_free (l : uline) : fstate_free (ralt_dec (fexf_of l)) = true.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fexf_of].
  - by rewrite (ralt_dec_lt4 1%nat ltac:(lia)).
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RSExec).
Qed.

Lemma fexf_of_nopanic (l : uline) : ralt_panic (ralt_dec (fexf_of l)) = false.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fexf_of].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)). by vm_compute.
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RSExec).
Qed.

Lemma cont_fexf (s : fstate) (l : uline) :
  cont s l (ralt_dec (fexf_of l)) = fexfb l.
Proof using.
  destruct l as [ws | ws N | N | ws npc | ws]; cbn [fexf_of fexfb].
  - rewrite (ralt_dec_lt4 1%nat ltac:(lia)). cbn [cont uline_ws].
    exact (line_alts_of_1 ws).
  - by rewrite (ralt_dec_enc RFExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RCExec).
  - by rewrite (ralt_dec_enc RSExec).
Qed.

(* NO SILENT ROUND: the model has none at any line ([FileDisc.ralt_ok]
   never admits [REcho 2]; a line sh forks for admits [ROom] instead), so
   the hook's [None] makes its four laws vacuous. *)
Lemma fnoc_none {P : Prop} (c : nat) : @None nat = Some c -> P.
Proof using. intros H. discriminate H. Qed.

(* ---- THE MODEL'S HOOKS ([LineModelLinks.lm_hooks] at the file model):
        the per-line alternatives the shell's own code names, state-
        freedom, and what a WRITER knows of a continuation without the
        discipline's premises.  Everything section 0 said of [fab] /
        [fabs] / [fapr] is then [LineModelLinks]'s lemma read back through
        the equations below ([fab] IS [lm_ab] up to the decision term). ---- *)
Lemma cont_prompt (s : fstate) (l : uline) (a : ralt) :
  ralt_ok l a -> ralt_panic a = false ->
  exists u : list (bv 8), cont s l a = u ++ u_prompt.
Proof using.
  intros Hok Hp. revert s.
  destruct a as [k | sel | | | | | | | | | |]; intros st.
  { (* [REcho]: on its own, so no [vm_compute] meets the line *)
    rewrite /ralt_ok in Hok. destruct l as [ws | ws N | N | ws npc | ws];
      cbn in Hok; try done.
    destruct Hok as [Hok _].
    cbn [ralt_panic] in Hp. apply bool_decide_eq_false in Hp.
    cbn [cont uline_ws].
    pose proof (line_alts_len_ge2 ws k ltac:(lia)) as Hl.
    pose proof (line_alts_dollar ws k ltac:(lia)) as Hd.
    pose proof (line_alts_space ws k ltac:(lia)) as Hsp.
    set (bl := line_alts_of ws !!! k) in *.
    exists (take (length bl - 2) bl).
    rewrite -{1}(take_drop (length bl - 2) bl). f_equal.
    apply list_eq. intros i. rewrite lookup_drop.
    destruct i as [| [| i]].
    - rewrite Nat.add_0_r Hd. by vm_compute.
    - replace (length bl - 2 + 1)%nat with (length bl - 1)%nat by lia.
      rewrite Hsp. by vm_compute.
    - rewrite lookup_ge_None_2; [ | lia ].
      symmetry. apply lookup_ge_None_2. vm_compute. lia. }
  all: try (cbn [ralt_panic] in Hp; by discriminate Hp).
  all: cbn [cont].
  (* [RCRan]: the contents, then the prompt -- or the diagnostic *)
  all: try (destruct (st !! lname l) as [bs |]; [ by exists bs | ]).
  (* a diagnostic at the line's name: its own line, then the prompt *)
  all: try (eexists; reflexivity).
  (* a CONSTANT block: its own bytes but the last two *)
  all: match goal with
       | |- exists pre : list (bv 8), ?c = pre ++ u_prompt =>
           exists (take (length c - 2) c); by vm_compute
       end.
Qed.

Lemma cont_nonnil_dec (s : fstate) (l : uline) (a : ralt) :
  ralt_ok l a \/ a = ralt_dec 0%nat -> cont s l a <> [].
Proof using.
  rewrite (ralt_dec_lt4 0%nat ltac:(lia)). exact (cont_nonnil s l a).
Qed.

Definition file_hooks : lm_hooks file_lm :=
  MkLMH file_lm fstate_free ∅ fpan_of fexf_of fexfb (fun _ => None) (fun _ => ralt_ok_dec)
    cont_state_free (fun _ _ => eq_refl) (fun _ _ _ _ _ H => H)
    (fun _ => fpan_of_ok) fpan_of_free fpan_of_panic
    (fun _ => fexf_of_ok) fexf_of_free fexf_of_nopanic cont_fexf
    (fun _ _ c => fnoc_none c) (fun _ c => fnoc_none c) (fun _ c => fnoc_none c)
    (fun _ _ c => fnoc_none c)
    (fun s l a Hok Hp _ => cont_prompt s l a Hok Hp)
    cont_nonnil_dec.

Lemma fline_lm (I : list (bv 8)) : fline I = lm_line_at file_lm I.
Proof using. reflexivity. Qed.

Lemma fab_lm (I : list (bv 8)) (a : nat) : fab I a = lm_ab file_lm file_hooks I a.
Proof using.
  rewrite /fab /lm_ab. case_decide as H1; case_decide as H2;
    [reflexivity | by destruct (H2 H1) | by destruct (H1 H2) | reflexivity].
Qed.

Lemma fapr_lm (I : list (bv 8)) (a : nat) : fapr I a <-> lm_apr file_lm file_hooks I a.
Proof using. reflexivity. Qed.

Lemma fabs_lm (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  fabs s0 cs I a = lm_abs file_lm s0 cs I a.
Proof using. rewrite /fabs /lm_abs fstate_upto_lm. reflexivity. Qed.

Lemma faprs_lm (I : list (bv 8)) (a : nat) : faprs I a <-> lm_aprs file_lm I a.
Proof using.
  split.
  - intros [H1 H2]. exact (conj (fun _ => H1) (conj H2 eq_refl)).
  - intros (H1 & H2 & _). exact (conj (H1 ∅) H2).
Qed.

(* the stream, at a boot state that may be unfiled *)
Lemma pending_at_f_lm_o ps cs f0 I :
  pending_at_f ps cs f0 I = lm_pending_at file_lm ps cs (f0_st f0) I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_f_lm_o ps cs f0 pre I :
  proc_before_from_f ps cs f0 pre I
  = lm_proc_before_from file_lm ps cs (f0_st f0) pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH.
Qed.

Lemma proc_before_f_lm_o ps cs f0 I :
  proc_before_f ps cs f0 I = lm_proc_before file_lm ps cs (f0_st f0) I.
Proof using. apply proc_before_from_f_lm_o. Qed.

Lemma proc_stream_f_lm_o ps cs f0 I :
  proc_stream_f ps cs f0 I = lm_proc_stream file_lm ps cs (f0_st f0) I.
Proof using. rewrite /proc_stream_f /lm_proc_stream. by rewrite proc_before_f_lm_o. Qed.

(* ---- what section 0 said, as corollaries ---- *)
Lemma fab_ok (I : list (bv 8)) (a i : nat) (b : bv 8) :
  fab I a !! i = Some b ->
  ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true.
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_ok file_lm file_hooks).
Qed.

Lemma fab_is (I : list (bv 8)) (a : nat) :
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a = cont ∅ (fline I) (ralt_dec a).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_is file_lm file_hooks).
Qed.

Lemma fab_at (I : list (bv 8)) (a : nat) (s : fstate) :
  ralt_ok (fline I) (ralt_dec a) -> fstate_free (ralt_dec a) = true ->
  fab I a = cont s (fline I) (ralt_dec a).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_at file_lm file_hooks).
Qed.

Lemma fab_len_ge2 (I : list (bv 8)) (a : nat) :
  fapr I a -> (2 <= length (fab I a))%nat.
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_len_ge2 file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fab_dollar (I : list (bv 8)) (a : nat) :
  fapr I a ->
  fab I a !! (length (fab I a) - 2)%nat = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_dollar file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fab_space (I : list (bv 8)) (a : nat) :
  fapr I a ->
  fab I a !! (length (fab I a) - 1)%nat = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite fab_lm. intros Hpr.
  exact (lm_ab_space file_lm file_hooks I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fapr_faprs (I : list (bv 8)) (a : nat) : fapr I a -> faprs I a.
Proof using.
  intros (H1 & _ & H3). exact (conj H1 H3).
Qed.

Lemma fabs_fab (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  fapr I a -> fabs s0 cs I a = fab I a.
Proof using.
  rewrite fabs_lm fab_lm. intros Hpr.
  exact (lm_abs_ab file_lm file_hooks s0 cs I a (proj1 (fapr_lm I a) Hpr)).
Qed.

Lemma fabs_prompt (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a -> exists pre : list (bv 8), fabs s0 cs I a = pre ++ u_prompt.
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_prompt file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_len_ge2 (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a -> (2 <= length (fabs s0 cs I a))%nat.
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_len_ge2 file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_dollar (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a ->
  fabs s0 cs I a !! (length (fabs s0 cs I a) - 2)%nat
  = Some (u_prompt !!! 0%nat).
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_dollar file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fabs_space (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : nat) :
  faprs I a ->
  fabs s0 cs I a !! (length (fabs s0 cs I a) - 1)%nat
  = Some (u_prompt !!! 1%nat).
Proof using.
  rewrite fabs_lm. intros Hpr.
  exact (lm_abs_space file_lm file_hooks s0 cs I a (proj1 (faprs_lm I a) Hpr)).
Qed.

Lemma fab_pan (I : list (bv 8)) : fab I (fpan_of (fline I)) = alt_panic.
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_pan file_lm file_lm_laws file_hooks).
Qed.

Lemma fab_exf (I : list (bv 8)) :
  fab I (fexf_of (fline I)) = fexfb (fline I).
Proof using.
  rewrite fab_lm fline_lm. apply (lm_ab_exf file_lm file_hooks).
Qed.

Lemma fapr_exf (I : list (bv 8)) : fapr I (fexf_of (fline I)).
Proof using.
  apply fapr_lm. apply (lm_apr_exf file_lm file_hooks).
Qed.



