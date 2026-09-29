(* ===================================================================== *)
(*  UShUModBase.v -- THE UNION ROUND'S PURE PREAMBLE, shared by its SHAPE  *)
(*  MODULES (design: claude-notes/design/shape-modules.md, stage 1).      *)
(*                                                                        *)
(*  What every module and the round read of the union model: the file's  *)
(*  codes read back as the file's ([ulm_*_R]), the line off the input's   *)
(*  last body ([ul_lastbody], [uline_of_u_eq]), the exec rows shared by  *)
(*  the cat, sync and seccomp supplies ([ucat_rows]) and the admitted     *)
(*  line families ([ush_line_union], [ush_line_upipe]).  Moved out of the  *)
(*  round file verbatim when the round became the fold over the modules   *)
(*  ([UShUPipes.sh_round_holds_union_closed]; the round file is gone).      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import FdSlots.
Require Import LineWords.
Require Import FileDisc.
Require Import FileState.
Require Import UkSh.
Require Import FileHooks.
Require Import LineModel.
Require Import LineModelLinks.
Require Import PipesDisc.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UShURoundDefs.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ===================================================================== *)
(*  S0  THE UNION'S CODES AT A FILE LINE, READ BACK AS THE FILE'S         *)
(* ===================================================================== *)
(* at every line but a pipeline, the file's range condition *)
Lemma ulm_ok_R' (s : fstate) (l : uline) (a : ralt) :
  (forall p n, l <> LPipe p n) -> lm_ok U s l (lm_dec U (ualt_code (UR a))) <-> ralt_ok l a.
Proof using.
  intros Hnp. change (lm_ok ulmG) with (uok adm_u_g). change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code.
  destruct l as [ws | ws Nf | Nf | p n | ws |]; [cbn [uok]; reflexivity | cbn [uok]; reflexivity
                                   | cbn [uok]; reflexivity | | cbn [uok]; reflexivity
                                   | cbn [uok]; reflexivity].
  exfalso. exact (Hnp p n eq_refl).
Qed.

Lemma ulm_ok_R (s : fstate) (l : uline) (a : ralt) :
  uline_nopipe l -> lm_ok U s l (lm_dec U (ualt_code (UR a))) <-> ralt_ok l a.
Proof using. intros Hnp. exact (ulm_ok_R' s l a (proj1 Hnp)). Qed.

Lemma ulm_cont_R (s : fstate) (l : uline) (a : ralt) :
  lm_cont U s l (lm_dec U (ualt_code (UR a))) = cont s l a.
Proof using.
  change (lm_cont ulmG) with ucont. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_step_R (s : fstate) (l : uline) (a : ralt) :
  lm_step U s l (lm_dec U (ualt_code (UR a))) = fsm s l a.
Proof using.
  change (lm_step ulmG) with ustep. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_term_R (a : ralt) : lm_term U (lm_dec U (ualt_code (UR a))) = false.
Proof using.
  change (lm_term ulmG) with uterm. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_panic_R (a : ralt) : lm_panic U (lm_dec U (ualt_code (UR a))) = ralt_panic a.
Proof using.
  change (lm_panic ulmG) with upanic. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_free_R (a : ralt) : lmh_free K (lm_dec U (ualt_code (UR a))) = fstate_free a.
Proof using.
  change (lmh_free ulmG_hooks) with ufree. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

(* a state-free file alternative of the round's line is the record's own
   (at the sync line too, which is no pipeline) *)
Lemma ulm_apr_R' (I : list (bv 8)) (a : ralt) :
  (forall p n, ul I <> LPipe p n) -> ralt_ok (ul I) a -> fstate_free a = true ->
  ralt_panic a = false -> lm_apr U K I (ualt_code (UR a)).
Proof using.
  intros Hnp Hok Hfr Hp. rewrite /lm_apr. split_and!.
  - apply (ulm_ok_R' _ (ul I) a Hnp). exact Hok.
  - rewrite ulm_free_R. exact Hfr.
  - rewrite ulm_panic_R. exact Hp.
Qed.

Lemma ulm_ab_R' (I : list (bv 8)) (a : ralt) :
  (forall p n, ul I <> LPipe p n) -> ralt_ok (ul I) a -> fstate_free a = true ->
  lm_ab U K I (ualt_code (UR a)) = cont ∅ (ul I) a.
Proof using.
  intros Hnp Hok Hfr. rewrite /lm_ab decide_True.
  - exact (ulm_cont_R ∅ (ul I) a).
  - split; [apply (ulm_ok_R' ∅ (ul I) a Hnp); exact Hok | rewrite ulm_free_R; exact Hfr].
Qed.

Lemma ulm_apr_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> fstate_free a = true ->
  ralt_panic a = false -> lm_apr U K I (ualt_code (UR a)).
Proof using.
  intros Hnp Hok Hfr Hp. rewrite /lm_apr. split_and!.
  - apply (ulm_ok_R _ (ul I) a Hnp). exact Hok.
  - rewrite ulm_free_R. exact Hfr.
  - rewrite ulm_panic_R. exact Hp.
Qed.

Lemma ulm_aprs_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> ralt_panic a = false ->
  lm_aprs U I (ualt_code (UR a)).
Proof using.
  intros Hnp Hok Hp. rewrite /lm_aprs. split_and!.
  - intros s. apply (ulm_ok_R s (ul I) a Hnp). exact Hok.
  - rewrite ulm_panic_R. exact Hp.
  - exact (ulm_term_R a).
Qed.

Lemma ulm_ab_R (I : list (bv 8)) (a : ralt) :
  uline_nopipe (ul I) -> ralt_ok (ul I) a -> fstate_free a = true ->
  lm_ab U K I (ualt_code (UR a)) = cont ∅ (ul I) a.
Proof using.
  intros Hnp Hok Hfr. rewrite /lm_ab decide_True.
  - exact (ulm_cont_R ∅ (ul I) a).
  - split; [apply (ulm_ok_R ∅ (ul I) a Hnp); exact Hok | rewrite ulm_free_R; exact Hfr].
Qed.

(* the union's parse agrees with the file's wherever the file parsed *)
Lemma uline_of_u_eq (b : list (bv 8)) (l0 : uline) :
  uline_of b = l0 -> l0 <> LEcho [] -> uline_of_u b = l0.
Proof using.
  rewrite /uline_of /uline_of_u. destruct (parse_line b) as [l |]; cbn.
  - intros H _. exact H.
  - intros Heq Hne. exfalso. apply Hne. rewrite -Heq. reflexivity.
Qed.

Lemma ul_lastbody (I : list (bv 8)) : ul I = uline_of_u (UkSh.ush_lastbody I).
Proof using. reflexivity. Qed.

(* the round's line is the last of the input's lines (the witness [flw]
   ends at it, sync SY3-A3bc) *)
Lemma ulines_in_last (I : list (bv 8)) :
  (0 < nlines I)%nat -> stdpp.list_basics.list.last (UnionAdm.ulines_in I) = Some (ul I).
Proof using.
  intros Hp. rewrite last_lookup UnionAdm.ulines_in_length.
  rewrite /UnionAdm.ulines_in list_lookup_fmap ul_lastbody /UkSh.ush_lastbody.
  rewrite (list_lookup_lookup_total_lt (bodies_of I) (pred (nlines I)));
    [| rewrite /nlines in Hp |- *; lia].
  rewrite (_ : pred (nlines I) = (nlines I - 1)%nat); [reflexivity | lia].
Qed.

(* the union's admitted line shapes: the file's three, and the pipelines
   the union's admission lets through *)
Definition ush_line_pipeU (p : producer) (n : list filt) : Prop :=
  adm_u_g (LPipes p n) = true /\ pl_ok (LPipes p n).

(* a [seccomp x] line IS among the loop's lines now the model's seccomp
   knob is on ([UnionDisc.adm_s_on]; seccomp lane S4): [uline_ok]'s
   [secc_ok] already asks for a non-empty argument list, which is all the
   knob admits *)
Definition ush_line_union (l : uline) : Prop :=
  match l with LPipe p n => ush_line_pipeU p n | _ => True end.

Definition ush_line_upipe (l : uline) : Prop :=
  exists (p : producer) (n : list filt), l = LPipe p n /\ ush_line_pipeU p n.

(* the cat child's rows (fd 0 the console, fd 1 the console, fd 2 the console), shared by the cat, sync and seccomp supplies *)
Definition ucat_rows (ld : list fdstate) : Prop :=
  UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld.
