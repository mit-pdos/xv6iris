(* ===================================================================== *)
(*  UShURoundDefs.v -- SH'S ROUND AT THE UNION: THE TIES, THE DEED, THE   *)
(*  FAMILIES AND THE WIDENED CREDENTIAL (cut C9f1; design:                *)
(*  claude-notes/design/union.md section 3, 'The credential the main loop *)
(*  carries', review items S6 and B3).                                    *)
(*                                                                        *)
(*  [UShRound]'s S0-S2 moved to the union claim [UnionOut.ucl] and its    *)
(*  record at the round's boot state ([UnionLinkInstAt.union_link_inst_at *)
(*  ug s0]).  S6: this is NOT a record swap -- the file round's ties call *)
(*  the file model directly ([fsm], [cont], [ralt_ok], [ralt_dec],        *)
(*  [UCatOut.cat_st]), so they are restated here over the UNION model     *)
(*  [UnionDisc.ulmU]: the round's state is [lm_upto ulmU] ([ust]), its    *)
(*  line [lm_line_at ulmU] ([ul]), its alternatives the union's codes      *)
(*  ([ualt_code (UR a)] at a file line), their step [lm_step ulmU].  The  *)
(*  ties are stated over the model's own vocabulary, so they hold at      *)
(*  every line shape, the pipelines included.                             *)
(*                                                                        *)
(*  THE WIDENED CREDENTIAL [Wcu] is [UkShPipesFork.pterm_wcN]'s shape:    *)
(*  the file family [Wcf] at every index, or below index 3 a pipeline     *)
(*  round's TERMINAL shape [PT] (cursor [5 + p]), or at index 0 its       *)
(*  COMMITTED shape [PD] with the deed at its PRE tie (C9f2: the block is *)
(*  not filed yet, so DONE's longer lower bound does not exist; the       *)
(*  filing makes DONE of it, a pipeline's step being the identity).       *)
(*  Amendment B3: the                                                     *)
(*  terminal shape carries NO deed (after a fork failure at node 0 the    *)
(*  stray [cat f] still holds it); the next read is refuted by D4 or       *)
(*  tainted, and the taint is DONE ([sh_deed_taint]).  The two shapes are *)
(*  PARAMETERS here: the pipeline cut (C9f2) names them, and nothing the  *)
(*  file shapes prove reads them -- [Wcu I 3] collapses to [Wcf I 3].     *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import AppCfg.
Require Import AppInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.
Require Import FileLinksAt.
Require Import FileLinkGen.
Require Import LinkRec.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShFork.
Require Import UShPanic.
Require Import PipeOut.
Require Import PipesView.
Require Import PipeOutN.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionView.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import UnionLinkInstAt.
Require EchoLinks.
Require UShFileRedir.             (* the file round's model-free pure lemmas *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.

Local Notation U := ulmU.
Local Notation K := ulmU_hooks.

(* ===================================================================== *)
(*  S0  THE THREE TIES, OVER THE UNION MODEL                              *)
(* ===================================================================== *)

(* the round's line and the state before it *)
Definition ul (I : list (bv 8)) : uline := lm_line_at U I.
Definition ust (cs : list nat) (sb : fstate) (I : list (bv 8)) : fstate :=
  lm_upto U cs sb (bodies_of I) (nlines I - 1).

Definition upre_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate) : Prop :=
  length cs = (nlines I - 1)%nat /\ c = ust cs sb I.

Definition udone_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate) : Prop :=
  length cs = nlines I /\ c = lm_after U cs sb I.

Definition upend_tie_at (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
    (a : nat) : Prop :=
  length cs = (nlines I - 1)%nat
  /\ (0 < nlines I)%nat
  /\ lm_ok U (ust cs sb I) (ul I) (lm_dec U a)
  /\ lm_term U (lm_dec U a) = false
  /\ lm_cont U (ust cs sb I) (ul I) (lm_dec U a) = u_prompt
  /\ c = lm_step U (ust cs sb I) (ul I) (lm_dec U a).

Definition upend_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate) : Prop :=
  exists a : nat, upend_tie_at cs sb I c a.

(* ---- the identity steps ---- *)

(* the silent alternative moves no file, at every line *)
Lemma ustep_noc (s : fstate) (l : uline) :
  lm_step U s l (lm_dec U (lmh_noc K l)) = s.
Proof using.
  change (lm_step ulmU) with ustep. change (lm_dec ulmU) with ualt_dec.
  change (lmh_noc ulmU_hooks) with unoc.
  destruct l as [ws | ws | | p n]; cbn [unoc].
  - rewrite ualt_dec_R. exact (UShFileRedir.fsm_fnoc s (LEcho ws)).
  - rewrite ualt_dec_R. exact (UShFileRedir.fsm_fnoc s (LEchoF ws)).
  - rewrite ualt_dec_R. exact (UShFileRedir.fsm_fnoc s LCat).
  - rewrite ualt_dec_code. by destruct p.
Qed.

(* a panic alternative moves no file, at every line *)
Lemma ustep_panic (s : fstate) (l : uline) (a : lm_alt U) :
  lm_panic U a = true -> lm_step U s l a = s.
Proof using.
  change (lm_step ulmU) with ustep. change (lm_panic ulmU) with upanic.
  destruct a as [r | x | x]; cbn [upanic ustep]; [| intros _; reflexivity | intros _; reflexivity].
  intros Hp. exact (UShFileRedir.fsm_panic s l r Hp).
Qed.

(* an alternative whose output is the bare prompt is not a panic *)
Lemma ucont_prompt_nopanic (s : fstate) (l : uline) (a : lm_alt U) :
  lm_cont U s l a = u_prompt -> lm_panic U a = false.
Proof using.
  intros H. destruct (lm_panic U a) eqn:Hp; [| reflexivity].
  exfalso. rewrite (lml_cont_panic ulmU_laws s l a Hp) in H.
  apply (f_equal length) in H.
  rewrite FileLinksLine.alt_panic_len5 EchoLinks.wr_prompt_len in H. discriminate H.
Qed.

(* ---- filing one alternative moves the state by one step ---- *)
Lemma ulm_after_snoc (cs : list nat) (a : nat) (sb : fstate) (I : list (bv 8)) :
  length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
  lm_after U (cs ++ [a]) sb I = lm_step U (ust cs sb I) (ul I) (lm_dec U a).
Proof using.
  intros Hlen Hpos. rewrite /lm_after /ust /ul /lm_line_at.
  destruct (nlines I) as [| n] eqn:Hn; [lia |].
  try rewrite Hn in Hlen.
  replace (S n - 1)%nat with n in Hlen |- * by lia.
  cbn [lm_upto]. f_equal.
  - apply (lm_upto_ext ulmU); [| intros j _; reflexivity].
    intros j Hj. rewrite list_lookup_total_alt lookup_app_l;
      [by rewrite -list_lookup_total_alt | lia].
  - rewrite /lm_at -Hlen ll_snoc_lookup_total. reflexivity.
Qed.

Lemma udone_tie_snoc (cs : list nat) (a : nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
  c = lm_step U (ust cs sb I) (ul I) (lm_dec U a) ->
  udone_tie (cs ++ [a]) sb I c.
Proof using.
  intros Hl Hp Hc. split; [rewrite length_app; cbn [length]; lia |].
  rewrite (ulm_after_snoc cs a sb I Hl Hp). exact Hc.
Qed.

(* DONE-of-PEND: the console files the alternative the deed decided *)
Lemma udone_tie_of_pend (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
    (a : nat) :
  upend_tie_at cs sb I c a -> udone_tie (cs ++ [a]) sb I c.
Proof using.
  intros (Hl & Hp & _ & _ & _ & Hc). exact (udone_tie_snoc cs a sb I c Hl Hp Hc).
Qed.

(* DONE-of-PRE at an alternative whose step is the identity *)
Lemma udone_tie_of_pre_id (cs : list nat) (a : nat) (sb : fstate)
    (I : list (bv 8)) (c : fstate) :
  (0 < nlines I)%nat -> upre_tie cs sb I c ->
  lm_step U (ust cs sb I) (ul I) (lm_dec U a) = ust cs sb I ->
  udone_tie (cs ++ [a]) sb I c.
Proof using.
  intros Hp [Hl Hc] Hid. apply (udone_tie_snoc cs a sb I c Hl Hp).
  rewrite Hid. exact Hc.
Qed.

(* PEND-of-PRE at the line's silent alternative *)
Lemma upend_tie_of_pre (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate) :
  (0 < nlines I)%nat -> upre_tie cs sb I c ->
  upend_tie_at cs sb I c (lmh_noc K (ul I)).
Proof using.
  intros Hp [Hl Hc]. split_and!;
    [ exact Hl | exact Hp | exact (lmh_noc_ok K _ _)
    | exact (lmh_free_term K _ (lmh_noc_free K _))
    | exact (lmh_noc_cont K _ _) | rewrite ustep_noc; exact Hc ].
Qed.

(* at a FILED list: the holder of PRE meets a list one longer that
   extends its own, and the filed alternative's step is the identity --
   or nothing is filed at all *)
Lemma udone_tie_of_pre_prefix (cs cs' : list nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  upre_tie cs' sb I c -> length cs = nlines I -> cs' `prefix_of` cs ->
  ((0 < nlines I)%nat ->
   lm_step U (ust cs' sb I) (ul I) (lm_at U cs (nlines I - 1)%nat) = ust cs' sb I) ->
  udone_tie cs sb I c.
Proof using.
  intros [Hl' Hc] Hl Hpre Hid.
  destruct (nlines I) as [| n] eqn:Hn.
  - try rewrite Hn in Hl. apply nil_length_inv in Hl. subst cs.
    split; [by rewrite Hn |].
    rewrite Hc /ust /lm_after Hn. reflexivity.
  - try rewrite Hn in Hl. try rewrite Hn in Hl'. try rewrite Hn in Hid.
    replace (S n - 1)%nat with n in * by lia.
    destruct Hpre as [rest ->].
    assert (Hr : length rest = 1%nat) by (rewrite length_app in Hl; lia).
    destruct rest as [| a [| a' rest']]; cbn [length] in Hr; [lia | | lia].
    apply (udone_tie_snoc cs' a sb I c); [rewrite Hn; lia | rewrite Hn; lia |].
    rewrite /lm_at -Hl' ll_snoc_lookup_total in Hid.
    rewrite (Hid ltac:(lia)). exact Hc.
Qed.

(* ...and the banner-owed reading of it: the last filed alternative is a
   panic, whose step is the identity *)
Lemma udone_tie_of_pre_ban (cs cs' : list nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  upre_tie cs' sb I c -> length cs = nlines I -> cs' `prefix_of` cs ->
  (I = [] \/ lm_panic U (lm_at U cs (nlines I - 1)%nat) = true) ->
  udone_tie cs sb I c.
Proof using.
  intros Hpre Hl Hp Hban.
  apply (udone_tie_of_pre_prefix cs cs' sb I c Hpre Hl Hp).
  intro Hpos. destruct Hban as [-> | Hpan];
    [rewrite nlines_nil in Hpos; lia | exact (ustep_panic _ _ _ Hpan)].
Qed.

(* PRE-of-DONE: a new complete line makes the settled state the state
   BEFORE the new round *)
Lemma upre_tie_of_done (cs : list nat) (sb : fstate) (I l : list (bv 8)) (c : fstate) :
  rest_of I = [] -> wl_nl ∉ l ->
  udone_tie cs sb I c -> upre_tie cs sb (I ++ l ++ [wl_nl]) c.
Proof using.
  intros Hr Hl [Hlen Hc].
  assert (Hassoc : I ++ l ++ [wl_nl] = (I ++ l) ++ [wl_nl])
    by (by rewrite app_assoc).
  assert (Hn : nlines (I ++ l ++ [wl_nl]) = S (nlines I))
    by (rewrite Hassoc nlines_snoc_nl (EchoLinks.nlines_app_nonl I l Hl);
        reflexivity).
  split; [rewrite Hn; lia |].
  rewrite Hc /lm_after /ust Hn.
  replace (S (nlines I) - 1)%nat with (nlines I) by lia.
  apply (lm_upto_ext ulmU); [intros j _; reflexivity |].
  intros j Hj.
  pose proof (bodies_of_app I (l ++ [wl_nl])) as Hpre.
  destruct (lookup_lt_is_Some_2 (bodies_of I) j Hj) as [x Hx].
  rewrite !list_lookup_total_alt Hx (prefix_lookup_Some _ _ _ _ Hx Hpre).
  reflexivity.
Qed.

(* ---- VACUITY: every tie has an inhabitant ---- *)
Example upre_tie_inhabited : upre_tie [] None [] None.
Proof using. split; vm_compute; reflexivity. Qed.

Example udone_tie_inhabited : udone_tie [] None [] None.
Proof using. split; vm_compute; reflexivity. Qed.

(* ---- a file line's alternatives at the union ---- *)
Lemma ulm_dec_R (a : ralt) : lm_dec U (ualt_code (UR a)) = UR a.
Proof using. exact (ualt_dec_code (UR a)). Qed.

(* every alternative of an [echo] or a [cat f] line leaves [f] alone *)
Lemma ustep_id_echo (s : fstate) (ws : list (list (bv 8))) (a : lm_alt U) :
  lm_step U s (LEcho ws) a = s.
Proof using.
  change (lm_step ulmU) with ustep. by destruct a.
Qed.

Lemma ustep_id_cat (s : fstate) (a : lm_alt U) : lm_step U s LCat a = s.
Proof using.
  change (lm_step ulmU) with ustep. by destruct a.
Qed.

(* ===================================================================== *)
(*  S1  THE DEED, THE FAMILIES AND THE WIDENED CREDENTIAL                 *)
(* ===================================================================== *)
Section UShURoundDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).
  Local Notation T := (file_taint (fgn_cl gf)).
  (* the era's boot state (RULING H'): the index the record and the deed
     share *)
  Context (s0 : fstate).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PA := (union_params_at ug s0).

  #[local] Instance uhd_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance uhd_T_tl0 : Timeless T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.

  (* the record's two families the loop carries, at [s0] *)
  Definition uWcl (I : list (bv 8)) (p : nat) : iProp Σ := lk_lcred FI (S gen_id) I p.
  Definition uWbl (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins, lk_pin FI (S gen_id) v ∗ lk_ban FI (S gen_id) v I 0%nat)%I.

  Global Instance uWcl_timeless I p : Timeless (uWcl I p).
  Proof using . rewrite /uWcl. apply lk_lcred_timeless. Qed.
  Global Instance uWbl_timeless I : Timeless (uWbl I).
  Proof using .
    rewrite /uWbl. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_ban_tl].
  Qed.

  (* THE DEED, tied to the model's state by a pure tie over the choice
     list the holder has a lower bound of *)
  Definition ush_deed_at
      (tie : list nat -> fstate -> list (bv 8) -> fstate -> Prop)
      (sb : fstate) (I : list (bv 8)) : iProp Σ :=
    ((∃ (cs : list nat) (s : dst) (v : era_pins),
        fown r s
        ∗ ⌜tie cs sb I (dst_content s)⌝
        ∗ f_typed (fgn_cl gf) s
        ∗ era_pin (fgn_echo gf) (S gen_id) v ∗ cs_lb v cs)
     ∨ T)%I.

  (* the line's witness rides with the deed from the read to the lend *)
  Definition uline_wit (I : list (bv 8)) : iProp Σ :=
    (FileLinksLine.flw gf I ∨ T)%I.

  Global Instance uline_wit_persistent I : Persistent (uline_wit I).
  Proof using . rewrite /uline_wit /file_taint /echo_taint. apply _. Qed.
  Global Instance uline_wit_timeless I : Timeless (uline_wit I).
  Proof using . rewrite /uline_wit /file_taint /echo_taint. apply _. Qed.

  Definition ush_pre_at (sb : fstate) (I : list (bv 8)) : iProp Σ :=
    (ush_deed_at upre_tie sb I ∗ uline_wit I)%I.
  Definition ush_done_at : fstate -> list (bv 8) -> iProp Σ := ush_deed_at udone_tie.
  Definition ush_pend_at : fstate -> list (bv 8) -> iProp Σ := ush_deed_at upend_tie.

  Local Notation PRE := (ush_pre_at s0).
  Local Notation DONE := (ush_done_at s0).
  Local Notation PEND := (ush_pend_at s0).

  Global Instance ush_deed_at_timeless tie sb I : Timeless (ush_deed_at tie sb I).
  Proof using . rewrite /ush_deed_at /file_taint /echo_taint. apply _. Qed.
  Global Instance ush_pre_at_timeless sb I : Timeless (ush_pre_at sb I).
  Proof using . rewrite /ush_pre_at. apply _. Qed.

  Lemma ush_deed_taint tie sb I : T -∗ ush_deed_at tie sb I.
  Proof using . iIntros "#HT". rewrite /ush_deed_at. by iRight. Qed.

  Lemma ush_pre_taint sb I : T -∗ ush_pre_at sb I.
  Proof using .
    iIntros "#HT". rewrite /ush_pre_at /uline_wit.
    iSplitL; [iApply (ush_deed_taint with "HT") | by iRight].
  Qed.

  (* THE FILE FAMILY AT THE UNION ([UShRound.Wcf]'s positions) *)
  Definition uWcf (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => ((uWcl I 0%nat ∗ DONE I) ∨ (uWcl I 3%nat ∗ PEND I))%I
    | S O => (uWcl I 1%nat ∗ DONE I)%I
    | S (S O) => (uWcl I 2%nat ∗ DONE I)%I
    | _ => (uWcl I 3%nat ∗ PRE I)%I
    end.
  Definition uWbf (I : list (bv 8)) : iProp Σ := (uWbl I ∗ DONE I)%I.

  Lemma uWcf_0 I :
    uWcf I 0%nat = ((uWcl I 0%nat ∗ DONE I) ∨ (uWcl I 3%nat ∗ PEND I))%I.
  Proof using . reflexivity. Qed.
  Lemma uWcf_1 I : uWcf I 1%nat = (uWcl I 1%nat ∗ DONE I)%I.
  Proof using . reflexivity. Qed.
  Lemma uWcf_2 I : uWcf I 2%nat = (uWcl I 2%nat ∗ DONE I)%I.
  Proof using . reflexivity. Qed.
  Lemma uWcf_S3 I p : uWcf I (S (S (S p))) = (uWcl I 3%nat ∗ PRE I)%I.
  Proof using . reflexivity. Qed.

  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (uWcl _ _) => apply uWcl_timeless
    | |- Timeless (uWbl _) => apply uWbl_timeless
    | |- Timeless (ush_pre_at _ _) => apply ush_pre_at_timeless
    | |- Timeless (ush_done_at _ _) => apply ush_deed_at_timeless
    | |- Timeless (ush_pend_at _ _) => apply ush_deed_at_timeless
    | |- _ => apply _
    end.

  Global Instance uWcf_timeless I p : Timeless (uWcf I p).
  Proof using .
    destruct p as [| [| [| p]]];
      [rewrite uWcf_0 | rewrite uWcf_1 | rewrite uWcf_2 | rewrite uWcf_S3]; tl_leaf.
  Qed.
  Global Instance uWbf_timeless I : Timeless (uWbf I).
  Proof using . rewrite /uWbf. tl_leaf. Qed.

  (* the head: nothing filed, the deed at its own boot value *)
  Lemma ush_done_head (s : dst) (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ cs_lb v [] -∗
    fown r s -∗ f_typed (fgn_cl gf) s -∗
    ush_done_at (dst_content s) [].
  Proof using .
    iIntros "#Hpin #Hcs Hd #Hty". rewrite /ush_done_at /ush_deed_at. iLeft.
    iExists [], s, v. iFrame "Hd Hpin Hcs Hty". iPureIntro.
    split; [by rewrite nlines_nil | ].
    rewrite /lm_after nlines_nil. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S2  THE RECORD'S CONVERSIONS AT THE FAMILY                          *)
  (* =================================================================== *)
  Lemma uHcltaint (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ T -∗ uWcl I p.
  Proof using . iIntros "Hp HT". iApply (lk_lcred_taint FI (S gen_id) I p v with "Hp HT"). Qed.

  Lemma uWcf_taint (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ T -∗ uWcf I p.
  Proof using .
    iIntros "#Hpin #HT". destruct p as [| [| [| p]]].
    - rewrite uWcf_0. iLeft. iSplitL "";
        [iApply (uHcltaint I 0%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")].
    - rewrite uWcf_1. iSplitL "";
        [iApply (uHcltaint I 1%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")].
    - rewrite uWcf_2. iSplitL "";
        [iApply (uHcltaint I 2%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")].
    - rewrite uWcf_S3. iSplitL "";
        [iApply (uHcltaint I 3%nat v with "Hpin HT") | iApply (ush_pre_taint with "HT")].
  Qed.


  (* two lower bounds of one choice list line up, and at equal length they
     AGREE *)
  Lemma ucs_lb_prefix_len (v : era_pins) (cs cs' : list nat) :
    (length cs' <= length cs)%nat ->
    cs_lb v cs -∗ cs_lb v cs' -∗ ⌜cs' `prefix_of` cs⌝.
  Proof using .
    intros Hl. iIntros "#H1 #H2".
    iDestruct (cs_lb_cmp v cs cs' with "H1 H2") as %[Hp | Hp];
      iPureIntro; [| exact Hp].
    rewrite (prefix_length_eq cs cs' Hp Hl). done.
  Qed.

  Lemma ucs_lb_agree_len (v : era_pins) (cs cs' : list nat) :
    length cs = length cs' ->
    cs_lb v cs -∗ cs_lb v cs' -∗ ⌜cs = cs'⌝.
  Proof using .
    intros Hl. iIntros "#H1 #H2".
    iDestruct (ucs_lb_prefix_len v cs cs' (Nat.eq_le_incl _ _ (eq_sym Hl)) with "H1 H2")
      as %Hp.
    iPureIntro. symmetry. apply (prefix_length_eq cs' cs Hp). exact (Nat.eq_le_incl _ _ Hl).
  Qed.

  (* the X arm of the line credential (an N-writer round's block, unfiled)
     is a PIPELINE's: at a file line it is refuted *)
  Lemma union_X_at_nopipe (k : nat) (v : era_pins) (I : list (bv 8)) :
    uline_nopipe (ul I) -> union_X_at ug s0 k v I -∗ False.
  Proof using .
    intros Hnp. rewrite /union_X_at /union_X.
    iIntros "[[_ Hx] _]". iDestruct "Hx" as (sR lR pre) "([%HlR _] & _)".
    iPureIntro. change (pv_line pview_unionU (lineV U I)) with (uv_line (ul I)) in HlR.
    destruct (uv_line_some (ul I) lR HlR) as (p & n & Hl & _).
    exact (Hnp p n Hl).
  Qed.

  (* the record's block-owed credential, closed at the round's stage *)
  Lemma uWcl3_close (I : list (bv 8)) (v : era_pins) (ps cs : list nat) (P : nat) :
    lm_wr_blk_t U ps cs s0 I P ->
    era_pin (fgn_echo gf) (S gen_id) v -∗
    gcur U PA v ps cs s0 I P (S gen_id) -∗ uWcl I 3%nat.
  Proof using .
    intro Hw. iIntros "#Hpin Hc".
    rewrite /uWcl /lk_lcred.
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    iExists v. iFrame "Hpin". rewrite /gwc_blk. iLeft. iExists ps, cs, s0, P.
    cbn [lm_blkcs]. rewrite Nat.add_0_r.
    rewrite /gcur. iDestruct "Hc" as "(Htn & #Hps & #Hcs & #HE & #Hf)".
    iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
  Qed.

  (* THE FOLD AT POSITION 0: a line credential beside a deed at PRE is a
     position-0 credential whenever every alternative of the line leaves
     [f] alone, at a file line (the X arm refuted) *)
  Lemma uWcf0_of_pre_line_id (I : list (bv 8)) :
    uline_nopipe (ul I) ->
    (forall (s : fstate) (a : lm_alt U), lm_step U s (ul I) a = s) ->
    uWcl I 0%nat -∗ PRE I -∗ uWcf I 0%nat.
  Proof using .
    intros Hnp Hid. iIntros "Hc Hp". rewrite uWcf_0.
    rewrite {1}/ush_pre_at /ush_deed_at. iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iLeft. iFrame "Hc". iApply (ush_deed_taint with "HT"). }
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    pose proof Htie as [Hlen _].
    rewrite /uWcl /lk_lcred.
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iAssert (∀ cs : list nat, ⌜length cs = nlines I⌝ -∗ ⌜cs' `prefix_of` cs⌝ -∗
               cs_lb v cs -∗ fown r s -∗ DONE I)%I as "Hdone".
    { iIntros (cs) "%Hl %Hpre #Hcs Hd". rewrite /ush_done_at /ush_deed_at. iLeft.
      iExists cs, s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
      apply (udone_tie_of_pre_prefix cs cs' s0 I _ Htie Hl Hpre).
      intros _. apply Hid. }
    rewrite /gwc_line /gwc_pro /gwc_post /gcur.
    cbn [gH gW gT union_params_at]. rewrite /f0w_at /fhead_at.
    iDestruct "Hc" as "[Hpro | [Hblk | Hx]]";
      [| | iDestruct (union_X_at_nopipe _ _ I Hnp with "Hx") as "[]"].
    - (* the prologue: the last filed alternative is a panic, or the head *)
      iDestruct "Hpro" as "[Hpro | [Hhd | #HT]]".
      + iDestruct "Hpro" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
        subst sw.
        pose proof Hw as (_ & _ & Hn & _).
        iDestruct (ucs_lb_prefix_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %Hpre.
        iLeft. iSplitL "Htn".
        * iExists v. iFrame "Hpin". iLeft. iLeft. iExists ps, cs, s0, P.
          iFrame "Htn Hps Hcs HE Hf". iSplit; by iPureIntro.
        * iApply ("Hdone" $! cs with "[%] [%] Hcs Hd"); [lia | exact Hpre].
      + iDestruct "Hhd" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & #Hvf & Hpre)".
        iLeft. iSplitL "Htn Hpre".
        * iExists v. iFrame "Hpin". iLeft. iRight. iLeft.
          iFrame "Htn Hps Hcs HE Hvf Hpre". by iSplit; iPureIntro.
        * iApply ("Hdone" $! [] with "[%] [%] Hcs Hd").
          { subst I. by rewrite nlines_nil. }
          { subst I. rewrite nlines_nil in Hlen. cbn in Hlen.
            apply nil_length_inv in Hlen. subst cs'. done. }
      + iLeft. iSplitL "";
          [iApply (uHcltaint I 0%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")].
    - (* a block written up to its prompt, at some alternative *)
      iDestruct "Hblk" as (a) "[%Hapr Hblk]".
      iDestruct "Hblk" as "[Hblk | #HT]"; last first.
      { iLeft. iSplitL "";
          [iApply (uHcltaint I 0%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")]. }
      iDestruct "Hblk" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
      subst sw.
      pose proof Hw as [(_ & _ & Hn & _) _].
      destruct (length (lm_abs U s0 cs I a) - 2)%nat as [| i] eqn:Hi.
      + (* the prompt is the block's first byte: still owed, deed PEND *)
        cbn [lm_blkcs]. rewrite Nat.add_0_r.
        iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
        iRight. iSplitL "Htn".
        * iApply (uWcl3_close I v ps cs P Hw with "Hpin [Htn]").
          rewrite /gcur. cbn [gW union_params_at]. rewrite /f0w_at.
          iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
        * rewrite /ush_pend_at /ush_deed_at. iLeft. iExists cs, s, v.
          iFrame "Hd Hty Hpin Hcs". iPureIntro. exists (lmh_noc K (ul I)).
          apply (upend_tie_of_pre cs s0 I _ ltac:(lia) Htie).
      + (* a byte before the prompt: the alternative is filed, deed DONE *)
        cbn [lm_blkcs].
        iDestruct (ucs_lb_prefix_len v (cs ++ [a]) cs'
                     ltac:(rewrite length_app; cbn [length]; lia)
                     with "Hcs Hcs'") as %Hpre.
        iLeft. iSplitL "Htn".
        * iExists v. iFrame "Hpin". iRight. iLeft. iExists a.
          iSplitR; [by iPureIntro |]. iLeft.
          iExists ps, cs, s0, P. rewrite Hi. cbn [lm_blkcs].
          iFrame "Htn Hps Hcs HE Hf".
          iSplit; iPureIntro; [exact Hw | reflexivity].
        * iApply ("Hdone" $! (cs ++ [a]) with "[%] [%] Hcs Hd");
            [rewrite length_app; cbn [length]; lia | exact Hpre].
  Qed.

  (* THE FOLD AT AN ALTERNATIVE THAT MAY MOVE [f]: the holder presents the
     block at the alternative [a] it took, beside a deed whose content is
     [a]'s own step from the round's entry state *)
  Lemma uWcf0_of_posts_alt (I : list (bv 8)) (a : nat) (v v' : era_pins)
      (cs' : list nat) (s : dst) :
    lm_aprs U I a ->
    length cs' = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    dst_content s = lm_step U (ust cs' s0 I) (ul I) (lm_dec U a) ->
    lk_pin FI (S gen_id) v -∗
    gwc_post U PA (S gen_id) v I a -∗
    fown r s -∗ f_typed (fgn_cl gf) s -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs' -∗
    uWcf I 0%nat.
  Proof using .
    intros Hapr Hlen Hpos Hc.
    iIntros "#Hpin Hblk Hd #Hty #Hpin' #Hcs'". rewrite uWcf_0.
    cbn [lk_pin union_link_inst_at gen_link_inst].
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iEval (rewrite /gwc_post; cbn [gH gW gT union_params_at]; rewrite /f0w_at) in "Hblk".
    iDestruct "Hblk" as "[Hblk | #HT]"; last first.
    { iLeft. iSplitL "";
        [iApply (uHcltaint I 0%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")]. }
    iDestruct "Hblk" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
    subst sw.
    pose proof Hw as [(_ & _ & Hn & _) _].
    destruct (length (lm_abs U s0 cs I a) - 2)%nat as [| i] eqn:Hi.
    - (* the prompt is the block's first byte: still owed, deed PEND at [a] *)
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
      assert (Hpr : lm_cont U (ust cs s0 I) (ul I) (lm_dec U a) = u_prompt).
      { destruct (lm_abs_prompt U K s0 cs I a Hapr) as [pre Hpre].
        pose proof (lm_abs_len_ge2 U K s0 cs I a Hapr) as Hge.
        change (lm_cont U (ust cs s0 I) (ul I) (lm_dec U a)) with (lm_abs U s0 cs I a).
        rewrite Hpre length_app in Hi Hge.
        assert (Hp0 : length pre = 0%nat)
          by (revert Hi Hge; vm_compute (length u_prompt); lia).
        apply nil_length_inv in Hp0. rewrite Hpre Hp0. reflexivity. }
      iRight. iSplitL "Htn".
      + iApply (uWcl3_close I v ps cs P Hw with "Hpin [Htn]").
        rewrite /gcur. cbn [gW union_params_at]. rewrite /f0w_at.
        iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
      + rewrite /ush_pend_at /ush_deed_at. iLeft. iExists cs, s, v.
        iFrame "Hd Hty Hpin Hcs". iPureIntro. exists a.
        destruct Hapr as (Hok & _ & Hterm).
        split_and!; [exact Hlen | exact Hpos | exact (Hok _) | exact Hterm
                    | exact Hpr | exact Hc].
    - (* a byte before the prompt: [a] is filed, deed DONE *)
      cbn [lm_blkcs].
      iDestruct (ucs_lb_prefix_len v (cs ++ [a]) cs'
                   ltac:(rewrite length_app; cbn [length]; lia)
                   with "Hcs Hcs'") as %Hpre.
      assert (Hcseq : cs = cs').
      { destruct Hpre as [k Hk].
        assert (Hkl : length k = 1%nat).
        { apply (f_equal length) in Hk.
          rewrite !length_app in Hk. cbn [length] in Hk. lia. }
        destruct k as [| x [| y k]]; cbn [length] in Hkl; try lia.
        apply app_inj_tail in Hk. exact (proj1 Hk). }
      subst cs'.
      iLeft. iSplitL "Htn".
      + iExists v. iFrame "Hpin".
        cbn [lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
        rewrite /gwc_line /gwc_post. cbn [gH gW gT union_params_at]. rewrite /f0w_at.
        iRight. iLeft. iExists a.
        iSplitR; [by iPureIntro |]. iLeft.
        iExists ps, cs, s0, P. rewrite Hi. cbn [lm_blkcs].
        iFrame "Htn Hps Hcs HE Hf".
        iSplit; iPureIntro; [exact Hw | reflexivity].
      + rewrite /ush_done_at /ush_deed_at. iLeft. iExists (cs ++ [a]), s, v.
        iFrame "Hd Hty Hpin Hcs". iPureIntro.
        exact (udone_tie_snoc cs a s0 I _ Hlen Hpos Hc).
  Qed.

  (* ...and at the record's own block ([lk_post]): the instance *)
  Lemma uWcf0_of_post_alt (I : list (bv 8)) (a : nat) (v v' : era_pins)
      (cs' : list nat) (s : dst) :
    lm_apr U K I a ->
    length cs' = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    dst_content s = lm_step U (ust cs' s0 I) (ul I) (lm_dec U a) ->
    lk_pin FI (S gen_id) v -∗ lk_post FI (S gen_id) v I a -∗
    fown r s -∗ f_typed (fgn_cl gf) s -∗
    era_pin (fgn_echo gf) (S gen_id) v' -∗ cs_lb v' cs' -∗
    uWcf I 0%nat.
  Proof using .
    intros Hapr Hlen Hpos Hc. iIntros "#Hpin Hblk Hd #Hty #Hpin' #Hcs'".
    iApply (uWcf0_of_posts_alt I a v v' cs' s (lm_apr_aprs U K I a Hapr) Hlen Hpos Hc
              with "Hpin [Hblk] Hd Hty Hpin' Hcs'").
    rewrite /lk_post. cbn [lk_blk lk_ab union_link_inst_at gen_link_inst].
    iApply (gwc_post_of_blk U PA (S gen_id) v I a Hapr with "Hblk").
  Qed.

  (* ---- THE LOOP'S LAWS AT THE FAMILY ---- *)

  (* a fork that failed re-enters at the boundary -- the deed pending at
     the line's silent alternative *)
  Lemma uHwbl_f (I : list (bv 8)) : ⊢ uWcf I 3%nat -∗ uWcf I 0%nat.
  Proof using .
    rewrite uWcf_S3 uWcf_0. iIntros "[Hc Hp]".
    rewrite {1}/ush_pre_at /ush_deed_at. iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iLeft. iSplitL "Hc";
        [iApply (lk_lcred_blk_line FI (S gen_id) I with "Hc")
        | iApply (ush_deed_taint with "HT")]. }
    rewrite /uWcl.
    iDestruct (lk_lcred_blk_lend FI (S gen_id) I with "Hc") as (v) "[#Hpin Hl]".
    cbn [lk_pin lk_lend union_link_inst_at gen_link_inst]. rewrite /gwc_lend.
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iLeft. iSplitL "";
        [iApply (uHcltaint I 0%nat v with "Hpin HT") | iApply (ush_deed_taint with "HT")]. }
    iDestruct "Hl" as (ps cs sw P) "(%Hw & Hcur)".
    iEval (rewrite /gcur; cbn [gH gW gT union_params_at]; rewrite /f0w_at) in "Hcur".
    iDestruct "Hcur" as "(Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
    subst sw.
    iRight. iSplitL "Htn".
    { iApply (uWcl3_close I v ps cs P Hw with "Hpin [Htn]").
      rewrite /gcur. cbn [gW union_params_at]. rewrite /f0w_at.
      iFrame "Htn Hps Hcs HE Hf". by iPureIntro. }
    rewrite /ush_pend_at /ush_deed_at. iLeft.
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    iExists cs', s, v'. iFrame "Hd Hty Hpin' Hcs'". iPureIntro.
    destruct Hw as [(_ & _ & Hn & _) _].
    exists (lmh_noc K (ul I)).
    exact (upend_tie_of_pre cs' s0 I _ ltac:(lia) Htie).
  Qed.


  (* the banner-owed credential is a boundary one, at the DONE arm *)
  Lemma uHwbwc_f (I : list (bv 8)) : ⊢ uWbf I -∗ uWcf I 0%nat.
  Proof using .
    rewrite /uWbf uWcf_0. iIntros "[Hb Hd]". iLeft. iFrame "Hd".
    rewrite /uWcl /uWbl. iApply (lk_lcred_of_ban FI (S gen_id) I with "Hb").
  Qed.

  (* sh's own fork panic: PRE -> DONE at the banner-owed credential, the
     last filed alternative a panic *)
  Lemma ush_done_of_pre_ban (I : list (bv 8)) :
    uWbl I -∗ PRE I -∗ uWbl I ∗ DONE I.
  Proof using .
    iIntros "Hb Hp". rewrite /ush_pre_at /ush_done_at /ush_deed_at.
    iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last (iFrame "Hb"; by iRight).
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    pose proof Htie as [Hlen _].
    rewrite /uWbl. iDestruct "Hb" as (v) "[#Hpin Hb]".
    cbn [lk_pin lk_ban union_link_inst_at gen_link_inst].
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
    rewrite /gwc_ban. cbn [gH gW gT union_params_at]. rewrite /f0w_at.
    iDestruct "Hb" as "[Hb | [Hb | #HT]]".
    - iDestruct "Hb" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
      subst sw.
      pose proof Hw as (_ & _ & Hn & Hpan & _).
      iDestruct (ucs_lb_prefix_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %Hpre.
      iSplitL "Htn".
      + iExists v. iFrame "Hpin". iLeft. iExists ps, cs, s0, P.
        iFrame "Htn Hps Hcs HE Hf". iSplit; by iPureIntro.
      + iLeft. iExists cs, s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
        exact (udone_tie_of_pre_ban cs cs' s0 I _ Htie ltac:(lia) Hpre Hpan).
    - iDestruct "Hb" as "[%Hi Hhd]". rewrite /fhead_at.
      iDestruct "Hhd" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & #Hvf & Hpre)".
      iSplitL "Htn Hpre".
      + iExists v. iFrame "Hpin". iRight. iLeft. iSplitR; [by iPureIntro |].
        iFrame "Htn Hps Hcs HE Hvf Hpre". by iSplit; iPureIntro.
      + iLeft. iExists [], s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
        apply (udone_tie_of_pre_ban [] cs' s0 I _ Htie).
        * subst I. by rewrite nlines_nil.
        * subst I. rewrite nlines_nil in Hlen. cbn in Hlen.
          apply nil_length_inv in Hlen. subst cs'. done.
        * by left.
    - iSplitL ""; [iExists v; iFrame "Hpin"; by iRight; iRight | by iRight].
  Qed.



  (* =================================================================== *)
  (*  S3  THE WIDENED CREDENTIAL AND THE LOOP'S LAWS AT IT                *)
  (* =================================================================== *)
  Section UShURoundWide.
  (* THE WIDENED CREDENTIAL, at the pipeline's two shapes *)
  Context (PT : list (bv 8) -> nat -> iProp Σ) (PD : list (bv 8) -> iProp Σ).

  (* the COMMITTED arm carries the deed at its PRE tie: the block is not
     filed yet (the prompt's first byte files it), so the holder's choice
     list is still the line's [nlines I - 1] -- DONE would need a lower
     bound one longer, which only the filing mints; a pipeline's step is
     the identity, so the filing turns this into DONE
     ([udone_tie_of_pre_id]).  It carries the era's boot witness at [s0]
     too (C9g): the filing hands back the block's writer at its own boot
     state, and the record's space credential is at [s0] *)
  Definition uWcu (I : list (bv 8)) (p : nat) : iProp Σ :=
    (uWcf I p ∨ (⌜(p < 3)%nat⌝ ∗ PT I (5 + p)%nat)
     ∨ (⌜p = 0%nat⌝ ∗ PD I ∗ ush_deed_at upre_tie s0 I ∗ f0cw gf (S gen_id) s0))%I.

  Lemma uWcu_of (I : list (bv 8)) (p : nat) : uWcf I p -∗ uWcu I p.
  Proof using . iIntros "H". rewrite /uWcu. by iLeft. Qed.

  Lemma uWcu_3 (I : list (bv 8)) : uWcu I 3%nat -∗ uWcf I 3%nat.
  Proof using .
    rewrite /uWcu. iIntros "[H | [[%Hlt _] | [%Hz _]]]"; [iExact "H" | lia | lia].
  Qed.

  Lemma uWcu_taint (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ T -∗ uWcu I p.
  Proof using . iIntros "#Hpin #HT". iApply uWcu_of. iApply (uWcf_taint with "Hpin HT"). Qed.


  Lemma uHwbl_u (I : list (bv 8)) : ⊢ uWcu I 3%nat -∗ uWcu I 0%nat.
  Proof using .
    iIntros "H". iApply uWcu_of. iApply uHwbl_f. iApply (uWcu_3 with "H").
  Qed.

  Lemma uHpanic :
    ⊢ union_links ug -∗ UkShDiag.ush_panic_law (PS := uprogSG_free) uWcu uWbf.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) FI PRE
                  with "[]") as "#Hp".
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_panic_law. iIntros "!>" (N I l) "%Hfd Hc".
    iDestruct (uWcu_3 with "Hc") as "Hc". rewrite uWcf_S3.
    iDestruct ("Hp" $! N I l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [exact Hfd | rewrite /uWcl; iExact "Hc" |].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp5".
    iDestruct ("Hend" with "Hp5") as "[Hb Hpre]".
    rewrite /uWbf. iApply (ush_done_of_pre_ban I with "[Hb] Hpre").
    rewrite /uWbl. iExact "Hb".
  Qed.

  (* a KILLED child pays the payload with the taint *)
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = T).

  Lemma uHktaint : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  Lemma ush_kill_law_u (v : era_pins) :
    era_pin (fgn_echo gf) (S gen_id) v -∗ UkShFork.ushf_kill_law uWcu.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [iApply uHktaint; iExact "Hk" |].
    iApply (uWcu_taint I 0%nat v with "Hpin HT").
  Qed.
  End UShURoundWide.
End UShURoundDefs.

#[global] Typeclasses Opaque uWcu.
