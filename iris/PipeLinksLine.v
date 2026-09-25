(* ===================================================================== *)
(*  PipeLinksLine.v -- THE PIPELINE APPLICATION'S CREDENTIAL FAMILIES     *)
(*  AND THEIR LAWS, i.e. everything [LinkRec.LinkRec] asks of an          *)
(*  application besides the link BUNDLE ([PipeLinks.pipe_links]).         *)
(*                                                                       *)
(*  Lane PIPE-LINK-INST (design app-pipe.md section 5.8, STOP B).         *)
(*  [EchoLinks.v] + [EchoLinksLine.v] + [EchoLinksPro.v] at the PIPELINE  *)
(*  stage, in [FileLinksLine.v]'s layout and with [FileLinksLine]'s names *)
(*  spelled with a [p] where the file spells an [f] -- so that the        *)
(*  round's port ([UShRound.v], stated end to end at                      *)
(*  [FileLinkInst.file_link_inst_at]) is a rename.                        *)
(*                                                                       *)
(*  WHAT IS SIMPLER THAN THE FILE'S.  There is no era state: no [o_fh],   *)
(*  no boot value [s0], no typed witness and no file deed, so every       *)
(*  family is [EchoLinks]'s existential over [ps], [cs] and [P] alone and *)
(*  the record needs only ONE instance (there is no state to index it     *)
(*  at).  The alternative's output [pab I a] reads the LINE and the       *)
(*  ALTERNATIVE and nothing else ([PipeDisc.pcont]).                      *)
(*                                                                       *)
(*  WHAT THE DESIGN GOT WRONG, and the one place this file is not the     *)
(*  file's minus a field: [pab] still needs the ADMISSIBILITY guard.      *)
(*  The design (app-pipe.md section 5.7 finding 8, and the lane brief)    *)
(*  says [lk_ab I a := pcont (pline_at I) (palt_of a)] needs "NO guard".  *)
(*  It needs no STATE guard -- that is the file's [fst_free] and it is    *)
(*  genuinely gone -- but it must still keep [palt_ok]: [pcont l a] is    *)
(*  NON-EMPTY at every [a] whatsoever ([PipeOutPure.pcont_nonnil]),       *)
(*  including the ones the line does not admit ([PPipe] at an [LEcho]     *)
(*  line, [PEcho 1] at an [LPipe] one), whereas echo's                    *)
(*  [line_alts_of ws !!! a] is [[]] out of range and the file's [fab]     *)
(*  decides.  Unguarded, a byte lookup would say nothing and              *)
(*  [PipeLinks.pipe_write_link_blk]'s [palt_ok] premise would be          *)
(*  unsuppliable -- i.e. [lk_blk_step] would be unprovable.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import LineModel.       (* the line model, and its writer-side reading *)
Require Import LineModelLinks.
Require Import LineModelInst.   (* the stream equations at [pipe_lm] *)
Require Import PipeHooks.       (* S0: the hooks, moved below [PipeOut] *)
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import EchoLinks.        (* the SHARED prologue/prompt lemmas *)
Require Import GenLinksLine.     (* the families, once *)
Require Import EchoLinksLine.    (* ...and the SHARED alternative lengths *)
Require Import EchoLinksPro.     (* ...and the SHARED prologue arithmetic *)
Require Import RiscvPtsto.
Require Import WpUart.
(* as in EchoDisc / PipeDisc / PipeOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S1  THE PURE SHAPES, AT THE PIPELINE MODEL                            *)
(*                                                                       *)
(*  [EchoLinks]'s [wr_pro] / [wr_blk] / [wr_open] / [wr_sp] / [wr_owed] / *)
(*  [wr_ban] and [EchoLinksLine]'s [wr_tail] / [wr_blk_t] / [wr_sp_t] /   *)
(*  [wr_open_t] / [blkcs] at [pro_pin_p], [proc_before_p],                *)
(*  [proc_stream_p] and [pro_idx_p].  Where echo tested                   *)
(*  [cs !!! (nlines I - 1) = 3] the pipeline tests                        *)
(*  [palt_panic (palt_at cs (nlines I - 1))] -- which is the SAME test    *)
(*  at either line shape, because [PEcho 3] is the only panicking         *)
(*  alternative and both shapes admit it.                                 *)
(* ===================================================================== *)

Definition wr_pro_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ ~ pro_done (pro_from (pro_idx_p cs (nlines I)) ps)
  /\ P = length (proc_stream_p ps cs I).

Definition wr_blk_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_p ps cs I).

Definition wr_open_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (pro_idx_p cs (nlines I) < pro_rounds ps)%nat
  /\ P = length (proc_stream_p ps cs I).

Definition wr_owed_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_pro_p ps cs I P \/ wr_blk_p ps cs I P.

Definition wr_sp_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open_p ps cs I (S P)
  /\ proc_stream_p ps cs I !! P = Some (u_prompt !!! 1%nat).

Definition wr_pre_p (cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then [] else alt_panic.

Definition wr_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j
        /\ P = (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
                + pro_round * j)%nat).

Definition wr_banp_p (ps cs : list nat) (I : list (bv 8)) (P i : nat) : Prop :=
  match i with
  | O => wr_ban_p ps cs I P
  | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban_p ps' cs I P
  end.

(* the round this block is in is the LAST one resolved *)
Definition wr_tail_p (ps cs : list nat) : Prop :=
  pro_from (S (pro_idx_p cs (length cs))) ps = [].

Definition wr_blk_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_blk_p ps cs I P /\ wr_tail_p ps cs.

Definition wr_sp_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_sp_p ps cs I P /\ wr_tail_p ps cs.

Definition wr_open_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_open_p ps cs I P /\ wr_tail_p ps cs.

Definition blkcs_p (cs : list nat) (a i : nat) : list nat :=
  match i with O => cs | S _ => cs ++ [a] end.

(* ---- the writer's stages are [LineModel]'s, by the stream equations ---- *)
Lemma wr_pro_p_lm ps cs I P : wr_pro_p ps cs I P = lm_wr_pro pipe_lm ps cs tt I P.
Proof using. rewrite /wr_pro_p /lm_wr_pro ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_blk_p_lm ps cs I P : wr_blk_p ps cs I P = lm_wr_blk pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_p /lm_wr_blk ?proc_stream_p_lm ?proc_before_p_lm. reflexivity. Qed.
Lemma wr_open_p_lm ps cs I P : wr_open_p ps cs I P = lm_wr_open pipe_lm ps cs tt I P.
Proof using. rewrite /wr_open_p /lm_wr_open ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_owed_p_lm ps cs I P : wr_owed_p ps cs I P = lm_wr_owed pipe_lm ps cs tt I P.
Proof using. rewrite /wr_owed_p /lm_wr_owed wr_pro_p_lm wr_blk_p_lm. reflexivity. Qed.
Lemma wr_sp_p_lm ps cs I P : wr_sp_p ps cs I P = lm_wr_sp pipe_lm ps cs tt I P.
Proof using. rewrite /wr_sp_p /lm_wr_sp wr_open_p_lm proc_stream_p_lm. reflexivity. Qed.
Lemma wr_ban_p_lm ps cs I P : wr_ban_p ps cs I P = lm_wr_ban pipe_lm ps cs tt I P.
Proof using. rewrite /wr_ban_p /lm_wr_ban ?proc_stream_p_lm ?proc_before_p_lm pro_idx_p_lm. reflexivity. Qed.
Lemma wr_banp_p_lm ps cs I P i : wr_banp_p ps cs I P i = lm_wr_banp pipe_lm ps cs tt I P i.
Proof using.
  rewrite /wr_banp_p /lm_wr_banp. destruct i; [apply wr_ban_p_lm |].
  f_equal. apply functional_extensionality. intros ps'. by rewrite wr_ban_p_lm.
Qed.
Lemma wr_tail_p_lm ps cs : wr_tail_p ps cs = lm_wr_tail pipe_lm ps cs.
Proof using. rewrite /wr_tail_p /lm_wr_tail pro_idx_p_lm. reflexivity. Qed.
Lemma wr_blk_t_p_lm ps cs I P : wr_blk_t_p ps cs I P = lm_wr_blk_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_blk_t_p /lm_wr_blk_t wr_blk_p_lm wr_tail_p_lm. reflexivity. Qed.
Lemma wr_sp_t_p_lm ps cs I P : wr_sp_t_p ps cs I P = lm_wr_sp_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_sp_t_p /lm_wr_sp_t wr_sp_p_lm wr_tail_p_lm. reflexivity. Qed.
Lemma wr_open_t_p_lm ps cs I P : wr_open_t_p ps cs I P = lm_wr_open_t pipe_lm ps cs tt I P.
Proof using. rewrite /wr_open_t_p /lm_wr_open_t wr_open_p_lm wr_tail_p_lm. reflexivity. Qed.

(* ---- what the shapes say about the input's parse ---- *)
Lemma wr_blk_nonnil_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> I <> [].
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_nonnil pipe_lm).
Qed.

Lemma wr_blk_lines_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> nlines I = S (length cs).
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_lines pipe_lm).
Qed.

Lemma wr_blk_started_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> nstarted I = S (length cs).
Proof using.
  rewrite wr_blk_p_lm. apply (lm_wr_blk_started pipe_lm).
Qed.

Lemma wr_blk_t_stage_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t_p ps cs I P ->
  rest_of I = []
  /\ nlines I = S (length cs)
  /\ P = length (proc_before_p ps cs I)
  /\ pro_pin_p ps cs I
  /\ wr_tail_p ps cs.
Proof using.
  rewrite wr_blk_t_p_lm proc_before_p_lm wr_tail_p_lm. intros Hw.
  destruct (lm_wr_blk_t_stage pipe_lm ps cs tt I P Hw) as (H1 & H2 & H3 & H4 & H5).
  split_and!; [exact H1 | exact H2 | exact H3 | by apply pro_pin_p_lm | exact H5].
Qed.

(* ---- the round pointer under a filed alternative ---- *)
Lemma pro_idx_p_snoc_ne (cs : list nat) (a : nat) :
  palt_panic (palt_of a) = false ->
  pro_idx_p (cs ++ [a]) (S (length cs)) = pro_idx_p cs (length cs).
Proof using.
  rewrite !pro_idx_p_lm. apply (lm_pro_idx_snoc_ne pipe_lm).
Qed.

Lemma pro_idx_p_snoc_3 (cs : list nat) :
  pro_idx_p (cs ++ [3%nat]) (S (length cs)) = S (pro_idx_p cs (length cs)).
Proof using.
  rewrite !pro_idx_p_lm. apply (lm_pro_idx_snoc_pan pipe_lm). exact ppan_panic.
Qed.

Lemma wr_tail_snoc_p (ps cs : list nat) (a : nat) :
  palt_panic (palt_of a) = false -> wr_tail_p ps cs -> wr_tail_p ps (cs ++ [a]).
Proof using.
  rewrite !wr_tail_p_lm. apply (lm_wr_tail_snoc pipe_lm).
Qed.

(* ---- filing an alternative reads no block below the boundary ---- *)
Lemma wr_blk_pin_snoc_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> pro_pin_p ps (cs ++ [a]) I.
Proof using.
  rewrite wr_blk_p_lm. intros Hw. apply pro_pin_p_lm.
  exact (lm_wr_blk_pin_snoc pipe_lm ps cs tt I P a Hw).
Qed.

Lemma wr_blk_low_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> proc_before_p ps (cs ++ [a]) I = proc_before_p ps cs I.
Proof using.
  rewrite wr_blk_p_lm !proc_before_p_lm. apply (lm_wr_blk_low pipe_lm).
Qed.

(* ---- the block a [wr_blk_p] owes, once alternative [a] is filed ---- *)
Lemma wr_blk_pending_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P ->
  pending_at_p ps (cs ++ [a]) I
  = alt_cont_p ps (cs ++ [a]) (bodies_of I) (length cs).
Proof using.
  intros Hw. pose proof (wr_blk_nonnil_p ps cs I P Hw) as Hne.
  destruct Hw as (_ & Hr & Hn & _).
  rewrite /pending_at_p decide_False; [| exact Hne].
  rewrite decide_True; [| exact Hr].
  replace (nlines I - 1)%nat with (length cs) by lia.
  reflexivity.
Qed.

Lemma wr_blk_line_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P -> pline_of (bodies_of I !!! length cs) = pline_at I.
Proof using.
  intros Hw. pose proof (wr_blk_lines_p ps cs I P Hw) as Hn.
  rewrite /pline_at Hn.
  replace (S (length cs) - 1)%nat with (length cs) by lia. reflexivity.
Qed.

Lemma wr_blk_cont_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of a) = false ->
  pending_at_p ps (cs ++ [a]) I = pcont (pline_at I) (palt_of a).
Proof using.
  rewrite wr_blk_p_lm pending_at_p_lm pline_at_lm. apply (lm_wr_blk_pending_s pipe_lm).
Qed.

Lemma wr_blk_cont3_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of a) = true ->
  pending_at_p ps (cs ++ [a]) I
  = pcont (pline_at I) (palt_of a)
    ++ pro_of (pro_from (S (pro_idx_p cs (length cs))) ps).
Proof using.
  intros Hw Ha.
  rewrite (wr_blk_pending_p ps cs I P a Hw) /alt_cont_p /palt_at
          (EchoLinksLine.snoc_lookup_total cs a) Ha
          (pro_idx_p_app_le cs [a] (length cs) ltac:(lia))
          (wr_blk_line_p ps cs I P Hw).
  reflexivity.
Qed.

(* THE STREAM BYTE THE WRITE LINK ASKS FOR *)
Lemma wr_blk_byte_p (ps cs : list nat) (I : list (bv 8)) (P a j : nat)
      (b : bv 8) :
  wr_blk_p ps cs I P -> pab I a !! j = Some b ->
  proc_stream_p ps (cs ++ [a]) I !! (P + j)%nat = Some b.
Proof using.
  intros Hw Hb. pose proof (pab_ok I a j b Hb) as Hok.
  pose proof (pab_nofork I a j b Hb) as Hfk.
  rewrite (pab_is I a (conj Hok Hfk)) in Hb.
  pose proof Hw as (_ & _ & _ & HP).
  rewrite /proc_stream_p (wr_blk_low_p ps cs I P a Hw) lookup_app_r; [| lia].
  replace (P + j - length (proc_before_p ps cs I))%nat with j by lia.
  destruct (palt_panic (palt_of a)) eqn:Ha.
  - rewrite (wr_blk_cont3_p ps cs I P a Hw Ha) lookup_app_l; [exact Hb |].
    exact (lookup_lt_Some _ _ _ Hb).
  - by rewrite (wr_blk_cont_p ps cs I P a Hw Ha).
Qed.

(* ---- the prologue grows by exactly its alternative ---- *)
Lemma pending_at_p_round_snoc (ps cs : list nat) (I : list (bv 8)) (a : nat) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true) ->
  ~ pro_done (pro_from (pro_idx_p cs (nlines I)) ps) ->
  (pro_idx_p cs (nlines I) <= pro_rounds ps)%nat ->
  pending_at_p (ps ++ [a]) cs I = pending_at_p ps cs I ++ pro_alts !!! a.
Proof using.
  rewrite !pending_at_p_lm !pro_idx_p_lm.
  apply (lm_pending_at_round_snoc pipe_lm pipe_lm_laws).
Qed.

(* ---- THE ROUND'S BANNER, STILL OWED ---- *)
Lemma wr_ban_pro_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P -> wr_pro_p ps cs I P.
Proof using.
  rewrite wr_ban_p_lm wr_pro_p_lm. apply (lm_wr_ban_pro pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_low_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  proc_before_p (ps ++ [3%nat]) cs I = proc_before_p ps cs I.
Proof using.
  rewrite wr_ban_p_lm !proc_before_p_lm. apply (lm_wr_ban_low pipe_lm).
Qed.

Lemma wr_ban_filed_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  exists j : nat,
    pro_from (pro_idx_p cs (nlines I)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_before_p (ps ++ [3%nat]) cs I) + length (wr_pre_p cs I)
            + pro_round * j)%nat.
Proof using.
  rewrite wr_ban_p_lm proc_before_p_lm pro_idx_p_lm. intros Hw.
  destruct (lm_wr_ban_filed pipe_lm ps cs tt I P Hw) as (j & H1 & H2).
  exists j. exact (conj H1 H2).
Qed.

Lemma wr_ban_byte_p (ps cs : list nat) (I : list (bv 8)) (P i : nat)
      (b : bv 8) :
  wr_ban_p ps cs I P -> u_banner !! i = Some b ->
  proc_stream_p (ps ++ [3%nat]) cs I !! (P + i)%nat = Some b.
Proof using.
  rewrite wr_ban_p_lm proc_stream_p_lm. apply (lm_wr_ban_byte pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_done_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P -> wr_pro_p (ps ++ [3%nat]) cs I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_p_lm wr_pro_p_lm. apply (lm_wr_ban_done pipe_lm pipe_lm_laws).
Qed.

Lemma wr_ban_round0_p : wr_ban_p [] [] [] 0%nat.
Proof using.
  rewrite wr_ban_p_lm. apply (lm_wr_ban_round0 pipe_lm).
Qed.

(* ---- a run of inputs that owe nothing leaves the stream alone ---- *)
Lemma proc_before_from_p_gap (ps cs : list nat) (pre k : list (bv 8)) :
  (forall J : list (bv 8), J `prefix_of` k -> J <> k ->
     pending_at_p ps cs (pre ++ J) = []) ->
  proc_before_from_p ps cs pre k = [].
Proof using.
  rewrite proc_before_from_p_lm. intros Hj.
  apply (lm_proc_before_from_gap pipe_lm). intros J HJ Hne.
  rewrite -pending_at_p_lm. exact (Hj J HJ Hne).
Qed.

Lemma proc_before_p_line (ps cs : list nat) (I l : list (bv 8)) :
  rest_of I = [] -> wl_nl ∉ l ->
  proc_before_p ps cs (I ++ l ++ [wl_nl]) = proc_stream_p ps cs I.
Proof using.
  rewrite proc_before_p_lm proc_stream_p_lm. apply (lm_proc_before_line pipe_lm).
Qed.

(* ===================================================================== *)
(*  S2  THE STEPS, PURE                                                   *)
(* ===================================================================== *)

(* (1) THE ROUND'S CHOICE BYTE, at an open prologue *)
Lemma wr_pro_dollar_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_sp_p (ps ++ [0%nat]) cs I (S P).
Proof using.
  rewrite wr_pro_p_lm wr_sp_p_lm. apply (lm_wr_pro_dollar pipe_lm pipe_lm_laws).
Qed.

(* (2) THE LINE'S CHOICE BYTE, at a settled round whose last line still
       owes its block: filing an alternative whose whole output IS the
       prompt makes the block the prompt itself, whatever the line was.
       Which code that is depends on the line ([PEcho 2] at an echo line,
       [PSilent] at a pipeline one), which is why the step is stated at an
       arbitrary such [c] and [wr_blk_dollar_p] is it at [pnoc_of]. *)
Lemma wr_blk_dollar_c_p (ps cs : list nat) (I : list (bv 8)) (P c : nat) :
  wr_blk_p ps cs I P -> palt_panic (palt_of c) = false ->
  pcont (pline_at I) (palt_of c) = u_prompt ->
  wr_sp_p ps (cs ++ [c]) I (S P).
Proof using.
  intros Hw Hnp Hpc. pose proof Hw as (Hpin & Hm & Hdv & HP).
  pose proof (wr_blk_started_p ps cs I P Hw) as Hst.
  assert (Hpend : pending_at_p ps (cs ++ [c]) I = u_prompt)
    by (rewrite (wr_blk_cont_p ps cs I P c Hw Hnp); exact Hpc).
  assert (Hup : proc_stream_p ps (cs ++ [c]) I
                = proc_before_p ps cs I ++ u_prompt)
    by (rewrite /proc_stream_p (wr_blk_low_p ps cs I P c Hw) Hpend; reflexivity).
  assert (Hlen : length (proc_stream_p ps (cs ++ [c]) I) = S (S P)).
  { rewrite Hup (length_app (proc_before_p ps cs I) u_prompt) wr_prompt_len.
    lia. }
  split.
  - rewrite /wr_open_p. split_and!.
    + exact (wr_blk_pin_snoc_p ps cs I P c Hw).
    + exact Hm.
    + rewrite (length_app cs [c]) Hdv. cbn [length]. lia.
    + rewrite Hdv (pro_idx_p_snoc_ne cs c Hnp). apply Hpin. lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (proc_before_p ps cs I))%nat with 1%nat by lia.
    exact wr_prompt_tail.
Qed.

Lemma wr_blk_dollar_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_p ps cs I P ->
  wr_sp_p ps (cs ++ [pnoc_of (pline_at I)]) I (S P).
Proof using.
  rewrite wr_blk_p_lm wr_sp_p_lm. apply (lm_wr_blk_dollar pipe_lm pipe_hooks).
Qed.

(* (3) THE SPACE *)
Lemma wr_sp_open_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp_p ps cs I P -> wr_open_p ps cs I (S P).
Proof using.
  rewrite wr_sp_p_lm wr_open_p_lm. apply (lm_wr_sp_open pipe_lm).
Qed.

(* (4) THE READ *)
Lemma wr_open_read_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open_p ps cs I P -> wl_nl ∉ l -> wr_blk_p ps cs (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_p_lm wr_blk_p_lm. apply (lm_wr_open_read pipe_lm).
Qed.

(* ---- the tight shapes' steps ---- *)
Lemma wr_blk_open_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t_p ps cs I P -> papr I a ->
  wr_open_t_p ps (cs ++ [a]) I (P + length (pab I a))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_open_t_p_lm pab_lm. intros Hw Hpr.
  exact (lm_wr_blk_open pipe_lm pipe_hooks ps cs tt I P a Hw (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma wr_blk_sp_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_blk_t_p ps cs I P -> papr I a ->
  wr_sp_t_p ps (cs ++ [a]) I (P + (length (pab I a) - 1))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_sp_t_p_lm pab_lm. intros Hw Hpr.
  exact (lm_wr_blk_sp pipe_lm pipe_hooks ps cs tt I P a Hw (proj1 (papr_lm I a) Hpr)).
Qed.

Lemma wr_sp_open_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_sp_t_p ps cs I P -> wr_open_t_p ps cs I (S P).
Proof using.
  rewrite wr_sp_t_p_lm wr_open_t_p_lm. apply (lm_wr_sp_open_t pipe_lm).
Qed.

Lemma wr_open_read_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
      (l : list (bv 8)) :
  wr_open_t_p ps cs I P -> wl_nl ∉ l ->
  wr_blk_t_p ps cs (I ++ l ++ [wl_nl]) P.
Proof using.
  rewrite wr_open_t_p_lm wr_blk_t_p_lm. apply (lm_wr_open_read_t pipe_lm).
Qed.

Lemma wr_pro_tail_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_tail_p (ps ++ [0%nat]) cs.
Proof using.
  rewrite wr_pro_p_lm wr_tail_p_lm. apply (lm_wr_pro_tail pipe_lm).
Qed.

Lemma wr_pro_dollar_t_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_pro_p ps cs I P -> wr_sp_t_p (ps ++ [0%nat]) cs I (S P).
Proof using.
  rewrite wr_pro_p_lm wr_sp_t_p_lm. apply (lm_wr_pro_dollar_t pipe_lm pipe_lm_laws).
Qed.

(* (5) THE PANIC LINE OPENS A FRESH ROUND AT THE SAME INPUT *)
Lemma wr_blk_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_blk_t_p ps cs I P ->
  wr_ban_p ps (cs ++ [3%nat]) I (P + length (pab I 3%nat))%nat.
Proof using.
  rewrite wr_blk_t_p_lm wr_ban_p_lm pab_lm.
  apply (lm_wr_blk_ban pipe_lm pipe_lm_laws pipe_hooks).
Qed.


(* ===================================================================== *)
(*  S3  THE DISCIPLINE LEMMA: an untainted input past a boundary means    *)
(*  the boundary's prompt was written ([EchoLinks.wr_owed_read_refute]    *)
(*  at the pipeline stage; the block's nonemptiness comes from            *)
(*  [PipeOutPure.pending_at_p_nonnil_pre], which is the reading of        *)
(*  [alts_pre_p] a WRITER's lower bound admits).                          *)
(* ===================================================================== *)
Lemma wr_owed_read_refute_p (ps cs ps0 cs0 : list nat) (I I0 : list (bv 8))
      (P : nat) :
  wr_owed_p ps cs I P ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage_p ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_before_p ps0 cs0 I0) <= P)%nat -> False.
Proof using.
  rewrite wr_owed_p_lm proc_before_p_lm. intros Hw HI Hne Hrs.
  exact (lm_wr_owed_read_refute pipe_lm pipe_lm_laws pipe_hooks ps cs ps0 cs0 tt I I0 P
           Hw HI Hne (proj1 (rd_stage_p_lm _ _ _ _) Hrs)).
Qed.


(* ===================================================================== *)
(*  S4  /INIT'S PROLOGUE DIAGNOSTICS, PURE ([EchoLinksPro] at the         *)
(*  pipeline stage).  Nothing here reads a line: the prologue's           *)
(*  alternatives are [EchoDisc.pro_alts] at either application.           *)
(* ===================================================================== *)
Lemma pending_at_p_round_wr_pre (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true) ->
  pending_at_p ps cs I
  = wr_pre_p cs I ++ pro_of (pro_from (pro_idx_p cs (nlines I)) ps).
Proof using.
  rewrite pending_at_p_lm pro_idx_p_lm.
  apply (lm_pending_at_round_pre pipe_lm pipe_lm_laws).
Qed.

Definition wr_pban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
  wr_pro_p ps cs I P
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat]).
Lemma wr_pban_p_lm ps cs I P : wr_pban_p ps cs I P = lm_wr_pban pipe_lm ps cs tt I P.
Proof using. rewrite /wr_pban_p /lm_wr_pban wr_pro_p_lm pro_idx_p_lm. reflexivity. Qed.

Lemma wr_pban_of_ban_p (ps cs : list nat) (I : list (bv 8)) (P : nat) :
  wr_ban_p ps cs I P ->
  wr_pban_p (ps ++ [3%nat]) cs I (P + length u_banner)%nat.
Proof using.
  rewrite wr_ban_p_lm wr_pban_p_lm. apply (lm_wr_pban_of_ban pipe_lm pipe_lm_laws).
Qed.

Definition wr_pdiag_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat)
  : Prop :=
  pro_pin_p ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ palt_panic (palt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat; a]
        /\ P = (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
                + pro_round * j + length u_banner + i)%nat).
Lemma wr_pdiag_p_lm ps cs I P a i : wr_pdiag_p ps cs I P a i = lm_wr_pdiag pipe_lm ps cs tt I P a i.
Proof using. rewrite /wr_pdiag_p /lm_wr_pdiag proc_before_p_lm !pro_idx_p_lm. reflexivity. Qed.

Lemma wr_pdiag_byte_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat)
      (b : bv 8) :
  wr_pdiag_p ps cs I P a i -> pro_alts !!! a !! i = Some b ->
  proc_stream_p ps cs I !! P = Some b.
Proof using.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)) Hb.
  rewrite /proc_stream_p (pending_at_p_round_wr_pre ps cs I Hm Hr) Hj
          EchoLinksPro.pro_of_fail_snoc HP.
  replace (length (proc_before_p ps cs I) + length (wr_pre_p cs I)
           + pro_round * j + length u_banner + i)%nat
    with (length (proc_before_p ps cs I)
          + (length (wr_pre_p cs I)
             + (length (pro_of (pro_fail j)) + (length u_banner + i))))%nat
    by (rewrite pro_of_fail_length; lia).
  rewrite (lookup_app_shift (proc_before_p ps cs I))
          (lookup_app_shift (wr_pre_p cs I))
          (lookup_app_shift (pro_of (pro_fail j))) (lookup_app_shift u_banner).
  exact Hb.
Qed.

Lemma wr_pdiag_1_of_pro_p (ps cs : list nat) (I : list (bv 8)) (P a : nat) :
  wr_pban_p ps cs I P -> wr_pdiag_p (ps ++ [a]) cs I (S P) a 1%nat.
Proof using.
  intros ((Hpin & Hm & Hdv & Hr & Hnd & HP) & (j & Hj)).
  assert (Hle : (pro_idx_p cs (nlines I) <= pro_rounds ps)%nat)
    by exact (pro_pin_p_round_le ps cs I Hm Hr Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [a])) by by eexists.
  assert (Hlow : proc_before_p (ps ++ [a]) cs I = proc_before_p ps cs I).
  { symmetry. apply proc_before_p_ext. intros J HJ Hne.
    apply (pending_at_p_ps_ext ps (ps ++ [a]) cs J Hpre).
    exact (Hpin (nlines J) (nstarted_strict J I HJ Hne)). }
  assert (H3 : length (pro_of (pro_fail j ++ [3%nat]))
               = (pro_round * j + length u_banner)%nat).
  { rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
    rewrite length_app pro_of_fail_length. reflexivity. }
  rewrite /wr_pdiag_p. split_and!.
  - exact (pro_pin_p_mono ps (ps ++ [a]) cs I Hpre Hpin).
  - exact Hm.
  - exact Hdv.
  - exact Hr.
  - exists j. split.
    + rewrite (pro_from_snoc_le _ ps a Hle) Hj. by rewrite -app_assoc.
    + rewrite Hlow HP /proc_stream_p (length_app (proc_before_p ps cs I))
              (pending_at_p_round_wr_pre ps cs I Hm Hr)
              (length_app (wr_pre_p cs I)) Hj H3. lia.
Qed.

Lemma wr_pdiag_S_p (ps cs : list nat) (I : list (bv 8)) (P a i : nat) :
  wr_pdiag_p ps cs I P a i -> wr_pdiag_p ps cs I (S P) a (S i).
Proof using.
  rewrite !wr_pdiag_p_lm. apply (lm_wr_pdiag_S pipe_lm).
Qed.

Lemma wr_pdiag_done_1_p (ps cs : list nat) (I : list (bv 8)) (P i : nat) :
  i = length (pro_alts !!! 1%nat) ->
  wr_pdiag_p ps cs I P 1%nat i -> wr_ban_p ps cs I P.
Proof using.
  intros Hi (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  assert (Hb : length u_banner = 18%nat) by (vm_compute; reflexivity).
  assert (Ha : length (pro_alts !!! 1%nat) = 21%nat)
    by (vm_compute; reflexivity).
  assert (Hrd : pro_round = 39%nat) by (vm_compute; reflexivity).
  rewrite /wr_ban_p. split_and!; try assumption.
  exists (S j). split.
  - rewrite Hj. by rewrite pro_fail_S.
  - rewrite HP Hi Hb Ha Hrd. lia.
Qed.


(* ===================================================================== *)
(*  S5  THE CREDENTIAL FAMILIES AS RESOURCES                              *)
(*                                                                       *)
(*  Every family takes the ERA INDEX [k] first, so that it fills a        *)
(*  [LinkRec] field by name; none of them READS it (the pipeline era has  *)
(*  no per-index state -- the era's pin carries the index already).       *)
(* ===================================================================== *)
Section pipe_links_line.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  (* =================================================================== *)
  (*  S5  THE FAMILIES ARE [GenLinksLine]'s, AT THE PIPELINE'S PARAMETERS *)
  (*                                                                     *)
  (*  The credential families are the generic ones ([GenLinksLine.gwc_*] *)
  (*  at [pipe_params]) and nothing here defines a second set: [pwc_*]   *)
  (*  below are ABBREVIATIONS of the generic families.  The pipeline's   *)
  (*  parameters are the degenerate ones -- the model's state is [unit], *)
  (*  so the boot-state witness is [emp]; /init's first byte needs no    *)
  (*  deed, so the era has no head arm ([False]).  THE PIPELINE'S OWN    *)
  (*  READING of a family -- no state, no witness, the landed shape over *)
  (*  [wr_*_p] -- is its [_view] equivalence, which is what a consumer   *)
  (*  that computes on a body spends ([rewrite pwc_blk_view] where it    *)
  (*  unfolded [pwc_blk]).  [pwc_post] keeps its own definition, the     *)
  (*  block at the state-free alternative ([LinkRec.lk_post]'s shape);   *)
  (*  [pwc_post_gen] is its reading of the generic post.                 *)
  (* =================================================================== *)
  Definition pipe_W (k : nat) (s : unit) : iProp Σ := emp%I.
  Definition pipe_Wb (k : nat) (s : unit) : iProp Σ := emp%I.
  Definition pipe_H (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ := False%I.

  Lemma pipe_W_pers k s : Persistent (pipe_W k s).
  Proof using . rewrite /pipe_W. apply _. Qed.
  Lemma pipe_W_tl k s : Timeless (pipe_W k s).
  Proof using . rewrite /pipe_W. apply _. Qed.
  Lemma pipe_W_bw k s : pipe_W k s -∗ pipe_Wb k s.
  Proof using . by iIntros "$". Qed.
  Lemma pipe_W_bw0 k s : pipe_W k s -∗ pipe_Wb 0 s.
  Proof using . by iIntros "$". Qed.
  Lemma pipe_Wb_agree k (s s' : unit) : pipe_Wb k s -∗ pipe_Wb k s' -∗ ⌜s = s'⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct s, s'. Qed.
  Lemma pipe_H_tl k v I : Timeless (pipe_H k v I).
  Proof using . rewrite /pipe_H. apply _. Qed.
  Lemma pipe_H_cur k v I :
    pipe_H k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.
  Lemma pipe_H_inp k v I : pipe_H k v I -∗ pipe_H k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.

  Definition pipe_params : gen_params pipe_lm :=
    MkGP pipe_lm pipe_lm_laws pipe_hooks
      PT _ _
      (era_pin γ) _ _ (era_pin_agree γ)
      pipe_W pipe_W_pers pipe_W_tl
      pipe_Wb pipe_W_pers pipe_W_tl 0 pipe_W_bw pipe_W_bw0 pipe_Wb_agree
      pipe_H pipe_H_tl pipe_H_cur pipe_H_inp.

  Local Notation pwc_pro := (gwc_pro pipe_lm pipe_params).
  Local Notation pwc_blk := (gwc_blk pipe_lm pipe_params).
  Local Notation pwc_owed := (gwc_owed pipe_lm pipe_params).
  Local Notation pwc_sp := (gwc_sp pipe_lm pipe_params).
  Local Notation pwc_open := (gwc_open pipe_lm pipe_params).
  Local Notation pwc_sp_t := (gwc_sp_t pipe_lm pipe_params).
  Local Notation pwc_open_t := (gwc_open_t pipe_lm pipe_params).
  Local Notation pwc_ban := (gwc_ban pipe_lm pipe_params).
  Local Notation pwc_lend := (gwc_lend pipe_lm pipe_params).
  Local Notation pwc_pr := (gwc_pr pipe_lm pipe_params).

  (* the block written up to its prompt, at the STATE-FREE alternative:
     [LinkRec.lk_post]'s shape ([pab] decides admissibility) *)
  Definition pwc_post (k : nat) (v : era_pins) (I : list (bv 8)) (a : nat)
    : iProp Σ := pwc_blk k v I a (length (pab I a) - 2)%nat.

  (* THE PIPELINE'S OWN LINE CREDENTIAL, one writer: the record's line
     ([PipeBoth.pwc_line2]) widens it by the terminal round's arm *)
  Definition pwc_line (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (pwc_pro k v I ∨ (∃ a : nat, ⌜papr I a⌝ ∗ pwc_post k v I a))%I.

  Definition pwc_lpr (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat)
    : iProp Σ :=
    match p with
    | O => pwc_line k v I
    | S O => pwc_sp_t k v I
    | S (S O) => pwc_open_t k v I
    | _ => pwc_blk k v I 0%nat 0%nat
    end.

  Definition pwc_rres (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage_p ps0 cs0 I⌝ ∗ turn_lb v (length (proc_before_p ps0 cs0 I))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0)%I.

  (* THE ERA'S TURN: [PipeOut.pturn], which is [EchoOut.eturn] verbatim *)
  Definition pturn_pre (k : nat) : iProp Σ := PipeOut.pturn g k.

  (* ---- structure ----

     THE DISPATCH, NOT [apply _] (upstream's leaf-instance pass, 2026-09-18:
     the tree carries 455 [Timeless] instances under mostly transparent
     definitions, so the hint net cannot discriminate and one search at
     this altitude tries nearly all of them).  Descend through the
     CONNECTIVES and name the leaf, SYNTACTICALLY -- a [first [...]]
     spelling unifies up to delta and peels through a name that has its
     own instance. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (echo_taint _) => apply echo_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (era_pin _ _ _) => apply era_pin_timeless
    | |- _ => apply _
    end.

  Local Ltac ps_leaf :=
    lazymatch goal with
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; ps_leaf
    | |- Persistent (bi_sep _ _) =>
        apply bi.sep_persistent; [ps_leaf | ps_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- _ => apply _
    end.

  Global Instance pwc_rres_persistent v I : Persistent (pwc_rres v I).
  Proof using . rewrite /pwc_rres. ps_leaf. Qed.
  Global Instance pwc_rres_timeless v I : Timeless (pwc_rres v I).
  Proof using . rewrite /pwc_rres. tl_leaf. Qed.

  (* NAME THE LEAF: the generic instances, at this instance *)
  Lemma pwc_pro_timeless k v I : Timeless (pwc_pro k v I).
  Proof using . apply (gwc_pro_timeless pipe_lm pipe_params). Qed.
  Lemma pwc_blk_timeless k v I a i : Timeless (pwc_blk k v I a i).
  Proof using . apply (gwc_blk_timeless pipe_lm pipe_params). Qed.
  Lemma pwc_sp_t_timeless k v I : Timeless (pwc_sp_t k v I).
  Proof using . apply (gwc_sp_t_timeless pipe_lm pipe_params). Qed.
  Lemma pwc_open_t_timeless k v I : Timeless (pwc_open_t k v I).
  Proof using . apply (gwc_open_t_timeless pipe_lm pipe_params). Qed.
  Global Instance pwc_post_timeless k v I a : Timeless (pwc_post k v I a).
  Proof using . rewrite /pwc_post. apply pwc_blk_timeless. Qed.
  Global Instance pwc_line_timeless k v I : Timeless (pwc_line k v I).
  Proof using .
    rewrite /pwc_line.
    apply bi.or_timeless; [apply pwc_pro_timeless |].
    apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_post_timeless].
  Qed.
  Global Instance pwc_lpr_timeless k v I p : Timeless (pwc_lpr k v I p).
  Proof using .
    rewrite /pwc_lpr. destruct p as [| [| [| p]]];
      [apply pwc_line_timeless | apply pwc_sp_t_timeless
      | apply pwc_open_t_timeless | apply pwc_blk_timeless].
  Qed.

  (* ---- THE PIPELINE'S READING of each family ---- *)
  Local Ltac view_open :=
    rewrite /gcur; cbn [gH gW gT pipe_params]; rewrite /pipe_W /pipe_H;
    apply bi.equiv_entails; split.

  Lemma pwc_pro_view k v I :
    pwc_pro k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_pro_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_pro. view_open.
    - iIntros "[Hl | [[] | HT]]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_pro_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight; iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_pro_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_owed_view k v I :
    pwc_owed k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_owed_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_owed. view_open.
    - iIntros "[Hl | [[] | HT]]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_owed_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight; iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_owed_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_sp_view k v I :
    pwc_sp k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_sp_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_sp. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_sp_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_sp_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_open_view k v I :
    pwc_open k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_open_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_open. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_open_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_open_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_sp_t_view k v I :
    pwc_sp_t k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_sp_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_sp_t. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_sp_t_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_sp_t_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_open_t_view k v I :
    pwc_open_t k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_open_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_open_t. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_open_t_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_open_t_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_lend_view k v I :
    pwc_lend k v I ⊣⊢
    ((∃ ps cs P : _, ⌜wr_blk_t_p ps cs I P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_lend. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_blk_t_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_blk_t_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_blk_view k v I a i :
    pwc_blk k v I a i ⊣⊢
    ((∃ ps cs P : _, ⌜wr_blk_t_p ps cs I P⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v (blkcs_p cs a i) ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_blk /lm_blkcs /blkcs_p. view_open.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_blk_t_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_blk_t_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  Lemma pwc_ban_view k v I i :
    pwc_ban k v I i ⊣⊢
    ((∃ ps cs P : _, ⌜wr_banp_p ps cs I P i⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ inp_lb v I) ∨ PT)%I.
  Proof using .
    rewrite /gwc_ban. view_open.
    - iIntros "[Hl | [[_ []] | HT]]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, P.
      iSplitR; [iPureIntro; by rewrite wr_banp_p_lm |]. iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight; iRight].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
      iLeft. iExists ps, cs, tt, P.
      iSplitR; [iPureIntro; by rewrite -wr_banp_p_lm |]. iFrame "Htn Hps Hcs HE".
  Qed.

  (* the generic post, at an admissible alternative, IS the block at the
     state-free reading: every pipeline alternative is state-free *)
  Lemma pwc_post_gen k v I a :
    papr I a ->
    gwc_post pipe_lm pipe_params k v I a ⊣⊢ pwc_post k v I a.
  Proof using .
    intros Ha. pose proof (proj1 (papr_lm I a) Ha) as Ha'.
    rewrite /pwc_post /gwc_post /gwc_blk pab_lm. cbn [gW pipe_params].
    rewrite /pipe_W. apply bi.equiv_entails; split.
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      rewrite (lm_abs_ab pipe_lm pipe_hooks tt cs I a Ha').
      iLeft. iExists ps, cs, tt, P. iSplitR; [by iPureIntro |].
      iFrame "Htn Hps Hcs HE".
    - iIntros "[Hl | HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs [] P) "(%Hw & Htn & Hps & Hcs & HE & _)".
      iLeft. iExists ps, cs, tt, P.
      rewrite (lm_abs_ab pipe_lm pipe_hooks tt cs I a Ha').
      iSplitR; [by iPureIntro |]. iFrame "Htn Hps Hcs HE".
  Qed.

  (* =================================================================== *)
  (*  S6  THE LINKS ENTAIL THE GENERIC INTERFACE; THE READ RECEIPT, THE   *)
  (*      TURN, THE RESIDUE, at the generic shapes                        *)
  (* =================================================================== *)
  Lemma pipe_links_gl : pipe_links g -∗ glinks pipe_lm pipe_params.
  Proof using .
    iIntros "#Hlk".
    iDestruct (pipe_links_eq with "Hlk") as %Hc.
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite /glinks. iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - (* W *)
      rewrite /gl_w.
      iIntros "!>" (k v P b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply (pipe_write_link g Hc k v P b ps0 cs0 I0 Φ with "Hpin Htn Hps Hcs HE HΦ").
      { exact H1. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H2). }
      { rewrite proc_stream_p_lm. destruct s0. exact H3. }
    - (* BLK *)
      rewrite /gl_blk.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply (pipe_write_link_blk g Hc k v P a b ps0 cs0 I0 Φ
                with "Hpin Htn Hps Hcs HE HΦ").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H4). }
      { rewrite proc_before_p_lm. destruct s0. exact H5. }
      { exact H6. } { exact H7. } { exact H8. }
    - (* PRO *)
      rewrite /gl_pro.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      iApply (pipe_write_link_pro g Hc k v P a b ps0 cs0 I0 Φ
                with "Hpin Htn Hps Hcs HE HΦ").
      { exact H1. } { exact H2. } { exact H3. }
      { exact (proj2 (pro_pin_p_lm _ _ _) H4). }
      { rewrite pro_idx_p_lm. exact H5. }
      { rewrite proc_stream_p_lm. destruct s0. exact H6. }
      { exact H7. } { exact H8. }
    - (* HEAD: absent *)
      rewrite /gl_head. iIntros "!>" (k v I a b Φ) "_ _ _ [] _".
    - (* TAINT *)
      rewrite /gl_taint. iIntros "!>" (k b Φ) "#HT HΦ".
      iApply ("Ht" $! k b Φ with "HT HΦ").
  Qed.

  Lemma pread_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    pread_ret g k v n ws -∗
    PT ∨ (∃ (ps0 cs0 : list nat) (s0 : unit) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage pipe_lm ps0 cs0 s0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before pipe_lm ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ pipe_Wb k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /pread_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, tt, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0".
    iSplitR; [iPureIntro; rewrite length_fmap length_app Hdl; reflexivity |].
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_p_lm _ _ _ _) Hrs) |].
    rewrite -proc_before_p_lm /pipe_Wb. iFrame "Htlb".
  Qed.

  Lemma pturn0_gen (k : nat) :
    pturn_pre k -∗
    (∃ v : era_pins, era_pin γ k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, era_pin γ k v ∗ pwc_ban k v [] 0%nat).
  Proof using .
    rewrite /pturn_pre /PipeOut.pturn /eturn. iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin".
    rewrite /gwc_ban. iLeft. iExists [], [], tt, 0%nat.
    rewrite Nat.add_0_r /pipe_W. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact (lm_wr_ban_round0 pipe_lm tt).
  Qed.

  Lemma pwc_rres_res (v : era_pins) (I : list (bv 8)) :
    pwc_rres v I -∗ gwc_rres pipe_lm pipe_params v I.
  Proof using .
    rewrite /pwc_rres /gwc_rres. iIntros "Hr".
    iDestruct "Hr" as (ps0 cs0) "(%Hrs & #Htlb & #Hps0 & #Hcs0)".
    iExists ps0, cs0, tt. iFrame "Hps0 Hcs0".
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_p_lm _ _ _ _) Hrs) |].
    rewrite -proc_before_p_lm /pipe_Wb. iFrame "Htlb".
  Qed.

  (* =================================================================== *)
  (*  S7  WHAT THE CONSUMERS NAME AT THE ONE-WRITER LINE: the generic     *)
  (*      laws at this instance                                           *)
  (* =================================================================== *)
  Lemma pwc_line_taint k v I : PT -∗ pwc_line k v I.
  Proof using .
    iIntros "HT". rewrite /pwc_line. iLeft.
    by iApply (gwc_pro_taint pipe_lm pipe_params).
  Qed.

  Lemma pwc_line_of_post k v I a :
    papr I a -> pwc_post k v I a -∗ pwc_line k v I.
  Proof using .
    intros Ha. iIntros "Hc". rewrite /pwc_line. iRight. iExists a.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  Lemma pwc_line_of_pro k v I : pwc_pro k v I -∗ pwc_line k v I.
  Proof using . iIntros "Hc". rewrite /pwc_line. by iLeft. Qed.

  Lemma pwc_line_of_blk0 k v I a : pwc_blk k v I a 0%nat -∗ pwc_line k v I.
  Proof using .
    iIntros "Hc".
    iApply (pwc_line_of_post k v I (pnoc_of (pline_at I)) (papr_noc I)).
    rewrite /pwc_post (pab_noc_len I).
    iApply (gwc_blk_0 pipe_lm pipe_params with "Hc").
  Qed.

  Lemma pwc_lend_of_blk0 k v I a : pwc_blk k v I a 0%nat -∗ pwc_lend k v I.
  Proof using . apply (gwc_lend_of_blk0 pipe_lm pipe_params). Qed.

  Lemma pwc_ban_done_line k v I :
    pwc_ban k v I (length u_banner) -∗ pwc_line k v I.
  Proof using .
    iIntros "H". iApply pwc_line_of_pro.
    iApply (gwc_ban_done_pro pipe_lm pipe_params with "H").
  Qed.

  Lemma pwc_blk_sp k v I a :
    papr I a ->
    pwc_blk k v I a (length (pab I a) - 1)%nat -∗ pwc_sp_t k v I.
  Proof using .
    intros Ha. rewrite pab_lm.
    apply (gwc_blk_sp pipe_lm pipe_params k v I a (proj1 (papr_lm I a) Ha)).
  Qed.

  Lemma pblk_step (k : nat) (v : era_pins) (I : list (bv 8)) (a i : nat)
      (b : bv 8) (Φ : iProp Σ) :
    pab I a !! i = Some b ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_blk k v I a i -∗
    (pwc_blk k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb.
    apply (gblk_step pipe_lm pipe_params (pipe_links g) (pipe_links_persistent g)
             pipe_links_gl k v I a i b Φ).
    cbn [gK pipe_params]. by rewrite -pab_lm.
  Qed.

  (* the one-writer line is the generic line with the per-shape arm empty *)
  Definition pipe_X0 (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ := False%I.
  Lemma pipe_X0_tl k v I : Timeless (pipe_X0 k v I).
  Proof using . rewrite /pipe_X0. apply _. Qed.
  Lemma pipe_X0_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pipe_X0 k v I -∗
    (pwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using . iIntros (_) "_ _ [] _". Qed.

  Lemma pwc_line_gen k v I :
    pwc_line k v I -∗ gwc_line pipe_lm pipe_params pipe_X0 k v I.
  Proof using .
    rewrite /pwc_line /gwc_line. iIntros "[Hc | Hc]"; [by iLeft |].
    iDestruct "Hc" as (a) "[%Ha Hc]". iRight. iLeft. iExists a.
    iSplitR; [iPureIntro; exact (lm_apr_aprs pipe_lm pipe_hooks I a (proj1 (papr_lm I a) Ha)) |].
    by rewrite (pwc_post_gen k v I a Ha).
  Qed.

  Lemma pprompt_dollar_line (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipe_links g -∗ pwc_line k v I -∗
    (pwc_sp_t k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (gprompt_dollar_line pipe_lm pipe_params pipe_X0 (pipe_links g)
              (pipe_links_persistent g) pipe_links_gl pipe_X0_dollar k v I b Φ Hb
              with "Hpin Hlk [Hc] HΦ").
    iApply (pwc_line_gen with "Hc").
  Qed.

End pipe_links_line.

(* THE FAMILY NAMES, at the fixed part: abbreviations of the generic
   families at [pipe_params] (printed back as [pwc_* g]) *)
Notation pwc_pro g := (gwc_pro pipe_lm (pipe_params g)).
Notation pwc_blk g := (gwc_blk pipe_lm (pipe_params g)).
Notation pwc_owed g := (gwc_owed pipe_lm (pipe_params g)).
Notation pwc_sp g := (gwc_sp pipe_lm (pipe_params g)).
Notation pwc_open g := (gwc_open pipe_lm (pipe_params g)).
Notation pwc_sp_t g := (gwc_sp_t pipe_lm (pipe_params g)).
Notation pwc_open_t g := (gwc_open_t pipe_lm (pipe_params g)).
Notation pwc_ban g := (gwc_ban pipe_lm (pipe_params g)).
Notation pwc_lend g := (gwc_lend pipe_lm (pipe_params g)).
Notation pwc_pr g := (gwc_pr pipe_lm (pipe_params g)).
