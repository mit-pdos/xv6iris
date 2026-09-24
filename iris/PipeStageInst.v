(* ===================================================================== *)
(*  PipeStageInst.v -- [StageRec.StageRec] AT THE PIPELINE APPLICATION.   *)
(*                                                                       *)
(*  Lane SH-PIPE-ROUND-2.  [PipeLinkInst.v] landed the [LinkRec]          *)
(*  instance and stopped exactly here: the CURSOR a paid child runs at.   *)
(*  This file is that record, and the design step it carries is WHICH     *)
(*  inputs it is about.                                                   *)
(*                                                                       *)
(*  ===== THE RULING ================================================== *)
(*                                                                       *)
(*  [StageRec.sk_apr0] hard-codes ALTERNATIVE ZERO: it owes               *)
(*  [lk_apr L I 0], which at the pipeline record is [papr I 0], i.e.      *)
(*  [palt_ok (pline_at I) (PEcho 0)].  At an [LPipe] line that is FALSE   *)
(*  ([PipeDisc.palt_ok_pipe_echo]: only [PEcho 3] joins a pipeline        *)
(*  line's [PEcho] arms).  So the stage record CANNOT be about a          *)
(*  pipeline line, and the design's "the cursor is cat's" is not a        *)
(*  [StageRec] instance at all:                                          *)
(*                                                                       *)
(*    - the ECHO child of an [LEcho] round writes alternative 0 and is    *)
(*      the [StageRec] client ([UShEchoPay.ushf_child_law_hold_at]);      *)
(*      [pipe_lineok] is the guard, and it is [FileLinkInst.              *)
(*      file_lineok] one model over;                                      *)
(*    - the CAT child of an [LPipe] round writes alternative               *)
(*      [palt_code PRan], whose bytes are the SAME list                    *)
(*      ([PipeDisc.pcont_PRan_alt0]) at a DIFFERENT code, and its         *)
(*      cursor is [UCatPipe.pcch] -- landed by lane CAT-PIPE, outside      *)
(*      this record on purpose.                                          *)
(*                                                                       *)
(*  The two cursors are the same family ([pwc_blk] at two alternatives);  *)
(*  what cannot be shared is [sk_apr0]'s NUMBER.  Reported.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
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
Require Import EchoOut.
Require Import PipeOut.
Require Import PipeLinksLine.
Require Import PipeHooks.         (* S0 of [PipeLinksLine], moved *)
Require Import PipeLinkInst.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import StageRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require FileDisc.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE PURE GUARD: WHICH INPUTS THE ECHO CURSOR IS ABOUT             *)
(* ===================================================================== *)

(* [Forall_forall] resolves to Stdlib's here (the [Require]s below bring
   [List] back on top of stdpp's), and Stdlib's takes [In] where every
   membership fact in the tree is [∈].  Go through the lookup form, which
   is unambiguous. *)
Local Lemma pipe_forall_in {A : Type} (P : A -> Prop) (l : list A) (x : A) :
  Forall P l -> x ∈ l -> P x.
Proof using.
  intros H Hx. apply elem_of_list_lookup in Hx as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ H Hi).
Qed.

(* A BODY THAT IS SOME ADMISSIBLE LINE'S BODY AND WHOSE WORDS ARE AN ECHO
   LINE IS AN ECHO BODY.  [FileDisc.fline_ok_echo] is this one model over
   and its case analysis is the same: the redirect body is killed by its
   '>', the cat line by its head word, the PIPE body by its bar. *)
Lemma pipe_body_ok_of_fline (b : list (bv 8)) :
  FileDisc.fline_ok b -> line_ok (wl_words b) -> body_ok b.
Proof using.
  intros [l [Hlok ->]] Hok.
  destruct l as [ws | ws | | ws npc].
  - (* LEcho: the body IS [wl_body ws] *)
    rewrite /FileDisc.line_body in Hok |- *.
    rewrite /FileDisc.uline_ok in Hlok.
    rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hlok)).
    split; [ reflexivity | exact Hlok ].
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok)))
      as Hbb.
    rewrite /FileDisc.line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    exact (FileDisc.wl_gt_not_body
             (pipe_forall_in _ _ _ Hsuf FileDisc.suf_gtf_gt)).
  - exfalso. rewrite /FileDisc.line_body in Hok.
    exact (FileDisc.cat_not_echo (line_ok_head _ Hok)).
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok)))
      as Hbb.
    rewrite /FileDisc.line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    destruct Hlok as (_ & Hn1 & _). destruct npc as [| m]; [lia |].
    rewrite FileDisc.suf_barcats_S in Hsuf. apply Forall_app in Hsuf as [Hsuf _].
    exact (FileDisc.fd_bar_not_body
             (pipe_forall_in _ _ _ Hsuf FileDisc.suf_barcat_bar)).
Qed.

(* ...AND THEN THE PIPELINE MODEL PARSES IT AS AN [LEcho] LINE. *)
Lemma pline_of_fline_echo (b : list (bv 8)) :
  FileDisc.fline_ok b -> line_ok (wl_words b) -> pline_of b = LEcho (wl_words b).
Proof using.
  intros Hf Hok. exact (pline_of_echo b (pipe_body_ok_of_fline b Hf Hok)).
Qed.

(* THE GUARD, at the record's own reading of the input's last line. *)
Definition pipe_lineok (I : list (bv 8)) : Prop :=
  pline_at I = LEcho (last_ws I).

Lemma pipe_lineok_of (I : list (bv 8)) :
  FileDisc.fline_ok (bodies_of I !!! (nlines I - 1)%nat) ->
  line_ok (last_ws I) -> pipe_lineok I.
Proof using.
  intros Hf Hok. rewrite /pipe_lineok /pline_at.
  rewrite (last_ws_lastbody I) in Hok |- *.
  exact (pline_of_fline_echo _ Hf Hok).
Qed.

(* ---- the model's alternative 0 at an echo line IS echo's own output --- *)
Lemma pipe_palt0 : palt_of 0%nat = PEcho 0%nat.
Proof using. apply palt_of_lt4. lia. Qed.

Lemma pipe_palt0_ok (I : list (bv 8)) :
  pipe_lineok I -> palt_ok (pline_at I) (palt_of 0%nat).
Proof using. intro Hl. rewrite Hl pipe_palt0. cbn [palt_ok]. lia. Qed.

Lemma pipe_palt0_nopanic : palt_panic (palt_of 0%nat) = false.
Proof using. rewrite pipe_palt0. by vm_compute. Qed.

Lemma pipe_palt0_nofork : palt_isforkS (palt_of 0%nat) = false.
Proof using. rewrite pipe_palt0. reflexivity. Qed.

Lemma pipe_pab0 (I : list (bv 8)) :
  pipe_lineok I -> pab I 0%nat = line_alts_of (last_ws I) !!! 0%nat.
Proof using.
  intro Hl.
  rewrite (pab_is I 0%nat (conj (pipe_palt0_ok I Hl) pipe_palt0_nofork))
          Hl pipe_palt0.
  reflexivity.
Qed.

Lemma pipe_pab0_len (I : list (bv 8)) :
  pipe_lineok I ->
  (length (pab I 0%nat) - 2)%nat = length (wl_line (drop 1 (last_ws I))).
Proof using.
  intro Hl. rewrite (pipe_pab0 I Hl) (line_alts_of_0_length (last_ws I)). lia.
Qed.

(* ===================================================================== *)
(*  S1  THE CURSOR AND THE STAGE                                          *)
(* ===================================================================== *)
Section pipe_stage_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Local Notation PI := (pipe_link_inst_at g).

  (* the stage a paid child runs at: the era's input, and nothing else --
     [FileLinkInst.file_stg] verbatim (the pipeline has no boot state
     either, so this record has exactly one field). *)
  Record pipe_stg := MkPipeStg { ps_I : list (bv 8) }.

  Local Lemma pi_cur_tl (k : nat) (v : era_pins) (st : pipe_stg) (p : nat) :
    Timeless (pwc_blk g k v (ps_I st) 0%nat p).
  Proof using . apply pwc_blk_timeless. Qed.

  Local Lemma pi_step (k : nat) (v : era_pins) (st : pipe_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    (pline_at (ps_I st) = LEcho ws /\ last_ws (ps_I st) = ws) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ lk_pin PI k v -∗ lk_links PI -∗ pwc_blk g k v (ps_I st) 0%nat i -∗
      (pwc_blk g k v (ps_I st) 0%nat (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros [Hln Hlast] Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (pblk_step g k v (ps_I st) 0%nat i b Φ with "Hpin Hlk Hc HΦ").
    rewrite (pipe_pab0 (ps_I st)
               ltac:(rewrite /pipe_lineok Hlast; exact Hln)).
    rewrite Hlast. exact Hb.
  Qed.

  Definition pipe_cur_inst : CurRec PI :=
    MkCurRec PI pipe_stg
      (fun st ws => pline_at (ps_I st) = LEcho ws /\ last_ws (ps_I st) = ws)
      (fun ws => line_alts_of ws !!! 0%nat)
      pipe_lineok
      (fun k v st p => pwc_blk g k v (ps_I st) 0%nat p)
      pi_cur_tl pi_step.

  (* THE LEND, OPENED.  [pwc_lend] and [pwc_blk _ _ _ 0 0] are the same
     proposition ([blkcs_p cs 0 0 = cs] and [P + 0 = P]); what the block's
     END pays is [lk_post PI], that family at [length (pab I 0) - 2]. *)
  Local Lemma pi_lend_stage (k : nat) (v : era_pins) (I : list (bv 8)) :
    pipe_lineok I ->
    ⊢ pwc_lend g k v I -∗
      (∃ st : pipe_stg,
         ⌜pline_at (ps_I st) = LEcho (last_ws I) /\ last_ws (ps_I st) = last_ws I⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat
            = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ pwc_blk g k v (ps_I st) 0%nat 0%nat
         ∗ □ (pwc_blk g k v (ps_I st) 0%nat
                (length (wl_line (drop 1 (last_ws I)))) -∗
              lk_post PI k v I 0%nat))
      ∨ lk_T PI.
  Proof using .
    intro Hlok. rewrite pwc_lend_view. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists (MkPipeStg I). cbn [ps_I].
    iSplitR; [ iPureIntro; split; [ exact Hlok | reflexivity ] | ].
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn".
    - rewrite pwc_blk_view. iLeft. iExists ps, cs, P.
      cbn [blkcs_p]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iIntros "!> Hc". rewrite /lk_post.
      cbn [lk_blk lk_ab pipe_link_inst_at gen_link_inst gK pipe_params].
      rewrite -pab_lm (pipe_pab0_len I Hlok). iExact "Hc".
  Qed.

  Local Lemma pi_apr0 (I : list (bv 8)) :
    pipe_lineok I -> lk_apr PI I 0%nat.
  Proof using .
    intro Hl. cbn [lk_apr pipe_link_inst_at gen_link_inst gK pipe_params].
    apply papr_lm. rewrite /papr.
    split_and!; [ exact (pipe_palt0_ok I Hl) | exact pipe_palt0_nopanic
                | exact pipe_palt0_nofork ].
  Qed.

  Definition pipe_stage_inst_at : StageRec PI :=
    MkStageRec PI pipe_cur_inst (fun _ => 0%nat) pi_lend_stage pi_apr0.

  (* =================================================================== *)
  (*  THE DEFINITIONAL CHECK ([LinkRec]'s / [PipeLinkInst]'s pattern).    *)
  (* =================================================================== *)
  Lemma pipe_stage_inst_cur (k : nat) (v : era_pins) (I : list (bv 8))
      (p : nat) :
    ck_cur (sk_cur pipe_stage_inst_at) k v (MkPipeStg I) p
    = pwc_blk g k v I 0%nat p.
  Proof using . reflexivity. Qed.
  Lemma pipe_stage_inst_alt (ws : list (list (bv 8))) :
    ck_alt (sk_cur pipe_stage_inst_at) ws = line_alts_of ws !!! 0%nat.
  Proof using . reflexivity. Qed.
  Lemma pipe_stage_inst_lineok (I : list (bv 8)) :
    ck_lineok (sk_cur pipe_stage_inst_at) I = pipe_lineok I.
  Proof using . reflexivity. Qed.

End pipe_stage_inst.

Global Arguments pipe_stg : clear implicits.
