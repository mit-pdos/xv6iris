(* ===================================================================== *)
(*  UShPipeRound.v -- SH'S ROUND AT THE PIPELINE APPLICATION              *)
(*  (lane SH-PIPE-ROUND-2; design claude-notes/design/app-pipe.md SS4.2,   *)
(*  SS5.8).                                                               *)
(*                                                                       *)
(*  [UShRound.v] is the FILE era's twin of this file and [UShRest.v]'s    *)
(*  [sh_rest_holds_at] is the generic glue at a [LinkRec]/[StageRec]      *)
(*  pair.  The pipeline era is SIMPLER than the file era in exactly one   *)
(*  way and HARDER in exactly one other:                                  *)
(*                                                                       *)
(*   - SIMPLER: there is NO STATE.  [UShRound]'s whole S0 (the three      *)
(*     ties, [pre_tie]/[done_tie]/[pend_tie] and their eleven step        *)
(*     lemmas) and the [Hold] that rides the cursor are GONE: the         *)
(*     pipeline claim carries no deed, so [Wcf I p] IS [pipe_Wcl_at I p]  *)
(*     and [Wbf I] IS [pipe_Wbl_at I].                                    *)
(*   - HARDER: the era has TWO line shapes whose CHILDREN DIFFER, and the *)
(*     second one forks twice more.  [UkShRedirBody.ushf_body_law_file]   *)
(*     is the mould for the dispatch; the pipe line's child law is        *)
(*     [sh_pipe_child_law] below, and it is the ONE thing this file does  *)
(*     not prove.                                                         *)
(*                                                                       *)
(*  SECTION MAP.                                                          *)
(*   S0  the era's PURE discipline readings -- the four [UkSh] section    *)
(*       hypotheses at [PipeDisc.disc_input_p] and                        *)
(*       [PipeUline.ush_line_pipe].                                       *)
(*   S1/S2  the families, and the ECHO arm's whole law at                 *)
(*       [PipeStageInst.pipe_stage_inst_at].                              *)
(*   S3  THE REFUTATION: the console turn admits ONE writer, so the       *)
(*       two-cursor lease is the round's LEND and not the [PBoth] arm's   *)
(*       premise (design SS4.3, refuted).                                  *)
(*   S4  the PIPE arm's line shape and [sh_pipe_child_law], the ONE       *)
(*       obligation the round is reduced to.                              *)
(*   S5  the dispatch and [sh_round_holds_pipe].                          *)
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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import ObsTrace.
Require Import ConsoleInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import PipeUline.
Require FileDisc.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import UkRun.
Require Import UexecExecInst.            (* THE INSTANCES *)
Require Import WpUart.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import LinkRec.
Require Import StageRec.
Require Import PipeLinkInst.
Require Import GenLinksLine.
Require Import PipeStageInst.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UShLine.
Require Import UShEcho.
Require Import UShPanic.
Require Import UShEchoPay.
Require Import UShRest.        (* [sh_sz_lo] / [sh_sz_al] / [sh_sz_ok] *)
Require Import UInitSh.        (* [sh_Rsh] -- the loop's own data at the break *)
Require Import SpecKexec.      (* [kexec_sz] *)
Require Import UserPtTree.
Require Import UkShPipeRound.  (* [ushq_line_at] -- the pipe line's shape *)
Require Import UkShPipeFork.   (* [pterm_wc] -- design SS4.3p's WIDENED credential *)
Require Import UkShPipeForkTwin.  (* the fork arm at it *)
Require Import UShCatPay.      (* [sh_cat_slot] -- the /cat pin the round's
                                  right child's exec needs (lane
                                  SH-PIPE-ROUND-6, finding (5)) *)
Require Import CtxIdDefs.
Require Import AppCfg AppPipeClaim.   (* [file_app] / [pipe_pred]: the record equation [Heq] *)
Require PipeProto.                    (* [pipeProtoG]: the binder below needs it in scope *)
Require UkPipeIface.                  (* [pifRegG]: likewise *)
Require UkPipeEntries.                (* echo at the console from the tree route *)
Require ExecRun.                      (* [udepw_at_refR_of_sup]: the U-tier exec rule *)
Require Import ExecEntry.             (* [image_entry] / [image_entry_taint] *)
Require Import UexecRet.              (* [uslot], [uslot_bupd] *)
Require UexecExecMint.                (* [udep_free] *)
Require LineModelLinks.               (* [lm_abs_ab]: the post at a state-free alternative *)
Require FsImg FsEchoPin FsAbsDefs.    (* the /echo pin the supply's walk resolves *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S0  THE ERA'S PURE DISCIPLINE READINGS                                *)
(*                                                                       *)
(*  [UkSh]'s section takes four facts about the input discipline and the  *)
(*  era's line constructor ([Dsc]/[Hdsc_ncr]/[Hdsc_short] and             *)
(*  [Dl]/[Hdsc_line]), and [UInitSh.cons_cred_holds_at] is stated at      *)
(*  exactly them.  These are the pipeline era's four, at                  *)
(*  [PipeDisc.disc_input_p] and [PipeUline.ush_line_pipe].                *)
(* ===================================================================== *)

(* the last byte of a disciplined input is a body byte -- BAR INCLUDED --
   or the newline *)
Lemma ushq_disc_snoc_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_p (I ++ [b]) -> pbody_byte b \/ b = wl_nl.
Proof using.
  intro Hd. destruct (decide (b = wl_nl)) as [-> | Hne]; [ by right | ].
  left. destruct Hd as (_ & Hr & _).
  rewrite (rest_of_snoc_other I b Hne) in Hr.
  apply Forall_app in Hr as [_ Hb].
  apply (Forall_lookup_1 _ _ 0%nat b Hb). reflexivity.
Qed.

(* ...AND ITS VALUE, which is the reading every branch of [gets] is
   decided by.  One more case than echo's ([wl_bar], 124), and it changes
   nothing: neither 13 nor 4 nor 0 is in the set. *)
Lemma ushq_disc_snoc_val (I : list (bv 8)) (b : bv 8) :
  disc_input_p (I ++ [b]) ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z \/ bv_unsigned b = 124%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof using.
  intro Hd. pose proof (ushq_disc_snoc_byte I b Hd) as Hp.
  destruct Hp as [Hp | Hnl];
    [ | left; rewrite Hnl; exact wl_nl_val ].
  destruct Hp as [Hp | Hbar];
    [ | right; right; left; rewrite Hbar; by vm_compute ].
  destruct Hp as [Ha | Hsp];
    [ | right; left; rewrite Hsp; exact wl_sp_val ].
  destruct Ha as [HA | Ha];
    [ right; right; right; left; exact HA | ].
  destruct Ha as [HB | HC];
    [ right; right; right; right; left; exact HB
    | right; right; right; right; right; exact HC ].
Qed.

(* [UkSh]'s [Hdsc_ncr] at the pipeline discipline *)
Lemma ushq_disc_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  disc_input_p (I ++ [b]) -> bv_unsigned b <> 13%Z.
Proof using. intro Hd. pose proof (ushq_disc_snoc_val I b Hd). lia. Qed.

(* ...AND THE ^D REFUTATION, [UkSh.disc_no_ctrl_d] one discipline over *)
Lemma ushq_disc_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4 -> disc_p h -> False.
Proof using.
  intros [h0 ->] Hx Hd.
  assert (Hb : bv_unsigned b = 4).
  { destruct (decide (b = (mword_of_int 13 : mword 8))) as [-> | Hne].
    - rewrite cons_xlate_cr in Hx. vm_compute in Hx. discriminate Hx.
    - rewrite (cons_xlate_other b Hne) in Hx. exact Hx. }
  destruct (UkSh.ush_cycles_snoc_in h0 b) as (s0 & Hin).
  pose proof (disc_p_seg _ _ Hd Hin) as Hseg.
  rewrite /disc_seg_p ins_app ins_in in Hseg.
  pose proof (ushq_disc_snoc_val (ins s0) b Hseg) as Hv. lia.
Qed.

(* ---- [UkSh]'s [Hdsc_line] at the pipeline era ------------------------ *)

(* a newline closes an admissible PIPELINE body *)
Lemma ushq_disc_snoc_nl (I : list (bv 8)) :
  disc_input_p (I ++ [wl_nl]) -> pbody_ok (rest_of I).
Proof using.
  intros (Hb & _ & _). rewrite bodies_of_snoc_nl in Hb.
  apply Forall_app in Hb as [_ Hlast].
  apply (Forall_lookup_1 _ _ 0%nat (rest_of I) Hlast). reflexivity.
Qed.

(* ...and that body IS the pipeline era's own line, at the three
   projections [UkSh.ush_line_at] reads ([PipeUline]'s bridge). *)
Lemma ushq_line_at_of_body (J : list (bv 8)) (f : nat -> bv 8) :
  pbody_ok J ->
  (forall j : nat, (j < length J)%nat -> f j = J !!! j) ->
  f (length J) = wl_nl ->
  exists lu : FileDisc.uline,
    PipeUline.ush_line_pipe lu
    /\ FileDisc.uline_ws lu = wl_words J
    /\ length (FileDisc.line_bytes lu) = S (length J)
    /\ UkSh.ush_line_at lu f 0%nat (S (length J)).
Proof using.
  intros Hb Hby Hfnl.
  destruct (pbody_ok_line J Hb) as [Hlok Hbody].
  set (lp := pline_of J).
  exists (PipeUline.uline_of_pline lp).
  assert (Hbytes : FileDisc.line_bytes (PipeUline.uline_of_pline lp)
                   = J ++ [wl_nl]).
  { rewrite (PipeUline.line_bytes_of_pline lp) /PipeDisc.line_bytes.
    by rewrite -Hbody. }
  assert (Hlen : length (FileDisc.line_bytes (PipeUline.uline_of_pline lp))
                 = S (length J))
    by (rewrite Hbytes length_app; cbn [length]; lia).
  split; [ exact (PipeUline.ush_line_pipe_of lp) | ].
  split.
  { rewrite (PipeUline.uline_ws_of_pline lp Hlok)
            /PipeUline.uline_of_pline.
    by rewrite -Hbody. }
  split; [ exact Hlen | ].
  rewrite /UkSh.ush_line_at. split_and!.
  - exact (PipeUline.uline_ok_of_pline lp Hlok).
  - by rewrite Hlen.
  - intros j Hj. rewrite Nat.add_0_l Hbytes.
    assert (Hnlat : (J ++ [wl_nl]) !!! length J = wl_nl).
    { pose proof (wl_lta_app_r J [wl_nl] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. exact Hr. }
    destruct (Nat.eq_dec j (length J)) as [-> | Hne].
    + by rewrite Hfnl Hnlat.
    + rewrite (Hby j ltac:(lia)).
      symmetry. exact (wl_lta_app_l J [wl_nl] j ltac:(lia)).
Qed.

Lemma ushq_disc_line_pipe (I : list (bv 8)) (f : nat -> bv 8) :
  disc_input_p (I ++ [wl_nl]) ->
  (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
  f (length (rest_of I)) = wl_nl ->
  exists lu : FileDisc.uline,
    PipeUline.ush_line_pipe lu
    /\ FileDisc.uline_ws lu = wl_words (rest_of I)
    /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
    /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))).
Proof using.
  intros Hd Hby Hfnl.
  exact (ushq_line_at_of_body (rest_of I) f (ushq_disc_snoc_nl I Hd) Hby Hfnl).
Qed.

(* ---- ...AND THE THIRD CONJUNCT OF THE LOOP'S SLOT ([UkSh.ush_posw]).
        The pipe era's line has a [FileDisc.fline_ok] body, which is what
        a child law reads to learn WHICH constructor the era filed.  The
        [LEcho] side is [PipeStageInst.pipe_lineok_of]; this is the
        producer, off the era's own [Hdsc_line]. ---- *)
Lemma ushq_fline_ok_of_pipe (lu : FileDisc.uline) :
  PipeUline.ush_line_pipe lu -> FileDisc.uline_ok lu ->
  FileDisc.fline_ok (FileDisc.line_body lu).
Proof using. intros _ Hok. exact (FileDisc.fline_ok_of lu Hok). Qed.


(* ===================================================================== *)
(*  S1/S2  THE FAMILIES, AND THE ECHO ARM'S THREE LAWS                    *)
(* ===================================================================== *)

Section UShPipeRound.
  (* [UShRound.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), MINUS
     the file claim's two classes -- the pipeline claim carries no per-era
     state, so neither [fileAppG] nor [fileOutG] is named anywhere below.
     NO [uexecSG] and NO [uprogSG] SECTION VARIABLE. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.

  (* the era's fixed record and its name record -- ECHO'S, because the
     pipeline claim is echo's shape with a persistent instance-free /cat
     conjunct (design SS5.7, lane PIPE-CLAIM) *)
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2). *)
  Context `{!pipeOutG Σ}.
  (* the tree route's instance at the console ([UkPipeIface.pipe_iface]):
     the protocol's class and the device registry (lane PIPECONS-EXIT) *)
  Context `{HpipeP : !PipeProto.pipeProtoG Σ}.
  Context `{HpifR : !UkPipeIface.pifRegG Σ}.
  Context (g : pipe_gn) (r : echo_names).
  Local Notation γ := (pgn_cl g).

  (* the record equations the top theorem hands over ([UInitBoot.
     echo_Hinit_boot]'s [Hcons]/[Htag]/[Hkill], one application on) *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = pecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = ptag g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = echo_taint γ).
  (* ...AND THE ERA'S RECORD EQUATION (lane PIPECONS-EXIT): the tree-route
     instance the echo child at the console runs at is stated at it *)
  Context (Heq : file_app = MkAppcfg echo_names (pipe_pred γ) r).

  Local Notation T := (echo_taint γ).
  Local Notation PI := (pipe_link_inst_at g).
  Local Notation SI := (pipe_stage_inst_at g).

  (* sh's own half of the console position pair ([UkSh]'s [γp]) *)
  Context (γp : gname).

  (* =================================================================== *)
  (*  THE FAMILIES.  There is NO [Hold]: [UShRound]'s [Wcf I p := Wcl I p *)
  (*  ∗ <the deed at p>] exists because the FILE era carries a deed        *)
  (*  between rounds, and the pipeline era carries nothing at all.  So    *)
  (*  the loop's two families ARE the record's own ([PipeLinkInst]'s      *)
  (*  [UShRound]-facing pair), and the generic laws below are applied at  *)
  (*  [Hold := emp] with the unit spliced in at the seam.                 *)
  (* =================================================================== *)
  Local Notation Wcf := (pipe_Wcl_at g).
  Local Notation Wbf := (pipe_Wbl_at g).

  (* ===================================================================== *)
  (*  NAME THE LEAF, DO NOT SEARCH.                                        *)
  (*                                                                       *)
  (*  MEASURED HERE, and it is the lane's first operational finding: in a  *)
  (*  file with this cone, [iIntros "#Hlk"] on [PipeLinks.pipe_links g] --  *)
  (*  six [□]-wands behind ONE transparent definition -- DOES NOT RETURN.   *)
  (*  The bundle has a [Global Instance] ([pipe_links_persistent], the one  *)
  (*  [PipeLinkInst] puts in [lk_links_pers]) and the hint net still does   *)
  (*  not reach it: the tree carries hundreds of [Persistent]/[Timeless]    *)
  (*  instances under transparent definitions (PIPE-LINK-INST's note on     *)
  (*  upstream's leaf-instance pass) and the search unfolds its way into    *)
  (*  the wand chain instead.  A bare probe -- [⊢ pipe_links g -∗ ⌜True⌝]   *)
  (*  proved by [iIntros "#Hlk"] -- times out at 200 s on its own.          *)
  (*                                                                       *)
  (*  So every [Persistent]/[Timeless] obligation this file raises is       *)
  (*  answered BY NAME at priority 0.                                       *)
  (* ===================================================================== *)
  #[local] Instance pipe_links_pers0 : Persistent (PipeLinks.pipe_links g) | 0
    := PipeLinks.pipe_links_persistent g.
  #[local] Instance pipe_T_pers0 : Persistent T | 0 := echo_taint_persistent γ.
  #[local] Instance pipe_T_tl0 : Timeless T | 0 := echo_taint_timeless γ.
  #[local] Instance pipe_Wcf_tl0 (I : list (bv 8)) (p : nat) :
    Timeless (Wcf I p) | 0 := pipe_Wcl_at_timeless g I p.
  #[local] Instance pipe_Wbf_tl0 (I : list (bv 8)) :
    Timeless (Wbf I) | 0 := pipe_Wbl_at_timeless g I.

  Local Lemma pipe_Wcf_pair (I : list (bv 8)) (p : nat) :
    Wcf I p ⊣⊢ (lk_lcred PI (S gen_id) I p ∗ emp)%I.
  Proof using . rewrite /pipe_Wcl_at. by rewrite right_id. Qed.

  Local Lemma pipe_Wbf_pair (I : list (bv 8)) :
    Wbf I ⊣⊢ ((∃ v : era_pins, lk_pin PI (S gen_id) v
                 ∗ lk_ban PI (S gen_id) v I 0%nat) ∗ emp)%I.
  Proof using . rewrite /pipe_Wbl_at. by rewrite right_id. Qed.

  (* the era's kill credential IS the echo taint -- the equation above,
     read as an entailment *)
  Lemma pipe_Hktaint : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  (* =================================================================== *)
  (*  THE ECHO CHILD'S GUARD, at the pipeline era's own lines.            *)
  (*                                                                     *)
  (*  [UShRound.file_D] one model over: the line the fork lends is        *)
  (*  admissible AND the era filed an [LEcho] at that input -- which is   *)
  (*  what [PipeStageInst.pipe_lineok] says and what the stage record is  *)
  (*  about.  A pipeline line answers the OTHER arm (S3).                 *)
  (* =================================================================== *)
  Definition pipe_D (I : list (bv 8)) : Prop :=
    line_ok (last_ws I) /\ pipe_lineok I.

  (* THE GUARD, OFF THE CHILD LAW'S OWN BOX: the line the fork lends is
     [line_ok] ([UkSh.ush_line_is]'s first conjunct) and the slot the loop
     left says the input's last body is SOME admissible line's body
     ([UkSh.ush_posw]'s third conjunct, [FileDisc.fline_ok] since lane
     ULINE-LPIPE).  [PipeStageInst.pipe_lineok_of] turns the two into the
     era's own constructor. *)
  Lemma pipe_D_of_line (I : list (bv 8)) (ws : list (list (bv 8))) :
    line_ok ws -> ws = last_ws I ->
    FileDisc.fline_ok (UkSh.ush_lastbody I) -> pipe_D I.
  Proof using .
    intros Hok Hwseq Hfb. subst ws. split; [ exact Hok | ].
    rewrite /UkSh.ush_lastbody in Hfb.
    exact (pipe_lineok_of I Hfb Hok).
  Qed.

  (* ...and the era's exec-failed BYTES are echo's at EVERY input
     ([PipeLinkInst.pipe_inst_exfb_echo]), so the guard costs nothing
     here -- it is the alternative's CODE that is per-line, and no
     consumer reads it. *)
  Lemma pipe_D_exfb (I : list (bv 8)) :
    pipe_D I ->
    lk_exfb PI I = alt_execfail
    /\ (length (lk_exfb PI I) - 2)%nat = 17%nat.
  Proof using . intros _. exact (pipe_inst_exfb_echo g I). Qed.

  (* ---- the four [Wc] laws [UShEchoPay]'s supply takes, at [Hold := emp] *)
  Local Lemma pwc3 (I0 : list (bv 8)) :
    ⊢ Wcf I0 3%nat -∗ ∃ v : era_pins,
        lk_pin PI (S gen_id) v ∗ lk_lpr PI (S gen_id) v I0 3%nat ∗ emp.
  Proof using .
    rewrite /pipe_Wcl_at /lk_lcred. iIntros "H".
    iDestruct "H" as (v) "[#Hp Hc]". iExists v.
    iSplitR; [ iExact "Hp" | ]. iSplitL; [ iExact "Hc" | done ].
  Qed.

  Local Lemma pwc3b (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_lpr PI (S gen_id) v0 I0 3%nat -∗
      emp -∗ Wcf I0 3%nat.
  Proof using .
    iIntros "#Hp Hc _". rewrite /pipe_Wcl_at /lk_lcred. iExists v0.
    iSplitR; [ iExact "Hp" | iExact "Hc" ].
  Qed.

  Local Lemma pwc0 (I0 : list (bv 8)) (v0 : era_pins) :
    ck_lineok (sk_cur SI) I0 ->
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_post PI (S gen_id) v0 I0 0%nat -∗
      emp -∗ Wcf I0 0%nat.
  Proof using .
    intro Hlok. iIntros "#Hp Hc _". rewrite /pipe_Wcl_at.
    iApply (lk_lcred_of_post_a PI (S gen_id) I0 0%nat v0
              (sk_apr0 SI I0 Hlok) with "Hp Hc").
  Qed.

  Local Lemma pwct (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_T PI -∗ Wcf I0 0%nat.
  Proof using .
    iIntros "#Hp #HT". rewrite /pipe_Wcl_at.
    iApply (lk_lcred_taint PI (S gen_id) I0 0%nat v0 with "Hp HT").
  Qed.

  (* the round's post, read back at the record: at an [LEcho] line the
     alternative-0 continuation is state-free ([sk_apr0]), so the block
     written up to its prompt at the block's own state IS the record's
     post ([UShRound.fpost_of_gwc] one model over) *)
  Local Lemma ppost_of_gwc (I0 : list (bv 8)) (v0 : era_pins) :
    ck_lineok (sk_cur SI) I0 ->
    gwc_post pipe_lm (pipe_params g) (S gen_id) v0 I0 0%nat -∗
    lk_post PI (S gen_id) v0 I0 0%nat.
  Proof using .
    intro Hlok. iIntros "Hc".
    rewrite /lk_post.
    cbn [lk_blk lk_ab pipe_link_inst_at gen_link_inst].
    rewrite /gwc_blk /gwc_post. iDestruct "Hc" as "[Hc | Hc]"; [ | by iRight ].
    iDestruct "Hc" as (ps cs sb P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    rewrite (LineModelLinks.lm_abs_ab pipe_lm (gK (pipe_params g)) sb cs I0 0%nat (sk_apr0 SI I0 Hlok)).
    (* the pipeline's witness family is [emp]: the frame may drop it *)
    iLeft. iExists ps, cs, sb, P. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE"; try iExact "Hf".
  Qed.

  (* =================================================================== *)
  (*  THE ECHO CHILD'S EXEC SUPPLY AT THE CONSOLE, FROM THE TREE ROUTE     *)
  (*  (lane PIPECONS-EXIT; program-specs SS3.4g).  [UShRound.              *)
  (*  echo_exec_sup_file] at the pipeline's record, over any family [Wc]  *)
  (*  with the four [Wc] laws at [Hold := emp] -- so the era's credential  *)
  (*  [Wcf] and the loop's widened one [Wct] are two applications -- with  *)
  (*  the image slot at [UkPipeEntries.pe_echo_cons_image_entry_alloc]:    *)
  (*  the lend opens into the block at its first byte ([gwc_blk ... 0 0]),  *)
  (*  and the block's end ([gwc_post] at code 0) folds at position 0.      *)
  (* =================================================================== *)
  Lemma echo_exec_sup_pipe (Wc : list (bv 8) -> nat -> iProp Σ) :
    (forall I0 : list (bv 8),
       ⊢ Wc I0 3%nat -∗ ∃ v : era_pins,
           lk_pin PI (S gen_id) v ∗ lk_lpr PI (S gen_id) v I0 3%nat ∗ emp) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin PI (S gen_id) v0 -∗ lk_lpr PI (S gen_id) v0 I0 3%nat -∗
         emp -∗ Wc I0 3%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ck_lineok (sk_cur SI) I0 ->
       ⊢ lk_pin PI (S gen_id) v0 -∗ lk_post PI (S gen_id) v0 I0 0%nat -∗
         emp -∗ Wc I0 0%nat) ->
    (forall (I0 : list (bv 8)) (v0 : era_pins),
       ⊢ lk_pin PI (S gen_id) v0 -∗ lk_T PI -∗ Wc I0 0%nat) ->
    ⊢ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq_at pipe_D Wc.
  Proof using Hcons Hkill Heq HpifR HpipeP.
    intros Hwc3 Hwc3b Hwc0 Hwct.
    iIntros "_ (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_wq_at. iIntros "!>" (I) "%HDI".
    destruct HDI as [Hokws Hlok].
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* the lend, opened: the era's pin and the block-owed family *)
    iDestruct (Hwc3 I with "Hcr") as (v) "(#Hpin & Hcr & HR)".
    (* the taint slot at the chosen payload *)
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wc I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wc I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwct I v with "Hpin"). iApply pipe_Hktaint. iExact "Hk". }
    iApply (ExecRun.udepw_at_refR_of_sup N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld
               ∗ lk_lpr PI (S gen_id) v I 3%nat ∗ emp)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr HR]").
    (* THE REFUND IS THE LEND, WHOLE *)
    { iIntros "!> ($ & Hc & HR)". iApply (Hwc3b I v with "Hpin Hc HR"). }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /ExecRun.uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img (last_ws I) M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd (last_ws I) _ _ _ M pm sz sa t gb
                Hokws with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    destruct Hfd1 as [rb Hl1].
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr HR".
    { iPureIntro.
      exact (UShEcho.sh_echo_path_of_holds (last_ws I) Hokws M sa t gb
               Himg Hbytes). }
    iSplitR "Hstd Hcr HR".
    { iApply (ExecRun.exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (FsAbsDefs.MkAnode (FsAbsDefs.AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr HR"; [ | iFrame "Hstd Hcr HR" ].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (_ & Hc & _)".
    (* ---- the lend at the record: the block at its first byte ---- *)
    cbn [lk_pin lk_lpr pipe_link_inst_at gen_link_inst gwc_lpr].
    iPoseProof (UkPipeEntries.pe_echo_cons_image_entry_alloc (PS := uprogSG_free)
                  g Hcons Hkill r Heq (last_ws I) M sa t gb fdv FsImg.ROOTINO chs pidv
                  v I rb (fun _ : Z => UkShFork.ushf_wq Wc I)
                  (fun _ _ => eq_refl) Hokws Himg Hbytes Hflen
                  ltac:(rewrite Hl; exact Hl1) Hlok
                  with "[] [] Hpin Hnp0 []") as "#He".
    { (* THE BLOCK'S END PAYS THE EXIT *)
      iIntros "!> Hpost". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwc0 I v Hlok with "Hpin [Hpost] [//]").
      iApply (ppost_of_gwc I v Hlok with "Hpost"). }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwct I v with "Hpin HT"). }
    { iApply (UexecExecMint.udep_free). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp Hc");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs ].
  Qed.

  (* ---- THE ECHO CHILD'S EXEC SUPPLY, at the era's guard: the tree
          route's ([echo_exec_sup_pipe] at the era's credential) ---- *)
  Lemma pipe_Hchild_echo :
    ⊢ PipeLinks.pipe_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq_at pipe_D Wcf.
  Proof using Hcons Hkill Heq HpifR HpipeP.
    iIntros "_". iApply (echo_exec_sup_pipe Wcf pwc3 pwc3b pwc0 pwct).
  Qed.

  (* ---- THE EXEC-FAILED DIAGNOSTIC'S LAW, at the parameterized carrier *)
  Lemma pipe_Hexecfail_D :
    ⊢ PipeLinks.pipe_links g -∗
      UkShEcho.ush_execfail_law_wq_at_D (PS := uprogSG_free) pipe_D
        (lk_exfb PI)
        (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat)
        Wcf.
  Proof using .
    rewrite /UkShEcho.ush_execfail_law_wq_at_D.
    iIntros "#Hlk".
    iIntros "!>" (I) "_".
    iPoseProof (UShPanic.ush_execfail_law_hold_at (PS := uprogSG_free) PI
                  (fun _ => emp)%I I with "[]") as "#Hx".
    { cbn [lk_links pipe_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | iSplitL; [ rewrite /pipe_Wcl_at; iExact "Hc" | done ] | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iDestruct ("Hend" with "Hp") as "[Hc _]".
    rewrite /pipe_Wcl_at. iExact "Hc".
  Qed.

  (* ---- sh's OWN FORK PANIC, at the era's families ---- *)
  Lemma pipe_Hpanic :
    ⊢ PipeLinks.pipe_links g -∗
      UkShDiag.ush_panic_law (PS := uprogSG_free) Wcf Wbf.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) PI
                  (fun _ => emp)%I with "[]") as "#Hp".
    { cbn [lk_links pipe_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_panic_law. iIntros "!>" (N I l) "%Hfd Hc".
    iDestruct ("Hp" $! N I l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | iSplitL; [ rewrite /pipe_Wcl_at; iExact "Hc" | done ] | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp5".
    iDestruct ("Hend" with "Hp5") as "[Hb _]".
    rewrite /pipe_Wbl_at. iExact "Hb".
  Qed.

  (* ---- ...AND THE ECHO CHILD'S WHOLE LAW ---- *)
  Lemma pipe_child_law_echo :
    ⊢ PipeLinks.pipe_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wcf.
  Proof using Hcons Hkill Heq HpifR HpipeP.
    iIntros "#Hlk #Hdep #Hslot".
    iPoseProof (pipe_Hexecfail_D with "Hlk") as "#Hxl".
    iPoseProof (pipe_Hchild_echo with "Hlk Hdep Hslot") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) pipe_D (lk_exfb PI)
              (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat) Wcf
              pipe_D_of_line pipe_D_exfb with "Hxl Hsup").
  Qed.

  (* ---- a KILLED child pays the payload with the taint ---- *)
  Lemma pipe_kill_law (v : era_pins) :
    era_pin γ (S gen_id) v -∗ UkShFork.ushf_kill_law Wcf.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [ iApply pipe_Hktaint; iExact "Hk" | ].
    iApply (pipe_Hcltaint g I 0%nat v with "Hpin HT").
  Qed.

  (* =================================================================== *)
  (*  S2b  THE ERA'S CREDENTIAL IS THE WIDENED ONE (design SS4.3p; lane   *)
  (*       SH-PIPE-ROUND-7 part 2).                                       *)
  (*                                                                     *)
  (*  The terminal round reaches the prompt only inside the LOOP'S OWN    *)
  (*  credential -- the fork arm's re-entry at 0x938 has no continuation  *)
  (*  but [UkShLoop.ushl_head] -- so the era runs at                      *)
  (*  [UkShPipeFork.pterm_wc g] and not at [pipe_Wcl_at g].  Every law    *)
  (*  below is the landed one at [Wcf] with [pterm_wc_3] on the way in    *)
  (*  (the body sees the credential at index 3 ALONE, where the widening  *)
  (*  collapses) and [pterm_wc_of] on the way out.                        *)
  (* =================================================================== *)
  Local Notation Wct := (UkShPipeFork.pterm_wc g).

  Local Lemma pwc3_t (I0 : list (bv 8)) :
    ⊢ Wct I0 3%nat -∗ ∃ v : era_pins,
        lk_pin PI (S gen_id) v ∗ lk_lpr PI (S gen_id) v I0 3%nat ∗ emp.
  Proof using .
    iIntros "H". iApply (pwc3 I0).
    iApply (UkShPipeFork.pterm_wc_3 g I0 with "H").
  Qed.

  Local Lemma pwc3b_t (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_lpr PI (S gen_id) v0 I0 3%nat -∗
      emp -∗ Wct I0 3%nat.
  Proof using .
    iIntros "#Hp Hc He".
    iApply (UkShPipeFork.pterm_wc_of g I0 3%nat).
    iApply (pwc3b I0 v0 with "Hp Hc He").
  Qed.

  Local Lemma pwc0_t (I0 : list (bv 8)) (v0 : era_pins) :
    ck_lineok (sk_cur SI) I0 ->
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_post PI (S gen_id) v0 I0 0%nat -∗
      emp -∗ Wct I0 0%nat.
  Proof using .
    intro Hlok. iIntros "#Hp Hc He".
    iApply (UkShPipeFork.pterm_wc_of g I0 0%nat).
    iApply (pwc0 I0 v0 Hlok with "Hp Hc He").
  Qed.

  Local Lemma pwct_t (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin PI (S gen_id) v0 -∗ lk_T PI -∗ Wct I0 0%nat.
  Proof using .
    iIntros "#Hp #HT".
    iApply (UkShPipeFork.pterm_wc_of g I0 0%nat).
    iApply (pwct I0 v0 with "Hp HT").
  Qed.

  (* ...at the loop's widened credential: the same supply, the four laws
     through [pterm_wc_3] / [pterm_wc_of] *)
  Lemma pipe_Hchild_echo_t :
    ⊢ PipeLinks.pipe_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq_at pipe_D Wct.
  Proof using Hcons Hkill Heq HpifR HpipeP.
    iIntros "_". iApply (echo_exec_sup_pipe Wct pwc3_t pwc3b_t pwc0_t pwct_t).
  Qed.

  Lemma pipe_Hexecfail_D_t :
    ⊢ PipeLinks.pipe_links g -∗
      UkShEcho.ush_execfail_law_wq_at_D (PS := uprogSG_free) pipe_D
        (lk_exfb PI)
        (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat)
        Wct.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (pipe_Hexecfail_D with "Hlk") as "#Hx".
    rewrite /UkShEcho.ush_execfail_law_wq_at_D.
    iIntros "!>" (I) "%HD".
    iPoseProof ("Hx" $! I with "[%]") as "#Hy"; [ exact HD | ].
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hy" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | iApply (UkShPipeFork.pterm_wc_3 g I with "Hc") | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iApply (UkShPipeFork.pterm_wc_of g I 0%nat).
    iApply ("Hend" with "Hp").
  Qed.

  Lemma pipe_Hpanic_t :
    ⊢ PipeLinks.pipe_links g -∗
      UkShDiag.ush_panic_law (PS := uprogSG_free) Wct Wbf.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (pipe_Hpanic with "Hlk") as "#Hp".
    rewrite /UkShDiag.ush_panic_law. iIntros "!>" (N I l) "%Hfd Hc".
    iApply ("Hp" $! N I l with "[%] [Hc]"); [ exact Hfd | ].
    iApply (UkShPipeFork.pterm_wc_3 g I with "Hc").
  Qed.

  Lemma pipe_child_law_echo_t :
    ⊢ PipeLinks.pipe_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wct.
  Proof using Hcons Hkill Heq HpifR HpipeP.
    iIntros "#Hlk #Hdep #Hslot".
    iPoseProof (pipe_Hexecfail_D_t with "Hlk") as "#Hxl".
    iPoseProof (pipe_Hchild_echo_t with "Hlk Hdep Hslot") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) pipe_D (lk_exfb PI)
              (fun I : list (bv 8) => (length (lk_exfb PI I) - 2)%nat) Wct
              pipe_D_of_line pipe_D_exfb with "Hxl Hsup").
  Qed.

  (* ...AND THE PROMPT'S LAW AT THE WIDENED CREDENTIAL.  Stated HERE and
     not at its call site ([UInitPipe.pipe_Hinit_boot]) on purpose: this
     section carries ONE [riscvGS]/[GenId] pair and the record equation
     [Hcons] beside it, so [UkShPipeFork.pterm_prompt_law] -- whose
     [Hcons] argument pins its own instances -- meets the landed law at
     the SAME ones.  At the boot lemma, which takes [HR] and [GEN] as
     explicit arguments beside the section's, the two sides of that wand
     are elaborated at different instances and the conversion walks into
     the two-writer family (measured: one [iApply] ran 1h28m). *)
  Lemma pipe_sh_prompt_law_t :
    ⊢ PipeLinks.pipe_links g -∗
      UShKernel.sh_prompt_law (PS := uprogSG_free) Wct.
  Proof using Hcons.
    iIntros "#Hlk".
    iDestruct (PipeLinks.pipe_links_taint g with "Hlk") as "#Ht".
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free) Wcf)%I as "#Hpl0".
    { iApply (UShPanic.sh_prompt_law_holds_line_at PI (PS := uprogSG_free)
                with "Hlk"). }
    rewrite /UShKernel.sh_prompt_law. iIntros "!>" (Np) "#Hro".
    (* [UkShPipeFork.pterm_prompt_law]'s body, INLINED.  Applying that
       lemma as a wand wedges -- the proofmode's [IntoWand] on a premise
       whose credential family is the record's [lk_lcred] runs past 90 s
       and (measured) past 90 min -- while its body is three [iDestruct]s
       on a [box] and one [iPoseProof] of [pterm_prompt_arm]. *)
    iPoseProof ("Hpl0" $! Np with "Hro") as "#Hlaw".
    rewrite {1}/UkSh.ush_prompt_law.
    iDestruct "Hlaw" as "[#Hplaw #Hclaw]".
    rewrite /UkSh.ush_prompt_law. iModIntro. iSplitR "".
    - iIntros (I l) "%Hfd2". destruct Hfd2 as [rb Hl2].
      iPoseProof (UkShPipeFork.pterm_prompt_arm g Hcons Np I l rb Hl2
                    with "Ht Hro") as "Hta".
      iIntros (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
      rewrite {1}/UkShPipeFork.pterm_wc.
      iDestruct "Hc" as "[Hc | [_ Hsh]]".
      + iApply ("Hplaw" $! I l with "[%] [%] [%] [%] Hcode [$Hstd $Hc] Hrun
                 [Hcont]");
          [ by exists rb | exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (UkShPipeFork.pterm_wc_of g I 2%nat with "Hw").
      + iApply ("Hta" $! h m avail with "[%] [%] [%] Hcode [$Hstd Hsh]
                 Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | | ].
        { rewrite Nat.add_0_r. iExact "Hsh". }
        iIntros (h' ret) "[Hstd Hsh'] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hsh'] Hrun").
        rewrite /UkShPipeFork.pterm_wc. iRight.
        iSplitR; [ iPureIntro; lia | ]. iExact "Hsh'".
    - iExact "Hclaw".
  Qed.

  Lemma pipe_kill_law_t (v : era_pins) :
    era_pin γ (S gen_id) v -∗ UkShFork.ushf_kill_law Wct.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [ iApply pipe_Hktaint; iExact "Hk" | ].
    iApply (UkShPipeFork.pterm_wc_of g I 0%nat).
    iApply (pipe_Hcltaint g I 0%nat v with "Hpin HT").
  Qed.


  (* =================================================================== *)
  (*  S3  THE REFUTATION THIS LANE OWES: THE CONSOLE TURN ADMITS EXACTLY  *)
  (*      ONE WRITER, SO THE TWO-WRITER LEASE IS THE ROUND'S LEND AND NOT *)
  (*      THE [PBoth] ARM'S PREMISE (design SS4.3, REFUTED).               *)
  (*                                                                     *)
  (*  design SS4.3 says the merge lease is "the one new stage mechanism"   *)
  (*  and that "everything else lands without it", with [pipe_both_law]   *)
  (*  as the round's ONE named premise.  That is false, and the reason is *)
  (*  one resource: the untainted arm of [pwc_blk] holds                  *)
  (*  [EchoOut.turn v P], HALF of a [mono_nat] authority whose other half *)
  (*  is the claim's ([turn_auth]).  Two children holding a block         *)
  (*  credential at one era pin is three halves, which is [False].        *)
  (*                                                                     *)
  (*  sh's runcmd child forks TWICE and the console block of the round    *)
  (*  may be written by EITHER child -- the left one at [PExecL] (`exec   *)
  (*  echo failed'), the right one at [PRan] (the line) and at [PExecR]   *)
  (*  (`exec cat failed'), BOTH at [PBoth] -- and which of them writes is *)
  (*  not known when the forks happen.  So the lend at the two forks      *)
  (*  cannot be the block credential, on ANY arm; it has to be the        *)
  (*  two-cursor family PIPE-2W is building, and that family has to cover *)
  (*  the four block shapes (the line, [dg_execL], [dg_execR], their      *)
  (*  merge) rather than the merge alone.                                 *)
  (* =================================================================== *)
  Lemma pipe_turn_one_writer (v : era_pins) (P1 P2 P3 : nat) :
    turn v P1 -∗ turn v P2 -∗ turn_auth v P3 -∗ False.
  Proof using .
    rewrite /turn /turn_auth. iIntros "H1 H2 H3".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[_ <-].
    iAssert (mono_nat_auth_own (ep_go v) 1 P1)%I with "[H1 H2]" as "H".
    { iEval (rewrite -Qp.half_half). iSplitL "H1"; [ iExact "H1" | iExact "H2" ]. }
    iDestruct (mono_nat_auth_own_agree with "H H3") as %[Hq _].
    iPureIntro. exact (Qp.not_add_le_l 1%Qp (1/2)%Qp Hq).
  Qed.

  (* ...AND THE SAME AT THE CREDENTIAL: at an UNTAINTED era only one
     process holds the block.  (The claim's half is the premise because
     it lives in the application invariant; a caller that holds the block
     twice opens it once and is done.) *)
  Lemma pipe_blk_one_writer (k : nat) (v : era_pins) (I I' : list (bv 8))
      (a a' i i' P : nat) :
    turn_auth v P -∗ pwc_blk g k v I a i -∗ pwc_blk g k v I' a' i' -∗ T.
  Proof using .
    iIntros "Ha Hb1 Hb2". rewrite !pwc_blk_view.
    iDestruct "Hb1" as "[Hb1 | #HT]"; last iExact "HT".
    iDestruct "Hb2" as "[Hb2 | #HT]"; last iExact "HT".
    iDestruct "Hb1" as (ps1 cs1 P1) "(_ & Ht1 & _)".
    iDestruct "Hb2" as (ps2 cs2 P2) "(_ & Ht2 & _)".
    iExFalso. iApply (pipe_turn_one_writer v _ _ P with "Ht1 Ht2 Ha").
  Qed.

  (* =================================================================== *)
  (*  S4  THE PIPE ARM: THE LINE SHAPE AND THE CHILD'S LAW                *)
  (*                                                                     *)
  (*  [UkShRedirBody]'s SS1/SS3 one line shape over.  The pipe line's      *)
  (*  shape is [UkShPipeRound.ushq_line_at] at the LEFT command's words;  *)
  (*  the existential binds those, because what the body walk is handed   *)
  (*  is [FileDisc.uline_ws (LPipe ws)] -- the WHOLE body's parse, five   *)
  (*  words at `echo a b | cat' -- and not the left command's three.      *)
  (* =================================================================== *)
  Definition ushq_lp (wsf : list (list (bv 8))) (gf : nat -> bv 8)
      (k len : nat) : Prop :=
    exists ws : list (list (bv 8)),
      wsf = ws ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat]
      /\ UkShPipeRound.ushq_line_at ws gf k len.

  (* the body walk's ONE reading of the line: its first byte is 'e'.  The
     same fact at either shape, because both run /echo -- the pipeline
     line is an echo line with six bytes glued on the end. *)
  Lemma ushq_lp0 (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
    ushq_lp wsf gf k len -> bv_unsigned (gf k) = 101%Z.
  Proof using .
    intros (ws & _ & Hok & Hlen & Hby).
    assert (Hok' : line_ok ws) by exact (proj1 Hok).
    (* the body is nonempty: its first word is `echo', and a word is *)
    assert (Hbody : (0 < length (wl_body ws))%nat).
    { pose proof (line_ok_wf _ Hok') as Hwf.
      pose proof Hok' as Hok2. destruct Hok2 as (_ & _ & Hge2 & _ & _).
      destruct ws as [| w rest].
      - exfalso. cbn [length] in Hge2. clear -Hge2. lia.
      - destruct (wl_wf_cons w rest Hwf) as [Hw _].
        rewrite wl_body_cons length_app.
        exact (Nat.lt_lt_add_r _ _ _ (wl_word_pos w Hw)). }
    assert (Hlpos : (0 < len)%nat).
    { rewrite Hlen /PipeDisc.line_bytes length_app. cbn [length].
      rewrite Nat.add_1_r. apply Nat.lt_0_succ. }
    pose proof (Hby 0%nat Hlpos) as H0. rewrite Nat.add_0_r in H0.
    rewrite H0.
    assert (Hb0 : PipeDisc.line_bytes (PipeDisc.LPipe ws) !!! 0%nat
                  = wl_body ws !!! 0%nat).
    { rewrite /PipeDisc.line_bytes /PipeDisc.line_body -app_assoc.
      exact (wl_lta_app_l (wl_body ws) _ 0%nat Hbody). }
    rewrite Hb0.
    assert (Hb1 : wl_body ws !!! 0%nat = wl_line ws !!! 0%nat).
    { symmetry. rewrite /wl_line.
      exact (wl_lta_app_l (wl_body ws) [wl_nl] 0%nat Hbody). }
    rewrite Hb1. exact (line_ok_head_byte0 ws Hok').
  Qed.

  (* the loop's typed line fact AT the pipe constructor IS the shape --
     [UkShRedirBody.ushs_lp_of_at] one shape over, and here it is a pure
     transport through [PipeUline]'s three projections. *)
  Lemma ushq_lp_of_at (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k len : nat) :
    UkSh.ush_line_at (FileDisc.LPipe ws 1) f k len ->
    ushq_lp (FileDisc.uline_ws (FileDisc.LPipe ws 1))
      (fun j : nat => f (k + j)%nat) 0%nat len.
  Proof using .
    intros (Hok & Hlen & Hby). exists ws.
    split; [ reflexivity | ].
    assert (Hb : FileDisc.line_bytes (FileDisc.LPipe ws 1)
                 = PipeDisc.line_bytes (PipeDisc.LPipe ws))
      by exact (PipeUline.line_bytes_of_pline (PipeDisc.LPipe ws)).
    rewrite /UkShPipeRound.ushq_line_at. split_and!.
    - exact (PipeUline.pline_ok_of_uline (PipeDisc.LPipe ws) Hok).
    - by rewrite Hlen Hb.
    - intros j Hj. rewrite Nat.add_0_l -Hb. exact (Hby j Hj).
  Qed.

  (* THE PIPE CHILD'S LAW ([UkShRedirBody.sh_redir_child_law]'s twin, at
     the shape the body walk consumes): from 0x9c0, with the pipeline
     line in its own buffer, the child parses it and runs [runcmd]'s PIPE
     arm -- and the WHOLE ROUND happens inside.  It is [UkShPipeRound.
     wp_kshm_child_pipe_line] plus the protocol, the two entries and the
     end-of-round reading; this lane states it and does not discharge it
     (see the report: the lend it has to make is PIPE-2W's lease, S3). *)
  (* ...AND IT TAKES THE /cat PIN (lane PIPE-STAGE-5; design SS4.3n's
     fourth bullet, SH-PIPE-ROUND-6 finding (5)).  The round this law is
     about EXECS /cat in its right child, and the (W) half of that exec
     ([UShCatPay.sh_exec_sup_cat_wq_holds_at], through
     [ExecRun.exec_walk_of_pin]) takes [UShCatPay.sh_cat_slot T], whose
     middle conjunct is the claim's law at [FsCatPin.era0_cat_pins].
     [UInitPipe.sh_pipe_child_law_all] asserts this law with NO
     resources, so everything the round needs must be a wand ANTECEDENT
     of it -- and the pin's ONE producer in the tree needs the ERA
     EQUATION, which lives in [UInitPipe.pipe_Hinit_boot] and nowhere
     below it.  So the pin is an antecedent here and
     [sh_round_holds_pipe] takes it as a premise; the Prop
     [sh_pipe_child_law_all] is unchanged.  The [box] is what keeps the
     law PERSISTENT, which is what the loop's [#]-intro of it needs. *)
  (* ...AND AT THE WIDENED CREDENTIAL (design SS4.3p): the child's exit
     payload is [UkShFork.ushf_wq Wct I], which [UkShPipeFork.pterm_wq_pay]
     says IS [pterm_pay I] -- the terminal round included.  No new
     definition, exactly as SS4.3j (1) predicted; what changed is the
     credential the WHOLE ERA runs at. *)
  (* ...AND IT TAKES THE LINK BUNDLE (design SS4.3r, lane SH-PIPE-ROUND-8
     finding (5); PIPE-STAGE-5's /cat-pin move once more).  Every byte
     step of the round's two-writer family ([PipeBoth.pblk2_cstep_L] /
     [pblk2_cstep_R_t]) takes [PipeLinks.pipe_link_taint g], whose only
     producer in the tree is [PipeLinks.pipe_links g].
     [UInitPipe.sh_pipe_child_law_all] asserts this law with NO resources,
     so the bundle has to be an ANTECEDENT here; [sh_round_holds_pipe]
     already holds it and supplies it.  The Prop [sh_pipe_child_law_all]
     does not move. *)
  (* ...AND IT TAKES THREE MORE ANTECEDENTS (design SS4.3u's standing
     grant and SS4.3z item 3; lane SH-PIPE-ROUND-11 finding (6)/(7)).  All
     three are supplied by [sh_round_holds_pipe] below and the Prop
     [sh_pipe_child_law_all] does not move:

       [UShEcho.sh_echo_slot T]   the LEFT child's exec supply takes it
         ([UShEchoPipePay.sh_exec_sup_echo_pipe_at]), exactly as the /cat
         pin is taken for the right child's.
       [∃ v, era_pin γ (S gen_id) v]   the era's pin, BEFORE the walk.
         The round's payload [UShPipeAssembly.pipe_Qc_at] and its lend
         [PipeBoth.blk2_inv ... v ...] both NAME [v], and both are fixed
         when [UShPipeChild.wp_kshm_child_pipe_paid_line_at] is applied --
         while the only [v] inside the walk is the one under the lend's
         own existential.  [era_pin] is an AGREEMENT ghost, so the two are
         the same [v].
       [□ (T -∗ UkSh.sh_deps)]   the FREE WRITE LAW under the taint.  The
         round's [panic("fork")] law wants [EchoOut.inp_lb v I] (it builds
         [UkShPipeFork.pterm_shape], whose second conjunct that is), and
         the lend's own reading of it ([UShPipeLaw.pipe_wcl3_inp]) is
         [(∃ v, era_pin ∗ inp_lb v I) ∨ T]: at a TAINTED turn there is no
         bound to read and the five bytes have to go out on the free law.
         Its only producer needs the era equation and [r], both of which
         live in [UInitPipe.pipe_Hinit_boot] and neither of which this law
         carries -- so it is an antecedent.  [udep] is NOT one:
         [UexecExecMint.udep_free] is closed. *)
  Definition sh_pipe_child_law : iProp Σ :=
    (□ (PipeLinks.pipe_links g -∗
        UShCatPay.sh_cat_slot T -∗
        UShEcho.sh_echo_slot T -∗
        (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
        □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
        UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
          Wct ushq_lp 68))%I.

  Global Instance sh_pipe_child_law_persistent :
    Persistent sh_pipe_child_law.
  Proof using .
    rewrite /sh_pipe_child_law.
    apply bi.intuitionistically_persistent.
  Qed.

  (* =================================================================== *)
  (*  S5  THE DISPATCH, AND THE ROUND                                     *)
  (* =================================================================== *)
  Local Notation Pm := (UShLine.ush_mid_at (lk_rres PI) γ γp).

  (* ...AND THE ERA'S READING OF THE PIECES (design SS4.3p, the read law
     at the widened credential): the mid-line pieces carry the READER'S
     residue at the same input, which is what [UkShPipeFork.
     pterm_read_law_of] -- the terminal arm's refutation -- takes as its
     one premise.  Persistent conjuncts, so the pieces come back whole. *)
  Lemma pipe_mid_rres (I' : list (bv 8)) :
    ⊢ Pm I' -∗ Pm I' ∗ (∃ v : era_pins, era_pin γ (S gen_id) v
                                        ∗ pwc_rres v I').
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hlb & #Hres)".
    iSplitR "".
    - iFrame "Hp Hpa Hrd". iExists v. by iFrame "Hpin Hdl Hlb Hres".
    - iExists v. by iFrame "Hpin Hres".
  Qed.

  (* ...and the pipeline era's own [pterm_read_law], off it *)
  Lemma pipe_pterm_read_law :
    UkShPipeFork.pterm_read_law g Pm.
  Proof using .
    exact (UkShPipeFork.pterm_read_law_of g Pm pipe_mid_rres).
  Qed.

  Lemma ushq_body_law_pipe (N : uk_names Σ) `{Hp : !ukn_const N} (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wct -∗
    UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wct -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      Wct ushq_lp 68 -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wct Wbf -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      N γp T Wct Wbf Pm PipeUline.ush_line_pipe sz.
  Proof using .
    intros Hszlo Hszal Hszok.
    iIntros "#Hkl #Hchl #Hchq #Hplaw".
    iPoseProof (UkShPipeForkTwin.ushf_body_law_echo_pipe (PS := uprogSG_free)
                  (SG := uexecSG_xv6) N γp T Wct Wbf Pm
                  (fun k H => H) sz Hszlo Hszal Hszok
                  (UkShPipeFork.pterm_wc_blk_line g)
                  with "Hkl Hchl Hplaw") as "#Hecho".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct Hd as [[ws | ws] ->]; cbn [PipeUline.uline_of_pline].
    - (* [echo a b] -- the landed walk *)
      iApply ("Hecho" $! (FileDisc.LEcho ws) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists ws | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* [echo a b | cat] -- the SAME walk at the pipe child's law *)
      iDestruct (UkSh.ush_jtab_ro (ukn_t N) with "Hjt") as "#Hro".
      iApply (UkShPipeForkTwin.wp_kshm_body_pipe (PS := uprogSG_free)
                (SG := uexecSG_xv6) N γp T Wct Wbf Pm (fun k0 H => H)
                ushq_lp 68 h m f k len
                (FileDisc.uline_ws (FileDisc.LPipe ws 1)) sz l n
                ltac:(lia) ushq_lp0
                Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (ushq_lp_of_at ws f k len Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb
                (UkShPipeFork.pterm_wc_blk_line g)
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchq Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp (ukn_t N) with "Hcode").
      + exact Hfd0.
  Qed.

  (* ...AND THE ROUND: the command loop's body obligation at the pipeline
     era's families, which is what [UInitSh.sh_pay_of_parts_at] takes and
     therefore what the pipeline theorem's [Hprog] spends. *)
  Lemma sh_round_holds_pipe (N : uk_names Σ) :
    ⊢ PipeLinks.pipe_links g -∗
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      (* ...AND THE FREE WRITE LAW UNDER THE TAINT (design SS4.3z item 3):
         the ONE thing the child law's new antecedent list adds to this
         lemma's own premises.  [UInitPipe.pipe_Hinit_boot] has it -- it is
         [UexecExecMint.udepw_law_of_sup_write] at the era's supply, the
         same three lines its [init_deps] is built from. *)
      □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
      sh_pipe_child_law -∗
      UkSh.ush_rest_l_at (PS := uprogSG_free) N γp T Wct Wbf Pm
        PipeUline.ush_line_pipe
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using Hcons Hkill Heq HpifR HpipeP.
    iIntros "#Hlk #Hdep #Hslot #Hcat #Hpin #Hdps #Hchl0".
    iPoseProof ("Hchl0" with "Hlk Hcat Hslot Hpin Hdps") as "#Hchq".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (pipe_kill_law_t v with "Hp") as "#Hkl".
    iPoseProof (pipe_child_law_echo_t with "Hlk Hdep Hslot") as "#Hchl".
    iPoseProof (pipe_Hpanic_t with "Hlk") as "#Hplaw".
    iIntros "!>" (l) "%Hc".
    iPoseProof (ushq_body_law_pipe N (Hp := Hc) (kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  with "Hkl Hchl Hchq Hplaw") as "#Hbody".
    iPoseProof (UkShPipeForkTwin.ushf_rest_of_body_at_pipe
                  (PS := uprogSG_free)
                  (SG := uexecSG_xv6) (Hpay := Hc) N γp T Wct Wbf Pm
                  (fun k H => H) PipeUline.ush_line_pipe
                  (kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok
                  (UkShPipeFork.pterm_wc_blk_line g) with "Hbody") as "Hb".
    rewrite /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.

End UShPipeRound.
