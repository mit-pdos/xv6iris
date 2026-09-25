(* ===================================================================== *)
(*  UShRound.v -- SH'S ROUND AT THE FILE APPLICATION (lane SKELETON, K2). *)
(*                                                                       *)
(*  [UShRest.sh_rest_holds] is the shell's round at the ECHO era: the     *)
(*  command loop's body obligation ([UkSh.ush_rest_l]) discharged at that *)
(*  era's credential families.  This is its twin at the FILE era, where   *)
(*  the loop has THREE child shapes instead of one and carries the DEED   *)
(*  between rounds (design/app-file.md SS3, SS4.2, SS5.4).                  *)
(*                                                                       *)
(*  EVERY PROOF IN THIS FILE IS CLOSED (2026-09-22).  It began as a SKELETON --  *)
(*  console tier, the kernel or a sibling lane still owes is a NAMED      *)
(*  SECTION HYPOTHESIS with its exact statement.                         *)
(*                                                                       *)
(*  ===== THE ONE RULING THIS FILE MAKES =============================== *)
(*                                                                       *)
(*  THE DEED RIDES INSIDE THE CREDENTIAL FAMILY, and therefore            *)
(*  [UkShFork.ushf_wq]'s TWIN needs no new definition in [UkShFork.v].    *)
(*  [UkSh]'s [Wc : list (bv 8) -> nat -> iProp] is ABSTRACT, so the file  *)
(*  era instantiates it at [Wcf I p := Wcl I p ∗ <the deed at p>] -- the *)
(*  console credential of lane LINK-GEN paired with the deed at the       *)
(*  model's state for the round whose input is [I].  Then                 *)
(*  [UkShFork.ushf_wq Wcf I] IS the block owed or the block written       *)
(*  together with the deed back, which is what the design asks for, and   *)
(*  [ushf_child_law], [ush_panic_law], [ush_rest_l] and                   *)
(*  [UkShEcho.sh_exec_sup_echo_wq] all typecheck at it unchanged.         *)
(*                                                                       *)
(*  RULING HOLD-POS (2026-09-18): THE DEED'S TIE DEPENDS ON THE ROUND'S   *)
(*  POSITION.  The lend ([Wcf I 3]) carries the deed at the state BEFORE  *)
(*  the round of [I]'s last line (PRE); the settled positions 1 and 2 and *)
(*  the banner-owed family carry it at the state AFTER that line (DONE);  *)
(*  position 0 is FOLDED -- either the line is filed and the deed is DONE, *)
(*  or the block is still owed and the deed says which silent alternative *)
(*  the prompt byte will file (PEND).  The pure ties and their step       *)
(*  lemmas are above the section; [Wcf]/[Wbf] and the laws are S1/S2/S3. *)
(*                                                                       *)
(*  WHY THE DEED MUST BE IN [Wc] AND NOT BESIDE IT: sh READS ITS DEED     *)
(*  BEFORE IT PRINTS (design SS5.3 ruling (b), CAT-ENTRY).  The prompt     *)
(*  byte is the round's BLOCK-FIRST byte whenever the child printed        *)
(*  nothing -- an [echo ... > f] round, or a [cat f] at an empty `f` --    *)
(*  so the alternative that byte files ([FileLinks.file_write_link_blk]'s  *)
(*  [a]) is decided by the deed's value.  A credential that could be spent *)
(*  without the deed in hand would therefore be spendable at the wrong     *)
(*  alternative.                                                          *)
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
Require Import UserChildren.
Require Import UmodeAbi.
Require Import ProcGeom.
Require Import UexecRet.
Require Import ExecEntry.
Require Import UkRun UkRunSys.
Require Import UkRunLeaf.                (* [wp_uk_cli] / [wp_uk_cjr]: the stub *)
Require Import UexecExecInst.            (* THE INSTANCES *)
Require Import WpUart.
Require Import FsCfg.
Require Import FsImg.
Require Import FsImgCheck.
Require Import FsInitPin.                (* [INIT_INO] *)
Require Import FsShPin.                  (* [SH_INO] *)
Require Import FsEchoPin.                (* [ECHO_INO] *)
Require Import FsCatPin.                 (* [CAT_INO] *)
Require Import AppFileCons.              (* the claim's readings *)
Require Import AppCfg.
Require Import AppInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileOutPure.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileOpen.                 (* [fdq], [file_open_pay] *)
Require Import FileWrite.                (* [file_wq]: what the ran exit reads back *)
Require Import UEchoFile.                (* [ef_pay] / [efq]: echo at a file *)
Require Import FsAbsDefs.                (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.                  (* [udepw_at_refR_of_sup]: the U-tier exec rule *)
Require Import UkShRedirBody.            (* [ushs_fd1f], [sh_redir_child_law] *)
Require Import UkShRedirChild.           (* the redirect child's walk, 0x9c0 to its exits *)
Require Import ExecWords.                (* [exec_ok]: a word list sh can exec *)
Require Import UkShDiagAt.               (* [ush_execfail_bytes] *)
Require Import UShCat.                   (* [cat_elf_loadable] *)
Require Import UShCatPay.                (* [sh_cat_slot], [cat_pl], [sh_cat_pin_resolves] *)
Require Import UShRest.                  (* [sh_sz_lo] / [sh_sz_al] / [sh_sz_ok] *)
Require Import UserOff.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShLoop.
Require Import UShLexRedir.  (* [ush_line_lexable_redir_holds] -- the
                                redirect line's lexability, PROVED *)
Require Import UCodeShK.
Require Import UkShRedirAns.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UkFileOpen.
Require Import SysOpenDefs.              (* [om_readable] / [om_writable] *)
Require Import LinkRec.                  (* the era's link record *)
Require Import FileLinksLine.            (* [fline] / [fexfb] -- the era's line *)
Require Import FileHooks.         (* S0 of [FileLinksLine], moved *)
Require Import StageRec.                 (* [ck_lineok] / [sk_apr0] *)
Require Import LineModel.
Require Import LineModelLinks.
Require Import FileLinkInst.
Require Import GenLinksLine.
Require Import FileLinkGen.             (* [file_link_inst_at] -- LINK-GEN-2 + INIT-FILE *)
Require Import FileLinksAt.              (* the families at the round's boot state *)
Require Import FileLinksAtInp.           (* their input readings, for the seam *)
Require Import UShLineHold.              (* [ush_wb_inp_hold] *)
Require Import UShPanicHold.             (* the prompt law with a frame; [ksh_w_mono] *)
Require Import UShLine.
Require Import UShEcho.
Require Import UShPanic.          (* the panic and exec-failed laws at a record *)
Require Import UShEchoPay.        (* the paid child's laws at a record *)
Require Import UShKernel.
Require Import UInitSh.
Require Import UCatOut.                  (* [cat_tie] -- the pure round tie *)
Require Import UCatLend.          (* [catq_cat] / [cat_lend] *)
Require UkFileIface.                     (* [fifRegG]: the binder below needs it in scope *)
Require UkFileEntries.                   (* the three entries from the tree route *)
Require FileDeltas.                      (* [f_bytes_typed_short] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S0  RULING HOLD-POS, PURELY: THE THREE TIES AND THEIR STEPS           *)
(*                                                                       *)
(*  [c] is the deed's content ([AppFile.dst_content]); [cs] the choice    *)
(*  list the holder has a lower bound of; [sb] the era's boot state.      *)
(*    PRE   the round of [I]'s last line has not run: [cs] resolves every *)
(*          line but the last, [c] is the state before it.               *)
(*    DONE  every line of [I] is resolved and [c] is the state after.     *)
(*    PEND  the last round's alternative [a] is decided and SILENT (its   *)
(*          console output is the bare prompt), the deed has moved to its *)
(*          effect, and the console has not filed it yet.                *)
(* ===================================================================== *)
Definition pre_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
  : Prop :=
  length cs = (nlines I - 1)%nat /\ c = UCatOut.cat_st cs sb I.

Definition done_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
  : Prop :=
  length cs = nlines I /\ c = fstate_after cs sb I.

Definition pend_tie_at (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
    (a : nat) : Prop :=
  length cs = (nlines I - 1)%nat
  /\ (0 < nlines I)%nat
  /\ ralt_ok (fline I) (ralt_dec a)
  /\ cont (UCatOut.cat_st cs sb I) (fline I) (ralt_dec a) = u_prompt
  /\ c = fsm (UCatOut.cat_st cs sb I) (fline I) (ralt_dec a).

Definition pend_tie (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
  : Prop := exists a : nat, pend_tie_at cs sb I c a.

(* ---- the f-effects that are the identity ---- *)
Lemma fsm_echo (s : fstate) (ws : list (list (bv 8))) (a : ralt) :
  fsm s (LEcho ws) a = s.
Proof using . reflexivity. Qed.

Lemma fsm_cat (s : fstate) (a : ralt) : fsm s LCat a = s.
Proof using . reflexivity. Qed.

(* ...and the PIPELINE application's line, for the same reason as [LCat]'s:
   [FileDisc.fsm] moves the file at [LEchoF] and nowhere else (lane
   ULINE-LPIPE) *)
Lemma fsm_pipe (s : fstate) (ws : producer) (n : nat) (a : ralt) :
  fsm s (LPipe ws n) a = s.
Proof using . reflexivity. Qed.

(* a panic alternative moves no file, at any line *)
Lemma fsm_panic (s : fstate) (l : uline) (a : ralt) :
  ralt_panic a = true -> fsm s l a = s.
Proof using .
  intro H. destruct l as [ws | ws | | ws];
    [ reflexivity | | reflexivity | reflexivity ].
  destruct a; try reflexivity; cbn [ralt_panic] in H; discriminate H.
Qed.

(* the line's silent alternative moves no file -- at a redirect line this
   IS the model fix of RULING HOLD-POS ([RFSilent]'s effect is identity) *)
Lemma fsm_fnoc (s : fstate) (l : uline) : fsm s l (ralt_dec (fnoc_of l)) = s.
Proof using .
  destruct l as [ws | ws | | ws]; cbn [fnoc_of];
    [ reflexivity | by rewrite (ralt_dec_enc RFSilent)
    | reflexivity | reflexivity ].
Qed.

(* an alternative whose output is the bare prompt is not a panic *)
Lemma cont_prompt_nopanic (s : fstate) (l : uline) (a : ralt) :
  cont s l a = u_prompt -> ralt_panic a = false.
Proof using .
  intro H. destruct a as [k | sel | | | | | | | | | |]; cbn [ralt_panic];
    try reflexivity.
  - case_bool_decide as Hk; [ | reflexivity ]. exfalso. subst k.
    cbn [cont] in H. rewrite line_alts_of_3 in H.
    apply (f_equal length) in H.
    rewrite FileLinksLine.alt_panic_len5 EchoLinks.wr_prompt_len in H.
    discriminate H.
  - exfalso. cbn [cont] in H. apply (f_equal length) in H.
    rewrite FileLinksLine.alt_panic_len5 EchoLinks.wr_prompt_len in H.
    discriminate H.
  - exfalso. cbn [cont] in H. apply (f_equal length) in H.
    rewrite FileLinksLine.alt_panic_len5 EchoLinks.wr_prompt_len in H.
    discriminate H.
Qed.

(* ---- filing one alternative moves the state by one [fsm] step ---- *)
Lemma fstate_after_snoc (cs : list nat) (a : nat) (sb : fstate) (I : list (bv 8)) :
  length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
  fstate_after (cs ++ [a]) sb I
  = fsm (UCatOut.cat_st cs sb I) (fline I) (ralt_dec a).
Proof using .
  intros Hlen Hpos. rewrite /fstate_after /UCatOut.cat_st /fline.
  destruct (nlines I) as [| n] eqn:Hn; [ lia | ].
  try rewrite Hn in Hlen. replace (S n - 1)%nat with n in Hlen |- * by lia.
  cbn [fstate_upto]. f_equal.
  - apply fstate_upto_ext; [ | intros j _; reflexivity ].
    intros j Hj. rewrite list_lookup_total_alt lookup_app_l;
      [ by rewrite -list_lookup_total_alt | lia ].
  - rewrite /ralt_at -Hlen fd_snoc_lookup_total. reflexivity.
Qed.

Lemma done_tie_snoc (cs : list nat) (a : nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
  c = fsm (UCatOut.cat_st cs sb I) (fline I) (ralt_dec a) ->
  done_tie (cs ++ [a]) sb I c.
Proof using .
  intros Hl Hp Hc. split; [ rewrite length_app; cbn [length]; lia | ].
  rewrite (fstate_after_snoc cs a sb I Hl Hp). exact Hc.
Qed.

(* (ii) DONE-of-PEND: the console files the alternative the deed decided *)
Lemma done_tie_of_pend (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate)
    (a : nat) :
  pend_tie_at cs sb I c a -> done_tie (cs ++ [a]) sb I c.
Proof using .
  intros (Hl & Hp & _ & _ & Hc). exact (done_tie_snoc cs a sb I c Hl Hp Hc).
Qed.

(* (iv) DONE-of-PRE at an alternative whose f-effect is the identity *)
Lemma done_tie_of_pre_id (cs : list nat) (a : nat) (sb : fstate)
    (I : list (bv 8)) (c : fstate) :
  (0 < nlines I)%nat -> pre_tie cs sb I c ->
  fsm (UCatOut.cat_st cs sb I) (fline I) (ralt_dec a) = UCatOut.cat_st cs sb I ->
  done_tie (cs ++ [a]) sb I c.
Proof using .
  intros Hp [Hl Hc] Hid. apply (done_tie_snoc cs a sb I c Hl Hp).
  rewrite Hid. exact Hc.
Qed.

(* (iii) PEND-of-PRE at the line's silent identity alternative *)
Lemma pend_tie_of_pre (cs : list nat) (sb : fstate) (I : list (bv 8)) (c : fstate) :
  (0 < nlines I)%nat -> pre_tie cs sb I c ->
  pend_tie_at cs sb I c (fnoc_of (fline I)).
Proof using .
  intros Hp [Hl Hc]. split_and!;
    [ exact Hl | exact Hp | exact (fnoc_of_ok (fline I))
    | exact (cont_fnoc _ (fline I)) | rewrite fsm_fnoc; exact Hc ].
Qed.

(* (iv'), at a FILED list: the holder of PRE meets a console whose list is
   one longer and extends its own, and the filed alternative's effect is
   the identity -- or nothing is filed at all ([nlines I = 0]) *)
Lemma done_tie_of_pre_prefix (cs cs' : list nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  pre_tie cs' sb I c -> length cs = nlines I -> cs' `prefix_of` cs ->
  ((0 < nlines I)%nat ->
   fsm (UCatOut.cat_st cs' sb I) (fline I) (ralt_at cs (nlines I - 1)%nat)
   = UCatOut.cat_st cs' sb I) ->
  done_tie cs sb I c.
Proof using .
  intros [Hl' Hc] Hl Hpre Hid.
  destruct (nlines I) as [| n] eqn:Hn.
  - (* no complete line: both lists are empty, both states the boot state *)
    try rewrite Hn in Hl. apply nil_length_inv in Hl. subst cs.
    split; [ by rewrite Hn | ].
    rewrite Hc /UCatOut.cat_st /fstate_after Hn. reflexivity.
  - try rewrite Hn in Hl. try rewrite Hn in Hl'. try rewrite Hn in Hid.
    replace (S n - 1)%nat with n in * by lia.
    destruct Hpre as [rest ->].
    assert (Hr : length rest = 1%nat) by (rewrite length_app in Hl; lia).
    destruct rest as [| a [| a' rest']]; cbn [length] in Hr; [ lia | | lia ].
    apply (done_tie_snoc cs' a sb I c); [ rewrite Hn; lia | rewrite Hn; lia | ].
    rewrite /ralt_at -Hl' fd_snoc_lookup_total in Hid.
    rewrite (Hid ltac:(lia)). exact Hc.
Qed.

(* ...and the banner-owed reading of it: the last filed alternative is a
   panic ([wr_ban_f]'s clause), whose f-effect is the identity *)
Lemma done_tie_of_pre_ban (cs cs' : list nat) (sb : fstate) (I : list (bv 8))
    (c : fstate) :
  pre_tie cs' sb I c -> length cs = nlines I -> cs' `prefix_of` cs ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true) ->
  done_tie cs sb I c.
Proof using .
  intros Hpre Hl Hp Hban.
  apply (done_tie_of_pre_prefix cs cs' sb I c Hpre Hl Hp).
  intro Hpos. destruct Hban as [-> | Hpan];
    [ rewrite nlines_nil in Hpos; lia | exact (fsm_panic _ _ _ Hpan) ].
Qed.

(* (i) PRE-of-DONE: a new complete line makes the settled state the state
   BEFORE the new round *)
Lemma pre_tie_of_done (cs : list nat) (sb : fstate) (I l : list (bv 8)) (c : fstate) :
  rest_of I = [] -> wl_nl ∉ l ->
  done_tie cs sb I c -> pre_tie cs sb (I ++ l ++ [wl_nl]) c.
Proof using .
  intros Hr Hl [Hlen Hc].
  assert (Hassoc : I ++ l ++ [wl_nl] = (I ++ l) ++ [wl_nl])
    by (by rewrite app_assoc).
  assert (Hn : nlines (I ++ l ++ [wl_nl]) = S (nlines I))
    by (rewrite Hassoc nlines_snoc_nl (EchoLinks.nlines_app_nonl I l Hl);
        reflexivity).
  split; [ rewrite Hn; lia | ].
  rewrite Hc /fstate_after /UCatOut.cat_st Hn.
  replace (S (nlines I) - 1)%nat with (nlines I) by lia.
  apply fstate_upto_ext; [ intros j _; reflexivity | ].
  intros j Hj.
  pose proof (bodies_of_app I (l ++ [wl_nl])) as Hpre.
  destruct (lookup_lt_is_Some_2 (bodies_of I) j Hj) as [x Hx].
  rewrite !list_lookup_total_alt Hx (prefix_lookup_Some _ _ _ _ Hx Hpre).
  reflexivity.
Qed.

(* ---- the block-first '$' at the DEED's alternative (the stage's own
        [wr_blk_dollar_f], with the state read instead of [fab]: the
        alternative need not be state-free -- [RCRan] at an empty `f`
        prints the bare prompt too) ---- *)
Lemma wr_blk_pending_at_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P -> ralt_panic (ralt_dec a) = false ->
  pending_at_f ps (cs ++ [a]) (Some s0) I
  = cont (UCatOut.cat_st cs s0 I) (fline I) (ralt_dec a).
Proof using .
  intros Hw Hnp.
  pose proof (wr_blk_nonnil_f ps cs s0 I P Hw) as Hne.
  pose proof Hw as (_ & Hr & Hn & _).
  assert (Hlast : (nlines I - 1)%nat = length cs) by lia.
  assert (Hat : ralt_at (cs ++ [a]) (nlines I - 1)%nat = ralt_dec a)
    by (rewrite /ralt_at Hlast fd_snoc_lookup_total; reflexivity).
  assert (Hup : fstate_upto (cs ++ [a]) s0 (bodies_of I) (nlines I - 1)%nat
                = fstate_upto cs s0 (bodies_of I) (nlines I - 1)%nat).
  { apply (fstate_upto_ext (cs ++ [a]) cs s0 (bodies_of I) (bodies_of I));
      [ | intros j _; reflexivity ].
    intros j Hj. rewrite list_lookup_total_alt lookup_app_l; [ | lia ].
    by rewrite -list_lookup_total_alt. }
  rewrite /pending_at_f decide_False; [ | exact Hne ].
  rewrite decide_True; [ | exact Hr ].
  rewrite /alt_cont_f f0_st_some Hat Hup Hnp app_nil_r. reflexivity.
Qed.

Lemma wr_blk_dollar_at_f (ps cs : list nat) (s0 : fstate) (I : list (bv 8))
    (P a : nat) :
  wr_blk_f ps cs s0 I P ->
  ralt_panic (ralt_dec a) = false ->
  cont (UCatOut.cat_st cs s0 I) (fline I) (ralt_dec a) = u_prompt ->
  wr_sp_f ps (cs ++ [a]) s0 I (S P).
Proof using .
  intros Hw Hnp Hcont. pose proof (wr_blk_started_f ps cs s0 I P Hw) as Hst.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  assert (Hpend : pending_at_f ps (cs ++ [a]) (Some s0) I = u_prompt)
    by (rewrite (wr_blk_pending_at_f ps cs s0 I P a Hw Hnp); exact Hcont).
  assert (Hlow : proc_before_f ps (cs ++ [a]) (Some s0) I
                 = proc_before_f ps cs (Some s0) I)
    by exact (wr_blk_low_f ps cs s0 I P a Hw).
  assert (Hup : proc_stream_f ps (cs ++ [a]) (Some s0) I
                = proc_before_f ps cs (Some s0) I ++ u_prompt)
    by (rewrite /proc_stream_f Hlow Hpend; reflexivity).
  assert (Hlen : length (proc_stream_f ps (cs ++ [a]) (Some s0) I) = S (S P)).
  { rewrite Hup (length_app (proc_before_f ps cs (Some s0) I) u_prompt)
            EchoLinks.wr_prompt_len. lia. }
  split.
  - rewrite /wr_open_f. split_and!.
    + exact (wr_blk_pin_snoc_f ps cs s0 I P a Hw).
    + exact Hm.
    + rewrite length_app Hdv. cbn [length]. lia.
    + rewrite Hdv (pro_idx_f_snoc_ne cs a Hnp).
      pose proof (Hpin (length cs) ltac:(rewrite Hst; lia)). lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [ | lia ].
    replace (S P - length (proc_before_f ps cs (Some s0) I))%nat
      with 1%nat by lia.
    exact EchoLinks.wr_prompt_tail.
Qed.

(* ---- VACUITY (design SS3.7's rule): every tie has an inhabitant ---- *)
Example pre_tie_inhabited : pre_tie [] None [] None.
Proof using . split; vm_compute; reflexivity. Qed.

Example done_tie_inhabited : done_tie [] None [] None.
Proof using . split; vm_compute; reflexivity. Qed.

(* the three silent alternatives, one per line shape; the redirect one at a
   PRESENT `f` is exactly what RULING HOLD-POS's model fix buys *)
Example pend_tie_cat_inhabited :
  pend_tie_at [] None (line_bytes LCat) None (ralt_enc RCSilent).
Proof using .
  rewrite /pend_tie_at ralt_dec_enc. vm_compute.
  split_and!; [ reflexivity | lia | exact I | reflexivity | reflexivity ].
Qed.

Example pend_tie_echo_inhabited :
  pend_tie_at [] None (line_bytes (LEcho fd_ws)) None 2%nat.
Proof using .
  rewrite /pend_tie_at. vm_compute.
  split_and!; [ reflexivity | lia | lia | reflexivity | reflexivity ].
Qed.

Example pend_tie_echof_inhabited :
  pend_tie_at [] (Some fd_content) (line_bytes (LEchoF fd_ws)) (Some fd_content)
    (ralt_enc RFSilent).
Proof using .
  rewrite /pend_tie_at ralt_dec_enc. vm_compute.
  split_and!; [ reflexivity | lia | exact I | reflexivity | reflexivity ].
Qed.

(* the words' line after the command fits a C int (the console write's
   count) -- [UkPipeEntries.pe_line_len], restated here to keep the round
   off the pipeline's cone *)
Lemma ush_line_len (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31.
Proof using .
  intros Hok. pose proof (EchoDisc.line_ok_len ws Hok) as Hl.
  unfold EchoDisc.line_max in Hl.
  assert (Hcn : forall (w : list (bv 8)) (r : list (list (bv 8))),
             (length (wl_line r) <= length (wl_line (w :: r)))%nat).
  { intros w r. rewrite !wl_line_length wl_body_cons length_app.
    destruct r as [| w' r'].
    - cbn. lia.
    - rewrite wl_tail_cons. cbn [length]. lia. }
  assert (Hle : (length (wl_line (drop 1 ws)) <= length (wl_line ws))%nat).
  { destruct ws as [| w r]; [reflexivity |].
    replace (drop 1 (w :: r)) with r by reflexivity. apply Hcn. }
  lia.
Qed.

Section UShRound.
  (* [UShRest.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), plus
     the file claim's and the file stage's classes.  NO [uexecSG] and NO
     [uprogSG] SECTION VARIABLE. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER (2026-09-22; durable-notes, "A section
     variable of a class type is a LOCAL INSTANCE").  [UShRest]'s binder
     list, copied here, declared one, and it was a SECOND instance beside
     [Xv6Cameras.offbox_offG] (through [xv6G]): the redirect and cat
     children had to be pinned at [offbox_offG] for the kernel's [ucwd],
     while the echo child, the kill law and the panic law elaborated at the
     section variable -- and the round, which feeds all five to one lemma,
     hung on the mismatch.  With the binder gone there is one instance in
     scope and the explicit [(ghost_varG0 := offbox_offG)] pins below name
     it. *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  (* the tree route's device registry ([UkFileIface]): the three entries
     the children run allocate it inside their slot *)
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  (* the era's record: [FileOut]'s gname pair, and the deed's names *)
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).

  (* ...AND THE ERA'S BOOT STATE (RULING H', 2026-09-18).  The round's
     hold is tied to the era's first state BY A SHARED INDEX and not by
     [FileOut.f0_lb]: that lower bound only exists after the era's first
     console byte ([GenLinks.gwrite_link_first] is its only producer),
     so a hold that asked for it was uninhabitable at /init's first
     instruction, where [UInitKernel.init_boot_pay] asks for [cc_wbn Cr 0]
     -- i.e. for [Wbf []] -- and the taint is not available and must not be
     (ADEQUACY's ruling).  THE STATE IS AN ERA CONSTANT, so it is a section
     variable beside [gen_id]; /init instantiates it at the deed's own
     content ([AppFile.dst_content s_deed]), which is what makes
     [UCatOut.cat_tie [] s0 [] s] hold by [eq_refl] at the head. *)
  Context (s0 : fstate).

  (* the record equations the top theorem hands over
     ([UInitBoot.echo_Hinit_boot]'s [Hcons] / [Htag] one application on) *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = fecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = ftag g).
  (* ...AND THE THIRD PROJECTION, beside the two (the program stream).
     [UInitBoot] derives all three from ONE interface equation
     ([Hiface]); the round took two of them as equations and the third as
     a hypothesis, which is the same fact twice. *)
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl g)).

  Local Notation T := (file_taint (fgn_cl g)).
  (* the era's LINK RECORD (lane LINK-GEN-2), AT THE BOOT STATE THE ROUND
     NAMES (RULING H', landed by lane INIT-FILE as [file_link_inst_at]).
     The unindexed record is this one's [∃ s0] packing
     ([FileLinkInst.file_Wcl_unpack] / [file_Wcl_at_pack] are the two
     directions), so nothing below is weaker for being read at the index --
     and the hold, which names the same [s0], is now tied to the
     credential STRUCTURALLY instead of through an agreement step. *)
  Local Notation FI := (FileLinkInst.file_link_inst_at g s0).

  (* =================================================================== *)
  (*  S1  THE FAMILIES                                                    *)
  (*                                                                     *)
  (*  [Wcl] / [Wbl] are lane LINK-GEN's: [EchoLinksLine.ewc_lcred] and    *)
  (*  [EchoLinks.ewc_ban] INSTANTIATED at [FileLinks] rather than twinned *)
  (*  (review SSD3).  They are PARAMETERS here, with exactly the five      *)
  (*  conversions the loop spends stated as hypotheses below -- which is  *)
  (*  where LINK-GEN's instance plugs in.  [Pm] is NOT a parameter:       *)
  (*  [UShLine.ush_mid_at] mentions only [EchoOut]'s era pins and the        *)
  (*  console lease, so the file era takes it verbatim at [fgn_echo g].   *)
  (* =================================================================== *)
  (* sh's own half of the console position pair ([UkSh]'s [γp]) *)
  Context (γp : gname).
  (* ...AND THEY ARE THE FILE INSTANCE NOW (the program stream), not
     parameters: [FileLinkInst.file_Wcl_at] / [file_Wbl_at] are lane
     LINK-GEN-2's record at this era AND AT THE ROUND'S OWN BOOT STATE, so
     the five conversions below are five applications of [LinkRec]'s own
     generic lemmas -- every one of them is about the record and not about
     the era, which is why the index costs nothing here. *)
  Local Notation Wcl := (FileLinkInst.file_Wcl_at g s0).
  Local Notation Wbl := (FileLinkInst.file_Wbl_at g s0).

  (* THE DEED, AT SH'S ROUND -- design SS4.2, "the deed meets the stage in
     sh's proof, PURELY", AT RULING HOLD-POS.  The deed's content is tied
     to the model's state by a PURE tie over the choice list the holder
     has a lower bound of and the era's boot state [s0] (the section's
     index, RULING H'); WHICH tie depends on the round's position, because
     at positions 0-2 the round of [I]'s last line has run and been filed
     and the same input needs one more [fsm] step than at the lend. *)
  Definition sh_deed_at
      (tie : list nat -> fstate -> list (bv 8) -> fstate -> Prop)
      (sb : fstate) (I : list (bv 8)) : iProp Σ :=
    ((∃ (cs : list nat) (s : dst) (v : era_pins),
        fown r s
        ∗ ⌜tie cs sb I (dst_content s)⌝
        ∗ f_typed (fgn_cl g) s
        ∗ era_pin (fgn_echo g) (S gen_id) v ∗ cs_lb v cs)
     ∨ T)%I.

  (* PRE ALSO HOLDS THE LINE'S WITNESS (the PROGRAM STREAM, stretch 9): the
     child that runs [echo ... > f] owes the claim "this line is one the
     ledger has" ([FileWrite.file_wq]'s [ws ∈ ls]; [Hopen_hand]'s too), and
     the only place the shell ever learns it is the read that completed
     the line -- off the consumed bytes' tags, through the reader's residue
     ([FileLinksLine.flw], [FileReadInst.fri_arms]).  So it rides with the
     deed from the read law ([Hwc_f]) to the fork's lend. *)
  Definition line_wit (I : list (bv 8)) : iProp Σ :=
    (FileLinksLine.flw g I ∨ T)%I.

  Global Instance line_wit_persistent I : Persistent (line_wit I).
  Proof using . rewrite /line_wit /T /file_taint /echo_taint. apply _. Qed.
  Global Instance line_wit_timeless I : Timeless (line_wit I).
  Proof using . rewrite /line_wit /T /file_taint /echo_taint. apply _. Qed.

  Definition sh_pre_at (sb : fstate) (I : list (bv 8)) : iProp Σ :=
    (sh_deed_at pre_tie sb I ∗ line_wit I)%I.
  Definition sh_done_at : fstate -> list (bv 8) -> iProp Σ := sh_deed_at done_tie.
  Definition sh_pend_at : fstate -> list (bv 8) -> iProp Σ := sh_deed_at pend_tie.

  Local Notation PRE := (sh_pre_at s0).
  Local Notation DONE := (sh_done_at s0).
  Local Notation PEND := (sh_pend_at s0).

  Global Instance sh_deed_at_timeless tie sb I : Timeless (sh_deed_at tie sb I).
  Proof using . rewrite /sh_deed_at /T /file_taint /echo_taint. apply _. Qed.

  (* the taint inhabits every tie -- the [∨ T] arm *)
  Lemma sh_deed_taint tie sb I : T -∗ sh_deed_at tie sb I.
  Proof using . iIntros "#HT". rewrite /sh_deed_at. by iRight. Qed.

  Global Instance sh_pre_at_timeless sb I : Timeless (sh_pre_at sb I).
  Proof using . rewrite /sh_pre_at. apply _. Qed.

  Lemma sh_pre_taint sb I : T -∗ sh_pre_at sb I.
  Proof using .
    iIntros "#HT". rewrite /sh_pre_at /line_wit.
    iSplitL; [ iApply (sh_deed_taint with "HT") | by iRight ].
  Qed.

  (* THE FAMILY THE LOOP CARRIES ([EchoLinksLine.ewc_lpr]'s shape, so that
     [p >= 3] is the lend):
       3   the lend: block owed, deed at PRE          (the child's entry)
       0   FOLDED: filed and DONE, or still owed with the deed PEND -- so
           no law ever meets "the deed says a, the console filed a'"
       1,2 the prompt's two settled positions, deed DONE. *)
  Definition Wcf (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => ((Wcl I 0%nat ∗ DONE I) ∨ (Wcl I 3%nat ∗ PEND I))%I
    | S O => (Wcl I 1%nat ∗ DONE I)%I
    | S (S O) => (Wcl I 2%nat ∗ DONE I)%I
    | _ => (Wcl I 3%nat ∗ PRE I)%I
    end.
  Definition Wbf (I : list (bv 8)) : iProp Σ :=
    (Wbl I ∗ DONE I)%I.

  Lemma Wcf_0 I :
    Wcf I 0%nat = ((Wcl I 0%nat ∗ DONE I) ∨ (Wcl I 3%nat ∗ PEND I))%I.
  Proof using . reflexivity. Qed.
  Lemma Wcf_1 I : Wcf I 1%nat = (Wcl I 1%nat ∗ DONE I)%I.
  Proof using . reflexivity. Qed.
  Lemma Wcf_2 I : Wcf I 2%nat = (Wcl I 2%nat ∗ DONE I)%I.
  Proof using . reflexivity. Qed.
  Lemma Wcf_S3 I p : Wcf I (S (S (S p))) = (Wcl I 3%nat ∗ PRE I)%I.
  Proof using . reflexivity. Qed.

  (* NAME THE LEAF, do not search (optimization.md, "Prove a big [Timeless]
     instance structurally").  [Timeless] patterns are keyed modulo delta and
     nearly every one of the tree's instances sits under a transparent
     definition, so ONE [apply _] at this altitude tries almost all of them:
     the four goals below measured 107s in a single sentence, which was this
     file's whole cost and the tail of the build's critical path.  Descend
     through the CONNECTIVES and name the leaf, SYNTACTICALLY -- a [first
     [...]] spelling would peel straight through a name that has its own
     instance. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (FileLinkInst.file_Wcl_at _ _ _ _) =>
           apply FileLinkInst.file_Wcl_at_timeless
    | |- Timeless (FileLinkInst.file_Wbl_at _ _ _) =>
           apply FileLinkInst.file_Wbl_at_timeless
    | |- Timeless (sh_pre_at _ _) => apply sh_pre_at_timeless
    | |- Timeless (sh_done_at _ _) => apply sh_deed_at_timeless
    | |- Timeless (sh_pend_at _ _) => apply sh_deed_at_timeless
    | |- _ => apply _
    end.

  Global Instance Wcf_timeless I p : Timeless (Wcf I p).
  Proof using .
    destruct p as [| [| [| p]]];
      [ rewrite Wcf_0 | rewrite Wcf_1 | rewrite Wcf_2 | rewrite Wcf_S3 ];
      tl_leaf.
  Qed.

  Global Instance Wbf_timeless I : Timeless (Wbf I).
  Proof using . rewrite /Wbf. tl_leaf. Qed.

  (* ...AND IT IS INHABITED AT THE ERA'S HEAD (RULING H' at HOLD-POS): at
     [I = []] nothing is filed, so the head is DONE at [cs = []] with the
     deed at its own boot value ([fstate_after [] s0 [] = s0]), and /init owes
     no lower bound but [cs_lb v []] -- which its turn carries
     ([UInitFileCons.file_Wbf_at_of_boot]). *)
  Lemma sh_done_head (s : dst) (v : era_pins) :
    era_pin (fgn_echo g) (S gen_id) v -∗ cs_lb v [] -∗
    fown r s -∗ f_typed (fgn_cl g) s -∗
    sh_done_at (dst_content s) [].
  Proof using .
    iIntros "#Hpin #Hcs Hd #Hty". rewrite /sh_done_at /sh_deed_at. iLeft.
    iExists [], s, v. iFrame "Hd Hpin Hcs Hty". iPureIntro.
    split; [ by rewrite nlines_nil | ].
    rewrite /fstate_after nlines_nil. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S2  LANE LINK-GEN'S OBLIGATIONS, at the ECHO shapes                 *)
  (*                                                                     *)
  (*  Each is an [EchoLinksLine]/[EchoLinks] lemma with [echo_links]      *)
  (*  replaced by [FileLinks]' bundle; they are exactly the conversions   *)
  (*  [UShRest.sh_rest_holds] and [UShKernel.sh_image_entry_at] spend.    *)
  (* =================================================================== *)

  (* [EchoLinksLine.ewc_lcred_blk_line], at the record *)
  Definition Hwbl : forall I : list (bv 8), ⊢ Wcl I 3%nat -∗ Wcl I 0%nat :=
    fun I => lk_lcred_blk_line FI (S gen_id) I.
  (* [UInitBoot]'s [Hsh_wbwc]: the banner-owed credential is a boundary one *)
  Definition Hwbwc : forall I : list (bv 8), ⊢ Wbl I -∗ Wcl I 0%nat :=
    fun I => lk_lcred_of_ban FI (S gen_id) I.
  (* [LinkRec.lk_lcred_taint]: the taint inhabits every credential -- AT A
     PIN (lane LINK-GEN's section 6, sharpened by LINK-GEN-2).  [Wcl I p]
     carries the era's pin under an existential and the pin is a linear
     [ghost_map] element persisted, which the taint does not produce; the
     ECHO-SIDE pin is the one the record's [lk_pin FI] IS
     ([FileLinkInst]: [lk_pin := era_pin (fgn_echo g)]), so ONE pin is
     enough and every spender ([sh_kill_law_file]) holds it. *)
  Definition Hcltaint : forall (I : list (bv 8)) (p : nat) (v : era_pins),
      ⊢ era_pin (fgn_echo g) (S gen_id) v -∗ T -∗ Wcl I p :=
    fun I p v => lk_lcred_taint FI (S gen_id) I p v.
  (* [UkSh]'s [Hwc]: the read that completed a line moves the credential
     from "2" at the old input to "3" at the new one.  The record's own
     lemma is stated at the PIN and the input's lower bound, and the loop's
     [ush_mid_at] carries both -- persistently -- so the bridge is one
     destructuring and no resource moves. *)
  Lemma Hwc : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) -∗ Wcl I 2%nat -∗
      UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl])
      ∗ Wcl (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros I l Hl. iIntros "Hmid Hc".
    rewrite /UShLine.ush_mid_at.
    iDestruct "Hmid" as "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hinp & Hres)".
    iSplitR "Hc".
    - iFrame "Hp Hpa Hrd". iExists v. iFrame "Hpin Hdl Hinp Hres".
    - iApply (lk_lcred_read FI (S gen_id) I l v Hl with "Hpin Hinp Hc").
  Qed.

  (* [UShLine.ush_wb_read_holds]: a read at a banner-owed credential taints *)
  Lemma Hwbr : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) -∗ Wbl I -∗
      UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) ∗ T.
  Proof using .
    intros I l Hl. iIntros "Hmid Hb".
    rewrite /UShLine.ush_mid_at.
    iDestruct "Hmid" as "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hinp & #Hres)".
    iSplitR "Hb".
    - iFrame "Hp Hpa Hrd". iExists v. iFrame "Hpin Hdl Hinp Hres".
    - iDestruct "Hb" as (v') "[#Hpin' Hb]".
      iDestruct (lk_pin_agr FI (S gen_id) v v' with "Hpin Hpin'") as %<-.
      iApply (lk_ban_read_taint FI (S gen_id) v I l Hl with "Hb Hres").
  Qed.
  (* the era's kill credential IS the file taint -- the equation above,
     read as an entailment *)
  Lemma Hktaint : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  (* ---- THE SAME FIVE AT THE POSITION-KEYED FAMILY (RULING HOLD-POS) ---- *)

  (* the taint inhabits every position *)
  Lemma Wcf_taint (I : list (bv 8)) (p : nat) (v : era_pins) :
    era_pin (fgn_echo g) (S gen_id) v -∗ T -∗ Wcf I p.
  Proof using .
    iIntros "#Hpin #HT". destruct p as [| [| [| p]]].
    - rewrite Wcf_0. iLeft. iSplitL "";
        [ iApply (Hcltaint I 0%nat v with "Hpin HT")
        | iApply (sh_deed_taint with "HT") ].
    - rewrite Wcf_1. iSplitL "";
        [ iApply (Hcltaint I 1%nat v with "Hpin HT")
        | iApply (sh_deed_taint with "HT") ].
    - rewrite Wcf_2. iSplitL "";
        [ iApply (Hcltaint I 2%nat v with "Hpin HT")
        | iApply (sh_deed_taint with "HT") ].
    - rewrite Wcf_S3. iSplitL "";
        [ iApply (Hcltaint I 3%nat v with "Hpin HT")
        | iApply (sh_pre_taint with "HT") ].
  Qed.

  (* (v) THE COUPLING: two lower bounds of one choice list line up, and at
     equal length they AGREE -- which is why DONE beside a filed console is
     never inconsistent. *)
  Lemma cs_lb_prefix_len (v : era_pins) (cs cs' : list nat) :
    (length cs' <= length cs)%nat ->
    cs_lb v cs -∗ cs_lb v cs' -∗ ⌜cs' `prefix_of` cs⌝.
  Proof using .
    intros Hl. iIntros "#H1 #H2".
    iDestruct (cs_lb_cmp v cs cs' with "H1 H2") as %[Hp | Hp];
      iPureIntro; [ | exact Hp ].
    rewrite (prefix_length_eq cs cs' Hp Hl). done.
  Qed.

  Lemma cs_lb_agree_len (v : era_pins) (cs cs' : list nat) :
    length cs = length cs' ->
    cs_lb v cs -∗ cs_lb v cs' -∗ ⌜cs = cs'⌝.
  Proof using .
    intros Hl. iIntros "#H1 #H2".
    iDestruct (cs_lb_prefix_len v cs cs' ltac:(lia) with "H1 H2") as %Hp.
    iPureIntro. symmetry. apply (prefix_length_eq cs' cs Hp). lia.
  Qed.

  (* ---- the record's block-owed credential, opened and closed at the
          round's stage ---- *)
  Local Lemma Wcl3_close (I : list (bv 8)) (v : era_pins) (ps cs : list nat)
      (P : nat) :
    wr_blk_t_f ps cs s0 I P ->
    era_pin (fgn_echo g) (S gen_id) v -∗
    FileLinksLine.fcur g v ps cs s0 I P (S gen_id) -∗ Wcl I 3%nat.
  Proof using .
    intro Hw. iIntros "#Hpin Hc".
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred.
    cbn [lk_pin lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
    iExists v. iFrame "Hpin". rewrite /gwc_blk. iLeft. iExists ps, cs, s0, P.
    cbn [lm_blkcs gW FileLinkGen.file_params_at].
    rewrite Nat.add_0_r /FileLinkGen.f0w_at /FileLinksLine.fcur.
    iDestruct "Hc" as "(Htn & #Hps & #Hcs & #HE & #Hf)".
    iFrame "Htn Hps Hcs HE Hf".
    iSplit; iPureIntro; [ by rewrite -wr_blk_t_f_lm | reflexivity ].
  Qed.

  (* the open credential says the input has no partial line *)
  Local Lemma Wcl2_rest (I : list (bv 8)) :
    Wcl I 2%nat -∗ Wcl I 2%nat ∗ (⌜rest_of I = []⌝ ∨ T).
  Proof using .
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred. iIntros "Hc".
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
    rewrite /gwc_open_t. iDestruct "Hc" as "[Hc | #HT]".
    - iDestruct "Hc" as (ps cs sw P) "(%Hw & Hcur)". iSplitL "Hcur".
      + iExists v. iFrame "Hpin". iLeft. iExists ps, cs, sw, P. iFrame "Hcur".
        by iPureIntro.
      + iLeft. iPureIntro. destruct Hw as [(_ & Hr & _) _]. exact Hr.
    - iSplitL ""; [ iExists v; iFrame "Hpin"; by iRight | by iRight ].
  Qed.

  (* (i) at the deed: the read that completed a line *)
  Lemma sh_pre_of_done (I l : list (bv 8)) :
    rest_of I = [] -> wl_nl ∉ l ->
    line_wit (I ++ l ++ [wl_nl]) -∗ DONE I -∗ PRE (I ++ l ++ [wl_nl]).
  Proof using .
    intros Hr Hl. rewrite /sh_pre_at /sh_done_at /sh_deed_at.
    iIntros "#Hlw Hd". iSplitL; [ | iExact "Hlw" ].
    iDestruct "Hd" as "[Hd | #HT]"; last by iRight.
    iDestruct "Hd" as (cs s v) "(Hd & %Htie & #Hty & #Hpin & #Hcs)".
    iLeft. iExists cs, s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
    exact (pre_tie_of_done cs s0 I l _ Hr Hl Htie).
  Qed.

  (* THE FOLD AT POSITION 0 (RULING HOLD-POS (vi)): a line credential
     beside a deed at PRE is a position-0 credential whenever every
     alternative of the line leaves `f` alone.  The line credential hides
     which alternative it filed, so the fold reads all three of its arms:
     the prologue (a panic, or the era's head), a block written up to its
     prompt (the alternative filed -- DONE by identity), or a block whose
     prompt IS its first byte (still owed -- PEND at the silent one). *)
  Lemma Wcf0_of_pre_line_id (I : list (bv 8)) :
    (forall (s : fstate) (a : ralt), fsm s (fline I) a = s) ->
    Wcl I 0%nat -∗ PRE I -∗ Wcf I 0%nat.
  Proof using .
    intros Hid. iIntros "Hc Hp". rewrite Wcf_0.
    rewrite {1}/sh_pre_at /sh_deed_at. iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iLeft. iFrame "Hc". iApply (sh_deed_taint with "HT"). }
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    pose proof Htie as [Hlen _].
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred.
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    (* the DONE arm, from any filed list that extends the deed's *)
    iAssert (∀ cs : list nat, ⌜length cs = nlines I⌝ -∗ ⌜cs' `prefix_of` cs⌝ -∗
               cs_lb v cs -∗ fown r s -∗ DONE I)%I as "Hdone".
    { iIntros (cs) "%Hl %Hpre #Hcs Hd". rewrite /sh_done_at /sh_deed_at. iLeft.
      iExists cs, s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
      apply (done_tie_of_pre_prefix cs cs' s0 I _ Htie Hl Hpre).
      intros _. apply Hid. }
    rewrite /gwc_line /gwc_pro /gwc_post /gcur. cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at /fhead_at
      /FileLinkGen.file_X.
    iDestruct "Hc" as "[Hpro | [Hblk | []]]".
    - (* the prologue: the last filed alternative is a panic, or the head *)
      iDestruct "Hpro" as "[Hpro | [Hhd | #HT]]".
      + iDestruct "Hpro" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
        subst sw.
        pose proof Hw as (_ & _ & Hn & _).
        iDestruct (cs_lb_prefix_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %Hpre.
        iLeft. iSplitL "Htn".
        * iExists v. iFrame "Hpin". iLeft. iLeft. iExists ps, cs, s0, P.
          iFrame "Htn Hps Hcs HE Hf". iSplit; by iPureIntro.
        * iApply ("Hdone" $! cs with "[%] [%] Hcs Hd"); [ lia | exact Hpre ].
      + iDestruct "Hhd" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & #Hvf & Hpre)".
        iLeft. iSplitL "Htn Hpre".
        * iExists v. iFrame "Hpin". iLeft. iRight. iLeft.
          iFrame "Htn Hps Hcs HE Hvf Hpre". by iSplit; iPureIntro.
        * iApply ("Hdone" $! [] with "[%] [%] Hcs Hd").
          { subst I. by rewrite nlines_nil. }
          { subst I. rewrite nlines_nil in Hlen. cbn in Hlen.
            apply nil_length_inv in Hlen. subst cs'. done. }
      + iLeft. iSplitL "";
          [ iApply (Hcltaint I 0%nat v with "Hpin HT")
          | iApply (sh_deed_taint with "HT") ].
    - (* a block written up to its prompt, at some alternative *)
      iDestruct "Hblk" as (a) "[%Hapr Hblk]".
      iDestruct "Hblk" as "[Hblk | #HT]"; last first.
      { iLeft. iSplitL "";
          [ iApply (Hcltaint I 0%nat v with "Hpin HT")
          | iApply (sh_deed_taint with "HT") ]. }
      iDestruct "Hblk" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
      subst sw. rewrite -wr_blk_t_f_lm in Hw. rewrite -(fabs_lm s0 cs I a).
      pose proof Hw as [(_ & _ & Hn & _) _].
      destruct (length (fabs s0 cs I a) - 2)%nat as [| i] eqn:Hi.
      + (* the prompt is the block's first byte: still owed, deed PEND *)
        cbn [lm_blkcs]. rewrite Nat.add_0_r.
        iDestruct (cs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
        iRight. iSplitL "Htn".
        * iApply (Wcl3_close I v ps cs P Hw with "Hpin [Htn]").
          rewrite /FileLinksLine.fcur. iFrame "Htn Hps Hcs HE Hf".
        * rewrite /sh_pend_at /sh_deed_at. iLeft. iExists cs, s, v.
          iFrame "Hd Hty Hpin Hcs". iPureIntro. exists (fnoc_of (fline I)).
          apply (pend_tie_of_pre cs s0 I _ ltac:(lia) Htie).
      + (* a byte before the prompt: the alternative is filed, deed DONE *)
        cbn [lm_blkcs].
        iDestruct (cs_lb_prefix_len v (cs ++ [a]) cs'
                     ltac:(rewrite length_app; cbn [length]; lia)
                     with "Hcs Hcs'") as %Hpre.
        iLeft. iSplitL "Htn".
        * iExists v. iFrame "Hpin". iRight. iLeft. iExists a.
          iSplitR; [ by iPureIntro | ]. iLeft.
          iExists ps, cs, s0, P.
          rewrite -(fabs_lm s0 cs I a) Hi. cbn [lm_blkcs].
          iFrame "Htn Hps Hcs HE Hf".
          iSplit; iPureIntro; [ by rewrite -wr_blk_t_f_lm | reflexivity ].
        * iApply ("Hdone" $! (cs ++ [a]) with "[%] [%] Hcs Hd");
            [ rewrite length_app; cbn [length]; lia | exact Hpre ].
  Qed.

  (* THE FOLD AT AN ALTERNATIVE THAT MOVES `f` (the redirect child's
     printing exits; [Wcf0_of_pre_line_id]'s twin).  There the line
     credential hid which alternative it filed and that was harmless,
     because every alternative left `f` alone.  Here the holder HAS moved
     the file -- a failed exec after the open truncated it, a round that
     wrote its chunks -- so it must present the block at the alternative
     [a] it took ([UShPanic.ush_diag_law_hold_at_alt] ends there), beside
     a deed whose content is [a]'s own f-effect on the round's entry
     state.  The block's choice list and the deed's agree by length
     ([cs_lb_agree_len]); past its first byte the block has FILED [a]
     (DONE, by [done_tie_snoc]), and a block whose prompt is its first
     byte is still owed (PEND at [a] itself: a two-byte block that ends
     with the prompt IS the prompt, [FileHooks.fabs_prompt]).
     STATED AT THE STATE-AWARE POST ([GenLinksLine.gwc_post] at
     [FileLinkGen.file_params_at]), so it serves the round whose bytes are
     the file's too ([RCRan]); the record's own block is the corollary
     below. *)
  Lemma Wcf0_of_posts_alt (I : list (bv 8)) (a : nat) (v v' : era_pins)
      (cs' : list nat) (s : dst) :
    faprs I a ->
    length cs' = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    dst_content s
      = fsm (UCatOut.cat_st cs' s0 I) (fline I) (ralt_dec a) ->
    lk_pin FI (S gen_id) v -∗
    gwc_post file_lm (file_params_at g s0) (S gen_id) v I a -∗
    fown r s -∗ f_typed (fgn_cl g) s -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs' -∗
    Wcf I 0%nat.
  Proof using .
    intros Hapr Hlen Hpos Hc.
    iIntros "#Hpin Hblk Hd #Hty #Hpin' #Hcs'". rewrite Wcf_0.
    cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    iEval (rewrite /gwc_post; cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at) in "Hblk".
    iDestruct "Hblk" as "[Hblk | #HT]"; last first.
    { iLeft. iSplitL "";
        [ iApply (Hcltaint I 0%nat v with "Hpin HT")
        | iApply (sh_deed_taint with "HT") ]. }
    iDestruct "Hblk" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
    subst sw. rewrite -wr_blk_t_f_lm in Hw. rewrite -(fabs_lm s0 cs I a).
    pose proof Hw as [(_ & _ & Hn & _) _].
    destruct (length (fabs s0 cs I a) - 2)%nat as [| i] eqn:Hi.
    - (* the prompt is the block's first byte: still owed, deed PEND at [a].
         The block IS the bare prompt: it ends with it ([fabs_prompt]) and
         is two bytes long. *)
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iDestruct (cs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
      assert (Hpr : cont (UCatOut.cat_st cs s0 I) (fline I) (ralt_dec a)
                    = u_prompt).
      { destruct (fabs_prompt s0 cs I a Hapr) as [pre Hpre].
        pose proof (fabs_len_ge2 s0 cs I a Hapr) as Hge.
        change (cont (UCatOut.cat_st cs s0 I) (fline I) (ralt_dec a))
          with (fabs s0 cs I a).
        rewrite Hpre length_app in Hi Hge.
        assert (Hp0 : length pre = 0%nat)
          by (revert Hi Hge; vm_compute (length u_prompt); lia).
        apply nil_length_inv in Hp0. rewrite Hpre Hp0. reflexivity. }
      iRight. iSplitL "Htn".
      + iApply (Wcl3_close I v ps cs P Hw with "Hpin [Htn]").
        rewrite /FileLinksLine.fcur. iFrame "Htn Hps Hcs HE Hf".
      + rewrite /sh_pend_at /sh_deed_at. iLeft. iExists cs, s, v.
        iFrame "Hd Hty Hpin Hcs". iPureIntro. exists a.
        split_and!; [ exact Hlen | exact Hpos | exact (proj1 Hapr)
                    | exact Hpr | exact Hc ].
    - (* a byte before the prompt: [a] is filed, deed DONE *)
      cbn [lm_blkcs].
      iDestruct (cs_lb_prefix_len v (cs ++ [a]) cs'
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
        cbn [lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
        rewrite /gwc_line /gwc_post. cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at.
        iRight. iLeft. iExists a.
        iSplitR; [ iPureIntro; by apply faprs_lm | ]. iLeft.
        iExists ps, cs, s0, P.
        rewrite -(fabs_lm s0 cs I a) Hi. cbn [lm_blkcs].
        iFrame "Htn Hps Hcs HE Hf".
        iSplit; iPureIntro; [ by rewrite -wr_blk_t_f_lm | reflexivity ].
      + rewrite /sh_done_at /sh_deed_at. iLeft. iExists (cs ++ [a]), s, v.
        iFrame "Hd Hty Hpin Hcs". iPureIntro.
        exact (done_tie_snoc cs a s0 I _ Hlen Hpos Hc).
  Qed.

  (* ...and at the record's own block ([lk_post], a state-free alternative):
     the instance. *)
  Lemma Wcf0_of_post_alt (I : list (bv 8)) (a : nat) (v v' : era_pins)
      (cs' : list nat) (s : dst) :
    fapr I a ->
    length cs' = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    dst_content s
      = fsm (UCatOut.cat_st cs' s0 I) (fline I) (ralt_dec a) ->
    lk_pin FI (S gen_id) v -∗ lk_post FI (S gen_id) v I a -∗
    fown r s -∗ f_typed (fgn_cl g) s -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs' -∗
    Wcf I 0%nat.
  Proof using .
    intros Hapr Hlen Hpos Hc. iIntros "#Hpin Hblk Hd #Hty #Hpin' #Hcs'".
    iApply (Wcf0_of_posts_alt I a v v' cs' s (fapr_faprs I a Hapr) Hlen Hpos Hc
              with "Hpin [Hblk] Hd Hty Hpin' Hcs'").
    rewrite /lk_post. cbn [lk_blk lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    iApply (gwc_post_of_blk file_lm (file_params_at g s0) (S gen_id) v I a
              ltac:(by apply fapr_lm) with "Hblk").
  Qed.

  (* ---- THE LOOP'S LAWS AT [Wcf] / [Wbf] ---- *)

  (* [UkShFork]'s [Hwbl]: a fork that failed re-enters at the boundary --
     the deed pending at the line's silent alternative ((ii) of the ruling) *)
  Lemma Hwbl_f (I : list (bv 8)) : ⊢ Wcf I 3%nat -∗ Wcf I 0%nat.
  Proof using .
    rewrite Wcf_S3 Wcf_0. iIntros "[Hc Hp]".
    rewrite {1}/sh_pre_at /sh_deed_at. iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iLeft. iSplitL "Hc";
        [ iApply (Hwbl I with "Hc") | iApply (sh_deed_taint with "HT") ]. }
    rewrite /FileLinkInst.file_Wcl_at.
    iDestruct (lk_lcred_blk_lend FI (S gen_id) I with "Hc") as (v) "[#Hpin Hl]".
    cbn [lk_pin lk_lend FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. rewrite /gwc_lend.
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iLeft. iSplitL "";
        [ iApply (Hcltaint I 0%nat v with "Hpin HT")
        | iApply (sh_deed_taint with "HT") ]. }
    iDestruct "Hl" as (ps cs sw P) "(%Hw & Hcur)".
    iEval (rewrite /gcur; cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at) in "Hcur".
    iDestruct "Hcur" as "(Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
    subst sw. rewrite -wr_blk_t_f_lm in Hw.
    iRight. iSplitL "Htn".
    { iApply (Wcl3_close I v ps cs P Hw with "Hpin [Htn]").
      rewrite /FileLinksLine.fcur. iFrame "Htn Hps Hcs HE Hf". }
    rewrite /sh_pend_at /sh_deed_at. iLeft.
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    iExists cs', s, v'. iFrame "Hd Hty Hpin' Hcs'". iPureIntro.
    destruct Hw as [(_ & _ & Hn & _) _].
    exists (fnoc_of (fline I)).
    exact (pend_tie_of_pre cs' s0 I _ ltac:(lia) Htie).
  Qed.

  (* [UInitBoot]'s [Hsh_wbwc]: the banner-owed credential is a boundary
     one, at the DONE arm *)
  Lemma Hwbwc_f (I : list (bv 8)) : ⊢ Wbf I -∗ Wcf I 0%nat.
  Proof using .
    rewrite /Wbf Wcf_0. iIntros "[Hb Hd]". iLeft. iFrame "Hd".
    iApply (Hwbwc I with "Hb").
  Qed.

  (* the reader's pieces carry the typed lines' witness in their residue
     ([FileLinksAt.fwc_rresw_at]); it is persistent, so it is read and the
     pieces go back whole *)
  Lemma mid_flw (I : list (bv 8)) :
    UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp I -∗
    UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp I
    ∗ FileLinksLine.flw g I.
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hu & Hua & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iAssert (FileLinksLine.flw g I) as "#Hw".
    { cbn [lk_rres FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
      rewrite /FileLinksAt.fwc_rresw_at. iDestruct "Hres" as "[_ $]". }
    iSplitL; [ | iExact "Hw" ]. iFrame "Hu Hua Hrd". iExists v.
    iSplitR; [ iExact "Hpin" | ]. iSplitL "Hdl"; [ iExact "Hdl" | ].
    iSplitR; [ iExact "HE" | iExact "Hres" ].
  Qed.

  (* [UkSh]'s [Hwc] at the family -- INIT-FILE's conjunct 5: the read that
     completed a line moves the credential from 2 at the old input to the
     lend at the new one, and the deed from DONE to PRE ((i) of the ruling) *)
  (* ...AS A FANCY UPDATE AT [top] (design SS4.3k): the FILE era needs
     none of it, so the whole of the landed proof sits under one
     [iModIntro]. *)
  Lemma Hwc_f : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) -∗ Wcf I 2%nat ={⊤}=∗
      UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl])
      ∗ Wcf (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros I l Hl. rewrite Wcf_2 Wcf_S3. iIntros "Hmid [Hc Hd]". iModIntro.
    iDestruct (mid_flw (I ++ l ++ [wl_nl]) with "Hmid") as "[Hmid #Hw]".
    iDestruct (Wcl2_rest I with "Hc") as "[Hc Hr]".
    iDestruct (Hwc I l Hl with "Hmid Hc") as "[$ $]".
    iDestruct "Hr" as "[%Hr | #HT]"; last (iApply (sh_pre_taint with "HT")).
    iApply (sh_pre_of_done I l Hr Hl with "[] Hd"). iLeft. iExact "Hw".
  Qed.

  (* the seam's two read-backs at the family ([UShLineAtHold.
     ush_posb_of_lend_L] takes [Wc]/[Wb] abstract at exactly these) *)
  Lemma Wcf_inp : UShLine.ush_wc_inp (fgn_echo g) T Wcf.
  Proof using .
    intros I p. iIntros "Hc". destruct p as [| [| [| p]]].
    - rewrite Wcf_0. iDestruct "Hc" as "[[Hc Hd] | [Hc Hd]]".
      + iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 0%nat with "Hc")
          as "[Hc $]". iLeft. iFrame "Hc Hd".
      + iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 3%nat with "Hc")
          as "[Hc $]". iRight. iFrame "Hc Hd".
    - rewrite Wcf_1. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 1%nat with "Hc")
        as "[Hc $]". iFrame "Hc Hd".
    - rewrite Wcf_2. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 2%nat with "Hc")
        as "[Hc $]". iFrame "Hc Hd".
    - rewrite Wcf_S3. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (FileLinksAtInp.file_wc_inp_at g s0 I 3%nat with "Hc")
        as "[Hc $]". iFrame "Hc Hd".
  Qed.

  Lemma Wbf_inp : UShLine.ush_wb_inp (fgn_echo g) T Wbf.
  Proof using .
    exact (UShLineHold.ush_wb_inp_hold (fgn_echo g) T Wbl DONE
             (FileLinksAtInp.file_wb_inp_at g s0)).
  Qed.

  (* =================================================================== *)
  (*  S3  THE PROMPT LINK, AT THE DEED (design SS4.2; CAT-ENTRY ruling (b)) *)
  (*                                                                     *)
  (*  sh's prompt byte is the round's BLOCK-FIRST byte exactly when the    *)
  (*  child printed nothing, and then it FILES the round's alternative:    *)
  (*  [RFRan sel] after an [echo ... > f] child (with [sel] read off the   *)
  (*  child's exit payload, i.e. off the deed's own content), [RCRan]      *)
  (*  after a [cat f] whose deed is empty.  Otherwise the child opened     *)
  (*  the block and the prompt is an ordinary byte.                       *)
  (*                                                                     *)
  (*  WHAT THIS LEMMA IS: the instantiation of                            *)
  (*  [FileLinks.file_write_link_blk] whose [a] is computed from the deed. *)
  (*  It is stated here because it is the ONE place where the claim and    *)
  (*  the stage meet, and they meet PURELY.                                *)
  (* =================================================================== *)
  (* THE STATEMENT AT RULING HOLD-POS: the deed is at the PEND tie -- its
     alternative [a] decided and silent -- and the stage is the block's
     ([wr_blk_f]); the byte is the prompt's '$' and the console files [a].
     PROVED: it is [FileLinks.file_write_link_blk] verbatim, with the
     block's first byte read off the tie's [cont … = u_prompt]. *)
  Lemma sh_prompt_alt_of_deed (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (ps0 cs0 : list nat) (I0 : list (bv 8)) (s : dst)
      (Φ : iProp Σ) :
    wr_blk_f ps0 cs0 s0 I0 P ->
    pend_tie_at cs0 s0 I0 (dst_content s) a ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ f0_lb vf s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k (u_prompt !!! 0%nat) Φ.
  Proof using Hcons.
    intros Hw (Hlen & Hpos & Hok & Hcont & _).
    pose proof (wr_blk_nonnil_f ps0 cs0 s0 I0 P Hw) as Hne.
    destruct Hw as (Hpin & Hr & Hn & HP).
    assert (Hhead :
      cont (fstate_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
           (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
        !! 0%nat = Some (u_prompt !!! 0%nat)).
    { rewrite /fline /UCatOut.cat_st in Hcont. rewrite Hcont.
      exact EchoLinks.wr_prompt_head. }
    iIntros "#Hpin #Hfp Ht #Hps #Hcs #HE #Hf HΦ".
    iApply (FileLinks.file_write_link_blk g Hcons k v vf P a
              (u_prompt !!! 0%nat) ps0 cs0 s0 I0 Φ Hne Hr ltac:(lia) Hpin HP
              Hok Hhead with "Hpin Hfp Ht Hps Hcs HE Hf HΦ").
  Qed.

  (* =================================================================== *)
  (*  S3'  THE PROMPT LAW AT THE FAMILY (RULING HOLD-POS (iv))            *)
  (*                                                                     *)
  (*  NOT A FRAME.  On the DONE arm it is the record's own law with the    *)
  (*  deed framed ([UShPanicHold.sh_prompt_law_hold]).  On the PEND arm    *)
  (*  the '$' is the round's block-first byte and FILES the deed's         *)
  (*  alternative ([sh_prompt_alt_of_deed]), landing the deed at DONE and  *)
  (*  the console at the space owed; the ' ' is the record's step.  The    *)
  (*  two-byte write's mould is [UShPanic.ksh_w_of_link_prompt_fam].      *)
  (* =================================================================== *)

  (* the write call at a disjunctive precondition: each arm its own walk *)
  Local Lemma ksh_w_or (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (St A B Co : iProp Σ) :
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ A) Co -∗
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ B) Co -∗
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ (A ∨ B)) Co.
  Proof using .
    iIntros "HA HB" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hs [HA' | HB']] Hrun Hcont".
    - iApply ("HA" $! h m avail with "[%] [%] [%] Hcode [$Hs $HA'] Hrun Hcont");
        assumption.
    - iApply ("HB" $! h m avail with "[%] [%] [%] Hcode [$Hs $HB'] Hrun Hcont");
        assumption.
  Qed.

  (* a tainted round writes its prompt on the record's own law, DONE := T *)
  Local Lemma ksh_w_prompt_taint (N : uk_names Σ) (I : list (bv 8))
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
    T -∗ FileLinks.file_links g -∗ UCodeShK.shk_rodata (ukn_t N) -∗
    UkSh.ksh_w (PS := uprogSG_free) N (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd N) l ∗ Wcl I 0%nat)
      (UserFd.ustd (ukn_fd N) l ∗ (Wcl I 2%nat ∗ DONE I)).
  Proof using .
    intros Hl2. iIntros "#HT #Hlk #Hro".
    iApply (UShPanicHold.ksh_w_mono (PS := uprogSG_free) N _ _ _
              (UserFd.ustd (ukn_fd N) l ∗ lk_lcred FI (S gen_id) I 0%nat)%I _
              (UserFd.ustd (ukn_fd N) l ∗ lk_lcred FI (S gen_id) I 2%nat)%I
              with "[] []").
    { iIntros "[Hs Hc]". iFrame "Hs". rewrite /FileLinkInst.file_Wcl_at.
      iExact "Hc". }
    { iIntros "[Hs Hc]". iFrame "Hs". iSplitL "Hc";
        [ rewrite /FileLinkInst.file_Wcl_at; iExact "Hc"
        | iApply (sh_deed_taint with "HT") ]. }
    iApply (UShPanic.ksh_w_of_link_lcred_at (PS := uprogSG_free) FI N I l rb
              Hl2 with "[] Hro").
    cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk".
  Qed.

  (* THE PEND ARM'S STEP FAMILY: position 0 is the round's cursor with the
     deed beside it; positions 1 and 2 are the record's settled shapes with
     the deed DONE. *)
  Local Definition pfam (v : era_pins) (P : nat) (I : list (bv 8)) (s : dst)
      (p : nat) : iProp Σ :=
    match p with
    | O => (turn v P ∗ fown r s)%I
    | S p' => (lk_lpr FI (S gen_id) v I (S p') ∗ DONE I)%I
    end.

  Local Lemma pfam_step (v : era_pins) (vf : file_era) (ps cs : list nat)
      (P a : nat) (I : list (bv 8)) (s : dst) :
    wr_blk_t_f ps cs s0 I P ->
    pend_tie_at cs s0 I (dst_content s) a ->
    FileLinks.file_links g -∗
    era_pin (fgn_echo g) (S gen_id) v -∗ file_era_pin g (S gen_id) vf -∗
    ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗ f0_lb vf s0 -∗
    f_typed (fgn_cl g) s -∗
    UShPanic.prompt_step (pfam v P I s).
  Proof using Hcons.
    intros Hw Htie. pose proof Htie as (Hlen & Hpos & Hok & Hcont & Hc).
    pose proof (cont_prompt_nopanic _ _ _ Hcont) as Hnp.
    pose proof Hw as [Hwb Ht].
    iIntros "#Hlk #Hpin #Hvf #Hps #Hcs #HE #Hf0 #Hty".
    rewrite /UShPanic.prompt_step. iIntros "!>" (p b Φ) "%Hb %Hp Hc HΦ".
    destruct p as [| [| p]]; [ | | exfalso; lia ].
    - (* '$': the block-first byte files the deed's alternative *)
      assert (Hb0 : b = u_prompt !!! 0%nat)
        by (rewrite EchoLinks.wr_prompt_head in Hb; by injection Hb).
      subst b. cbn [pfam]. iDestruct "Hc" as "[Htn Hd]".
      iApply (sh_prompt_alt_of_deed (S gen_id) v vf P a ps cs I s Φ Hwb Htie
                with "Hpin Hvf Htn Hps Hcs HE Hf0 [HΦ Hd]").
      iIntros "Hres". iApply "HΦ". cbn [pfam].
      iDestruct "Hres" as "[(Htn' & _ & #Hcs' & _ & _) | #HT]"; last first.
      { iSplitL "";
          [ iApply (lk_lpr_taint FI (S gen_id) v I 1%nat with "HT")
          | iApply (sh_deed_taint with "HT") ]. }
      iSplitL "Htn'".
      + (* the space owed, at the stage the '$' left *)
        rewrite (lk_lpr_1 FI). cbn [lk_sp_t FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
        rewrite /gwc_sp_t /gcur. cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at.
        iLeft. iExists ps, (cs ++ [a]), s0, (S P).
        iSplitR.
        { iPureIntro. rewrite -wr_sp_t_f_lm. split;
            [ exact (wr_blk_dollar_at_f ps cs s0 I P a Hwb Hnp Hcont)
            | exact (wr_tail_snoc_f ps cs a Hnp Ht) ]. }
        iFrame "Htn' Hps Hcs' HE". iSplitL; [ | by iPureIntro ].
        rewrite /FileLinksLine.f0w. iSplitR; [ by iPureIntro | ].
        iExists vf. iFrame "Hvf Hf0".
      + (* the deed, DONE: the filed alternative is the deed's own *)
        rewrite /sh_done_at /sh_deed_at. iLeft. iExists (cs ++ [a]), s, v.
        iFrame "Hd Hty Hpin Hcs'". iPureIntro.
        exact (done_tie_of_pend cs s0 I _ a Htie).
    - (* ' ': the record's own step, the deed framed *)
      cbn [pfam]. iDestruct "Hc" as "[Hc Hd]".
      iApply (lk_lpr_step FI (S gen_id) v I 1%nat b Φ Hb Hp
                with "Hpin Hlk Hc [HΦ Hd]").
      iIntros "Hc". iApply "HΦ". cbn [pfam]. iFrame "Hc Hd".
  Qed.

  (* the PEND arm of the prompt call *)
  Local Lemma ksh_w_prompt_pend (N : uk_names Σ) (I : list (bv 8))
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
    FileLinks.file_links g -∗ UCodeShK.shk_rodata (ukn_t N) -∗
    UkSh.ksh_w (PS := uprogSG_free) N (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd N) l ∗ (Wcl I 3%nat ∗ PEND I))
      (UserFd.ustd (ukn_fd N) l ∗ (Wcl I 2%nat ∗ DONE I)).
  Proof using Hcons.
    intros Hl2. iIntros "#Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd [Hc Hp]] Hrun Hcont".
    (* a tainted deed: the record's law, DONE := T *)
    rewrite {1}/sh_pend_at /sh_deed_at.
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iDestruct (Hwbl I with "Hc") as "Hc".
      iApply (ksh_w_prompt_taint N I l rb Hl2
                with "HT Hlk Hro [%] [%] [%] Hcode [$Hstd $Hc] Hrun Hcont");
        assumption. }
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    destruct Htie as (a & Htie). pose proof Htie as (Hlen & Hpos & Hok & Hcont & Hc).
    (* the console: the block owed at the round's stage, or the taint *)
    rewrite /FileLinkInst.file_Wcl_at.
    iDestruct (lk_lcred_blk_lend FI (S gen_id) I with "Hc") as (v) "[#Hpin Hl]".
    cbn [lk_pin lk_lend FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. rewrite /gwc_lend.
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iDestruct (Hcltaint I 0%nat v with "Hpin HT") as "Hc0".
      iApply (ksh_w_prompt_taint N I l rb Hl2
                with "HT Hlk Hro [%] [%] [%] Hcode [$Hstd $Hc0] Hrun Hcont");
        assumption. }
    iDestruct "Hl" as (ps cs sw P) "(%Hw & Hcur)".
    iEval (rewrite /gcur; cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at) in "Hcur".
    iDestruct "Hcur" as "(Htn & #Hps & #Hcs & #HE & #[Hf0 %Hs])".
    subst sw. rewrite -wr_blk_t_f_lm in Hw.
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    pose proof Hw as [(_ & _ & Hn & _) _].
    iDestruct (cs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    rewrite /FileLinksLine.f0w. iDestruct "Hf0" as "[%Hk Hf0]".
    iDestruct "Hf0" as (vf) "[#Hvf #Hf0lb]".
    (* the two bytes as one step family, then the call *)
    iPoseProof (pfam_step v vf ps cs P a I s Hw Htie
                  with "Hlk Hpin Hvf Hps Hcs HE Hf0lb Hty") as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) N
              (pfam v P I s) l rb Hl2
              with "Hst Hro [%] [%] [%] Hcode [$Hstd Htn Hd] Hrun [Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | cbn [pfam]; iFrame "Htn Hd" | ].
    iIntros (h' ret) "[Hstd Hc] Hrun".
    iApply ("Hcont" $! h' ret with "[$Hstd Hc] Hrun").
    cbn [pfam]. iDestruct "Hc" as "[Hc Hd]". iFrame "Hd".
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred. iExists v.
    cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iFrame "Hpin Hc".
  Qed.

  (* THE PROMPT LAW, at the family *)
  Lemma sh_prompt_law_file :
    ⊢ FileLinks.file_links g -∗
      UShKernel.sh_prompt_law (PS := uprogSG_free) Wcf.
  Proof using Hcons.
    iIntros "#Hlk".
    iPoseProof (UShPanic.sh_prompt_law_holds_line_at (PS := uprogSG_free) FI
                  with "[]") as "#Hpl".
    { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk". }
    iPoseProof (UShPanicHold.sh_prompt_law_hold (PS := uprogSG_free) Wcl DONE
                  with "Hpl") as "#Hpld".
    rewrite /UShKernel.sh_prompt_law. iIntros "!>" (N) "#Hro".
    iDestruct ("Hpld" $! N with "Hro") as "#Hd". rewrite /UkSh.ush_prompt_law.
    iDestruct "Hd" as "#[Hdopen Hdclosed]". iModIntro. iSplitL "".
    - iIntros (I l) "%Hfd". pose proof Hfd as [rb Hl2].
      rewrite Wcf_0 Wcf_2.
      iApply (ksh_w_or N _ _ _ (UserFd.ustd (ukn_fd N) l)
                (Wcl I 0%nat ∗ DONE I)%I (Wcl I 3%nat ∗ PEND I)%I
                with "[] []").
      + iApply ("Hdopen" $! I l). by iPureIntro.
      + iApply (ksh_w_prompt_pend N I l rb Hl2 with "Hlk Hro").
    - iIntros (l) "%Hcl". iApply ("Hdclosed" $! l). by iPureIntro.
  Qed.

  (* =================================================================== *)
  (*  S4  THE LINE READ, AT [FileOut.ftag]                                *)
  (*                                                                     *)
  (*  [UkSh.ush_tag_law] reads the era's line list off the machine's rx    *)
  (*  tag; at this application the tag is [ftag], whose third conjunct is  *)
  (*  [AppFile.fl_lb] -- the lower bound the child's create step needs     *)
  (*  ([AppFile.f_typed_some] wants [ws ∈ ls]).  This is the file twin of  *)
  (*  [UInitBoot]'s [Htg], and it is where sh's fork lend gets the line.   *)
  (* =================================================================== *)
  (*  ===== A SHAPE THAT DOES NOT COMPILE AS STATED ==================== *)
  (*                                                                     *)
  (*  [UkSh.ush_tag_law T] is [box (forall h, riscv_rx_tag h -* pure      *)
  (*  (EchoDisc.disc h) or T)] -- the ECHO discipline -- and the file     *)
  (*  era CANNOT supply it: [FileOut.ftag]'s second conjunct is           *)
  (*  [pure (FileDisc.disc_f h) or file_taint], and [disc_f h] does NOT   *)
  (*  imply [disc h] (lane STAGE's own ruling: a [cat] line is not an     *)
  (*  echo line).  So what this file proves is the FILE tag law, and      *)
  (*  [UkSh.ush_tag_law]'s [disc] must become a PARAMETER                 *)
  (*  [D : list mobs -> Prop] before [UInitSh.sh_pay_of_parts] can be     *)
  (*  applied at this era.  That is a NEW obligation; it surfaces in K3,  *)
  (*  not here, because [UkSh.ush_rest_l] does not mention the tag.       *)
  (*  PROVED (the program stream): the era's tag IS [FileOut.ftag] and its *)
  (*  second conjunct is this disjunction, so the law is the projection.    *)
  Lemma sh_tag_law_file :
    ⊢ □ (∀ h : list mobs,
           riscv_rx_tag h -∗ ⌜FileDisc.disc_f h⌝ ∨ T).
  Proof using Htag.
    rewrite Htag. iIntros "!>" (h) "Ht".
    rewrite /FileOut.ftag. iDestruct "Ht" as "(_ & Hd & _)". iExact "Hd".
  Qed.

  (* =================================================================== *)
  (*  S5  THE THREE-WAY CHILD DISPATCH                                    *)
  (*                                                                     *)
  (*  sh's child branches on the parsed line's shape -- a PURE case on     *)
  (*  [FileDisc]'s [uline_of] of the buffer, which sh's own tag law ties   *)
  (*  to the typed line (design SS5.4).  Three shapes, three entries:       *)
  (*                                                                     *)
  (*    LEcho      [UkShEcho.wp_kshm_child_echo_holds] at the FILE links  *)
  (*               -- echo at the console, [UEchoOut]'s entry.            *)
  (*    LEchoF     [UkShRedirSeam.wp_kshm_child_alloc_redir], whose open   *)
  (*               is a CALL PREMISE instantiated by [UkFileOpen]'s deed   *)
  (*               create corollary, then [exec /echo] at K1's entry.      *)
  (*    LCat       cat's tree-route entry at a deed FRACTION.              *)
  (* =================================================================== *)

  (* ---- the redirect child's open receipt, on both arms ---- *)
  (* [UkShRedirAns.ush_open_ans2]'s two payload slots, at this claim.  [K]
     is the fd arm's -- the descriptor's TYPE, `f` present and EMPTY at it,
     AND the program's own half of the offset shadow at ZERO, which is what
     lane OFF-LINK's publish hands out and what K1's entry asks for.  [Kf]
     is the [-1] arm's and is NOT [emp]: the create may have fired before
     [filealloc] failed. *)
  (* RESTATED BY THE KERNEL STREAM at the kernel's own payload.  It was
     [∃ i γo om, ⌜ty = FdInode i γo om⌝ ∗ fown r (Some (i, [])) ∗ uoff γo 0]:
     the mode existential is right, but the TAINT ARM was missing, and the
     open leaf cannot drop it -- a tainted claim promises nothing about the
     file system and cannot refute the kernel's [FdDevice] arm
     ([FileOpen]'s note at [file_open_fd_K]).  [UkFileOpen.redir_K OffHeld]
     IS that statement, and it is what
     [UkFileOpen.wp_uk_ecall_open_create_deed_d] at [OffHeld] hands back. *)
  Definition redir_K (ty : fdtype) : iProp Σ :=
    UkFileOpen.redir_K OffHeld (fgn_cl g) r ty.

  (* ...AND THE [-1] ARM'S, WITH THE TAINT (the PROGRAM STREAM): the
     kernel's own payload is [FileOpen.file_open_pay], whose third arm is
     the era's taint -- a failed open at a tainted application hands back
     no deed, and a [Kf] without that arm cannot be produced. *)
  Definition redir_Kf (s : dst) : iProp Σ :=
    (fown r s ∨ (⌜s = None⌝ ∗ ∃ i : Z, fown r (Some (i, []))) ∨ T)%I.

  (* [fab] at an admissible, state-free alternative IS its continuation
     (the guard in [FileHooks.fab] discharged once, so no consumer
     rewrites under a [decide]) *)
  Local Lemma fab_of_apr (I : list (bv 8)) (a : nat) :
    ralt_ok (fline I) (ralt_dec a) /\ fstate_free (ralt_dec a) = true ->
    fab I a = cont None (fline I) (ralt_dec a).
  Proof using . intro H. rewrite /fab. by case_decide. Qed.

  (* ---- THE REDIRECT CHILD'S THREE PRINTING-OR-SILENT EXITS, each closing
          at the loop's position-0 credential.  The entry facts are PRE's
          own ([pre_tie]: the deed's choice list is one short of the
          input's lines, and the content is the round's entry state); what
          differs is what the child did to `f` and what it printed. ---- *)

  (* echo RAN: it prints nothing on the console (fd 1 is `f`), so the block
     is still owed whole and the deed is PEND at [RFRan sel] -- whose
     continuation is the bare prompt by computation.  [sel] is whichever
     chunks landed (design SS0, limit 1), read off the write credential. *)
  Lemma redir_ran_exit (I : list (bv 8)) (ws : wordline) (i : Z)
      (sel : list nat) (v' : era_pins) (cs : list nat) :
    fline I = LEchoF ws ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    Wcl I 3%nat -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs -∗
    FileWrite.file_wq (fgn_cl g) r i ws sel
      (length (subseq (echo_chunks ws) sel)) -∗
    Wcf I 0%nat.
  Proof using .
    intros Hfl Hlen Hpos. iIntros "Hc #Hpin #Hcs Hq".
    rewrite /FileWrite.file_wq. iDestruct "Hq" as "[Hq | #HT]"; last first.
    { iApply (Wcf_taint I 0%nat v' with "Hpin HT"). }
    iDestruct "Hq" as (ls) "(Hd & _ & %Hok & %Hsel & #Hlb & %Hin)".
    rewrite Wcf_0. iRight. iFrame "Hc".
    rewrite /sh_pend_at /sh_deed_at. iLeft.
    iExists cs, (Some (i, subseq (echo_chunks ws) sel)), v'.
    iFrame "Hd Hpin Hcs". iSplit.
    - iPureIntro. exists (ralt_enc (RFRan sel)).
      rewrite /pend_tie_at ralt_dec_enc Hfl.
      split_and!; [ exact Hlen | exact Hpos | exact Hsel | reflexivity
                  | reflexivity ].
    - rewrite /f_typed. iExists ls. iFrame "Hlb". iPureIntro.
      exists ws, sel. split_and!; [ exact Hin | exact Hok | exact Hsel
                                  | reflexivity ].
  Qed.

  (* the exec FAILED after the open truncated: the diagnostic is written,
     `f` is empty *)
  Lemma redir_execfail_exit (I : list (bv 8)) (ws : wordline) (i : Z)
      (v v' : era_pins) (cs : list nat) :
    fline I = LEchoF ws ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ralt_enc RFExec) -∗
    fown r (Some (i, [])) -∗ f_typed (fgn_cl g) (Some (i, [])) -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hfl Hlen Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
    iApply (Wcf0_of_post_alt I (ralt_enc RFExec) v v' cs (Some (i, []))
              with "Hp Hblk Hd Hty Hpin' Hcs");
      [ rewrite /fapr ralt_dec_enc Hfl; split_and!; [ exact Logic.I | | ];
        reflexivity
      | exact Hlen | exact Hpos
      | rewrite ralt_dec_enc Hfl; reflexivity ].
  Qed.

  (* the open FAILED: `f` is as the round found it ([RFOpenU]), or the
     create had fired before the failure and left it empty ([RFOpenM], at
     an absent `f` only -- [redir_Kf]'s second arm says so).  TWO lemmas
     and not one over [redir_Kf]: which arm the call returned is known
     BEFORE the diagnostic is written, and the diagnostic's law is run at
     the matching alternative, so its end state holds ONE block. *)
  Lemma redir_openfail_exit_u (I : list (bv 8)) (ws : wordline) (s : dst)
      (v v' : era_pins) (cs : list nat) :
    fline I = LEchoF ws ->
    pre_tie cs s0 I (dst_content s) -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ralt_enc RFOpenU) -∗
    fown r s -∗ f_typed (fgn_cl g) s -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hfl [Hlen Hc] Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
    iApply (Wcf0_of_post_alt I (ralt_enc RFOpenU) v v' cs s
              with "Hp Hblk Hd Hty Hpin' Hcs");
      [ rewrite /fapr ralt_dec_enc Hfl; split_and!; [ exact Logic.I | | ];
        reflexivity
      | exact Hlen | exact Hpos
      | rewrite ralt_dec_enc Hfl; exact Hc ].
  Qed.

  Lemma redir_openfail_exit_m (I : list (bv 8)) (ws : wordline) (i : Z)
      (v v' : era_pins) (cs : list nat) :
    fline I = LEchoF ws ->
    pre_tie cs s0 I None -> (0 < nlines I)%nat ->
    lk_pin FI (S gen_id) v -∗
    lk_post FI (S gen_id) v I (ralt_enc RFOpenM) -∗
    fown r (Some (i, [])) -∗ f_typed (fgn_cl g) (Some (i, [])) -∗
    era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs -∗
    Wcf I 0%nat.
  Proof using .
    intros Hfl [Hlen Hc] Hpos. iIntros "#Hp Hblk Hd #Hty #Hpin' #Hcs".
    iApply (Wcf0_of_post_alt I (ralt_enc RFOpenM) v v' cs (Some (i, []))
              with "Hp Hblk Hd Hty Hpin' Hcs");
      [ rewrite /fapr ralt_dec_enc Hfl; split_and!; [ exact Logic.I | | ];
        reflexivity
      | exact Hlen | exact Hpos
      | rewrite ralt_dec_enc Hfl -Hc; reflexivity ].
  Qed.

  (* ---- WHAT THE OPEN'S RECEIPT SAYS ABOUT THE INODE (the PROGRAM
          STREAM, item (3)'s first premise).  K1's entry takes four
          inequalities -- `f`'s inode is not /init's, sh's, /echo's or
          cat's -- and they are the CLAIM's fact and not the open's: the
          deed pins `f`'s row, the image inodes' rows are pinned by
          [FileFsPure.file_fs_pure], and the contents differ by LENGTH.
          [AppFileCons.file_deed_inum_acc] is that reading; this is the one
          invariant opening that turns the receipt into it. ---- *)
  Lemma redir_K_inum (ty : fdtype) (E : coPset) :
    ↑appN ⊆ E ->
    app_inv fsc_fs -∗ redir_K ty ={E}=∗
      redir_K ty ∗
      ((∃ (i : Z) (γo : gname),
          ⌜ty = FdInode i γo OffHeld⌝
          ∗ ⌜i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO
             /\ i <> CAT_INO⌝)
       ∨ T).
  Proof using Heq.
    intros HE. iIntros "#Hinv HK".
    rewrite /redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
    iDestruct "HK" as "[HK | #HT]"; last first.
    { iModIntro. iSplitR; [ by iRight | by iRight ]. }
    iDestruct "HK" as (i γo) "(%Hty & [Hd Htk] & Hpub)".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [ exact HE | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hka & Hp & >%Hdom & #Hx)".
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iDestruct (AppFileCons.file_deed_inum_acc (fgn_cl g) r _ i []
                 ltac:(cbn [length]; rewrite /EchoDisc.line_max; lia)
                 with "Hd Hp") as "(Hp & Hd & Hres)".
    iMod ("Hclose" with "[Hka Hp Hx]") as "_".
    { iNext. rewrite /app_body. iExists I0. iFrame "Hka Hx".
      iSplitL; [ | by iPureIntro ].
      rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp". }
    iModIntro. iSplitL "Hd Htk Hpub".
    { iLeft. iExists i, γo. iFrame "Hpub Hd Htk". by iPureIntro. }
    iDestruct "Hres" as "[%Hne | #Ht]"; [ | by iRight ].
    iLeft. iExists i, γo. iSplitR; by iPureIntro.
  Qed.

  (* ---- NOT A HYPOTHESIS ANY MORE (the PROGRAM STREAM): sh's open STUB,
          walked into the kernel's create corollary at [OffHeld].

          THE STATEMENT HAD TO BE FIXED FIRST, and that is the whole of
          what was wrong with it: [ush_open_call2] was handed [a0 = file],
          an ADDRESS, and NOTHING about the bytes there or about the cwd,
          while the kernel resolves a PATH -- so as stated the hypothesis
          was not provable by anyone, and assuming it assumed something
          false.  It now takes the name as the image the ecall reads, the
          three path facts, and the ledger's own answer (fd 1 is the lowest
          closed slot, which is true of the redirect child's table because
          it closed fd 1 before calling).  Every one of them is a fact the
          CALLER has: sh's cwd is the root for the whole era, and the
          line's bytes are in its own buffer at the lexed offset.

          The walk is usys.S's three-instruction stub, [UShConsK.
          sh_open_console_leaf_holds]'s mould with the file leaf in the
          middle: [c.li a7,15] at 0xcc6, [ecall] at 0xcc8, [c.jr ra] at
          0xccc. ---- *)
  (* ---- NOT A HYPOTHESIS ANY MORE (the PROGRAM STREAM): sh's open STUB,
          walked into the kernel's create corollary at [OffHeld].

          THE STATEMENT HAD TO BE FIXED FIRST: [ush_open_call2] was handed
          [a0 = file], an ADDRESS, and NOTHING about the bytes there or
          about the cwd, while the kernel resolves a PATH -- so as stated
          nobody could prove it.  It now takes the name as the image the
          ecall reads, the three path facts, and the ledger's own answer
          (fd 1 is the lowest closed slot, true of the redirect child's
          table because it closed fd 1 before calling).  Every one is a
          fact the CALLER has: sh's cwd is the root for the whole era and
          the line's bytes are in its own buffer at the lexed offset.

          AND THE DEPOSIT INSTANCE HAD TO BE NAMED: [UkFileOpen]'s create
          corollary was at the AMBIENT [uprogSG_gen] while sh's redirect
          child runs at [uprogSG_free], whose record shares neither field
          -- so it now takes the instance per lemma, and this walk names
          [uprogSG_free].

          The walk itself is usys.S's three-instruction stub, [UShConsK.
          sh_open_console_leaf_holds]'s mould with the file leaf in the
          middle: [c.li a7,15] at 0xcc6, [ecall] at 0xcc8, [c.jr ra] at
          0xccc. ---- *)
  Local Lemma sh_open_stub_pc : User.ShSyms.open = 0xcc6.
  Proof using .
    destruct UCodeShK.shk_syms_pins as (_&_&_&_&_&H&_&_&_&_). exact H.
  Qed.

  Local Lemma ucallee_saved_a0a7 (m : regfile) (rv : mword 64) :
    ucallee_saved m
      (<[Regidx (mword_of_int 10 : mword 5) := rv]>
         (<[Regidx (mword_of_int 17 : mword 5)
            := (mword_of_int 15 : mword 64)]> m)).
  Proof using .
    intros rr Hrr.
    destruct (decide (rr = (mword_of_int 10 : mword 5))) as [-> | Hne0].
    { exfalso. vm_compute in Hrr. discriminate Hrr. }
    destruct (decide (rr = (mword_of_int 17 : mword 5))) as [-> | Hne7].
    { exfalso. vm_compute in Hrr. discriminate Hrr. }
    rewrite (upd_ne _ (Regidx (mword_of_int 10 : mword 5)) (Regidx rr) rv
               ltac:(intro He; apply Hne0; injection He as He'; by rewrite He')).
    rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5)) (Regidx rr)
               (mword_of_int 15 : mword 64)
               ltac:(intro He; apply Hne7; injection He as He'; by rewrite He')).
    reflexivity.
  Qed.

  (* ...AND THE DEED IS HANDED AT THE CALL (stretch 9): the call resource
     is built from PERSISTENT facts alone, so the child can hold it across
     the parse with its lend whole, and the deed flows lend -> call ->
     receipt ([UkShRedirAns.ush_open_call2]'s [Dd]). *)
  Lemma Hopen_hand (N : uk_names Σ) (file : Z) (l : list fdstate)
      (ls : list wordline) (ws : wordline) (jo : option Z) :
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv fsc_fs -∗ file_cons_cred (fgn_cl g) r jo -∗ fl_lb (fgn_cl g) ls -∗
    (* ...AND THE CWD'S CAMERA IS PINNED TOO (the PROGRAM STREAM's rule,
       one class further out than the deposit): [UserCwd.ucwd] takes a
       [ghost_varG Σ Z], [UkShRedirAns]'s section has its own and the
       KERNEL's files read the one the whole-system record carries
       ([Xv6Cameras.offbox_offG] off [Xv6G.xv6_offbox]).  Both are in scope
       here, resolution picks the section variable, and the two print
       identically -- so the open leaf's [ucwd] and this call's are not the
       same proposition unless this says which. *)
    UkShRedirAns.ush_open_call2 (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG)
      N FsImg.ROOTINO file 1537 l redir_K (fun s : dst => fown r s) redir_Kf.
  Proof using Heq.
    intros Hin Hokw. iIntros "#Hinv #Hmade #Hlb".
    rewrite /UkShRedirAns.ush_open_call2.
    iIntros (h m av Img pl s) "%Ha0 %Ha1 %Hpath %Hnp %Hstart %Hlast %Hfdl
             #Himg Hown #Hcode Hcwd Hstd Hrun Hcont".
    rewrite sh_open_stub_pc.
    (* ---- 0xcc6  c.li a7,15 ---- *)
    iApply (wp_uk_cli (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N h m (mword_of_int 0xcc6)
              (mword_of_int 15 : mword 6) (mword_of_int 17 : mword 5) av
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (UCodeShK.uis_shk_cc6 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0xcc6 : mword 64) 2
                 = mword_of_int 0xcc8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx (mword_of_int 17 : mword 5)
                   := regval_into_reg
                        (sign_extend' 64 (mword_of_int 15 : mword 6)
                         : mword 64)]> m
                 = <[Regidx (mword_of_int 17 : mword 5)
                     := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx (mword_of_int 17 : mword 5)
                 := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx (mword_of_int 10 : mword 5)
                   = (mword_of_int file : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                 (Regidx (mword_of_int 10 : mword 5))
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx (mword_of_int 11 : mword 5)
                   = (mword_of_int 1537 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                 (Regidx (mword_of_int 11 : mword 5))
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0xcc8  ecall -- the DEED's create corollary at [OffHeld] ---- *)
    iApply (UkFileOpen.wp_uk_ecall_open_create_deed_d (PSx := uprogSG_free)
              N OffHeld h1 m1 (mword_of_int 0xcc8) l av (fgn_cl g) r jo s
              ls ws FsImg.ROOTINO Img (mword_of_int file : mword 64) pl
              Heq
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx (mword_of_int 17 : mword 5))
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hpath Ha0'
              ltac:(rewrite Ha1'; vm_compute; reflexivity)
              ltac:(rewrite Ha1'; vm_compute; reflexivity)
              Hnp Hstart Hlast Hin Hokw
              with "[] Himg Hrun Hcwd Hstd Hinv Hmade Hlb Hown [Hcont]").
    { iApply (UCodeShK.uis_shk_cc8 with "Hcode"). }
    iIntros (h2 rv) "Hans Hcwd Hrun".
    (* ---- 0xccc  c.jr ra ---- *)
    assert (E1 : add_vec_int (mword_of_int 0xcc8 : mword 64) 4
                 = mword_of_int 0xccc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    set (m2 := <[Regidx (mword_of_int 10 : mword 5) := rv]> m1).
    assert (Hra : m2 !!! Regidx (mword_of_int 1 : mword 5)
                  = m !!! Regidx (mword_of_int 1 : mword 5)).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx (mword_of_int 10 : mword 5))
                  (Regidx (mword_of_int 1 : mword 5)) rv
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx (mword_of_int 17 : mword 5))
                  (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N h2 m2 (mword_of_int 0xccc)
              (mword_of_int 1 : mword 5)
              (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) av
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_ccc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 m2 rv with "[%] [%] Hcwd [Hans] Hrun").
    - exact (ucallee_saved_a0a7 m rv).
    - unfold m2.
      exact (upd_eq m1 (Regidx (mword_of_int 10 : mword 5)) rv).
    - (* THE ANSWER, AT THE TWO ARMS THE REDIRECT CHILD READS *)
      rewrite /UkShRedirAns.ush_open_ans2.
      iDestruct "Hans" as "[[%Hm1 [Hstd Hpay]] | Hfd]".
      + iRight. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
        rewrite /redir_Kf /FileOpen.file_open_pay. iExact "Hpay".
      + iDestruct "Hfd" as (fd ty) "([%Hrv %Hlt] & Hal & HK)".
        iDestruct (UserFd.ualloc_std (ukn_fd N) l fd 1%nat _ Hfdl with "Hal")
          as "[%Hfd1 Hstd]".
        iLeft. iExists ty. iSplitR.
        { iPureIntro. rewrite Hrv Hfd1. reflexivity. }
        iSplitL "Hstd".
        { iEval (rewrite Ha1') in "Hstd".
          iEval (vm_compute om_readable) in "Hstd".
          iEval (vm_compute om_writable) in "Hstd".
          iExact "Hstd". }
        rewrite /redir_K. iExact "HK".
  Qed.

  (* ---- NOT A HYPOTHESIS ANY MORE (the program stream): the redirect
          line's lexability is a THEOREM,
          [UShLexRedir.ush_line_lexable_redir_holds], and the threading is
          [UkShRedirBody]'s three-way case.  Kept as a [Definition] so the
          round's [Proof using] lines read as they did. ---- *)
  Definition Hlexr : UkShLoop.ush_line_lexable_redir :=
    UShLexRedir.ush_line_lexable_redir_holds.

  (* ---- HYPOTHESIS: the echo-at-console child, at the FILE links.
          [UShEchoPay.sh_exec_sup_echo_wq_holds]'s twin -- with LINK-GEN
          it is an instantiation, without it a ~1,250-line twin. ---- *)
  (*  ...AND IT IS DISCHARGED (the PROGRAM STREAM).  What blocked it was
      the GUARD: [UkShEcho.sh_exec_sup_echo_wq] quantified its box over
      every input with [EchoDisc.line_ok (last_ws I)], and at the file era
      that admits inputs whose line is NOT an [LEcho] one -- so the supply
      was stated where it cannot hold (the lend at an [LEchoF] input opens
      into the PROMPT's alternative, not echo's).  The guard is now the
      era's own ([sh_exec_sup_echo_wq_at D]) and this is it: the line is
      admissible AND the era filed an [LEcho] at that input.  The consumer
      proves it from the child law's own box, which is why nothing above
      has to carry it.

      (This law names no deposit instance -- [sh_exec_sup_echo_wq_at] takes
      only [uexecSG].  The two laws above DO, and they are annotated: left
      implicit, [uprogSG] resolves to the ambient instance and the
      discharge, which is at [uprogSG_free], is not well-typed against it
      -- and the conversion between two deposit instances does not come
      back.  That is a fifth silent-hang shape.) *)
  Definition file_D (I : list (bv 8)) : Prop :=
    EchoDisc.line_ok (last_ws I) /\ FileLinkInst.file_lineok I.

  (* THE GUARD, OFF THE CHILD LAW'S OWN BOX: the line the fork lends is
     [line_ok] ([UkSh.ush_line_is]'s first conjunct) and the slot the loop
     left says the input's last body PARSES ([UkSh.ush_posw]'s third), and
     [FileDisc.fbody_ok_echo] turns the two into the era's line. *)
  Lemma file_D_of_line (I : list (bv 8)) (ws : list (list (bv 8))) :
    EchoDisc.line_ok ws -> ws = last_ws I ->
    FileDisc.fline_ok (UkSh.ush_lastbody I) -> file_D I.
  Proof using .
    intros Hok Hwseq Hfb. subst ws. split; [ exact Hok | ].
    rewrite /UkSh.ush_lastbody in Hfb.
    rewrite /FileLinkInst.file_lineok /fline.
    rewrite (last_ws_lastbody I) in Hok |- *.
    exact (FileDisc.fline_ok_echo _ Hfb Hok).
  Qed.

  (* ...and at such an input the era's exec-failed bytes ARE the constants
     ([FileHooks.fexfb] is [alt_execcat] only at an [LCat] line), which
     is LINK-GEN-4's open item closed at the same guard. *)
  Lemma file_D_exfb (I : list (bv 8)) :
    file_D I ->
    lk_exfb FI I = EchoDisc.alt_execfail
    /\ (length (lk_exfb FI I) - 2)%nat = 17%nat.
  Proof using .
    intros [_ Hln]. cbn [lk_exfb file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    rewrite -fline_lm. rewrite /FileLinkInst.file_lineok in Hln. rewrite Hln.
    cbn [lmh_exfb gK FileLinkGen.file_params_at FileHooks.file_hooks fexfb].
    split; [ reflexivity | ].
    rewrite UShPanic.alt_execfail_len. reflexivity.
  Qed.

  (* the four [Wc] laws at this family, which are [UShEchoPay]'s [lkw_*]
     at [Hold := PRE] (RULING HOLD-POS: the lend carries the deed at the
     round's PRE-state; the child's exit at position 0 folds by the line's
     identity f-effect -- every alternative of an [LEcho] line leaves `f`
     alone, [Wcf0_of_pre_line_id]) *)
  Local Lemma fwc3 (I0 : list (bv 8)) :
    ⊢ Wcf I0 3%nat -∗ ∃ v : era_pins,
        lk_pin FI (S gen_id) v ∗ lk_lpr FI (S gen_id) v I0 3%nat
        ∗ PRE I0.
  Proof using .
    rewrite Wcf_S3 /FileLinkInst.file_Wcl_at /lk_lcred.
    iIntros "[H HR]". iDestruct "H" as (v) "[#Hp Hc]".
    iExists v. iSplitR "Hc HR"; [ iExact "Hp" | ].
    iSplitL "Hc"; [ iExact "Hc" | iExact "HR" ].
  Qed.

  Local Lemma fwc3b (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin FI (S gen_id) v0 -∗ lk_lpr FI (S gen_id) v0 I0 3%nat -∗
      PRE I0 -∗ Wcf I0 3%nat.
  Proof using .
    iIntros "#Hp Hc HR". rewrite Wcf_S3.
    iSplitR "HR"; [ | iExact "HR" ].
    rewrite /FileLinkInst.file_Wcl_at /lk_lcred. iExists v0.
    iSplitR; [ iExact "Hp" | iExact "Hc" ].
  Qed.

  Local Lemma fwc0 (I0 : list (bv 8)) (v0 : era_pins) :
    ck_lineok (sk_cur (FileLinkInst.file_stage_inst_at g s0)) I0 ->
    ⊢ lk_pin FI (S gen_id) v0 -∗ lk_post FI (S gen_id) v0 I0 0%nat -∗
      PRE I0 -∗ Wcf I0 0%nat.
  Proof using .
    intro Hlok. iIntros "#Hp Hc HR".
    assert (Hl : FileLinkInst.file_lineok I0) by exact Hlok.
    rewrite /FileLinkInst.file_lineok in Hl.
    iApply (Wcf0_of_pre_line_id I0 ltac:(intros s a; rewrite Hl; reflexivity)
              with "[Hc] HR").
    rewrite /FileLinkInst.file_Wcl_at.
    iApply (lk_lcred_of_post_a FI (S gen_id) I0 0%nat v0
              (sk_apr0 (FileLinkInst.file_stage_inst_at g s0) I0 Hlok)
              with "Hp Hc").
  Qed.

  Local Lemma fwct (I0 : list (bv 8)) (v0 : era_pins) :
    ⊢ lk_pin FI (S gen_id) v0 -∗ T -∗ Wcf I0 0%nat.
  Proof using .
    iIntros "#Hp #HT". cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    iApply (Wcf_taint I0 0%nat v0 with "Hp HT").
  Qed.

  (* the round's post, read back at the record: at an [LEcho] line the
     alternative-0 continuation is state-free, so the block written up to
     its prompt at the block's own state IS the record's post *)
  Local Lemma fpost_of_gwc (I0 : list (bv 8)) (v0 : era_pins) :
    FileLinkInst.file_lineok I0 ->
    gwc_post file_lm (file_params_at g s0) (S gen_id) v0 I0 0%nat -∗
    lk_post FI (S gen_id) v0 I0 0%nat.
  Proof using .
    intro Hlok. iIntros "Hc".
    rewrite /lk_post.
    cbn [lk_blk lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    rewrite /gwc_blk /gwc_post. iDestruct "Hc" as "[Hc | Hc]"; [ | by iRight ].
    iDestruct "Hc" as (ps cs sb P) "(%Hw & Htn & Hps & Hcs & HE & Hf)".
    rewrite (lm_abs_ab _ _ sb cs I0 0%nat (FileLinkInst.file_apr0 I0 Hlok)).
    iLeft. iExists ps, cs, sb, P. iFrame "Htn Hps Hcs HE Hf". by iPureIntro.
  Qed.

  (* =================================================================== *)
  (*  THE ECHO CHILD'S EXEC SUPPLY AT THE CONSOLE, FROM THE TREE ROUTE     *)
  (*  (program-specs SS3.4g).  [UShEchoPay.sh_exec_sup_echo_wq_holds_at_D]'s *)
  (*  body -- the same U-tier rule, the same walk pin, the same taint slot *)
  (*  -- with the image slot at [UkFileEntries.                            *)
  (*  echo_cons_image_entry_of_tree]: the lend opens into the block at its *)
  (*  first byte ([gwc_blk ... 0 0]) and the deed's arm of [PRE] into the  *)
  (*  deed's half the entry lends to the core and the ticket beside it;    *)
  (*  the exit reassembles [PRE] and folds it at position 0 ([fwc0]).  The *)
  (*  console's credential ([file_cons_cred]) is the instance core's.     *)
  (* =================================================================== *)
  Lemma echo_exec_sup_file (jo : option Z) :
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      file_cons_cred (fgn_cl g) r jo -∗
      UkShEcho.sh_exec_sup_echo_wq_at file_D Wcf.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hmade".
    rewrite /UkShEcho.sh_exec_sup_echo_wq_at. iIntros "!>" (I) "%HDI".
    destruct HDI as [Hokws Hlok].
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* the lend, opened: the era's pin, the block-owed family and PRE *)
    iDestruct (fwc3 I with "Hcr") as (v) "(#Hpin & Hcr & HR)".
    (* the taint slot at the chosen payload *)
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcf I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcf I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (fwct I v with "Hpin"). iApply Hktaint. iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld
               ∗ lk_lpr FI (S gen_id) v I 3%nat ∗ PRE I)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr HR]").
    (* THE REFUND IS THE LEND, WHOLE *)
    { iIntros "!> ($ & Hc & HR)". iApply (fwc3b I v with "Hpin Hc HR"). }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
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
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr HR"; [ | iFrame "Hstd Hcr HR" ].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (_ & Hc & HR)".
    (* ---- the lend at the record: the block at its first byte ---- *)
    cbn [lk_pin lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
    (* ---- PRE: the deed's arm, or the taint's generic slot ---- *)
    rewrite /sh_pre_at. iDestruct "HR" as "[Hdeed #Hwit]".
    rewrite {1}/sh_deed_at. iDestruct "Hdeed" as "[Hdeed | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hdeed" as (cs s v') "(Hown & %Htie & #Hty & #Hpin' & #Hcs)".
    rewrite /fown /fdeed. iDestruct "Hown" as "[Hdq Htk]".
    iPoseProof (UkFileEntries.echo_cons_image_entry_of_tree (PS := uprogSG_free)
                  g Hcons (last_ws I) M sa t gb fdv FsImg.ROOTINO chs pidv
                  v s0 I (fgn_cl g) r (1/2)%Qp s rb jo
                  (fun _ : Z => UkShFork.ushf_wq Wcf I) (ftkt r s)
                  (fun _ _ => eq_refl) Heq eq_refl Hokws Himg Hbytes Hflen
                  eq_refl ltac:(rewrite Hl; exact Hl1) Hlok
                  (ush_line_len (last_ws I) Hokws)
                  with "[] [] [] [] Hmade Hinv Hpin Hnp0 Hdep") as "#He".
    { iIntros "!> Hk". iApply Hktaint. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { (* THE BLOCK'S END PAYS THE EXIT: the deed comes back and PRE with it *)
      iIntros "!> Hpost Hdq Htk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (fwc0 I v Hlok with "Hpin [Hpost] [Hdq Htk]").
      - iApply (fpost_of_gwc I v Hlok with "Hpost").
      - rewrite /sh_pre_at /sh_deed_at. iSplitL; [ | iExact "Hwit" ].
        iLeft. iExists cs, s, v'. rewrite /fown /fdeed /FileOpen.fdq.
        iFrame "Hty Hpin' Hcs".
        iSplitL "Hdq Htk"; [ iFrame "Hdq Htk" | by iPureIntro ]. }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (fwct I v with "Hpin HT"). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Hc Hdq Htk]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /FileOpen.fdq. iFrame "Hc Hdq Htk".
  Qed.

  Lemma Hchild_echo :
    ⊢ FileLinks.file_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl g) r jo) -∗
      UkShEcho.sh_exec_sup_echo_wq_at file_D Wcf.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "_ #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iApply (echo_exec_sup_file jo with "Hdep Hslot Hmade").
  Qed.

  (* =================================================================== *)
  (*  THE REDIRECT CHILD'S EXEC SUPPLY (item 2d): [exec /echo] with fd 1   *)
  (*  on `f`.                                                             *)
  (*                                                                     *)
  (*  [UShEchoPay.sh_exec_sup_echo_wq_holds_at_D]'s body -- the same rule  *)
  (*  ([ExecRun.udepw_at_refR_of_sup]), the same walk pin, the same taint  *)
  (*  slot -- with echo's entry FROM THE TREE ROUTE                       *)
  (*  ([UkFileEntries.efile_image_entry_of_tree], program-specs SS3.4g) in  *)
  (*  the image slot.  The lend is what is left of the round's credential after the  *)
  (*  open took the deed ([Wcl I 3]) beside the open's RECEIPT, read       *)
  (*  ([redir_K']: the deed at `f` present and empty, the program's half   *)
  (*  of the offset at 0, and the claim's fact that `f`'s inode is none of *)
  (*  the image's).  The entry's payment is built INSIDE the image slot,   *)
  (*  off the payload the rule hands in, because the inode and the offset  *)
  (*  name are existential in the receipt; a TAINTED receipt buys the      *)
  (*  generic slot instead.  The refund is the lend, whole.                *)
  (* =================================================================== *)
  Definition redir_K' (ty : fdtype) : iProp Σ :=
    (redir_K ty
     ∗ ((∃ (i : Z) (γo : gname),
           ⌜ty = FdInode i γo OffHeld⌝
           ∗ ⌜i <> INIT_INO /\ i <> SH_INO /\ i <> ECHO_INO
              /\ i <> CAT_INO⌝)
        ∨ T))%I.

  Lemma redir_exec_sup (I : list (bv 8)) (ws : wordline) (v' : era_pins)
      (cs : list nat) (ls : list wordline) :
    fline I = LEchoF ws -> EchoDisc.line_ok ws -> ws ∈ ls ->
    length cs = (nlines I - 1)%nat -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs -∗
      fl_lb (fgn_cl g) ls -∗
      ∀ ty : fdtype,
        UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
          (ghost_varG0 := offbox_offG)
          (UkShRedirBody.ushs_fd1f ty) ws
          (fun _ : Z => UkShFork.ushf_wq Wcf I)
          (Wcl I 3%nat ∗ redir_K' ty).
  Proof using Heq Hkill Hcons HfifR.
    intros Hfl Hokws Hin Hlen Hpos.
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hpin' #Hcs #Hlb" (ty).
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* the taint slot at the chosen payload *)
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcf I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcf I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Wcf_taint I 0%nat v' with "Hpin'"). iApply Hktaint.
      iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat ∗ redir_K' ty)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    (* THE REFUND IS THE LEND, WHOLE *)
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img ws M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd ws _ _ _ M pm sz sa t gb Hokws
                with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (UShEcho.sh_echo_path_of_holds ws Hokws M sa t gb Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [ | iFrame "Hstd Hcr" ].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (Hstd & Hc & HK & Hino)".
    (* a tainted receipt buys the generic slot *)
    iDestruct "Hino" as "[Hino | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hino" as (i γo) "(%Hty & %Hi)".
    destruct Hi as (Hi1 & Hi2 & Hi3 & Hi4).
    rewrite /redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
    iDestruct "HK" as "[HK | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "HK" as (i1 γo1) "(%Hty1 & Hd & Hpub)".
    rewrite Hty in Hty1. injection Hty1 as <- <-.
    iDestruct (UserOff.foff_pub_of_held with "Hpub") as "Hu".
    (* the entry FROM THE TREE ROUTE, at what is left of the lend *)
    iPoseProof (UkFileEntries.efile_image_entry_of_tree (PS := uprogSG_free)
                  g Hcons ws M sa t gb fdv FsImg.ROOTINO chs pidv
                  (fgn_cl g) r
                  (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat)%I
                  i γo false
                  (fun _ : Z => UkShFork.ushf_wq Wcf I)
                  (fun _ _ => eq_refl) Heq eq_refl Hokws Himg Hbytes Hflen
                  eq_refl
                  ltac:(rewrite Hl -Hty; exact Hfd1) Hi1 Hi2 Hi3 Hi4
                  with "[] [] [] [] Hinv Hnp0 Hdep") as "#He".
    { (* echo RAN: the exit pays the round's payload *)
      iIntros "!> [[_ Hc] Hex]". iDestruct "Hex" as (sel) "Hcur".
      rewrite /UkShFork.ushf_wq. iRight.
      rewrite /UEchoFile.efq /FileWrite.file_cur.
      iDestruct "Hcur" as "[[Hq _] | [#HT _]]".
      - iApply (redir_ran_exit I ws i sel v' cs Hfl Hlen Hpos
                  with "Hc Hpin' Hcs Hq").
      - iApply (Wcf_taint I 0%nat v' with "Hpin' HT"). }
    { iIntros "!> Hk". iApply Hktaint. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Wcf_taint I 0%nat v' with "Hpin' HT"). }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Hstd Hc Hd Hu]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /UEchoFile.ef_pay /UEchoFile.efq. iFrame "Hstd Hc".
    iApply (FileWrite.file_cur_fired (fgn_cl g) r i ws [] γo with "[Hd] Hu").
    rewrite /FileWrite.file_wq. iLeft. iExists ls. iFrame "Hd Hlb".
    iPureIntro. split_and!;
      [ reflexivity | exact Hokws | exact (sel_ok_nil _) | exact Hin ].
  Qed.

  (* ---- THE EXEC-FAILED DIAGNOSTIC'S LAW at the file families, AT THE
          PARAMETERIZED CARRIER (lane LINK-GEN-4) AND UNDER THE ERA'S GUARD
          (lane HOLD-POS).  [UkShEcho.ush_execfail_law_wq_at] was stated at
          EVERY input, and at the position-keyed family that is REFUTED at
          an [echo ... > f] input: the exec-failed alternative there is
          [RFExec], which truncates `f`, while the lend's deed is at the
          round's PRE-state -- so [Wcf I 0]'s DONE arm wants a content the
          deed does not have and its PEND arm wants an output that is not
          the bare prompt.  The law was only ever SPENT at an input the echo
          child law admits ([file_D]: an [LEcho] line), where every
          alternative leaves `f` alone, so the guarded carrier
          [ush_execfail_law_wq_at_D] is the honest statement and this is
          its discharge: the record's framed law at [Hold := PRE], folded
          at the exit by [Wcf0_of_pre_line_id]. ---- *)
  Lemma Hexecfail_D :
    ⊢ FileLinks.file_links g -∗
      UkShEcho.ush_execfail_law_wq_at_D (PS := uprogSG_free) file_D
        (lk_exfb FI)
        (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat)
        Wcf.
  Proof using .
    iIntros "#Hlk". rewrite /UkShEcho.ush_execfail_law_wq_at_D.
    iIntros "!>" (I) "%HD".
    iPoseProof (UShPanic.ush_execfail_law_hold_at (PS := uprogSG_free) FI PRE I
                  with "[]") as "#Hx".
    { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk". }
    rewrite Wcf_S3 /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | rewrite /FileLinkInst.file_Wcl_at; iExact "Hc" | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp".
    iDestruct ("Hend" with "Hp") as "[Hc Hh]".
    destruct HD as [_ Hl]. rewrite /FileLinkInst.file_lineok in Hl.
    iApply (Wcf0_of_pre_line_id I ltac:(intros s a; rewrite Hl; reflexivity)
              with "[Hc] Hh").
    rewrite /FileLinkInst.file_Wcl_at. iExact "Hc".
  Qed.

  (* ---- sh's own fork panic at the file families (RULING HOLD-POS (v)):
          the record's framed law at [Hold := PRE], plus PRE -> DONE at the
          banner-owed credential -- [wr_ban_f] pins the last filed
          alternative as a PANIC, whose f-effect is the identity
          ([done_tie_of_pre_ban]); the era's head is DONE at [cs = []]. ---- *)
  Lemma sh_done_of_pre_ban (I : list (bv 8)) :
    Wbl I -∗ PRE I -∗ Wbl I ∗ DONE I.
  Proof using .
    iIntros "Hb Hp". rewrite /sh_pre_at /sh_done_at /sh_deed_at.
    iDestruct "Hp" as "[Hp _]".
    iDestruct "Hp" as "[Hp | #HT]"; last (iFrame "Hb"; by iRight).
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs')".
    pose proof Htie as [Hlen _].
    rewrite /FileLinkInst.file_Wbl_at. iDestruct "Hb" as (v) "[#Hpin Hb]".
    cbn [lk_pin lk_ban FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst].
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    rewrite /gwc_ban. cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at.
    iDestruct "Hb" as "[Hb | [Hb | #HT]]".
    - iDestruct "Hb" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
      subst sw.
      pose proof Hw as (_ & _ & Hn & Hpan & _).
      iDestruct (cs_lb_prefix_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %Hpre.
      iSplitL "Htn".
      + iExists v. iFrame "Hpin". iLeft. iExists ps, cs, s0, P.
        iFrame "Htn Hps Hcs HE Hf". iSplit; by iPureIntro.
      + iLeft. iExists cs, s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
        exact (done_tie_of_pre_ban cs cs' s0 I _ Htie ltac:(lia) Hpre Hpan).
    - iDestruct "Hb" as "[%Hi Hhd]". rewrite /fhead_at.
      iDestruct "Hhd" as "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & #Hvf & Hpre)".
      iSplitL "Htn Hpre".
      + iExists v. iFrame "Hpin". iRight. iLeft. iSplitR; [ by iPureIntro | ].
        iFrame "Htn Hps Hcs HE Hvf Hpre". by iSplit; iPureIntro.
      + iLeft. iExists [], s, v. iFrame "Hd Hty Hpin Hcs". iPureIntro.
        apply (done_tie_of_pre_ban [] cs' s0 I _ Htie).
        * subst I. by rewrite nlines_nil.
        * subst I. rewrite nlines_nil in Hlen. cbn in Hlen.
          apply nil_length_inv in Hlen. subst cs'. done.
        * by left.
    - iSplitL ""; [ iExists v; iFrame "Hpin"; by iRight; iRight | by iRight ].
  Qed.

  Lemma Hpanic :
    ⊢ FileLinks.file_links g -∗
      UkShDiag.ush_panic_law (PS := uprogSG_free) Wcf Wbf.
  Proof using .
    iIntros "#Hlk".
    iPoseProof (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) FI PRE
                  with "[]") as "#Hp".
    { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk". }
    rewrite /UkShDiag.ush_panic_law. iIntros "!>" (N I l) "%Hfd Hc".
    rewrite Wcf_S3.
    iDestruct ("Hp" $! N I l with "[%] [Hc]") as (Pf) "(H0 & #Hstep & #Hend)";
      [ exact Hfd | rewrite /FileLinkInst.file_Wcl_at; iExact "Hc" | ].
    iExists Pf. iFrame "H0 Hstep". iIntros "!> Hp5".
    iDestruct ("Hend" with "Hp5") as "[Hb Hpre]".
    rewrite /Wbf. iApply (sh_done_of_pre_ban I with "[Hb] Hpre").
    rewrite /FileLinkInst.file_Wbl_at. iExact "Hb".
  Qed.

  (* =================================================================== *)
  (*  THE cat CHILD (item 3).  It was a section hypothesis -- an           *)
  (*  [image_entry] at [line_ok ws], which `cat f` does not meet, under    *)
  (*  [app_taint], with the payload conversion a premise -- and is a       *)
  (*  LEMMA at [UkShFork.ushf_child_law_at Wcf ushs_lp_cat 68] now, the    *)
  (*  shape [UkShRedirBody.ushf_body_law_file] takes.                      *)
  (*                                                                     *)
  (*  The walk is [UkShEcho.wp_kshm_child_x_holds] at the words of `cat f` *)
  (*  and cat's exec-failed alternative; the supply is [ExecRun.           *)
  (*  udepw_at_refR_of_sup] with the tree route's cat entry                *)
  (*  ([UkFileEntries.cat_child_of_entry_of_tree]) in the image slot.      *)
  (*  sh lends cat ONE fraction of `f`'s ghost state -- the                *)
  (*  deed's own half, [fdq r (1/2) s] -- and the console cursor, and cat  *)
  (*  returns exactly that (RULING CAT-DEED, amended); the ticket's half   *)
  (*  crosses cat's entry as its FRAME.  The console credential and cat's  *)
  (*  cursor are the same resources: the lend is OPENED into the cursor    *)
  (*  inside the image slot, and cat's end cursor closes into the          *)
  (*  state-aware post ([GenLinksLine.gwc_post]), which is what lets a     *)
  (*  round that printed the file's contents fold ([Wcf0_of_posts_alt]).   *)
  (* =================================================================== *)
  Definition cat_ws : list (list (bv 8)) := FileDisc.uline_ws LCat.

  (* the rows cat's entry reads off the child's table: 0, 1 and 2 *)
  Definition cat_rows (ld : list fdstate) : Prop :=
    UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld.

  Local Lemma cat_ws_exec_ok : exec_ok cat_ws.
  Proof using . apply (bool_decide_unpack _). vm_compute. exact Logic.I. Qed.
  Local Lemma cat_ws_len : length cat_ws = 2%nat.
  Proof using . vm_compute. reflexivity. Qed.
  Local Lemma cat_ws_alen1 : UkShEcho.echo_alen cat_ws 1%nat = 1%nat.
  Proof using . vm_compute. reflexivity. Qed.
  Local Lemma cat_ws_fname (j : nat) :
    (j < 1)%nat ->
    LineWords.wl_line cat_ws !!! (UkShEcho.echo_off cat_ws 1%nat + j)%nat
    = FsImgCheck.fname_f !!! j.
  Proof using . intro Hj. destruct j as [| j]; [ | lia ]. by vm_compute. Qed.
  Local Lemma cat_ws_head : cat_ws !!! 0%nat = UShCatPay.cat_pl.
  Proof using . by vm_compute. Qed.
  Local Lemma cat_ws_line : LineWords.wl_line cat_ws = FileDisc.line_bytes LCat.
  Proof using . by vm_compute. Qed.

  Local Lemma cat_xline (gb : nat -> bv 8) (len : nat) :
    UkSh.ush_line_at LCat gb 0%nat len ->
    UkShEcho.ush_xline_is cat_ws gb 0%nat len.
  Proof using .
    intros (_ & Hlen & Hby). split; [ exact cat_ws_exec_ok | ].
    rewrite cat_ws_line. exact (conj Hlen Hby).
  Qed.

  (* cat's exec-failed alternative, around its name *)
  Local Lemma cat_execfail_bytes :
    UkShDiagAt.ush_execfail_bytes FileDisc.alt_execcat (cat_ws !!! 0%nat).
  Proof using .
    rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
    - vm_compute. lia.
    - intros p Hp.
      assert (Hl : (p < length FileDisc.alt_execcat)%nat)
        by (vm_compute in Hp |- *; lia).
      exact (list_lookup_lookup_total_lt FileDisc.alt_execcat p Hl).
    - intros p Hp.
      apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
               (fun q : nat => FileDisc.alt_execcat !!! q) 0%nat 5%nat);
        [ vm_compute; reflexivity | lia ].
    - intros j Hj.
      assert (Hj3 : (j < 3)%nat) by (vm_compute in Hj; lia).
      destruct j as [| [| [| j]]]; try lia; vm_compute; reflexivity.
    - intros p Hp.
      apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x12a8)
               (fun q : nat => FileDisc.alt_execcat !!! (q + 1)%nat)
               7%nat 8%nat);
        [ vm_compute; reflexivity | lia ].
  Qed.

  (* cat's END CURSOR IS THE STATE-AWARE POST: the same turn, bounds and
     boot-state witness; the block's length is [fabs] at the credential's
     own choice list, which at a cat line IS [UCatOut.cat_out_len] + 2. *)
  Local Lemma cch_post (I : list (bv 8)) (a : nat) (v : era_pins)
      (vf : file_era) (ps cs : list nat) (P : nat) :
    fline I = LCat ->
    wr_blk_t_f ps cs s0 I P ->
    file_era_pin g (S gen_id) vf -∗
    UCatOut.cch g v vf ps cs s0 I a P (UCatOut.cat_out_len cs s0 I a) -∗
    gwc_post file_lm (file_params_at g s0) (S gen_id) v I a.
  Proof using .
    intros Hfl Hw. iIntros "#Hvf Hc".
    rewrite /UCatOut.cch /gwc_post. cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at.
    iDestruct "Hc" as "[(Htn & Hps & Hcs & HE & Hf0) | HT]"; [ | by iRight ].
    assert (Hix : UCatOut.cat_out_len cs s0 I a
                  = (length (fabs s0 cs I a) - 2)%nat)
      by (rewrite /UCatOut.cat_out_len /fabs /UCatOut.cat_st Hfl
                  UCatOut.cat_prompt_len; reflexivity).
    iLeft. iExists ps, cs, s0, P. rewrite -(fabs_lm s0 cs I a) -Hix.
    rewrite /UCatOut.catcs /lm_blkcs. iFrame "Htn Hps Hcs HE".
    iSplitR; [ iPureIntro; by rewrite -wr_blk_t_f_lm | ].
    iSplitL; [ | by iPureIntro ].
    rewrite /f0w. iSplitR; [ by iPureIntro | ]. iExists vf. iFrame "Hvf Hf0".
  Qed.

  (* ---- THE EXEC SUPPLY: [exec /cat] ---- *)
  Lemma cat_exec_sup (I : list (bv 8)) (s : dst) (v' : era_pins)
      (cs' : list nat) (jo : option Z) :
    fline I = LCat ->
    pre_tie cs' s0 I (dst_content s) -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      file_cons_cred (fgn_cl g) r jo -∗
      era_pin (fgn_echo g) (S gen_id) v' -∗ cs_lb v' cs' -∗
      f_typed (fgn_cl g) s -∗
      UkShEcho.sh_exec_sup_echo_at (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG)
        cat_rows cat_ws
        (fun _ : Z => UkShFork.ushf_wq Wcf I)
        (Wcl I 3%nat ∗ fown r s).
  Proof using Heq Hkill Hcons HfifR.
    intros Hfl Htie Hpos. pose proof Htie as [Hlen Hcon].
    iIntros "#Hdep (#Hinv & #Hcl & #Hgen) #Hmade #Hpin' #Hcs' #Hty".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc sa t gb ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hrows Hstd #Hcmd Hcr".
    iAssert (□ (T -∗ UkShFork.ushf_wq Wcf I))%I as "#HQt".
    { iIntros "!> #HT". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Wcf_taint I 0%nat v' with "Hpin' HT"). }
    iAssert (image_entry_taint T
               (fun _ : Z => UkShFork.ushf_wq Wcf I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcf I) W' with "HT Hmp []").
      iIntros "!> #Hk". iApply "HQt". iApply Hktaint. iExact "Hk". }
    iApply (udepw_at_refR_of_sup (ghost_varG0 := offbox_offG) N' m pc
              (mword_of_int sa) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShCatPay.cat_pl ElfUser.cat_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Wcl I 3%nat ∗ fown r s)%I
              _ UShCat.cat_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> H". iExact "H". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv chs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img cat_ws M sa t gb ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd_x cat_ws _ _ _ M pm sz sa t gb
                cat_ws_exec_ok with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hflen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro. rewrite -cat_ws_head.
      exact (UShEcho.sh_exec_path_of_x_holds cat_ws cat_ws_exec_ok
               M sa t gb Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsCatPin.era0_cat_pins T FsImg.ROOTINO
                UShCatPay.cat_pl [FsImg.ROOTINO; FsCatPin.CAT_INO]
                FsCatPin.CAT_INO
                (MkAnode (AFile ElfUser.cat_elf) 1%nat)
                UShCatPay.sh_cat_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr"; [ | iFrame "Hstd Hcr" ].
    rewrite Hpeq. rewrite /image_entry. iModIntro.
    iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf %Hch0 %Hpid0 %Hargs Hmp
                               (_ & Hc & Hd)".
    (* ---- the lend, OPENED into cat's cursor ---- *)
    rewrite {1}/FileLinkInst.file_Wcl_at /lk_lcred.
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst gwc_lpr].
    iEval (rewrite /gwc_blk; cbn [gH gW gT FileLinkGen.file_params_at]; rewrite /FileLinkGen.f0w_at) in "Hc".
    iDestruct "Hc" as "[Hc | #HT]"; last first.
    { iApply ("Hgen'" $! W' with "HT Hmp"). }
    iDestruct "Hc" as (ps cs sw P) "(%Hw & Htn & #Hps & #Hcs & #HE & #[Hf %Hs])".
    subst sw. rewrite -wr_blk_t_f_lm in Hw.
    rewrite /f0w. iDestruct "Hf" as "[%Hk Hvf]".
    iDestruct "Hvf" as (vf) "[#Hvf #Hf0]".
    iDestruct (era_pin_agree (fgn_echo g) (S gen_id) v v' with "Hpin Hpin'")
      as %<-.
    pose proof Hw as [(Hpin0 & Hr & Hn & HP) _].
    cbn [lm_blkcs].
    iDestruct (cs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    destruct Hrows as ([wr0 Hr0] & [rb1 Hr1] & [rb2 Hr2]).
    assert (Hnone : fd_lowest_closed (take NSTD fdv) = None).
    { rewrite Hl. destruct ld as [| y0 [| y1 [| y2 l3]]];
        [ discriminate Hr0 | discriminate Hr1 | discriminate Hr2 | ].
      cbn in Hr0, Hr1, Hr2. injection Hr0 as ->. injection Hr1 as ->.
      injection Hr2 as ->.
      assert (Hl3 : l3 = []).
      { pose proof (f_equal length Hl) as Hll. rewrite length_take in Hll.
        cbn [length] in Hll. unfold NSTD in Hll. destruct l3; [ done | ].
        cbn [length] in Hll. lia. }
      subst l3. reflexivity. }
    (* the content's C-int bound, off the claim's typing of it *)
    iAssert (⌜forall (i : Z) (bs : list (bv 8)), s = Some (i, bs) ->
               (Z.of_nat (length bs) < 2 ^ 31)%Z⌝)%I as %Hshort.
    { destruct s as [[i0 bs0] |]; [ | iPureIntro; intros ? ? Hn0; discriminate Hn0 ].
      rewrite /f_typed. iDestruct "Hty" as (ls0) "[_ %Hbt]".
      iPureIntro. pose proof (FileDeltas.f_bytes_typed_short ls0 bs0 Hbt) as Hb.
      unfold EchoDisc.line_max in Hb.
      intros i bs Hs. injection Hs as _ Hbs. rewrite -Hbs. lia. }
    iPoseProof (UkFileEntries.cat_child_of_entry_of_tree (PS := uprogSG_free)
                  g Hcons cat_ws M sa t gb fdv
                  FsImg.ROOTINO chs pidv v vf ps cs s0 I P (fgn_cl g) r
                  (1/2)%Qp s rb1 rb2 jo
                  (fun _ : Z => UkShFork.ushf_wq Wcf I) (ftkt r s)
                  (fun _ _ => eq_refl) Heq eq_refl
                  (conj Hr (conj Hn (conj Hfl (conj HP Hpin0))))
                  Hcon cat_ws_exec_ok Himg Hbytes Hflen
                  cat_ws_len cat_ws_alen1 cat_ws_fname eq_refl
                  ltac:(rewrite Hl; exact Hr1) ltac:(rewrite Hl; exact Hr2)
                  Hnone (proj2 Hw) Hshort
                  with "[] [] [] HQt Hmade Hinv Hpin Hvf Hnp0 Hdep") as "#He".
    { iIntros "!> Hk". iApply Hktaint. iExact "Hk". }
    { iIntros "!> HT". rewrite Hkill. iExact "HT". }
    { (* WHAT cat PRODUCES, AND THE TICKET, PAY THE ROUND *)
      iIntros "!> [Hfiled HD] Htk". rewrite /UkShFork.ushf_wq. iRight.
      iDestruct "HD" as "[Hdq | #HT]"; last first.
      { iApply (Wcf_taint I 0%nat v with "Hpin HT"). }
      iAssert (fown r s) with "[Hdq Htk]" as "Hown".
      { rewrite /fown /fdeed /FileOpen.fdq. iFrame "Hdq Htk". }
      iDestruct "Hfiled" as "[Hc | Hc]".
      - rewrite /UCatOut.catq_filed.
        iDestruct (cch_post I (ralt_enc RCRan) v vf ps cs P Hfl Hw
                     with "Hvf Hc") as "Hpost".
        iApply (Wcf0_of_posts_alt I (ralt_enc RCRan) v v cs s
                  with "[] Hpost Hown Hty Hpin Hcs");
          [ rewrite /faprs ralt_dec_enc Hfl; split;
              [ exact Logic.I | reflexivity ]
          | exact Hlen | exact Hpos
          | rewrite ralt_dec_enc Hfl fsm_cat; exact Hcon
          | cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; iExact "Hpin" ].
      - rewrite /UCatOut.catq_filed.
        iDestruct (cch_post I (ralt_enc RCNoOpen) v vf ps cs P Hfl Hw
                     with "Hvf Hc") as "Hpost".
        iApply (Wcf0_of_posts_alt I (ralt_enc RCNoOpen) v v cs s
                  with "[] Hpost Hown Hty Hpin Hcs");
          [ rewrite /faprs ralt_dec_enc Hfl; split;
              [ exact Logic.I | reflexivity ]
          | exact Hlen | exact Hpos
          | rewrite ralt_dec_enc Hfl fsm_cat; exact Hcon
          | cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; iExact "Hpin" ]. }
    rewrite /image_entry.
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp
                                          [Htn Hd]");
      [ exact Hok | exact Hcwd0 | exact Hlzf | exact Hch0 | exact Hpid0
      | exact Hargs | ].
    rewrite /UCatLend.cat_lend /fown /fdeed /FileOpen.fdq.
    iDestruct "Hd" as "[Hdq Htk]". iFrame "Hdq Htk".
    rewrite /UCatOut.cch /UCatOut.catcs. iLeft.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE Hf0".
  Qed.

  (* ---- THE cat CHILD'S LAW ---- *)
  Lemma Hchild_cat :
    ⊢ FileLinks.file_links g -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl g) r jo) -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) Wcf UkShRedirBody.ushs_lp_cat 68.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv sa len ws gb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch _ HM Hcr
       Hrun".
    (* the law hands the child its children set EXACTLY ([uch ∅]) and its
       pid; the walk takes any set and no pid ([UkShEcho]'s own assembly
       drops the same two) *)
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch".
    destruct Hline as [-> Hlat].
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [ | lia ]. exfalso.
      rewrite /last_ws in Hlws. rewrite /nlines in Hn.
      apply nil_length_inv in Hn. rewrite Hn in Hlws. cbn in Hlws.
      revert Hlws. vm_compute. discriminate. }
    assert (Hfl : fline I = LCat).
    { apply (FileDisc.fline_ok_cat_words (UkSh.ush_lastbody I) Hfok).
      rewrite -(last_ws_lastbody I). symmetry. exact Hlws. }
    (* ---- the lend, opened ---- *)
    rewrite Wcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo g) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /FileLinkInst.file_Wcl_at /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcf I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Wcf_taint I 0%nat v0 with "Hpin0"). iApply Hktaint.
      iExact "Hk". }
    iAssert (□ (∀ W : UexecSlot.uvis,
                  T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
                  UexecRet.uslot (SG := uexecSG_xv6) W))%I
      as "#Hgenw".
    { iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcf I) W with "HT' Hmy Hkillq"). }
    rewrite {1}/sh_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs)".
    pose proof Htie as [Hlen Hcon].
    (* ---- THE WALK, at 8 more steps of budget than it needs ---- *)
    assert (Hbud : (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
                   = (60 + (8 + (UkShDiag.ush_Dg + (n + 8))))%nat) by lia.
    rewrite Hbud.
    iApply (UkShEcho.wp_kshm_child_x_holds (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) cat_rows cat_ws FileDisc.alt_execcat
              (fun _ : Z => UkShFork.ushf_wq Wcf I)
              (Wcl I 3%nat ∗ fown r s)%I
              (∃ v : era_pins,
                 lk_pin FI (S gen_id) v
                 ∗ lk_post FI (S gen_id) v I (ralt_enc RCExec) ∗ fown r s)%I
              N' (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len gb sz ld (n + 8)%nat
              Hpeq Hs1 (cat_xline gb len Hlat) cat_execfail_bytes
              Hsa Hs64 Hs38 Hszlo Hszal Hszok Hrows (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hstr Hwsp Hsy Hstd Hcwd
                    Hch HM [Hc Hd] Hrun").
    - (* exec /cat *)
      iApply (cat_exec_sup I s v' cs jo Hfl Htie Hpos
                with "Hdep Hslot Hmade Hpin' Hcs Hty").
    - (* the child died before the exec: the lend, whole *)
      iIntros "!> [Hc Hd]". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwbl_f I). rewrite Wcf_S3. iFrame "Hc".
      rewrite /sh_pre_at /sh_deed_at. iFrame "Hwit".
      iLeft. iExists cs, s, v'. iFrame "Hd Hty Hpin' Hcs". by iPureIntro.
    - (* exec failed: the diagnostic at [RCExec] *)
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                    (ghost_varG0 := offbox_offG) FI (fown r s) I
                    (ralt_enc RCExec) with "[]") as "#Hx".
      { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk". }
      iEval (cbn [lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; rewrite -fab_lm;
             rewrite (fab_of_apr I (ralt_enc RCExec)
                        ltac:(rewrite ralt_dec_enc Hfl; split;
                              [ exact Logic.I | reflexivity ]))
                     ralt_dec_enc Hfl) in "Hx".
      iExact "Hx".
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight.
      iDestruct "H" as (v) "(#Hp & Hblk & Hd)".
      iApply (Wcf0_of_post_alt I (ralt_enc RCExec) v v' cs s
                with "Hp Hblk Hd Hty Hpin' Hcs");
        [ rewrite /fapr ralt_dec_enc Hfl; split_and!; [ exact Logic.I | | ];
          reflexivity
        | exact Hlen | exact Hpos
        | rewrite ralt_dec_enc Hfl fsm_cat; exact Hcon ].
    - iFrame "Hc Hd".
  Qed.

  (* ---- THE REDIRECT CHILD'S LAW (item 2d; it was a section hypothesis at
          a stale twin of [UkShRedirBody.sh_redir_child_law] -- 60 steps
          for 68, no [fline_ok] -- and is a LEMMA at that statement now).

          The walk is [UkShRedirChild.wp_kshm_child_file_redir]; what this
          supplies is the file application's reading of its pieces:
            the lend          [Wcf I 3 = Wcl I 3 ∗ PRE I], OPENED FIRST, so
                              the deed's state is known before the walk is
                              applied -- a tainted PRE does not walk, it
                              hands the run to the generic slot
                              ([UkRun.urun_gen]);
            the line          the fork's words identify it
                              ([FileDisc.fline_ok_redir_words]: the typed
                              line is [LEchoF ws] and the file is `f`);
            the open          [Hopen_hand], the deed its hand, the line's
                              witness from PRE;
            the receipt       read by [redir_K_inum];
            exec /echo        [redir_exec_sup];
            the diagnostics   [UShPanic.ush_diag_law_hold_at_alt] at the
                              alternative the child is in, closed by the
                              three exits above.
          [cons_made] is a PREMISE: the open needs it, /init has it, and
          nothing in the round did (PROGRAM-STREAM stretch 10). ---- *)
  Local Lemma ush_execfail_law_at_wand (dg : list (bv 8)) (n : nat)
      (Cr Cd Cd' : iProp Σ) :
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr Cd -∗
    □ (Cd -∗ Cd') -∗
    UkShDiag.ush_execfail_law_at (PS := uprogSG_free)
      (ghost_varG0 := offbox_offG) dg n Cr Cd'.
  Proof using .
    iIntros "#Hl #Hw". rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct ("Hl" $! N l with "[%] Hc") as (Pf) "(H0 & #Hs & #He)";
      [ exact Hfd | ].
    iExists Pf. iFrame "H0 Hs". iIntros "!> Hp". iApply "Hw". iApply "He".
    iExact "Hp".
  Qed.

  Local Lemma fab_redir_alts (I : list (bv 8)) (ws : wordline) :
    fline I = LEchoF ws ->
    fab I (ralt_enc RFExec) = alt_execfail
    /\ fab I (ralt_enc RFOpenU) = alt_openfail
    /\ fab I (ralt_enc RFOpenM) = alt_openfail.
  Proof using .
    intro Hfl. split_and!;
      (rewrite fab_of_apr;
         [ rewrite ralt_dec_enc Hfl; reflexivity
         | rewrite ralt_dec_enc Hfl; split; [ exact Logic.I | reflexivity ] ]).
  Qed.

  Lemma Hchild_redir :
    ⊢ FileLinks.file_links g -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl g) r jo) -∗
      UkShRedirBody.sh_redir_child_law (PS := uprogSG_free)
        (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG) Wcf.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade". iDestruct "Hmade" as (jo) "#Hmade".
    iPoseProof "Hslot" as "(#Hinv & _ & #Hgen)".
    rewrite /UkShRedirBody.sh_redir_child_law.
    iIntros "!>" (N' h m dw dv sa len ws file fb sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hfok %Hsa %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hwsp Hsy Hstd Hcwd Hch Hpid HM Hcr
       Hrun".
    (* PIPE-PID gave [sh_redir_child_law] the pid row and the empty
       children set; the file era's walk still takes [uch_any] and no pid. *)
    iDestruct (UserChildren.uch_any_of with "Hch") as "Hch". iClear "Hpid".
    pose proof (proj1 Hline) as Hokws.
    (* ---- the line, off the fork's words ---- *)
    assert (Hpos : (0 < nlines I)%nat).
    { destruct (nlines I) as [| k] eqn:Hn; [ | lia ]. exfalso.
      rewrite /last_ws in Hlws. rewrite /nlines in Hn.
      apply nil_length_inv in Hn. rewrite Hn in Hlws. cbn in Hlws.
      destruct ws; discriminate Hlws. }
    assert (Hlb : last_ws I = wl_words (UkSh.ush_lastbody I)).
    { rewrite (last_ws_lastbody I). reflexivity. }
    destruct (FileDisc.fline_ok_redir_words (UkSh.ush_lastbody I) ws file
                Hfok Hokws ltac:(rewrite -Hlb; symmetry; exact Hlws))
      as [Hfl ->].
    change (uline_of (UkSh.ush_lastbody I)) with (fline I) in Hfl.
    destruct (fab_redir_alts I ws Hfl) as (Hax & Hau & Ham).
    (* ---- the lend, opened ---- *)
    rewrite Wcf_S3. iDestruct "Hcr" as "[Hc [Hpre #Hwit]]".
    iAssert (∃ v0 : era_pins, era_pin (fgn_echo g) (S gen_id) v0)%I
      as (v0) "#Hpin0".
    { rewrite /FileLinkInst.file_Wcl_at /lk_lcred.
      iDestruct "Hc" as (v0) "[#Hp _]". iExists v0.
      cbn [lk_pin FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hp". }
    iAssert (□ (app_taint -∗ UkShFork.ushf_wq Wcf I))%I as "#Hkillq".
    { iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Wcf_taint I 0%nat v0 with "Hpin0"). iApply Hktaint.
      iExact "Hk". }
    (* a TAINTED lend does not walk: the run goes to the generic slot *)
    iAssert (□ (∀ W : UexecSlot.uvis,
                  T -∗ ChildTok.my_pay (UexecSlot.uvis_gen W) (ukn_pay N') -∗
                  UexecRet.uslot (SG := uexecSG_xv6) W))%I
      as "#Hgenw".
    { iIntros "!>" (W) "#HT' #Hmy". rewrite Hpeq.
      iApply ("Hgen" $! (UkShFork.ushf_wq Wcf I) W with "HT' Hmy Hkillq"). }
    rewrite {1}/sh_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    iDestruct "Hpre" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs)".
    pose proof Htie as [Hlen Hcon].
    rewrite /line_wit. iDestruct "Hwit" as "[Hwit | #HT]"; last first.
    { iApply (urun_gen (PS := uprogSG_free) (SG := uexecSG_xv6)
                (ghost_varG0 := offbox_offG) N' T h m
                (mword_of_int 0x9c0) _ ltac:(vm_compute; reflexivity)
                with "Hgenw HT Hrun"). }
    pose proof (fline_echof_in I ws Hpos Hfl) as Hinl.
    rewrite /FileLinksLine.flw. iDestruct "Hwit" as "[%Hnil | Hwit]".
    { exfalso. rewrite Hnil in Hinl. by apply elem_of_nil in Hinl. }
    iDestruct "Hwit" as (ls) "[#Hfl %Hall]".
    pose proof (Hall ws Hinl) as Hin.
    iAssert (∀ i : Z, f_typed (fgn_cl g) (Some (i, [])))%I as "#Hty0".
    { iIntros (i). rewrite /f_typed. iExists ls. iFrame "Hfl". iPureIntro.
      exists ws, []. split_and!;
        [ exact Hin | exact Hokws | exact (sel_ok_nil _) | reflexivity ]. }
    (* ---- the fd rows ---- *)
    destruct Hrows as ([wr0 Hr0] & [rb1 Hr1] & Hfd2).
    (* ---- THE WALK ---- *)
    iApply (UkShRedirChild.wp_kshm_child_file_redir (PS := uprogSG_free)
              (SG := uexecSG_xv6) (ghost_varG0 := offbox_offG)
              (fun k H => H) (A := dst) N'
              (ukn_const_of_eq N' _ Hpeq (fun _ _ => eq_refl))
              h m dw dv sa len ws FsImgCheck.fname_f fb sz ld
              _ n
              (fun _ : Z => UkShFork.ushf_wq Wcf I)
              redir_K redir_K' (fun s1 : dst => fown r s1) redir_Kf s
              (Wcl I 3%nat ∗ fown r s)%I (Wcl I 3%nat)
              (Wcf I 0%nat) (Wcf I 0%nat)
              Hpeq Hs1 Hline eq_refl eq_refl Hsa Hs64 Hs38 Hszlo Hszal
              Hszok Hr1 ltac:(discriminate)
              ltac:(intros ? ? ?; discriminate) Hfd2
              ltac:(destruct ld as [| y0 [| y1 l2]];
                    [ discriminate Hr0 | discriminate Hr1 | ];
                    cbn in Hr0; injection Hr0 as ->; reflexivity)
              with "Hcode Hjt Hpcode Hpro Hstr Hwsp Hsy Hstd Hcwd Hch HM
                    [] [] [] [] [] [] [] [] [] [Hc Hd] Hrun").
    - (* the open *)
      iApply (Hopen_hand N' _ _ ls ws jo Hin Hokws with "Hinv Hmade Hfl").
    - (* the receipt, read *)
      iIntros "!>" (ty) "HK".
      iMod (redir_K_inum ty ⊤ ltac:(set_solver) with "Hinv HK") as "[HK Hi]".
      iModIntro. rewrite /redir_K'. iFrame "HK Hi".
    - (* exec /echo at the file *)
      iApply (redir_exec_sup I ws v' cs ls Hfl Hokws Hin Hlen Hpos
                with "Hdep Hslot Hpin' Hcs Hfl").
    - (* exec failed *)
      iIntros (ty).
      iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG) FI
                    (redir_K' ty) I (ralt_enc RFExec) with "[]") as "#Hx".
      { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iExact "Hlk". }
      iEval (cbn [lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; rewrite -fab_lm; rewrite Hax)
        in "Hx".
      iApply (ush_execfail_law_at_wand with "Hx").
      iIntros "!> H". iDestruct "H" as (v) "(#Hp & Hblk & [HK _])".
      rewrite /redir_K /UkFileOpen.redir_K /FileOpen.file_open_fd_K.
      iDestruct "HK" as "[HK | #HT]"; last first.
      { iApply (Wcf_taint I 0%nat v' with "Hpin' HT"). }
      iDestruct "HK" as (i γo) "(_ & Hd & _)".
      iApply (redir_execfail_exit I ws i v v' cs Hfl Hlen Hpos
                with "Hp Hblk Hd Hty0 Hpin' Hcs").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight. iExact "H".
    - (* open failed *)
      rewrite /UkShDiag.ush_execfail_law_at.
      iIntros "!>" (N l) "%Hfd [HK Hc]".
      iAssert (FileLinks.file_links g -∗ lk_links FI)%I as "Hlkw".
      { cbn [lk_links FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]. iIntros "$". }
      iDestruct ("Hlkw" with "Hlk") as "#Hlk'".
      rewrite /redir_Kf. iDestruct "HK" as "[Hd | [[%Hs Hd] | #HT]]".
      + iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r s) I (ralt_enc RFOpenU) with "Hlk'") as "#Hx".
        iEval (cbn [lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; rewrite -fab_lm; rewrite Hau)
          in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd]") as (Pf) "(H0 & #Hs & #He)";
          [ exact Hfd | iFrame "Hc Hd" | ].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd)".
        iApply (redir_openfail_exit_u I ws s v v' cs Hfl Htie Hpos
                  with "Hp' Hblk Hd Hty Hpin' Hcs").
      + iDestruct "Hd" as (i) "Hd".
        iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI (fown r (Some (i, []))) I (ralt_enc RFOpenM)
                      with "Hlk'") as "#Hx".
        iEval (cbn [lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; rewrite -fab_lm; rewrite Ham)
          in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc Hd]") as (Pf) "(H0 & #Hs & #He)";
          [ exact Hfd | iFrame "Hc Hd" | ].
        iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
        iDestruct ("He" with "Hp") as (v) "(#Hp' & Hblk & Hd)".
        iApply (redir_openfail_exit_m I ws i v v' cs Hfl
                  ltac:(rewrite Hs in Htie; exact Htie) Hpos
                  with "Hp' Hblk Hd Hty0 Hpin' Hcs").
      + iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                      (ghost_varG0 := offbox_offG)
                      FI emp%I I (ralt_enc RFOpenU) with "Hlk'") as "#Hx".
        iEval (cbn [lk_ab FileLinkInst.file_link_inst_at FileLinkGen.file_link_gen_at GenLinksLine.gen_link_inst]; rewrite -fab_lm; rewrite Hau)
          in "Hx".
        iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hs & _)";
          [ exact Hfd | iFrame "Hc" | ].
        iExists Pf. iFrame "H0 Hs". iIntros "!> _".
        iApply (Wcf_taint I 0%nat v' with "Hpin' HT").
    - iIntros "!> H". rewrite /UkShFork.ushf_wq. iRight. iExact "H".
    - (* the child died before the open: the lend, whole *)
      iIntros "!> [Hc Hd]". rewrite /UkShFork.ushf_wq. iRight.
      iApply (Hwbl_f I). rewrite Wcf_S3. iFrame "Hc".
      rewrite /sh_pre_at /sh_deed_at /line_wit. iSplitL.
      + iLeft. iExists cs, s, v'. iFrame "Hd Hty Hpin' Hcs". by iPureIntro.
      + iLeft. rewrite /FileLinksLine.flw. iRight. iExists ls.
        iFrame "Hfl". by iPureIntro.
    - iIntros "[$ $]".
    - iFrame "Hc Hd".
  Qed.

  (* ...AND THE DISPATCH ITSELF: the three shapes assembled into the one
     law [UkShFork.ushf_rest_of_body] takes.  The case is PURE -- on
     [FileDisc.uline_of (wl_body (last_ws I))] -- and sh's tag law ties it
     to the line the discipline admitted. *)
  (* ...AND THE ECHO ARM OF IT IS PROVED (the PROGRAM STREAM): the landed
     [UkShFork.ushf_child_law] IS the echo child's law, and at this era it
     is [UkShEcho.ushf_child_law_holds_at] at the era's guard and the
     era's diagnostic -- both of which [file_D] answers.  The three-way
     DISPATCH (the redirect and cat arms) is [UkShRedirBody]'s body law and
     does not come through this name. *)
  (*  ...AND ITS PROOF IS ONE APPLICATION, WHICH DOES NOT ELABORATE (the
      PROGRAM STREAM, and it is the ONLY thing between the metric and 6):

        iPoseProof (Hexecfail with "Hlk") as "#Hxl".
        iPoseProof (Hchild_echo with "Hlk Hdep Hslot") as "#Hsup".
        iApply (UkShEcho.ushf_child_law_holds_at (PS := uprogSG_free)
                  (fun k H => H) file_D (lk_exfb FI)
                  (fun I => (length (lk_exfb FI I) - 2)%nat) Wcf
                  file_D_of_line file_D_exfb with "Hxl Hsup").

      Every premise is in hand -- both laws are PROVED above, at exactly
      the two shapes the lemma takes -- and the application HANGS: twenty
      minutes with no output, with [iApply] and with [iPoseProof] alike,
      and [Local Opaque] on the record literal does not help.  It is the
      fifth silent-hang shape at a size that is not localised yet; what it
      is NOT is a missing fact.  Left as this file's third open proof
      rather than committed red, and it is the next thing this stream
      does. *)
  Lemma sh_child_law_file :
    ⊢ FileLinks.file_links g -∗ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl g) r jo) -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) (SG := uexecSG_xv6) Wcf.
  Proof using Heq Hkill Hcons HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hmade".
    iPoseProof (Hexecfail_D with "Hlk") as "#Hxl".
    iPoseProof (Hchild_echo with "Hlk Hdep Hslot Hmade") as "#Hsup".
    iApply (UkShEcho.ushf_child_law_holds_at_D (PS := uprogSG_free)
              (SG := uexecSG_xv6) (fun k H => H) file_D (lk_exfb FI)
              (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat) Wcf
              file_D_of_line file_D_exfb with "Hxl Hsup").
  Qed.

  (* ...and a KILLED child pays the payload with the taint (the taint
     inhabits the credential AND the deed's arm).  PROVED (the program
     stream): the taint is the era's ([Hktaint]), it inhabits the link
     record's credential at the era's pin ([Hcltaint], which is
     [FileLinkInst.file_Hcltaint] now) and it is every tie's own right
     arm ([Wcf_taint]).  The PIN is a premise because the credential's is linear under
     an existential and the killed child holds none -- the round has it
     ([sh_round_holds_file]'s third argument). *)
  Lemma sh_kill_law_file (v : era_pins) :
    era_pin (fgn_echo g) (S gen_id) v -∗ UkShFork.ushf_kill_law Wcf.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [ iApply Hktaint; iExact "Hk" | ].
    iApply (Wcf_taint I 0%nat v with "Hpin HT").
  Qed.

  (* =================================================================== *)
  (*  S6  THE ROUND -- [UShRest.sh_rest_holds]'s TWIN                     *)
  (*                                                                     *)
  (*  WHAT SH-ROUND MUST DELIVER: the command loop's body obligation at   *)
  (*  the file era's families, which is what [UInitSh.sh_pay_of_parts]    *)
  (*  takes and therefore what K3's [file_prog_law] spends.              *)
  (* =================================================================== *)
  (* PROVED (2026-09-22): one application of [UkShRedirBody.
     ushf_rest_of_body_file] to the five laws above -- the kill law, the
     echo child's, the redirect child's ([Hchild_redir]), cat's
     ([Hchild_cat]) and sh's own fork panic -- exactly as [UShRest.
     sh_rest_holds] is one application of [UkShFork.ushf_rest_of_body] to
     echo's three, and [UShPipeRound.sh_round_holds_pipe] of its twin.
     STATED at [ush_rest_l_at ... ush_line_file] (the era's own three line
     shapes), which is what [UInitSh.sh_pay_of_parts_at] takes; the
     premises are the union of the children's: BOTH slots (echo's for the
     echo and redirect children, cat's for cat's) and [cons_made] (the
     open and cat's read). *)
  Lemma sh_round_holds_file (N : uk_names Σ) :
    ⊢ FileLinks.file_links g -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      UShCatPay.sh_cat_slot T -∗
      (∃ v : era_pins, era_pin (fgn_echo g) (S gen_id) v) -∗
      (∃ jo : option Z, file_cons_cred (fgn_cl g) r jo) -∗
      UkSh.ush_rest_l_at (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
        N γp T Wcf Wbf
        (UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp)
        UkShRedirBody.ush_line_file
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using Hcons Hkill Htag Heq HfifR.
    iIntros "#Hlk #Hdep #Hslot #Hcat #Hpin #Hmade".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (sh_kill_law_file v with "Hp") as "#Hkl".
    iPoseProof (sh_child_law_file with "Hlk Hdep Hslot Hmade") as "#Hchl".
    iPoseProof (Hchild_redir with "Hlk Hdep Hslot Hmade") as "#Hred".
    iPoseProof (Hchild_cat with "Hlk Hdep Hcat Hmade") as "#Hcatl".
    iPoseProof (Hpanic with "Hlk") as "#Hplaw".
    iIntros "!>" (l) "%Hc".
    iPoseProof (UkShRedirBody.ushf_rest_of_body_file
                  (PS := uprogSG_free) (SG := uexecSG_xv6)
                  (ghost_varG0 := offbox_offG) (Hpay := Hc)
                  N γp T Wcf Wbf
                  (UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp)
                  (fun k H => H) (SpecKexec.kexec_sz ElfUser.sh_elf)
                  UShRest.sh_sz_lo UShRest.sh_sz_al UShRest.sh_sz_ok Hwbl_f
                  with "Hkl Hchl Hred Hcatl Hplaw") as "Hb".
    rewrite /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.

End UShRound.
