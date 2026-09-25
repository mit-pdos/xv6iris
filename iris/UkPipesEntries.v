(* ===================================================================== *)
(* UkPipesEntries.v -- THE N-STAGE PIPELINE'S THREE STAGE ENTRIES (design *)
(* claude-notes/design/pipes-general.md SS1.2, SS5 cut C6): echo at the    *)
(* head, a MIDDLE cat, the LAST cat, each an [ExecEntry.image_entry] from *)
(* [UkTreeEntry.echo_image_entry_env_c] / [cat_image_entry_env_c] at the  *)
(* round's ONE instance [UkPipesIface.pipes_iface], with the registry     *)
(* allocated INSIDE the slot ([UexecRet.uslot_bupd]) at the stage's       *)
(* protected devices -- [UkPipeEntries]' moves, one pipe generalised to   *)
(* any stage.  Nothing here is repointed; the landed one-round entries    *)
(* stay (C8 retires them).                                               *)
(*                                                                        *)
(*   [pse_echo_image_entry]  echo at the head: fd 1 the first pipe's write *)
(*                           end ([pipe_env (DOutH [L])], device 0 the     *)
(*                           write end, protected).                        *)
(*   [pse_mid_image_entry]   a middle cat: [copy_env (DCopy flt_id true    *)
(*                           [] L [])]                                     *)
(*                           ([ProgTree.cat_copy_conforms true]): fd 0 the  *)
(*                           input pipe's read end and fd 1 the output     *)
(*                           pipe's write end on the copy device (device   *)
(*                           1, sink [CSPipe]), fd 2 a live console writer *)
(*                           [PDCon w2 A2] owing [alts2] ([[]] and         *)
(*                           [cat_dg_write] among them).                   *)
(*   [pse_last_image_entry]  the last cat: [copy_env (DCopy flt_id false   *)
(*                           [] L [])],                                    *)
(*                           the sink the console writer [CSCon wL] (the   *)
(*                           content source [L]), fd 2 as above.           *)
(*                                                                        *)
(* Each entry's [Pay] is the stage's LEND ([UkPipesIface.pns_echo_lend] /  *)
(* [pns_copy_lend]), stated at the payload [Q] the stage's parent owes:    *)
(* the lend carries the exit wand [pns_xkQ kds Q] from the stage's final  *)
(* device states (or the taint) to [Q (-1)].                               *)
(*                                                                        *)
(* THE LINK TO C3b's STAGE LAWS ([UkShPipesRound.ush_left_law] /           *)
(* [ush_last_law]).  Those laws are sh's [runcmd] on the stage's EXEC     *)
(* leaf at the child's ledger -- [<[1 := wr gp]> (<[0 := st0]> ld0)] for *)
(* a left stage, [<[0 := rd gp]> ld0] for the last -- holding the lend    *)
(* [RcL k st0 gp] / [RcR k st0 gp] and owing [Qc k st0], constant in the  *)
(* status ([HQc]).  The entries here are what the EXEC ARM of that walk    *)
(* consumes, at [Q := Qc k st0] and [Pay := the lend] (existential in the *)
(* pipe's protocol names, [pse_image_entry_ex]): at a left stage [k = 0]  *)
(* [RcL 0 st0 gp := ∃ pn, pns_echo_lend .. pn gp (Qc 0 st0)] (fd 1 is     *)
(* [wr gp], so [take NSTD sts !! 1 = Some (FdOpen false true (FdPipe gp))] *)
(* is the entry's row); at a left stage [k > 0], whose [st0] is the       *)
(* previous pipe's read end [rd gin], [RcL k (rd gin) gp := ∃ pin w2 A2    *)
(* alts2 pn, pns_copy_lend .. pin gin (CSPipe pn gp) (Qc k (rd gin))];    *)
(* the last stage's [RcR k st0 gp := ∃ pin w2 A2 alts2 wL,                 *)
(* pns_copy_lend .. pin gp (CSCon wL) (Qc k st0)], its fd 1 and fd 2 the   *)
(* console rows of [ld0].  THE GAP to a discharge (C7): the stage laws are *)
(* discharged today only at the taint ([UkShPipesRound]'s section 3,       *)
(* through [UkShDiag.wp_kshr_runcmd_final] at [ush_rstage_simple]); a      *)
(* PAYING instance needs the stage record whose exec-success arm is these  *)
(* entries and whose exec-failure arm prints [exec cat failed] as the     *)
(* family writer [WLeft k] (a kit and a deposit for [dg_execR] in [RcL]), *)
(* and the round's [urun_nopipe] rows for the pipe ends.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import FdSlots ProcGeom UserFd UserCwd UserHeap.
Require Import UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import LineWords LineBytes EchoDisc ExecWords.
Require Import EchoOut AppEcho.
Require Import LineModel LineModelLinks.
Require Import PipeOut.
Require Import PipesDisc PipeBothNPure PipeBothN GenOut PipeOutN PipesView.
Require Import PipeNames PipeProto.
Require Import AppCfg AppInv.
Require Import CtxIdDefs.
Require Import ExecArgs ExecEntry.
Require Import ElfFile ElfUser.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Require Import UkHandler.
Require Import UkShMain UkShEcho UShEcho UkShCat.
Require Import UkTreeEntry.
Require Import UkPipesIface.
Local Open Scope Z_scope.
(* THE PURE ARGV BRIDGES (moved from the one-pipe [UkPipeEntries], cut C8) *)
(* the words' line after the command fits a C int *)
Lemma pe_line_len (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31.
Proof using .
  intros Hok. pose proof (EchoDisc.line_ok_len ws Hok) as Hl.
  unfold EchoDisc.line_max in Hl.
  assert (Hcons : forall (w : list (bv 8)) (r : list (list (bv 8))),
             (length (wl_line r) <= length (wl_line (w :: r)))%nat).
  { intros w r. rewrite !wl_line_length wl_body_cons length_app.
    destruct r as [| w' r'].
    - cbn. lia.
    - rewrite wl_tail_cons. cbn [length]. lia. }
  assert (Hle : (length (wl_line (drop 1 ws)) <= length (wl_line ws))%nat).
  { destruct ws as [| w r]; [reflexivity |].
    replace (drop 1 (w :: r)) with r by reflexivity. apply Hcons. }
  lia.
Qed.

Lemma pe_drop1_ne (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> drop 1 ws <> [].
Proof using .
  intros Hok Hd. pose proof (EchoDisc.line_ok_ge2 ws Hok) as H2.
  apply (f_equal length) in Hd. rewrite length_drop in Hd. cbn in Hd. lia.
Qed.

(* THE LANDED CAT ENTRY'S ARGV, READ AS THE TREE ENTRY'S: the token
   [(a, b)] of sh's node is the one-word line [[cmd_cat]] at the string's
   own address.  The word-list reading bounds the node's two addresses by
   [2 ^ 38]; the landed one by the machine word, so the bound is a premise. *)
Lemma pe_cat_1w_args (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
    (gn : nat -> bv 8) :
  0 < t < 2 ^ 38 ->
  0 < sv + Z.of_nat a < 2 ^ 38 ->
  UkShCat.cat_argv_bytes a b gn ->
  uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
  exec_ok [UkShCat.cmd_cat]
  /\ UShEcho.echo_node_img [UkShCat.cmd_cat] Mn (sv + Z.of_nat a) t
       (fun j : nat => gn (a + j)%nat)
  /\ UkShEcho.echo_argv_bytes [UkShCat.cmd_cat] (fun j : nat => gn (a + j)%nat).
Proof using .
  intros Ht Hs Hbytes Himg.
  pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
  destruct Hbytes as (_ & Hin & Hnul).
  rewrite UkShCat.cmd_cat_len in Hin.
  pose proof (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) as Hlk.
  destruct Himg as (_ & _ & _ & Hptr & Hterm & Hrow).
  assert (Hoff : UkShEcho.echo_off [UkShCat.cmd_cat] 0 = 0%nat) by reflexivity.
  assert (Halen : UkShEcho.echo_alen [UkShCat.cmd_cat] 0 = 3%nat)
    by exact UkShCat.cmd_cat_len.
  split_and!.
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - rewrite /UShEcho.echo_node_img. cbn [length]. split_and!.
    + lia.
    + lia.
    + intros i Hi. assert (i = 0%nat) as -> by lia. rewrite Hoff. lia.
    + intros i Hi k Hk. assert (i = 0%nat) as -> by lia. rewrite Hoff.
      pose proof (Hptr 0%nat _ Hlk k Hk) as Hp.
      cbn [UserHeap.ua_ptr] in Hp. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
    + intros k Hk. pose proof (Hterm k Hk) as Hp.
      rewrite UkShMain.ush_args_length in Hp. exact Hp.
    + intros i Hi j Hj. assert (i = 0%nat) as -> by lia.
      rewrite Halen in Hj. rewrite ?Hoff.
      pose proof (Hrow 0%nat _ Hlk j ltac:(cbn [UserHeap.ua_len]; lia)) as Hp.
      cbn [UserHeap.ua_ptr UserHeap.ua_bytes] in Hp. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
    + intros i Hi. assert (i = 0%nat) as -> by lia. rewrite ?Hoff ?Halen.
      pose proof (Hrow 0%nat _ Hlk 3%nat ltac:(cbn [UserHeap.ua_len]; lia)) as Hp.
      cbn [UserHeap.ua_ptr UserHeap.ua_bytes] in Hp.
      rewrite <- Hnul, Hb3. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
  - split.
    + intros i j Hi Hj. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
      rewrite Halen in Hj. rewrite ?Hoff. cbn [Nat.add].
      rewrite (Hin j Hj).
      do 3 (destruct j as [| j]; [reflexivity |]). lia.
    + intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
      rewrite ?Hoff ?Halen. cbn [Nat.add]. rewrite <- Hb3. exact Hnul.
Qed.


Import Defs.

(* ===================================================================== *)
(*  1.  THE PROTECTED DEVICES' LISTS                                      *)
(* ===================================================================== *)

Lemma pse_nodup0 (x : pdev) : stdpp.base.NoDup ([(0%nat, x)].*1).
Proof using . cbn. apply NoDup_singleton. Qed.

Lemma pse_nodup01 (x y : pdev) : stdpp.base.NoDup ([(0%nat, x); (1%nat, y)].*1).
Proof using . cbn. apply NoDup_cons_2; [set_solver | apply NoDup_singleton]. Qed.

Lemma pse_dp0 (x : pdev) : dp_in ([(0%nat, x)].*1) {[0%nat]}.
Proof using . intros d Hd. cbn in Hd. apply elem_of_list_singleton in Hd as ->. set_solver. Qed.

Lemma pse_dp01 (x y : pdev) : dp_in ([(0%nat, x); (1%nat, y)].*1) {[0%nat; 1%nat]}.
Proof using .
  intros d Hd. cbn in Hd. apply elem_of_cons in Hd as [-> | Hd]; [set_solver |].
  apply elem_of_list_singleton in Hd as ->. set_solver.
Qed.

(* ===================================================================== *)
(*  2.  THE ENTRIES                                                       *)
(* ===================================================================== *)

Section UkPipesEntries.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  (* [UkPipesIface]'s pin of the family's cursor camera *)
  #[local] Existing Instance eo_turn | 0.

  (* THE ROUND ([UkPipesIface]'s section context, name for name) *)
  Context (g : pipe_gn).
  Context (LM : lmodel) (PV : pview LM) (CP : gen_cparams LM) (sd : lm_st LM).
  Context (WA : gen_wa LM CP sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT CP).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g LM CP sd WA).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Hypothesis Hsup : ⊢ □ (T -∗ app_sup).
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st LM) (lR : pline').
  Hypothesis HlR : pv_line PV (lineV LM I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc PV sR).
  Context (Hadmit : pns_admV PV lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)) (HL31 : pns_short L).
  Context (TERM : wid -> list (bv 8) -> bool)
          (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop).
  Context (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s)).
  Context (γc γm : wid -> gname).

  Local Instance pse_cat_code_persistent (N' : uk_names Σ) :
    Persistent (up_code (cat_prog N')).
  Proof using . simpl. apply _. Qed.
  Local Instance pse_echo_code_persistent (N' : uk_names Σ) :
    Persistent (up_code (echo_prog N')).
  Proof using . simpl. apply _. Qed.

  (* THE INSTANCE AT THE MINTED RECORD, at a registry and its protected
     devices *)
  Definition pse_iface_cat (γreg : gname) (kds : list (nat * pdev))
      (Hkds : stdpp.base.NoDup kds.*1) (N' : uk_names Σ) (HNc : ukn_const N') :
      ep_ifaceP (Dp := kds.*1) N' (cat_prog N') :=
    pipes_iface g LM PV CP sd WA Hext Hcons Hkill v I sR lR HlR Hfc Hadmit Hplok L HL31 TERM TOK dep dep_tl
      γc γm N' (cat_prog N') (HNc := HNc)
      (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
      (cat_stub_close N') (cat_stub_exit N') γreg kds Hkds.

  Definition pse_iface_echo (γreg : gname) (kds : list (nat * pdev))
      (Hkds : stdpp.base.NoDup kds.*1) (N' : uk_names Σ) (HNc : ukn_const N') :
      ep_ifaceP (Dp := kds.*1) N' (echo_prog N') :=
    pipes_iface g LM PV CP sd WA Hext Hcons Hkill v I sR lR HlR Hfc Hadmit Hplok L HL31 TERM TOK dep dep_tl
      γc γm N' (echo_prog N') (HNc := HNc)
      (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
      (echo_stub_close N') (echo_stub_exit N') γreg kds Hkds.

  (* ------------------------------------------------------------------- *)
  (*  2a. ECHO AT THE HEAD                                                *)
  (* ------------------------------------------------------------------- *)
  Lemma pse_echo_image_entry (ws : list (list (bv 8))) (M : gmap Z (bv 8)) (s0 t : Z)
      (gb : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (rb : bool) (Q : Z -> iProp Σ) (pn : pnames) (gp : pipe_names) :
    (forall x y : Z, Q x = Q y) ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdPipe gp)) ->
    L = wl_line (drop 1 ws) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q (pns_echo_lend LM CP L γc γm pn gp Q) uslot.
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hkill Hplok TERM TOK dep_tl pnsRegG0 ufdG0 v.
    intros HQc Hok Hnode Hab Hfdl Hl1 HLw.
    iIntros "#Hnpw #Hdep".
    set (wv := fun _ : nat => PDWr pn gp).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hokk %Hcw %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (pns_reg_alloc wv) as (γreg) "Hpool". iModIntro.
    set (If := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                 pse_iface_echo γreg [(0%nat, PDWr pn gp)] (pse_nodup0 _) N'
                   (ukn_const_of_eq N' Q Hpq HQc)).
    assert (Hc : conforms (pipe_env (DOutH [L]) (fun _ => None)) (echo_tree ws)).
    { rewrite HLw. exact (echo_pipe_conforms ws _ (pe_drop1_ne ws Hok) (pe_line_len ws Hok)). }
    iPoseProof (echo_image_entry_env_c (PS := PS) ws M s0 t gb sts cw cs pidv Q
                  (own γreg (pns_pool ∅ wv) ∗ pns_echo_lend LM CP L γc γm pn gp Q)%I
                  If (pipe_env (DOutH [L]) (fun _ => None)) {[0%nat]}
                  Hok Hnode Hab Hfdl Hc (echo_tree_safe _ _) (pse_dp0 _)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd _ [Hpool Hlend]".
      rewrite /If /pse_iface_echo.
      iEval (rewrite -Hpq) in "Hlend".
      iApply (pns_echo_env_res g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31
                TERM TOK dep dep_tl γc γm N' (echo_prog N')
                (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                (echo_stub_close N') (echo_stub_exit N') γreg _ (pse_nodup0 _)
                pn gp (take NSTD sts) rb wv (fun _ => None) eq_refl eq_refl Hl1
                with "Hstd Hpool Hlend"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hokk | exact Hcw | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2b. A COPY STAGE (the middle cat, the last cat): one proof, the      *)
  (*      sink a parameter                                                *)
  (* ------------------------------------------------------------------- *)
  Lemma pse_copy_image_entry (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32) (Q : Z -> iProp Σ)
      (w2 : wid) (A2 alts2 : list (list (bv 8))) (pin : pnames) (gin : pipe_names)
      (sk : csink) (wb rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    0 < t < 2 ^ 38 ->
    0 < sv + Z.of_nat a < 2 ^ 38 ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    take NSTD sts !! 0%nat = Some (FdOpen true wb (FdPipe gin)) ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (pns_sink_ty sk)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    [] ∈ alts2 -> (pns_sink_h sk = true -> cat_dg_write ∈ alts2) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (pns_copy_lend g LM PV CP v I sR lR L TERM TOK dep γc γm w2 A2 alts2 pin gin FCat sk Q) uslot.
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hkill Hplok dep_tl pnsRegG0 ufdG0.
    intros HQc Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hnil Hdg.
    destruct (pe_cat_1w_args a b Mn sv t gn Ht Hs Hbytes Himg) as (Hok & Hnode & Hab).
    iIntros "#Hnpw #Hdep".
    set (wv := fun d : nat => match d with O => PDCon w2 A2 | S _ => PDCopy (pin, gin) FCat sk end).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hokk %Hcw %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (pns_reg_alloc wv) as (γreg) "Hpool". iModIntro.
    set (If := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                 pse_iface_cat γreg [(0%nat, PDCon w2 A2); (1%nat, PDCopy (pin, gin) FCat sk)]
                   (pse_nodup01 _ _) N' (ukn_const_of_eq N' Q Hpq HQc)).
    iPoseProof (cat_image_entry_env_c (PS := PS) [UkShCat.cmd_cat] Mn (sv + Z.of_nat a) t
                  (fun j : nat => gn (a + j)%nat) sts cw cs pidv Q
                  (own γreg (pns_pool ∅ wv)
                   ∗ pns_copy_lend g LM PV CP v I sR lR L TERM TOK dep γc γm w2 A2 alts2 pin gin FCat sk Q)%I
                  If (copy_env (DCopy flt_id (pns_sink_h sk) [] L []) alts2 (fun _ => None) [])
                  {[0%nat; 1%nat]}
                  Hok Hnode Hab Hfdl
                  (cat_copy_conforms (pns_sink_h sk) L alts2 (fun _ => None) [] Hnil Hdg)
                  (cat_tree_safe _ _) (pse_dp01 _ _)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd _ [Hpool Hlend]".
      rewrite /If /pse_iface_cat.
      iEval (rewrite -Hpq) in "Hlend".
      iApply (pns_copy_env_res g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31
                TERM TOK dep dep_tl γc γm N' (cat_prog N')
                (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                (cat_stub_close N') (cat_stub_exit N') γreg _ (pse_nodup01 _ _)
                w2 A2 alts2 pin gin FCat sk (take NSTD sts) wb rb1 rb2 wv (fun _ => None)
                eq_refl eq_refl eq_refl Hl0 Hl1 Hl2
                with "Hstd Hpool Hlend"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hokk | exact Hcw | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* THE MIDDLE CAT: the sink the next pipe's write end ([h = true]), fd 2
     owing [cat_dg_write] among its alternatives *)
  Lemma pse_mid_image_entry (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32) (Q : Z -> iProp Σ)
      (w2 : wid) (A2 alts2 : list (list (bv 8))) (pin : pnames) (gin : pipe_names)
      (pn : pnames) (gp : pipe_names) (wb rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    0 < t < 2 ^ 38 ->
    0 < sv + Z.of_nat a < 2 ^ 38 ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    take NSTD sts !! 0%nat = Some (FdOpen true wb (FdPipe gin)) ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdPipe gp)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    [] ∈ alts2 -> cat_dg_write ∈ alts2 ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (pns_copy_lend g LM PV CP v I sR lR L TERM TOK dep γc γm w2 A2 alts2 pin gin FCat (CSPipe pn gp) Q)
      uslot.
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hkill Hplok dep_tl pnsRegG0 ufdG0.
    intros HQc Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hnil Hdg.
    exact (pse_copy_image_entry a b Mn sv t gn sts cw cs pidv Q w2 A2 alts2 pin gin
             (CSPipe pn gp) wb rb1 rb2 HQc Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hnil
             (fun _ => Hdg)).
  Qed.
  (* THE LAST CAT, fd 2 MUTE (lane PIPES-C7): [pse_last_image_entry] with
     the registry's device 0 [PDMute] -- the last stage's diagnostics are
     no writer of the model's, so the only console writer it holds is the
     sink's [wL] *)
  Lemma pse_last_image_entry_m (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32) (Q : Z -> iProp Σ)
      (pin : pnames) (gin : pipe_names) (wL : wid) (wb rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    0 < t < 2 ^ 38 ->
    0 < sv + Z.of_nat a < 2 ^ 38 ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    take NSTD sts !! 0%nat = Some (FdOpen true wb (FdPipe gin)) ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (pns_copy_lend_m g LM PV CP v I sR lR L TERM TOK dep γc γm pin gin FCat (CSCon wL) Q) uslot.
  Proof using HL31 Hadmit Hcons Hext Hsup HlR Hfc Hkill Hplok dep_tl pnsRegG0 ufdG0.
    intros HQc Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2.
    destruct (pe_cat_1w_args a b Mn sv t gn Ht Hs Hbytes Himg) as (Hok & Hnode & Hab).
    iIntros "#Hnpw #Hdep".
    set (wv := fun d : nat => match d with O => PDMute | S _ => PDCopy (pin, gin) FCat (CSCon wL) end).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hokk %Hcw %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (pns_reg_alloc wv) as (γreg) "Hpool". iModIntro.
    set (If := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                 pse_iface_cat γreg [(0%nat, PDMute); (1%nat, PDCopy (pin, gin) FCat (CSCon wL))]
                   (pse_nodup01 _ _) N' (ukn_const_of_eq N' Q Hpq HQc)).
    iPoseProof (cat_image_entry_env_c (PS := PS) [UkShCat.cmd_cat] Mn (sv + Z.of_nat a) t
                  (fun j : nat => gn (a + j)%nat) sts cw cs pidv Q
                  (own γreg (pns_pool ∅ wv)
                   ∗ pns_copy_lend_m g LM PV CP v I sR lR L TERM TOK dep γc γm pin gin FCat (CSCon wL) Q)%I
                  If (copy_env (DCopy flt_id false [] L []) [[]] (fun _ => None) [])
                  {[0%nat; 1%nat]}
                  Hok Hnode Hab Hfdl
                  (cat_copy_conforms false L [[]] (fun _ => None) []
                     (elem_of_list_here _ _) (fun Hf => match Bool.diff_false_true Hf with end))
                  (cat_tree_safe _ _) (pse_dp01 _ _)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd _ [Hpool Hlend]".
      rewrite /If /pse_iface_cat.
      iEval (rewrite -Hpq) in "Hlend".
      iApply (pns_copy_env_res_m g LM PV CP sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31
                TERM TOK dep dep_tl γc γm N' (cat_prog N')
                (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                (cat_stub_close N') (cat_stub_exit N') γreg _ (pse_nodup01 _ _)
                pin gin FCat (CSCon wL) (take NSTD sts) wb rb1 rb2 wv (fun _ => None)
                eq_refl eq_refl eq_refl Hl0 Hl1 Hl2
                with "Hstd Hpool Hlend"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hokk | exact Hcw | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.
End UkPipesEntries.
