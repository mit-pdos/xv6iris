(* ===================================================================== *)
(*  UnionReadInstAt.v -- THE UNION ERA'S READ RECORD AT THE ROUND'S BOOT  *)
(*  STATE, AND SH'S READ LEAF AT IT (cut C9g; design:                     *)
(*  claude-notes/design/union.md section 4).                              *)
(*                                                                        *)
(*  [FileReadInst.file_read_inst_at] at the union.  The round is stated   *)
(*  at [UnionLinkInstAt.union_link_inst_at ug s0]; its links, pin,        *)
(*  receipt, taint and reader's residue are the unindexed record's terms  *)
(*  ([urresw] names no boot state), so the read record at the index is    *)
(*  [UnionReadInst.union_read_inst] with every field [change]d to the     *)
(*  unindexed spelling -- a bridge and not a second proof.                 *)
(*                                                                        *)
(*  Beside it, the tag's reading at the union discipline: a disciplined   *)
(*  history never ends in ^D, so [UkSh.ush_tag_law] holds at the union's  *)
(*  tag [UnionOut.utag].                                                   *)
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
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOut.
Require Import LineModel.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import UnionLinkInstAt.
Require Import UnionReadInst.
Require Import LinkRec.
Require Import ReadRec.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import ConsoleInv.
Require Import WpUart.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UkRun.
Require Import UexecExecInst.
Require Import AppInv.
Require Import FsCfg.
Require Import PipeOut.            (* [cs_frozen_at_lb_absurd] *)
Require Import PipeOutW.           (* [secc_tok_at] *)
Require Import GenOutWild.         (* [lm_stored_wild_undisc] *)
Require Import UserConsole.
Require Import UkSh.
Require Import UShLine.
Require Import CtxIdDefs.
Local Open Scope list_scope.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  0.  A UNION-DISCIPLINED HISTORY NEVER ENDS IN ^D                      *)
(* ===================================================================== *)
Lemma union_disc_no_ctrl_d (h : list mobs) (b : bv 8) :
  obs_ends_in Uart0 h b -> bv_unsigned (cons_xlate b) = 4%Z -> lm_disc U h -> False.
Proof using.
  intros [h0 ->] Hx Hd.
  assert (Hb : bv_unsigned b = 4%Z).
  { destruct (decide (b = (mword_of_int 13%Z : mword 8))) as [-> | Hne].
    - rewrite cons_xlate_cr in Hx. vm_compute in Hx. discriminate Hx.
    - rewrite (cons_xlate_other b Hne) in Hx. exact Hx. }
  destruct (UkSh.ush_cycles_snoc_in h0 b) as (s0 & Hin).
  apply elem_of_list_In in Hin.
  pose proof (proj1 (Forall_forall _ _) Hd _ Hin) as (s & _ & Hseg & _).
  rewrite ins_app ins_in in Hseg.
  assert (Hin' : b ∈ ins s0 ++ [b]).
  { apply elem_of_app. right. by apply elem_of_list_singleton. }
  pose proof (lm_disc_input_byte_val U (ulm_byte_laws adm_u_g adm_s_on) (ins s0 ++ [b]) b
                Hseg Hin') as Hv.
  lia.
Qed.

(* ===================================================================== *)
(*  1.  THE READ RECORD AT THE INDEX                                      *)
(* ===================================================================== *)
Section union_read_inst_at.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId}.
  Context `{FSC : fscfg}.
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = utag ug).
  Context (s0 : fstate).

  Local Notation UI := (union_link_inst ug).
  Local Notation UIs := (union_link_inst_at ug s0).
  Local Notation UR := (union_read_inst ug Htag).

  (* each field [change]d to the unindexed record's spelling first: the two
     records are different terms whose projections agree, and unifying the
     whole entailment would try [UIs =?= UI] field by field *)
  Local Lemma uria_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ lk_links UIs -∗ lk_pin UIs k v -∗ dl_cnt v (1/2) n -∗
      (lk_rr UIs k v n ws -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Htag xv6G0.
    change (lk_links UIs) with (lk_links UI).
    change (lk_pin UIs k v) with (lk_pin UI k v).
    change (lk_rr UIs k v n ws) with (lk_rr UI k v n ws).
    exact (rk_rd UI UR k n v ws Φ).
  Qed.

  Local Lemma uria_rd_taint (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) :
    ⊢ lk_links UIs -∗ lk_T UIs -∗ (lk_T UIs -∗ Φ) -∗
      cons_link Uart0 (S gen_id) (ConsLog.EvRead ws) Φ.
  Proof using Htag xv6G0.
    change (lk_links UIs) with (lk_links UI).
    change (lk_T UIs) with (lk_T UI).
    exact (rk_rd_taint UI UR ws Φ).
  Qed.

  Local Lemma uria_arms (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ lk_epin UIs (S gen_id) v -∗ inp_lb v I -∗ lk_rres UIs v I -∗
      lk_rr UIs (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow fsc_cons False sl dd dc -∗
      ucons_stored_lb fsc_cons sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜lm_disc_input U (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ lk_rres UIs v (I ++ J))
      ∨ lk_T UIs.
  Proof using Htag xv6G0.
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    change (lk_epin UIs) with (lk_epin UI).
    change (lk_rres UIs) with (lk_rres UI).
    change (lk_rr UIs) with (lk_rr UI).
    change (lk_T UIs) with (lk_T UI).
    change (lm_disc_input U) with (rk_disc UI UR).
    exact (rk_arms UI UR v I ws sl sl' hs dd dc g0 Hddc Hlws Hwinf Hpre2 Hwsj).
  Qed.

  Definition union_read_inst_at : ReadRec UIs :=
    MkReadRec UIs (lm_disc_input U) uria_rd uria_rd_taint uria_arms.

  Lemma union_read_inst_at_disc : rk_disc UIs union_read_inst_at = lm_disc_input U.
  Proof using . reflexivity. Qed.
End union_read_inst_at.

(* ===================================================================== *)
(*  2.  SH'S READ LEAF AT THE INDEXED RECORD, AND THE TAG'S READING        *)
(* ===================================================================== *)
Section union_read_leaf_at.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG] BINDER ([UShRound]'s header): the loop's leaf is read
     at the kernel's own instance, the one the round is pinned at *)
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = utag ug).
  Context (s0 : fstate).

  Local Notation UIs := (union_link_inst_at ug s0).
  Local Notation UT := (file_taint (fgn_cl gf)).

  (* the record's pin names the era: at the era's own number it is the
     echo-side pin *)
  Lemma union_pin_refl_at (v : era_pins) :
    ⊢ era_pin (fgn_echo gf) (S gen_id) v -∗ lk_pin UIs (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma union_ep_refl_at (v : era_pins) :
    ⊢ era_pin (fgn_echo gf) (S gen_id) v -∗ lk_epin UIs (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  (* THE MARKED ARM'S LAW AT THE UNION (seccomp design 10.12, lane S5b).
     The dirty credential is the supply (the taint, as ever) or the era's
     reader-side wild credential [UnionOut.urdwild]: the token at its line
     [I0] and the reader's position there.  Against a read at [I] whose
     receipt took a byte stored at [p >= length I]:
     - the residue's own line is the [seccomp x] line ([uwild_at I]): the
       residue keeps its newline's stored position ([uring_at I]), the byte
       sits past it in the same stored order, so its push trace strictly
       extends the newline's and D4 refutes its tag's discipline
       ([GenOutWild.lm_stored_wild_undisc]); the tag's other half is [UT];
     - it is not: the position bound puts [I0] at or below [I]; equal is
       the wild line itself, and strictly below is refuted by the token's
       frozen choice list against the residue's ([cs_frozen_at_lb_absurd],
       [uwild_read_absurd]'s argument). *)
  Lemma union_dirty_law
      (Hstw : ⊢ app_sup -∗ UT)
      (Hrdw : @riscv_rdwild Σ (@riscv_fixedGS Σ _) = urdwild ug) :
    UShLine.ush_dirty_law UIs (fgn_echo gf).
  Proof using Htag.
    intros I v sl p h b Hch Hp Hsl Hend Hbt.
    iIntros "#Hsl #Htag #Hpin #HE #Hres Hrp #Hdirty".
    cbn [lk_T lk_rres union_link_inst_at gen_link_inst].
    iEval (rewrite Htag /utag) in "Htag".
    iDestruct "Htag" as "(%Hsh & #Hd & _)".
    iDestruct "Hd" as "[%Hdisc | #HT]"; [| iExact "HT"].
    rewrite /cons_dirty_cred /app_rdcred.
    iDestruct "Hdirty" as "#[Hs | Hw]"; [iApply Hstw; iExact "Hs" |].
    iEval (rewrite Hrdw /urdwild) in "Hw".
    iDestruct "Hw" as (I0 v1) "(#Htok & %Hwl & #Hpin1 & #Hlb)".
    iDestruct (era_pin_agree with "Hpin Hpin1") as %<-.
    iDestruct (rpos_lb_le with "Hrp Hlb") as %Hle.
    iEval (rewrite /usecc_tok_at /secc_tok_at) in "Htok".
    iDestruct "Htok" as (v0) "(#Hp0 & _ & #HI0 & %Hn0 & #Hfz & _)".
    iDestruct (era_pin_agree with "Hpin Hp0") as %<-.
    destruct Hn0 as (Hpos0 & Hr0 & _).
    assert (Hne0 : I0 <> []) by (intros ->; rewrite nlines_nil in Hpos0; lia).
    iDestruct (inp_lb_cmp v I0 I with "HI0 HE") as %Hcmp.
    assert (Hdec : Decision (uwild_at I)) by (rewrite /uwild_at; apply _).
    destruct (decide (uwild_at I)) as [Hwa | Hnwa].
    - (* THE RESIDUE'S OWN LINE IS THE SECCOMP LINE: its newline's stored
         position, and the byte past it *)
      rewrite /urresw. iDestruct "Hres" as "(_ & _ & Hwt)".
      iDestruct ("Hwt" with "[%]") as "[[_ Hring] | #HT]"; [exact Hwa | | iExact "HT"].
      rewrite /uring_at. iDestruct "Hring" as (sl' h0) "[#Hsl' %Hr]".
      destruct Hr as (Hsl0 & Hins & Hb0).
      destruct Hwa as (HneI & HrI & HwI).
      assert (HposI : (0 < length I)%nat) by (destruct I; [done | cbn; lia]).
      iAssert (⌜sl !! (length I - 1)%nat = Some (h0, wl_nl)⌝)%I as %Hsln.
      { rewrite /ucons_stored_lb.
        iDestruct (own_valid_2 with "Hsl Hsl'") as %Hcmp2%mono_list_lb_op_valid_L.
        iPureIntro. destruct Hcmp2 as [Hpx | Hpx].
        - assert (Hlt : (length I - 1 < length sl)%nat)
            by (apply lookup_lt_Some in Hsl; lia).
          destruct (lookup_lt_is_Some_2 sl (length I - 1)%nat Hlt) as [x Hx].
          pose proof (prefix_lookup_Some _ _ _ _ Hx Hpx) as Hx'.
          rewrite Hsl0 in Hx'. injection Hx' as ->. exact Hx.
        - exact (prefix_lookup_Some _ _ _ _ Hsl0 Hpx). }
      iExFalso. iPureIntro.
      apply (lm_stored_wild_undisc U sl (length I - 1)%nat p h0 h wl_nl b I Hch Hsln
               ltac:(lia) Hsl Hend ltac:(by rewrite Hins) HneI HrI (uwild_wild _ HwI)
               Hsh ltac:(by rewrite Hbt Hb0) Hdisc).
    - (* IT IS NOT: the position bound puts the token's line at or below
         the reader's; at it is the wild line, below it the frozen list *)
      iExFalso.
      assert (HI0I : I0 `prefix_of` I).
      { destruct Hcmp as [Hc | Hc]; [exact Hc |].
        assert (I = I0) as -> by (apply prefix_length_eq; [exact Hc | lia]). done. }
      destruct HI0I as [z Hz].
      destruct z as [| x z].
      { rewrite app_nil_r in Hz. subst I. exfalso. apply Hnwa.
        split_and!; [exact Hne0 | exact Hr0 | exact Hwl]. }
      rewrite /urresw /gwc_rres. iDestruct "Hres" as "(Hrr & _ & _)".
      iDestruct "Hrr" as (ps0 cs0 s1) "(%Hrd & _ & _ & #Hcs0 & _)".
      destruct Hrd as (_ & _ & _ & Hlen).
      assert (Hrl : I0 `prefix_of` removelast I).
      { subst I. rewrite removelast_app; [| discriminate]. by eexists. }
      pose proof (nlines_prefix _ _ Hrl) as Hnl.
      iApply (cs_frozen_at_lb_absurd v (nlines I0 - 1)%nat cs0 ltac:(lia) with "Hfz Hcs0").
  Qed.

  Lemma union_read_leaf_holds_at (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T UIs)
          (UShLine.ush_rd_x_at (lk_rres UIs) (fgn_echo gf) Wb) ->
    (⊢ app_sup -∗ lk_T UIs) ->
    (⊢ lk_T UIs -∗ app_rdcred) ->
    (@riscv_rdwild Σ (@riscv_fixedGS Σ _) = urdwild ug) ->
    (⊢ lk_links UIs) ->
    ⊢ UkSh.ush_read_recv_leaf_at (PS := uprogSG_free) N γp (lk_T UIs)
        (UShLine.ush_mid_at (lk_rres UIs) (fgn_echo gf) γp) (lm_disc_input U)
        fsc_cons l.
  Proof using Htag.
    intros Hpeq Hstw Htsw Hrdw Hlk.
    iApply (UShLine.ush_read_recv_leaf_holds_at (union_read_inst_at ug Htag s0)
              (fgn_echo gf) Wb N γp l Hpeq Htsw (union_dirty_law Hstw Hrdw)
              (fun v => union_pin_refl_at v) Hlk).
  Qed.

  (* THE TAG'S READING at the union discipline *)
  Lemma union_tag_law_at :
    ⊢ UkSh.ush_tag_law_at UT (lm_disc U).
  Proof using Htag.
    rewrite /UkSh.ush_tag_law_at. iIntros "!>" (h) "Hr".
    rewrite Htag /utag. iDestruct "Hr" as "(_ & Hd & _)". iExact "Hd".
  Qed.

  Lemma union_tag_law_holds : ⊢ UkSh.ush_tag_law UT.
  Proof using Htag.
    iApply (UkSh.ush_tag_law_of_at UT (lm_disc U) union_disc_no_ctrl_d).
    iApply union_tag_law_at.
  Qed.
End union_read_leaf_at.
