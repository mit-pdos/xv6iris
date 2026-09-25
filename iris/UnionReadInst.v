(* ===================================================================== *)
(*  UnionReadInst.v -- THE UNION ERA'S READ RECORD (cut C9e'; design:     *)
(*  claude-notes/design/union.md section 3).                              *)
(*                                                                        *)
(*  [FileReadInst.file_read_inst] at the union: the discipline is the     *)
(*  union model's [lm_disc_input ulmU], the read link is                  *)
(*  [UnionLinks.union_read_link], and the WINDOW ARM reads the receipt    *)
(*  [UnionLinks.uread_ret] into the record's residue [urresw] -- the      *)
(*  generic cursor bounds and the TYPED LINES' WITNESS                    *)
(*  [FileLinksLine.flw], read off the last consumed byte's TAG            *)
(*  ([UnionOut.utag]: the ledger's line list's lower bound).              *)
(*                                                                        *)
(*  Only the record: sh's read leaf at it is the union round's (C9f).     *)
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
Require Import EchoOutPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.
Require Import FileLineWit.        (* the consumed input's lines are its last byte's history's *)
Require Import PipeOut.           (* [pipeOutG]: the section binds it *)
Require Import PipesLinksV.
Require Import UnionDisc.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import ReadRec.
Require Import RiscvPtsto.
Require Import ConsoleInv.
Require Import UserConsole.
Require Import WpUart.
Require Import Xv6Cameras.
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation U := ulmU.

(* the ring's translation is the identity on a disciplined union input:
   every byte of it is printable or the newline *)
Lemma lm_disc_input_U_no_cr (I : list (bv 8)) (j : nat) :
  lm_disc_input U I -> (j < length I)%nat -> cons_xlate (I !!! j) = I !!! j.
Proof using.
  intros Hd Hj.
  assert (Hin : I !!! j ∈ I).
  { apply elem_of_list_lookup_2 with j. apply list_lookup_lookup_total_lt. exact Hj. }
  pose proof (lm_disc_input_byte_val U (ulm_byte_laws adm_u_f) I (I !!! j) Hd Hin) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

Section union_read_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.
  (* THE TAG IS THE UNION ERA'S ([UnionOut.utag]) *)
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = utag ug).

  Local Notation UI := (union_link_inst ug).

  Local Lemma uri_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ union_links ug -∗ UPIN k v -∗ dl_cnt v (1/2) n -∗
      (uread_ret ug k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk #Hpin Hdl HΦ".
    iDestruct (union_links_rd with "Hlk") as "#Hrdl".
    iApply ("Hrdl" $! k v n ws with "Hpin Hdl HΦ").
  Qed.

  Local Lemma uri_rd_taint (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ union_links ug -∗ UT -∗ (UT -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk HT HΦ".
    iDestruct (union_links_rd_taint with "Hlk") as "#Hrdt".
    iApply ("Hrdt" $! k ws with "HT HΦ").
  Qed.

  (* THE LAST CONSUMED ENTRY'S TAG ([FileReadInst]'s, verbatim): the
     window's tags are the delivered bytes' and the swallow row holds the
     swallowed byte's, so one of the two rows names it *)
  Local Lemma uri_last_tag (cn : cons_names)
      (I : list (bv 8)) (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8)
      (y : list mobs * bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    list_basics.last ws = Some y ->
    ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
    ucons_swallow cn False sl dd dc -∗
    ucons_stored_lb cn sl' -∗
    riscv_rx_tag y.1.
  Proof using .
    intros Hddc Hlws (Hsll & Hhsl & Hwin) Hpre Hwsj Hlast.
    iIntros "#Htags #Hsw #Hlb".
    rewrite last_lookup Hlws in Hlast.
    assert (Hdc : (0 < dc)%nat)
      by (apply lookup_lt_Some in Hlast; rewrite Hlws in Hlast; lia).
    pose proof (Hwsj (pred dc) ltac:(lia)) as Hy. rewrite Hlast in Hy.
    rewrite /ucons_swallow. iDestruct "Hsw" as "[%Heq | [%Heq Hs]]".
    - rewrite Heq in Hy.
      destruct (Hwin (pred dd) ltac:(lia)) as (h & b & Hsl & Hh & _ & _).
      pose proof (prefix_lookup_Some _ _ _ _ Hsl Hpre) as Hsl'.
      assert (Hyy : Some y = Some (h, b)) by (rewrite Hy; exact Hsl').
      injection Hyy as ->. cbn [fst].
      iApply (big_sepL_lookup _ hs (pred dd) h Hh with "Htags").
    - iDestruct "Hs" as (h b) "(_ & #Hlbs & _ & #Htag & _)".
      iEval (rewrite /ucons_stored_lb) in "Hlbs Hlb".
      iDestruct (own_valid_2 with "Hlbs Hlb") as %Hcmp%mono_list_lb_op_valid_L.
      assert (Hidx : (length I + pred dc = length sl)%nat) by lia.
      rewrite Hidx in Hy.
      assert (Hs1 : (sl ++ [(h, b)]) !! length sl = Some (h, b))
        by (rewrite lookup_app_r; [ | lia ]; by rewrite Nat.sub_diag).
      assert (y = (h, b)) as ->.
      { destruct Hcmp as [Hc | Hc].
        - pose proof (prefix_lookup_Some _ _ _ _ Hs1 Hc) as H1.
          rewrite H1 in Hy. by injection Hy as ->.
        - symmetry in Hy.
          pose proof (prefix_lookup_Some _ _ _ _ Hy Hc) as H1.
          rewrite Hs1 in H1. by injection H1 as ->. }
      iExact "Htag".
  Qed.

  (* THE WINDOW ARM at the union: the receipt's trailing disjunct carries
     the state's witness beside the writer's cursor, and the typed lines'
     witness at the far end is read off the last consumed byte's tag *)
  Local Lemma uri_arms (cn : cons_names) (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ UPIN (S gen_id) v -∗ inp_lb v I -∗
      urresw ug v I -∗
      uread_ret ug (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow cn False sl dd dc -∗
      ucons_stored_lb cn sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜lm_disc_input U (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ urresw ug v (I ++ J))
      ∨ UT.
  Proof using Htag.
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    iIntros "#Hpin #HE0 [#Hres0 #Hw0] Hret #Htags #Hsw #Hlb2".
    rewrite /uread_ret /vread_ret.
    iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]"; [ by iRight | ].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsce & %Hboots & #HEin & %Hdinp & Hrest)".
    iEval (rewrite Hlws) in "Hdlr".
    iDestruct (inp_lb_cmp v I (snd <$> (dl ++ ws)) with "HE0 HEin") as %Hcmp.
    assert (Hlen' : length (snd <$> (dl ++ ws)) = (length I + dc)%nat).
    { rewrite length_fmap length_app Hdl Hlws. reflexivity. }
    assert (Hpre' : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hcmp as [Hc | Hc]; [ exact Hc | ].
      pose proof (prefix_length _ _ Hc) as Hle.
      assert (Hdc0 : dc = 0%nat) by lia.
      assert (Heq : (snd <$> (dl ++ ws)) = I).
      { apply (list_eq_same_length _ _ (length I)); [ lia | lia | ].
        intros i x y Hi Hx Hy.
        pose proof (prefix_lookup_Some _ _ i x Hx Hc) as Hxy.
        rewrite Hxy in Hy. by injection Hy as <-. }
      rewrite Heq. done. }
    destruct Hpre' as [J HJ].
    assert (HJlen : length J = dc)
      by (rewrite HJ length_app in Hlen'; lia).
    assert (HJdisc : lm_disc_input U (I ++ J)) by (rewrite <- HJ; exact Hdinp).
    iDestruct "Hrest" as "#Hrest".
    iAssert (gwc_rres U (union_params ug) v (I ++ J)) as "#Hresn".
    { iDestruct "Hrest" as "[%Hws0 | Hbb]".
      - assert (Hdc0 : dc = 0%nat)
          by (rewrite <- Hlws, Hws0; reflexivity).
        assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iExact "Hres0".
      - iDestruct "Hbb" as (cs0 ps0 s0) "(#Hcs & #Hps & #Hw & _ & #Htlb & %Hrds)".
        rewrite /gwc_rres. iExists ps0, cs0, s0.
        rewrite <- HJ. iFrame "Htlb Hps Hcs".
        iSplitR; [ by iPureIntro | ].
        iDestruct "Hw" as (vf) "[#Hvf #Hf0]".
        iExists vf. iFrame "Hvf". iApply (f0_lb_bl with "Hf0"). }
    iAssert (inp_lb v (I ++ J)) as "#HEn";
      [ rewrite <- HJ; iExact "HEin" | ].
    (* THE WITNESS AT THE FAR END: off the last consumed entry's tag, or
       the residue's own where nothing was consumed *)
    iAssert (flw gf (I ++ J) ∨ UT)%I as "#Hwn".
    { destruct (decide (dc = 0%nat)) as [Hdc0 | Hdc0].
      { assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iLeft. iExact "Hw0". }
      destruct (list_basics.last ws) as [y |] eqn:Hlast; last first.
      { exfalso. apply last_None in Hlast. subst ws. cbn in Hlws. lia. }
      iDestruct (uri_last_tag cn I ws sl sl' hs dd dc g0 y
                   Hddc Hlws Hwinf Hpre2 Hwsj Hlast
                   with "Htags Hsw Hlb2") as "Hty".
      iEval (rewrite Htag /utag) in "Hty".
      iDestruct "Hty" as "(%Hsh & _ & #Hfl)".
      iLeft. rewrite /flw. iRight.
      iExists (echof_lines_of y.1). iFrame "Hfl". iPureIntro.
      intros w Hw. rewrite <- HJ in Hw. destruct y as [hy cy].
      apply (echof_lines_of_consumed (S gen_id) (dl ++ ws) hy cy w).
      - rewrite /seg_of.
        destruct Hpref as [z Hz].
        intros j x Hx. apply (Hidx j x).
        rewrite /seg_of Hz fmap_app. apply lookup_app_l_Some. exact Hx.
      - exact (proj1 (proj2 Hrok)).
      - exact Hboots.
      - rewrite last_app Hlast. reflexivity.
      - exact Hsh.
      - exact Hw. }
    iDestruct "Hwn" as "[#Hwn | #HT]"; [ | by iRight ].
    iLeft. iFrame "Hdlr". iExists J.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ | iFrame "HEn"; rewrite /urresw; iFrame "Hresn Hwn" ].
    iPureIntro. intro Hdd0.
    exact (rr_byte_of_rows (lm_disc_input U) sl sl' ws dl hs pops I J dd dc g0
             lm_disc_input_U_no_cr
             Hdd0 Hddc Hwinf Hpre2 Hwsj Hpref Hdl HJ HJdisc ltac:(lia)).
  Qed.

  Definition union_read_inst : ReadRec UI :=
    MkReadRec UI (lm_disc_input U) uri_rd uri_rd_taint uri_arms.

  Lemma union_read_inst_disc : rk_disc UI union_read_inst = lm_disc_input U.
  Proof using . reflexivity. Qed.
End union_read_inst.
