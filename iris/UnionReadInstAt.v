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
  pose proof (lm_disc_input_byte_val U (ulm_byte_laws adm_u_g adm_s_off) (ins s0 ++ [b]) b
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
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.
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
  Proof using Htag uartGhostG0.
    change (lk_links UIs) with (lk_links UI).
    change (lk_pin UIs k v) with (lk_pin UI k v).
    change (lk_rr UIs k v n ws) with (lk_rr UI k v n ws).
    exact (rk_rd UI UR k n v ws Φ).
  Qed.

  Local Lemma uria_rd_taint (k : nat) (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) :
    ⊢ lk_links UIs -∗ lk_T UIs -∗ (lk_T UIs -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Htag uartGhostG0.
    change (lk_links UIs) with (lk_links UI).
    change (lk_T UIs) with (lk_T UI).
    exact (rk_rd_taint UI UR k ws Φ).
  Qed.

  Local Lemma uria_arms (cn : cons_names) (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ lk_epin UIs (S gen_id) v -∗ inp_lb v I -∗ lk_rres UIs v I -∗
      lk_rr UIs (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow cn False sl dd dc -∗
      ucons_stored_lb cn sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜lm_disc_input U (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ lk_rres UIs v (I ++ J))
      ∨ lk_T UIs.
  Proof using Htag uartGhostG0.
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    change (lk_epin UIs) with (lk_epin UI).
    change (lk_rres UIs) with (lk_rres UI).
    change (lk_rr UIs) with (lk_rr UI).
    change (lk_T UIs) with (lk_T UI).
    change (lm_disc_input U) with (rk_disc UI UR).
    exact (rk_arms UI UR cn v I ws sl sl' hs dd dc g0 Hddc Hlws Hwinf Hpre2 Hwsj).
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

  Lemma union_pin_refl_at (v : era_pins) :
    ⊢ era_pin (fgn_echo gf) (S gen_id) v -∗ lk_pin UIs (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma union_ep_refl_at (v : era_pins) :
    ⊢ era_pin (fgn_echo gf) (S gen_id) v -∗ lk_epin UIs (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma union_read_leaf_holds_at (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T UIs)
          (UShLine.ush_rd_x_at (lk_rres UIs) (fgn_echo gf) Wb) ->
    (⊢ app_sup -∗ lk_T UIs) ->
    (⊢ lk_T UIs -∗ app_sup) ->
    (⊢ riscv_wild (S gen_id) -∗ lk_T UIs) ->
    (⊢ lk_links UIs) ->
    ⊢ UkSh.ush_read_recv_leaf_at (PS := uprogSG_free) N γp (lk_T UIs)
        (UShLine.ush_mid_at (lk_rres UIs) (fgn_echo gf) γp) (lm_disc_input U)
        fsc_cons l.
  Proof using Htag.
    intros Hpeq Hstw Htsw Hwdw Hlk.
    iApply (UShLine.ush_read_recv_leaf_holds_at (union_read_inst_at ug Htag s0)
              (fgn_echo gf) Wb N γp l Hpeq Hstw Htsw Hwdw
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
