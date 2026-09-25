(* ===================================================================== *)
(*  UnionLinks.v -- THE UNION APPLICATION'S CONSOLE LINKS (cut C9e';      *)
(*  design: claude-notes/design/union.md section 3).                      *)
(*                                                                        *)
(*  [PipesLinksV]'s links at the union claim [UnionOut.ucl]: the taint    *)
(*  route, the four single-writer writes (the era head filing the boot    *)
(*  state out of [f0boot]), the read link and its receipt, the close and  *)
(*  the byte, the FILING link of an N-writer round through the union's    *)
(*  view, and [App.al_echo] as a closed entailment at the union's tag.    *)
(*                                                                        *)
(*  THE BUNDLE a program holds is the record equation itself, as a pure   *)
(*  persistent fact ([union_links]), and the links are read off it where  *)
(*  they are spent, as at [FileLinks] and [PipesLinks].                    *)
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
Require Import GenOutPure.
Require Import GenOut.
Require Import AppEcho.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesLinksV.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionView.
Require Import UnionOutPure.
Require Import UnionOut.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation U := ulmU.
Local Notation UB := (ulm_byte_laws adm_u_f).

Section union_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation pg := (ugn_pipe ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.

  (* the record equations, as section parameters *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug).

  Local Lemma Hcons' :
    @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV pg U (ucparams ug) None (uwa ug).
  Proof using Hcons. exact Hcons. Qed.

  (* ---- the taint route ---- *)
  Lemma union_cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    UT -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    exact (vcons_link_of_taint pg U (ucparams ug) None (uwa ug) Hcons' k ev Φ).
  Qed.

  Lemma union_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    UT -∗ (UT -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    exact (vwrite_link_taint pg U (ucparams ug) None (uwa ug) Hcons' k b Φ).
  Qed.

  (* (H) THE ERA'S HEAD WRITE: the first process byte files the boot
     state out of the deed's typed witness ([f0boot]) *)
  Lemma union_write_link_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : fstate) (Φ : iProp Σ) :
    fstate_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (f0boot gf k s0 ∨ UT) -∗
    (((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hok Halt Hhead.
    exact (vwrite_link_first pg U (ucparams ug) None (uwa ug) Hcons' k v a b s0 Φ
             Hok Halt Hhead).
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND, the open round
     refuted *)
  Lemma union_write_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    lm_proc_stream U ps0 cs0 s0 I0 !! P = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ f0cw gf k s0) ∨ UT)
     -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    exact (vwrite_link pg U (ucparams ug) None (uwa ug) Hcons' k v P b ps0 cs0 s0 I0 Φ
             Hn Hpin0 Hb).
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, filing the round's alternative *)
  Lemma union_write_link_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    P = length (lm_proc_before U ps0 cs0 s0 I0) ->
    lm_ok U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) ->
    lm_term U (lm_dec U a) = false ->
    lm_cont U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hne Hr Hn Hpin0 HP Hok Hfk Hb.
    exact (vwrite_link_blk pg U (ucparams ug) UB None (uwa ug) Hcons'
             k v P a b ps0 cs0 s0 I0 Φ Hne Hr Hn Hpin0 HP Hok Hfk Hb).
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE (the file's witness is strict) *)
  Lemma union_write_link_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic U (lm_at U cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx U cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream U ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hr Hop Hn Hpin0 Hnd HP Halt Hb.
    exact (vwrite_link_pro pg U (ucparams ug) None (uwa ug) Hcons'
             k v P a b ps0 cs0 s0 I0 Φ (or_intror (or_introl I))
             Hr Hop Hn Hpin0 Hnd HP Halt Hb).
  Qed.

  (* (R) THE READ LINK AND ITS RECEIPT: the window, the era's input at its
     far end, its discipline, and the writer's stage with the state's
     witness ([f0cw]: the era's file pin and the boot state's bound) *)
  Definition uread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    vread_ret U (ucparams ug) k v n ws.

  Lemma union_read_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    UPIN k v -∗ dl_cnt v (1/2) n -∗ (uread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    exact (vread_link pg U (ucparams ug) UB None (uwa ug) Hcons' k v n ws Φ).
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma union_close_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons. exact (vclose_link pg U (ucparams ug) None (uwa ug) Hcons' k Φ). Qed.

  Lemma union_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using Hcons.
    exact (vbyte_link pg U (ucparams ug) UB None (uwa ug) Hcons' k b Φ).
  Qed.

  Lemma union_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using Hcons.
    exact (vcons_run pg U (ucparams ug) UB None (uwa ug) Hcons' k cs Φ).
  Qed.

  (* (F) THE FILING LINK OF AN N-WRITER ROUND, through the union's view *)
  Lemma union_file_link (k : nat) (v : era_pins) (I : list (bv 8)) (sR : fstate)
      (lR : pline') (pre : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    pv_line pview_unionU (lineV U I) = Some lR -> adm_u_f lR = true ->
    line_blocks (files_of sR) lR pre -> b = u_prompt !!! 0%nat ->
    pwc_blkU ug v I sR k pre false -∗
    (((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
         ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
         ∗ f0cw gf k s0 ∗ turn v (S (P + length pre))%nat
         ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun pre)]) ∗ inp_lb v I)
      ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HlR Ha Hbl Hbv.
    exact (vfile_link pg U (ucparams ug) UB None (uwa ug) (uwa_ext ug) Hcons'
             pview_unionU k v I sR lR pre b Φ HlR Ha Hbl Hbv).
  Qed.

  (* THE ECHO SHIFT -- [App.al_echo], a CLOSED entailment at the union's
     tag *)
  Lemma union_happ_echo
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = utag ug) :
    ⊢ ∀ (GEN : GenId) (XI : CurCtx),
        @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
  Proof using Hcons.
    iIntros (GEN XI).
    rewrite /SpecConsoleintr.cons_echo_shift Htag.
    iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
    iDestruct "Htg" as "(%Hsh & [%Hdisc | #HT] & _)"; last first.
    { iApply (union_cons_link_of_taint with "HT [HΦ]").
      by iApply union_cons_run. }
    iIntros (o H) "#Hlb Hres %Hok %Hev".
    rewrite (vchist_at0 pg U (ucparams ug) None (uwa ug) Hcons').
    destruct (um_disc_open_seg U h Hsh Hdisc) as (s & _ & Hseg).
    iDestruct (peclV_open pg U (ucparams ug) UB None (uwa ug) (S gen_id) (default [] o) H
                 h c cs Hok Hev (proj1 Hseg) Hk Hdisc Hsh with "Hres") as "Hres".
    iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
    rewrite (vchist_at0 pg U (ucparams ug) None (uwa ug) Hcons').
    iFrame "Hlbh Hres".
    by iApply union_cons_run.
  Qed.
End union_links.

(* ===================================================================== *)
(*  THE BUNDLE: the record equation, as a pure persistent fact            *)
(* ===================================================================== *)
Section union_links_bundle.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.

  Definition union_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        UPIN k v -∗ dl_cnt v (1/2) n -∗
        (uread_ret ug k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition union_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        UT -∗ (UT -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition union_links : iProp Σ :=
    ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug⌝%I.

  Global Instance union_link_rd_persistent : Persistent union_link_rd | 0.
  Proof using . rewrite /union_link_rd. apply bi.intuitionistically_persistent. Qed.
  Global Instance union_link_rd_taint_persistent : Persistent union_link_rd_taint | 0.
  Proof using . rewrite /union_link_rd_taint. apply bi.intuitionistically_persistent. Qed.
  Global Instance union_links_persistent : Persistent union_links | 0.
  Proof using . rewrite /union_links. apply bi.pure_persistent. Qed.

  Lemma union_links_eq :
    union_links -∗ ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug⌝.
  Proof using . rewrite /union_links. by iIntros "%Hc". Qed.

  Lemma union_links_rd : union_links -∗ union_link_rd.
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /union_link_rd. iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
    iApply (union_read_link ug Hc with "Hpin Hdl HΦ").
  Qed.

  Lemma union_links_rd_taint : union_links -∗ union_link_rd_taint.
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /union_link_rd_taint. iIntros "!>" (k ws Φ) "#HT HΦ".
    iApply (union_cons_link_of_taint ug Hc with "HT [HΦ]").
    by iApply "HΦ".
  Qed.

  Lemma union_links_holds
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug) :
    ⊢ union_links.
  Proof using . by iPureIntro. Qed.
End union_links_bundle.

(* THE BUNDLE IS OPAQUE TO THE INSTANCE SEARCH ([PipeLinks]'s measured
   rule): a [Persistent (union_links _)] goal is settled by its own
   instance and nothing else is tried. *)
#[global] Typeclasses Opaque union_links.
