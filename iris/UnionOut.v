(* ===================================================================== *)
(*  UnionOut.v -- THE UNION APPLICATION'S CONSOLE CLAIM, ITS TAG AND ITS  *)
(*  LEDGER (cut C9e'; design: claude-notes/design/union.md section 3,     *)
(*  'The claim', review item S7).                                         *)
(*                                                                        *)
(*  THE CLAIM is the N-writer claim [PipeOutN.peclV] at the union model   *)
(*  [UnionDisc.ulmG]:                                                     *)
(*                                                                        *)
(*    ucl := gcl ulmG ucparams ∅ uwa ∨ popenU                          *)
(*                                                                        *)
(*  - [ucparams]: the FILE's taint, era pin and writer's witness          *)
(*    ([FileOut.file_cparams]' fields) at the union's laws and hooks;     *)
(*  - [uwa]: the FILE's witness authority ([FileOut.f0wa] / [f0boot] /    *)
(*    the filing [f0wa_file]) with the PIPELINE's byte ledger as its      *)
(*    stream extension ([gext := PipeOut.pext]);                          *)
(*  - [popenU]: [PipeOutN.popenV]'s open round at the union, CARRYING the *)
(*    witness authority [gwa uwa k (gs_st so)] -- so the file's filed     *)
(*    ledger and the claim's copy of the boot witness survive an open     *)
(*    pipeline round (the review's requirement).                          *)
(*                                                                        *)
(*  S7: the family's credential [pwc_blkU] is [PipeOutN.pwc_blkV] at the  *)
(*  union, and carries the pure tie [lm_upto cs s0 (bodies_of I) (n-1) =  *)
(*  sR]: the state the family's [runN] is built at IS the state the       *)
(*  claim's [lm_blk_at] reads.                                            *)
(*                                                                        *)
(*  THE FIXED PART is [union_gn]: the file's ([FileOut.file_gn]) and the  *)
(*  pipeline byte ledger's era map; the pipeline stack runs at            *)
(*  [ugn_pipe] = [MkPipeGn (fgn_echo gf) ugn_pera].                        *)
(*                                                                        *)
(*  THE LEDGER is [FileOut.file_led]'s shape at the union discipline,     *)
(*  plus the byte ledger's map [PipeOut.pera_map]; its taint counter      *)
(*  cases on the landed decider [UnionDecU.lm_disc_ulmG_dec] -- no        *)
(*  classical axiom -- and its conclusion is [UnionOutPure.union_phi].    *)
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
Require Import GenOutHist.
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
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import PipesLedPure.
Require Import PipesLinksV.
Require Import GenOutWild.
Require Import PipeOutW.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionDecU.          (* [lm_disc_ulmG_dec]: the ledger's counter *)
Require Import UnionView.
Require Import UnionOutPure.
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  0.  THE FIXED PART                                                    *)
(* ===================================================================== *)
Record union_gn := MkUnionGn {
  ugn_file : file_gn;   (* the file application's: taint, era maps, lines *)
  ugn_pera : gname;     (* ghost_map nat pipe_era: the era's BYTE LEDGER *)
}.

(* the pipeline stack's fixed part: the file's echo half and the byte
   ledger's map *)
Definition ugn_pipe (ug : union_gn) : pipe_gn :=
  MkPipeGn (fgn_echo (ugn_file ug)) (ugn_pera ug).

Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g adm_s_off).

(* THE UNION'S WILD LINES: the [seccomp x] line (seccomp design 10) --
   any nonempty tail is its terminal alternative's continuation at every
   state, and its merge set is everything *)
Definition uwild (l : uline) : bool :=
  match l with LSecc _ => true | _ => false end.

Lemma uwild_wild (l : uline) : uwild l = true -> lm_wild U l.
Proof using.
  destruct l as [ws | ws N | N | p fs | ws]; try discriminate. intros _. split.
  - intros s u Hu. exists (ualt_code (US u)).
    cbn [ulmG ulm lm_ok lm_term lm_cont lm_dec]. rewrite ualt_dec_code.
    split_and!; [exact Hu | reflexivity | reflexivity].
  - intros u. cbn [ulmG ulm lm_merge umerge]. exact I.
Qed.

(* a pipeline line is not wild *)
Lemma uwild_pv (l : uline) (lR : pline') :
  pv_line pview_unionU l = Some lR -> uwild l = false.
Proof using.
  intros Hl. destruct (uv_line_some l lR Hl) as (p & fs & -> & _). reflexivity.
Qed.

Section union_out.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation pg := (ugn_pipe ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).

  (* =================================================================== *)
  (*  1.  THE PARAMETERS AND THE CLAIM                                    *)
  (* =================================================================== *)

  (* the file's taint, pin and writer's witness, at the union's model *)
  Definition ucparams : gen_cparams U :=
    MkGCP U ulmG_laws ulmG_hooks UT _ _
      UPIN _ _ (era_pin_agree (fgn_echo gf)) (f0cw gf) _ _.

  (* the file's witness authority, the pipeline's byte ledger beside it *)
  Definition uwa : gen_wa U ucparams ∅ :=
    @MkGWA Σ _ U ucparams ∅ (f0wa gf) _ (f0wa_agree_d gf) (f0_typed gf) _
      (f0wa_W gf) (f0boot gf) (f0wa_file gf) True (fun _ => f0wa_agree gf)
      False (fun Hf => match Hf with end)
      (pext pg) _ (pext_grow pg).

  Lemma uwa_ext k l : gext uwa k l = pext pg k l.
  Proof using . reflexivity. Qed.

  (* THE OPEN ROUND: [popenV] at the union, carrying the witness
     authority [f0wa] of the stage's filed state *)
  Definition popenU (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    popenV pg U UPIN (f0wa gf) ∅ k ho H.

  (* THE CLAIM: three arms (seccomp design 10.3) -- the taint, the
     disciplined claim under the era's wild flag at 0, and the WILD arm *)
  Definition ucl : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ :=
    pwclV pg U ucparams ∅ uwa uwild.

  (* THE ERA'S WILD TOKEN (seccomp design 10.1) *)
  Definition usecc_tok (k : nat) : iProp Σ := secc_tok U ucparams k.

  Global Instance usecc_tok_persistent k : Persistent (usecc_tok k).
  Proof using . rewrite /usecc_tok. apply _. Qed.
  Global Instance usecc_tok_timeless k : Timeless (usecc_tok k).
  Proof using . rewrite /usecc_tok. apply _. Qed.

  (* ...at its own line *)
  Definition usecc_tok_at (k : nat) (I0 : list (bv 8)) : iProp Σ :=
    secc_tok_at U ucparams k I0.
  Global Instance usecc_tok_at_persistent k I0 : Persistent (usecc_tok_at k I0).
  Proof using . rewrite /usecc_tok_at. apply _. Qed.
  Global Instance usecc_tok_at_timeless k I0 : Timeless (usecc_tok_at k I0).
  Proof using . rewrite /usecc_tok_at. apply _. Qed.
  Lemma usecc_tok_of_at (k : nat) (I0 : list (bv 8)) : usecc_tok_at k I0 -∗ usecc_tok k.
  Proof using . exact (secc_tok_of_at U ucparams k I0). Qed.

  Lemma ucl_unfold (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ucl k ho H ⊣⊢ UT ∨ (∃ v, UPIN k v ∗ secc_flag v 0 ∗ peclV pg U ucparams ∅ uwa k ho H)
                  ∨ wildV U ucparams ∅ uwa uwild k ho H.
  Proof using . done. Qed.

  Global Instance ucl_timeless k ho H : Timeless (ucl k ho H).
  Proof using . rewrite /ucl. apply _. Qed.

  Lemma ucl_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    UT -∗ ucl k ho H.
  Proof using . iIntros "#HT". iApply (pwclV_taint pg U ucparams ∅ uwa uwild k ho H with "HT"). Qed.

  (* THE LICENCES: the taint moves the claim by any event, the wild token
     by any process event *)
  Lemma ucl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    UT -∗ ucl k ho H ==∗ ucl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT Hc". iApply (pwclV_sup pg U ucparams ∅ uwa uwild k ho H ev with "HT Hc"). Qed.

  Lemma ucl_wild_lic (k : nat) :
    usecc_tok k -∗
    □ ∀ (h : list mobs) (H : LogEntryDefs.cons_hist) (ev : ConsLog.cons_ev),
        ⌜(exists b, ev = ConsLog.EvOut b) \/ (exists ws, ev = ConsLog.EvRead ws)⌝ -∗
        ⌜ConsLog.cons_ev_ok H ev⌝ -∗
        ucl k h H ==∗ ucl k h (ConsLog.cons_step H ev).
  Proof using . exact (pwclV_wild_lic pg U ucparams UB ∅ uwa uwild k). Qed.

  (* =================================================================== *)
  (*  2.  THE FILE LINES' EVENTS: the generic claim's, the open round     *)
  (*      refuted                                                         *)
  (* =================================================================== *)

  (* (H) THE ERA'S HEAD WRITE, filing the boot state out of [f0boot] *)
  Lemma ucl_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : fstate) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    fstate_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (f0boot gf k s0 ∨ UT) -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hok Halt Hhead. iIntros "Hpin Ht Hps Hcs HE Hbt Hcl".
    iApply (pwclV_step_write_first pg U ucparams ∅ uwa uwild uwild_wild
              k v a b s0 ho H Hok Halt Hhead with "Hpin Ht Hps Hcs HE Hbt Hcl").
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND *)
  Lemma ucl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    lm_proc_stream U ps0 cs0 s0 I0 !! P = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hn Hpin0 Hb. iIntros "Hpin Ht Hps Hcs HE HW Hcl".
    iApply (pwclV_step_write pg U ucparams ∅ uwa uwild uwild_wild
              k v P b ps0 cs0 s0 I0 ho H Hn Hpin0 Hb with "Hpin Ht Hps Hcs HE HW Hcl").
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, filing the round's alternative, at a line
     that is not a [seccomp x] line (premise; seccomp design 10.10: no
     escape -- the shell's round there never presents a block-first byte) *)
  Lemma ucl_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    uwild (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) = false ->
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
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hnw Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead.
    iIntros "Hpin Ht Hps Hcs HE HW Hcl".
    iApply (pwclV_step_write_blk pg U ucparams UB ∅ uwa uwild uwild_wild
              k v P a b ps0 cs0 s0 I0 ho H
              Hnw Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead
              with "Hpin Ht Hps Hcs HE HW Hcl").
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE: the file's witness is STRICT (a
     filed lower bound pins the state), so no cursor premise *)
  Lemma ucl_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic U (lm_at U cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx U cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream U ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0cw gf k s0 -∗
    ucl k ho CH ==∗
      ucl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ f0cw gf k s0) ∨ UT).
  Proof using .
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "Hpin Ht Hps Hcs HE HW Hcl".
    iApply (pwclV_step_write_pro pg U ucparams ∅ uwa uwild uwild_wild
              k v P a b ps0 cs0 s0 I0 ho CH
              (or_intror (or_introl I)) Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hps Hcs HE HW Hcl").
  Qed.

  (* THE DRAIN: the trace fact at the era's own boot state, that state's
     deed witness ([gwa_ty uwa = f0_typed]), the era pin and a lower bound
     of the state -- [FileOut.fdrain_ret] at the union model, from either
     arm of the claim *)
  Definition udrain_ret (k : nat) (seg : list mobs) : iProp Σ :=
    (UT
     ∨ ∃ (s0 : fstate) (vf : file_era),
         ⌜lm_good_out U s0 seg⌝ ∗ ⌜fstate_ok s0⌝ ∗ f0_typed gf s0
         ∗ file_era_pin gf k vf ∗ f0_lb vf s0)%I.

  Lemma ucl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    ucl k ho CH -∗ ucl k ho CH ∗ udrain_ret k seg.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. iIntros "Hcl".
    iDestruct (pwclV_drain pg U ucparams UB ∅ uwa uwild uwild_wild k h ho CH seg
                 Hsh Hk Hpre Hins Hwire Hne with "Hcl") as "[$ Hd]".
    rewrite /udrain_ret /gdrain_ret.
    iDestruct "Hd" as "[#HT | (%s0 & %Hgo & %Hok & #Hty & #Hw)]"; [by iLeft |].
    iRight. iDestruct "Hw" as (vf) "[#Hfp #Hlb]".
    iExists s0, vf. iFrame "Hty Hfp Hlb". by iPureIntro.
  Qed.

  (* THE READ: the generic receipt, and at a read that completes a wild
     line the era's wild token (the transition, seccomp design 10.4) *)
  Lemma ucl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    UPIN k v -∗ dl_cnt v (1/2) n -∗ ucl k ho CH ==∗
      ucl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ rd_retW U ucparams uwild k v n CH ws.
  Proof using .
    intros Hread. iIntros "Hpin Hdl Hcl".
    iApply (pwclV_step_read pg U ucparams UB ∅ uwa uwild uwild_wild k v n ho CH ws Hread
              with "Hpin Hdl Hcl").
  Qed.

  (* THE KERNEL'S OWN EVENTS *)
  Lemma ucl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    ucl k ho H -∗ ucl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using . intros Hok Hev. exact (pwclV_close pg U ucparams ∅ uwa uwild k ho H Hok Hev). Qed.

  Lemma ucl_step_byte (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    ucl k ho CH ==∗ ucl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using .
    intros Hok Hev. exact (pwclV_step_byte pg U ucparams UB ∅ uwa uwild k ho CH b Hok Hev).
  Qed.

  Lemma ucl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input U (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc U h -> trace_shape h true ->
    ucl k ho H -∗ ucl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh.
    exact (pwclV_open pg U ucparams UB ∅ uwa uwild uwild_wild k ho H h c cs
             Hok Hev Hd Hb Hdh Hsh).
  Qed.

  (* =================================================================== *)
  (*  3.  THE PIPELINE ROUNDS' EVENTS (C9c'), at the union                *)
  (* =================================================================== *)

  (* THE FAMILY'S CREDENTIAL at the round's state [sR] (S7: it carries
     the tie [lm_upto cs s0 (bodies_of I) (nlines I - 1) = sR]) *)
  Definition pwc_blkU (v : era_pins) (I : list (bv 8)) (sR : fstate) (k : nat)
      (pre : list (bv 8)) (tm : bool) : iProp Σ :=
    pwc_blkV pg U UPIN (f0cw gf) UT v I sR k pre tm.

  Definition ptkU (v : era_pins) (I : list (bv 8)) (k : nat) : iProp Σ :=
    ptkV UT v I k.

  Definition pwitU (I : list (bv 8)) (sR : fstate) (tm : bool) (pre : list (bv 8)) : Prop :=
    pwitV U I sR tm pre.

  Global Instance pwc_blkU_timeless v I sR k pre tm : Timeless (pwc_blkU v I sR k pre tm).
  Proof using . rewrite /pwc_blkU /pwc_blkV /pledV. apply _. Qed.

  Global Instance ptkU_persistent v I k : Persistent (ptkU v I k).
  Proof using . rewrite /ptkU /ptkV. apply _. Qed.

  (* the tie, read off the credential *)
  Lemma pwc_blkU_tie (v : era_pins) (I : list (bv 8)) (sR : fstate) (k : nat)
      (pre : list (bv 8)) (tm : bool) :
    pwc_blkU v I sR k pre tm -∗
    (∃ (ps cs : list nat) (s0 : fstate) (P : nat),
       ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
       ∗ f0cw gf k s0) ∨ UT.
  Proof using .
    rewrite /pwc_blkU /pwc_blkV. iIntros "[Hx | #HT]"; [| by iRight].
    iDestruct "Hx" as (ps cs s0 P) "(%Hw & _ & #HW & _)".
    iLeft. iExists ps, cs, s0, P. by iFrame "HW".
  Qed.

  (* THE ENTRY: a round writer's lend before the block's first byte *)
  Lemma pwc_blkU_entry (v : era_pins) (I : list (bv 8)) (k : nat)
      (ps cs : list nat) (s0 : fstate) (P : nat) :
    wr_blkV U ps cs s0 I P ->
    UPIN k v -∗ f0cw gf k s0 -∗ turn v P -∗ ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗
    pwc_blkU v I (lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat) k [] false.
  Proof using .
    intros Hw. iIntros "Hpin HW Ht Hps Hcs HE".
    iApply (pwc_blkV_entry pg U UPIN (f0cw gf) UT v I k ps cs s0 P Hw
              with "Hpin HW Ht Hps Hcs HE").
  Qed.

  (* THE CLAIM PAYS THE FAMILY'S ONE OBLIGATION, at the round's state, at
     a line that is NOT WILD (a terminal family byte at the [seccomp x]
     line would be admissible there; the family's lines are pipelines) *)
  Theorem pblkU_ecl_holds (v : era_pins) (I : list (bv 8)) (sR : fstate) :
    uwild (lineV U I) = false ->
    ⊢ eclN ucl (pwc_blkU v I sR) (ptkU v I) (pwitU I sR).
  Proof using .
    intros Hnw. exact (pwclV_ecl_holds pg U ucparams ∅ uwa uwa_ext uwild uwild_wild
                         v I sR Hnw).
  Qed.

  (* THE MODEL'S BLOCKS ARE THE CLAIM'S NON-TERMINAL WITNESS, through the
     union's view, at a well-formed round state *)
  Lemma pipesU_HWIT (I : list (bv 8)) (sR : fstate) (lR : pline') :
    pv_line pview_unionU (lineV U I) = Some lR -> fstate_ok sR ->
    adm_u_g lR = true -> pl_ok lR ->
    forall pre bl, blkN (wids (lcats lR)) (runN (files_of sR) lR) bl ->
      pre `prefix_of` bl -> pwitU I sR false pre.
  Proof using .
    intros HlR Hok Ha Hl.
    exact (pipesV_HWIT U pview_unionU I sR lR HlR
             (pview_union_fc_ok adm_u_g adm_s_off sR Hok) Ha Hl).
  Qed.

  (* THE FILING at the credential: the prompt's first byte files the
     block the family handed back, as the view's [PLRun pre] *)
  Lemma pwc_blkU_file (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline')
      (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (pre : list (bv 8)) (b : bv 8) :
    pv_line pview_unionU (lineV U I) = Some lR -> adm_u_g lR = true ->
    line_blocks (files_of sR) lR pre -> pre <> [] -> b = u_prompt !!! 0%nat ->
    pwc_blkU v I sR k pre false -∗ ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
            ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ f0cw gf k s0 ∗ turn v (S (P + length pre))%nat
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun pre)]) ∗ inp_lb v I) ∨ UT).
  Proof using .
    intros HlR Ha Hbl Hne Hbv. iIntros "Hpw Hcl".
    iApply (pwclV_blk_file pg U ucparams UB ∅ uwa uwa_ext uwild pview_unionU v I sR lR
              k ho H pre b HlR Ha Hbl Hne Hbv with "Hpw Hcl").
  Qed.

  (* ...and the EMPTY block: no writer wrote, the prompt is the block's
     first byte, filed between rounds as the view's [PLRun []] *)
  Lemma pwc_blkU_file_empty (v : era_pins) (I : list (bv 8)) (sR : fstate) (lR : pline')
      (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) (b : bv 8) :
    pv_line pview_unionU (lineV U I) = Some lR ->
    b = u_prompt !!! 0%nat ->
    pwc_blkU v I sR k [] false -∗ ucl k ho H ==∗
      ucl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
            ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ f0cw gf k s0 ∗ turn v (S P)
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun [])]) ∗ inp_lb v I) ∨ UT).
  Proof using .
    intros HlR Hbv. iIntros "Hpw Hcl".
    iApply (pwclV_blk_file_empty pg U ucparams UB ∅ uwa uwild uwild_wild pview_unionU
              v I sR lR k ho H b uwild_pv HlR Hbv with "Hpw Hcl").
  Qed.

  (* =================================================================== *)
  (*  4.  THE TAG                                                         *)
  (* =================================================================== *)

  (* [FileOut.ftag] at the union's discipline: the trace's shape, the
     discipline or the taint, and a lower bound of the ledger's typed line
     list -- which is how a typed line reaches the child's create step *)
  Definition utag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜lm_disc U h⌝ ∨ UT)
     ∗ fl_lb (fgn_cl gf) (efl_of h))%I.

  Global Instance utag_persistent h : Persistent (utag h).
  Proof using . rewrite /utag. apply _. Qed.
  Global Instance utag_timeless h : Timeless (utag h).
  Proof using . rewrite /utag. apply _. Qed.

  (* =================================================================== *)
  (*  5.  THE FOUNDING: the era's ghosts become the claim at the start of *)
  (*      its era and init's credential                                   *)
  (* =================================================================== *)
  Lemma union_era_split (k : nat) (v : era_pins) (vf : file_era) (w : pipe_era)
      (gb : gname) :
    UPIN k v -∗ file_era_pin gf k vf -∗ pera_pin pg k w -∗
    era_full v -∗ f0_auth vf [] -∗ f0f_auth vf [] -∗
    blk_auth w [] -∗ rblk_auth gb [] -∗ cur_half w 1 0%nat gb false -∗
      ucl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ fturn gf k.
  Proof using .
    iIntros "#Hpin #Hfp #Hpera (Ht & Hcs & Hps & HE & Hdl & Hdll & Hsc) Hf0 Hfla Hblk Hrb Hcur1".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll Hfla Hblk Hrb Hcur1 Hsc".
    { rewrite /ucl. iApply (pwclV_mid pg U ucparams ∅ uwa uwild k [] (LogEntryDefs.MkCH [] [] [] None) v with "Hpin Hsc").
      rewrite /peclV /gcl. iLeft. iRight. iExists v, (gstage0 U).
      cbn [gs_ps gs_cs gs_E gs_w gs_st gstage0 LogEntryDefs.ch_dl length].
      iSplitR; [iExact "Hpin" |].
      iSplitL "Hfla".
      { iExists vf. iFrame "Hfp Hfla". cbn [f0_wit default].
        iSplit; [done | iApply (f0_typed_none gf)]. }
      iSplitL "Hblk Hcur1 Hrb".
      { rewrite uwa_ext /pext.
        iExists w, 0%nat, gb, [], false. iFrame "Hpera Hcur1 Hrb".
        rewrite (_ : lm_stream U ∅ _ = []); [iExact "Hblk" | reflexivity]. }
      rewrite (_ : lm_pcount U [] [] (gs_state U ∅ (gstage0 U)) [] [] = 0%nat);
        [| reflexivity].
      iFrame "Ht1 Hcs Hps HE Hdl1 Hdll".
      iPureIntro.
      rewrite /gcl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (lm_out_pure_0 U ∅ k [] fstate_ok_empty).
      - exact (lm_cs_len_ok_0 U).
      - exact (lm_ps_len_ok_0 U ∅).
      - exact (gin_pure_0 U k).
      - by rewrite /garm_era.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of fmap_nil. reflexivity.
      - exact (lm_dl_ok_0 U). }
    rewrite /fturn. iExists v, vf. iFrame "Hpin Hfp Ht2 Hdl2 Hcslb Hpslb Hf0".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

  (* =================================================================== *)
  (*  6.  THE LEDGER                                                      *)
  (*                                                                      *)
  (*  [FileOut.file_led] at the union's discipline, with the pipeline     *)
  (*  byte ledger's era map beside the file's.  THE COUNTER CASES ON THE  *)
  (*  LANDED DECIDER [UnionDecU.lm_disc_ulmG_dec]: no hypothesis, no      *)
  (*  classical axiom.                                                    *)
  (* =================================================================== *)
  Definition union_phi_res (h : list mobs) : iProp Σ :=
    (∃ s0s : list fstate,
       ⌜lm_disc U h -> union_phi_body h s0s⌝ ∗ f0_pinned gf h s0s)%I.

  Global Instance union_phi_res_timeless h : Timeless (union_phi_res h).
  Proof using . rewrite /union_phi_res. apply _. Qed.

  Definition union_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint (fgn_echo gf)) 1
       (if decide (lm_disc U h) then 0%nat else 1%nat)
     ∗ pin_map (fgn_echo gf) h
     ∗ f0_map gf h
     ∗ pera_map pg h
     ∗ fl_auth (fgn_cl gf) (efl_of h)
     ∗ (union_phi_res h ∨ UT))%I.

  Global Instance union_led_timeless h : Timeless (union_led h).
  Proof using . rewrite /union_led. apply _. Qed.

  (* the birth's yield *)
  Definition union_cl_all : iProp Σ :=
    (file_cl_all gf ∗ ghost_map_auth (ugn_pera ug) 1 (∅ : gmap nat pipe_era))%I.

  Lemma union_led_init : union_cl_all -∗ union_led [].
  Proof using .
    rewrite /union_cl_all /file_cl_all /file_cl /echo_cl /union_led /pin_map
      /f0_map /pera_map.
    iIntros "[[[[Ht Hm] Hfl] Hmf] Hme]".
    rewrite decide_True; [| exact (lm_disc_nil U)].
    rewrite (_ : efl_of [] = []); last first.
    { rewrite /efl_of /echof_lines_of /cycles_of /cycles_rev /=. reflexivity. }
    iFrame "Ht Hfl".
    iSplitL "Hm"; [iExists ∅; iFrame "Hm"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hmf"; [iExists ∅; iFrame "Hmf"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hme"; [iExists ∅; iFrame "Hme"; iPureIntro; apply pin_dom_empty |].
    iLeft. iExists []. iSplitR.
    { iPureIntro. intros _. exact union_phi_body_nil. }
    iApply f0_pinned_undrained. reflexivity.
  Qed.

  (* THE POWER STEP: the on-arm allocates the era's three records (echo's,
     the file's boot state, the byte ledger), mints the pins, and splits
     the ghosts into the era's claim and init's credential *)
  Lemma union_led_pow (h : list mobs) (on : bool) :
    union_led h ==∗
      union_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else ucl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ fturn gf (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hfm & Hme & Hfl & Hphi)". rewrite /union_led.
    rewrite (decide_ext _ (lm_disc U h) 0%nat 1%nat
               (lm_disc_power U h on union_st_ok)).
    rewrite (_ : efl_of (h ++ [if on then ObsPowerOff else ObsPowerOn])
                 = efl_of h); [| exact (efl_of_power h on)].
    destruct on.
    - iDestruct (pin_map_step (fgn_echo gf) h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iDestruct (f0_map_step gf h ObsPowerOff eq_refl with "Hfm") as "Hfm".
      iDestruct (pera_map_step pg h ObsPowerOff eq_refl with "Hme") as "Hme".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hfm Hme Hfl".
      iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]". iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        exact (union_phi_body_off h s0s
                 (Hb (proj1 (lm_disc_power U h true union_st_ok) Hd))). }
      iApply f0_pinned_undrained.
      by rewrite (open_seg_power h ObsPowerOff eq_refl).
    - iMod era_full_alloc as (v) "Hfull".
      iMod f0_alloc as (vf) "[Hf0 Hfla]".
      iMod blk_alloc as (w gb) "(Hblk & Hrb & Hcur1)".
      iMod (pin_map_on (fgn_echo gf) h v with "Hpm") as "[Hpm #Hpin]".
      iMod (f0_map_on gf h vf with "Hfm") as "[Hfm #Hfp]".
      iMod (pera_map_on pg h w with "Hme") as "[Hme #Hpera]".
      iDestruct (union_era_split (S (obs_boots h)) v vf w gb
                   with "Hpin Hfp Hpera Hfull Hf0 Hfla Hblk Hrb Hcur1") as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn".
      + iFrame "Ht Hpm Hfm Hme Hfl".
        iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
        iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]".
        iExists (s0s ++ [∅]). iSplitR.
        { iPureIntro. intros Hd.
          exact (union_phi_body_on h s0s
                   (Hb (proj1 (lm_disc_power U h false union_st_ok) Hd))). }
        iApply f0_pinned_undrained.
        by rewrite (open_seg_power h ObsPowerOn eq_refl).
      + iFrame "Hcl Hturn".
  Qed.

  (* THE OUTPUT STEP, AND THE ERA'S FIRST DRAIN ([FileOut.file_led_tx] at
     the union): the drain hands the era's boot state, its deed witness
     and a lower bound pinned to the era's record *)
  Lemma union_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (UT
     ∨ (match i with
        | Uart0 => ∃ (s0 : fstate) (vf : file_era),
                     ⌜lm_good_out U s0 (open_seg h ++ [ObsUartOut Uart0 b])⌝
                     ∗ f0_typed gf s0 ∗ file_era_pin gf (obs_boots h) vf
                     ∗ f0_lb vf s0
        | _ => True
        end)) -∗
    union_led h ==∗ union_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Ht & Hpm & Hfm & Hme & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo gf) h (ObsUartOut i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step gf h (ObsUartOut i b) eq_refl with "Hfm") as "Hfm".
    iDestruct (pera_map_step pg h (ObsUartOut i b) eq_refl with "Hme") as "Hme".
    rewrite /union_led.
    rewrite (decide_ext _ (lm_disc U h) 0%nat 1%nat (lm_disc_out U h i b Hsh)).
    rewrite (_ : efl_of (h ++ [ObsUartOut i b]) = efl_of h);
      [| exact (efl_of_out h i b Hsh)].
    iFrame "Ht Hpm Hfm Hme".
    iDestruct "Hphi" as "[Hphi | HT]"; last first.
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hphi" as (s0s) "[%Hb #Hpin0]".
    destruct i; last first.
    { iModIntro. iFrame "Hfl". iLeft. iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        apply (union_phi_body_step_io h (ObsUartOut Uart1 b) s0s Hsh eq_refl
                 eq_refl), Hb.
        exact (proj1 (lm_disc_out U h Uart1 b Hsh) Hd). }
      iApply (f0_pinned_io gf h (ObsUartOut Uart1 b) s0s eq_refl eq_refl
                with "Hpin0"). }
    iDestruct "Hgo" as "[#HT | Hgo]".
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hgo" as (s0 vf) "(%Hgo & #Hty & #Hfp & #Hlb)".
    iDestruct (f0_typed_adm gf (echof_lines_of h) s0
                 with "Hfl Hty") as "[Hfl %Hadm]".
    iAssert (⌜obs_wire Uart0 (open_seg h) <> [] ->
               exists u1, s0s = u1 ++ [s0]⌝)%I as "%Hlast".
    { destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
      - iPureIntro. intro Hne. by destruct (Hne Hw).
      - iDestruct (f0_pinned_drained gf h s0s vf s0 Hw with "Hfp Hlb Hpin0")
          as %Hl. iPureIntro. by intros _. }
    iModIntro. iFrame "Hfl". iLeft.
    iExists (removelast s0s ++ [s0]). iSplitR; last first.
    { iApply (f0_pinned_drain gf h b (removelast s0s) vf s0 with "Hfp Hlb"). }
    iPureIntro. intros Hd.
    exact (union_phi_body_drain h b s0s s0 Hsh
             (proj1 (lm_disc_out U h Uart0 b Hsh) Hd) Hgo Hadm Hlast
             (Hb (proj1 (lm_disc_out U h Uart0 b Hsh) Hd))).
  Qed.

  (* THE INPUT STEP: the counter decides, and the byte's TAG is handed
     out, its line list's lower bound grown by what the input completed *)
  Lemma union_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    union_led h ==∗
      union_led (h ++ [ObsUartIn i b]) ∗ utag (h ++ [ObsUartIn i b]).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hfm & Hme & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo gf) h (ObsUartIn i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step gf h (ObsUartIn i b) eq_refl with "Hfm") as "Hfm".
    iDestruct (pera_map_step pg h (ObsUartIn i b) eq_refl with "Hme") as "Hme".
    iMod (fl_auth_grow_pre gf (efl_of h) (efl_of (h ++ [ObsUartIn i b]))
            (efl_of_snoc h (ObsUartIn i b)) with "Hfl")
      as "[Hfl #Hfllb]".
    assert (Hin : lm_disc U (h ++ [ObsUartIn i b]) -> lm_disc U h).
    { destruct i;
        [ exact (lm_disc_in U UB h b Hsh)
        | exact (proj1 (lm_disc_other U h (ObsUartIn Uart1 b) eq_refl I Hsh)) ]. }
    iAssert (union_phi_res (h ++ [ObsUartIn i b]) ∨ UT)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb #Hp]".
      iExists s0s. iSplitR.
      - iPureIntro. intros Hd.
        apply (union_phi_body_step_io h (ObsUartIn i b) s0s Hsh
                 ltac:(by destruct i) ltac:(by destruct i)), Hb.
        exact (Hin Hd).
      - iApply (f0_pinned_io gf h (ObsUartIn i b) s0s ltac:(by destruct i)
                  ltac:(by destruct i) with "Hp"). }
    assert (Hsh' : trace_shape (h ++ [ObsUartIn i b]) true)
      by (eapply trace_shape_snoc; [exact Hsh | reflexivity]).
    rewrite /union_led /utag.
    destruct (decide (lm_disc U (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; [| exact (Hin Hd')].
      iModIntro. iFrame "Hcnt Hpm Hfm Hme Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iLeft. by iPureIntro.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (lm_disc U h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hfm Hme Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iRight. rewrite /file_taint /echo_taint.
      iExact "Hlb".
  Qed.

  (* THE CONCLUSION's read at the end of the run *)
  Lemma union_led_phi (h : list mobs) :
    union_led h -∗ ⌜union_phi h⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & _ & _ & [Hphi | HT'])".
    { iDestruct "Hphi" as (s0s) "[%Hb _]". iPureIntro.
      exact (union_phi_of_body h s0s Hb). }
    rewrite /file_taint /echo_taint.
    iDestruct (mono_nat_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. rewrite /union_phi. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.
End union_out.

(* ===================================================================== *)
(*  7.  THE BIRTH STEP: the file's, and the byte ledger's map beside it   *)
(* ===================================================================== *)
Section union_birth.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.

  Lemma union_birth_all : ⊢ |==> ∃ ug : union_gn, union_cl_all ug.
  Proof using .
    iMod file_birth_all as (gf) "Hf".
    iMod (ghost_map_alloc_empty (K := nat) (V := pipe_era)) as (gm) "Hm".
    iModIntro. iExists (MkUnionGn gf gm). rewrite /union_cl_all /=.
    iFrame "Hf Hm".
  Qed.
End union_birth.
