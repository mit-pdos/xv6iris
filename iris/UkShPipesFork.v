(* ===================================================================== *)
(*  UkShPipesFork.v -- THE PIPE ERA'S FORK RE-ENTRY AT THE N-STAGE ROUND  *)
(*  (cut C8): [UkShPipeFork]'s widened credential with the N-writer        *)
(*  family's terminal shape.                                              *)
(*                                                                       *)
(*  A fork that fails at node [i] of the right spine is the TERMINAL      *)
(*  round: sh node [i] writes `fork\n' as the family's writer [WSh i]     *)
(*  ([PipeBothNPure.termw]), the stages above it were waited, and the     *)
(*  runcmd child exits paying the round's [UShPipesDefs.Qtop] at its      *)
(*  third arm.  The main loop then writes the prompt's two bytes as the   *)
(*  SAME writer's positions 5 and 6 ([pipesN_prompt_at]), with the waited *)
(*  stages' halves at their whole sources in hand -- and D4 refutes any   *)
(*  line read after it: the terminal byte froze the claim's resolution    *)
(*  at [nlines I - 1] ([PipeOutN.ptkN]), which a later line's read        *)
(*  residue contradicts.                                                  *)
(*                                                                       *)
(*  THE WIDENED CREDENTIAL is [UkShPipeFork.pterm_wc]'s shape verbatim:   *)
(*  the era's own at every index, or at [p < 3] the terminal shape at     *)
(*  cursor [5 + p]; it collapses at index 3, which is all the loop's body *)
(*  ever sees.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOut.
Require Import AppEcho.
Require Import LineModel.
Require Import LineModelLinks.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import PipesLinks.
Require Import PipesLinkInst.
Require Import PipesFire.
Require Import UkPipesIface.      (* [pnsN], [pipesNG] *)
Require Import GenLinksLine.
Require Import LinkRec.
Require Import FdSlots UserFd.
Require Import UkRun.
Require Import UkSh.
Require Import UkShFork.
Require Import Xv6G Xv6Cameras.
Require Import EchoOutPure.
Require Import IrefSlots ProcAvail FileInvDefs.
Require Import ConsoleInv.
Require Import UCodeShK.
Require Import UShPanic.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import UexecExecInst.
Require Import CtxIdDefs.
Local Open Scope list_scope.
Require PipeDisc.
Local Notation alt_forkc := PipeDisc.alt_forkc.

Local Notation fcE := (fun _ : bytes => @None bytes).

(* ===================================================================== *)
(*  S0  THE PROMPT AT A TERMINAL ROUND, AT ANY NODE                       *)
(*                                                                       *)
(*  [PipeOutN.pipesN_prompt] at a node [i] other than the era's index:    *)
(*  the family's era [k] and the panicking node [WSh i] are two numbers.  *)
(* ===================================================================== *)
Section pipes_prompt_at.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!ghost_varG Σ (option (list (bv 8)))}.
  Context (g : pipe_gn) (fc : bytes -> option bytes) (adm : pline' -> bool).
  Context (Lw : lm_laws (pipes_lm fc adm)).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl' g fc adm Lw).
  Context (Hfc : fc_ok fc).
  Context (v : era_pins) (I : list (bv 8)).
  Context (Ha : adm (lineN fc adm I) = true) (Hl : pl_ok (lineN fc adm I)).

  Local Notation wsN := (wids (lcats (lineN fc adm I))).
  Local Notation RUNN := (runN fc (lineN fc adm I)).
  Local Notation PWN := (pwc_blkN g fc adm v I).
  Local Notation TKN := (ptkN g v I).
  Local Notation WITN := (pwitN fc adm I).
  Local Notation TOKN := (tokN fc (lineN fc adm I)).

  Lemma pipesN_prompt_at (N : namespace) (k i : nat) (γc γm : wid -> gname)
      (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s))
      (sw : nat -> list (bv 8)) (c : nat) (b : bv 8) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    WSh i ∈ wsN -> (0 < c)%nat -> alt_forkc !! c = Some b ->
    (forall x, x ∈ heldN i sw -> x.1.1 ∈ wsN) ->
    pwc_fork_exitN wsN RUNN PWN TKN termw TOKN dep N k γc γm (WSh i) alt_forkc c -∗
    ([∗ list] x ∈ heldN i sw, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2)) -∗
    (pwc_fork_exitN wsN RUNN PWN TKN termw TOKN dep N k γc γm (WSh i) alt_forkc (S c)
     -∗ ([∗ list] x ∈ heldN i sw,
           wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2))
     -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hfc Ha Hl.
    intros Hns Hw Hc Hb Hhin. iIntros "Hex Hh HΦ".
    iApply (pprompt_forkN_h wsN (wids_NoDup _) (pecl' g fc adm Lw) Hcons RUNN PWN
              (pwc_blkN_timeless g fc adm v I) TKN (ptkN_persistent g v I) WITN
              (pipesN_HWIT fc adm I Hfc Ha Hl) termw TOKN dep dep_tl
              N k γc γm (WSh i) alt_forkc c b (heldN i sw) Φ Hns Hw Hc Hb Hhin
              (cstep_okNh_prompt fc adm I Ha i sw c Hc (lookup_lt_Some _ _ _ Hb))
              with "[] Hex Hh HΦ").
    iApply pblkN_ecl_holds.
  Qed.
End pipes_prompt_at.

(* a list of per-writer existentials, at a duplicate-free list, is one
   existential function *)
Lemma big_sepL_exist_fun {PROP : bi} {A B : Type} `{!EqDecision A} (d : B)
    (l : list A) (Φ : A -> B -> PROP) :
  stdpp.base.NoDup l ->
  ([∗ list] x ∈ l, ∃ y, Φ x y) ⊢ ∃ f : A -> B, [∗ list] x ∈ l, Φ x (f x).
Proof using.
  induction l as [| x l IH]; intros Hnd.
  - iIntros "_". iExists (fun _ => d). done.
  - pose proof (NoDup_cons_1_1 x l Hnd) as Hx. pose proof (NoDup_cons_1_2 x l Hnd) as Hnd'. clear Hnd. rename Hnd' into Hnd.
    rewrite big_sepL_cons. iIntros "[Hx Hl]". iDestruct "Hx" as (y) "Hx".
    iDestruct (IH Hnd with "Hl") as (f) "Hl".
    iExists (fun z => if decide (z = x) then y else f z).
    rewrite big_sepL_cons decide_True //. iFrame "Hx".
    iApply (big_sepL_impl with "Hl"). iIntros "!>" (i z Hz) "H".
    rewrite decide_False; [done |]. intros ->. apply Hx.
    by eapply elem_of_list_lookup_2.
Qed.

Section UkShPipesFork.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{!uartGhostG Σ}.

  Local Notation T := (echo_taint γ).
  Local Notation Wcf := (pipes_Wcl_at g).
  Local Notation Wbf := (pipes_Wbl_at g).
  Local Notation lE I := (lineN fcE adm_echo I).

  (* =================================================================== *)
  (*  S1  THE TERMINAL SHAPE AND THE WIDENED CREDENTIAL                   *)
  (* =================================================================== *)
  Definition pterm_shapeN (I : list (bv 8)) (c : nat) : iProp Σ :=
    (∃ (v : era_pins) (γc γm : wid -> gname) (dep : wid -> list (bv 8) -> iProp Σ)
       (i : nat) (sw : nat -> list (bv 8)),
       ⌜(forall w s, Timeless (dep w s)) /\ adm_echo (lE I) = true /\ pl_ok (lE I)
        /\ (i < lcats (lE I))%nat /\ (1 <= nlines I)%nat⌝
       ∗ era_pin γ (S gen_id) v
       ∗ inp_lb v I
       ∗ pwc_fork_exitN (wids (lcats (lE I))) (runN fcE (lE I))
           (pwc_blkN g fcE adm_echo v I) (ptkN g v I) termw (tokN fcE (lE I))
           dep pnsN (S gen_id) γc γm (WSh i) alt_forkc c
       ∗ [∗ list] x ∈ heldN i sw,
           wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2))%I.

  (* THE ROUND COMMITTED BUT NOT FILED: every writer of the family at its
     whole source and not terminal -- what a completed round, or one whose
     top [pipe(2)] failed, hands the main loop; the prompt's first byte
     files it ([PipeOutN.pipesN_file], then the filing link) *)
  Definition pdone_shapeN (I : list (bv 8)) : iProp Σ :=
    (∃ (v : era_pins) (γc γm : wid -> gname) (dep : wid -> list (bv 8) -> iProp Σ),
       ⌜(forall w s, Timeless (dep w s)) /\ adm_echo (lE I) = true /\ pl_ok (lE I)⌝
       ∗ era_pin γ (S gen_id) v
       ∗ inp_lb v I
       ∗ blkN_inv (wids (lcats (lE I))) (runN fcE (lE I))
           (pwc_blkN g fcE adm_echo v I) termw (tokN fcE (lE I)) dep pnsN (S gen_id) γc γm
       ∗ [∗ list] w ∈ wids (lcats (lE I)),
           ∃ s, wcurN γc w (1/2) (length s) ∗ wmodeN γm w (1/2) (Some s)
                ∗ ⌜termw w s = false⌝)%I.

  Definition pterm_payN (I : list (bv 8)) : iProp Σ :=
    (UkShFork.ushf_wq Wcf I ∨ pterm_shapeN I 5%nat ∨ pdone_shapeN I)%I.

  Lemma pterm_shapeN_pin (I : list (bv 8)) (c : nat) :
    pterm_shapeN I c -∗
    (∃ v : era_pins, era_pin γ (S gen_id) v) ∗ pterm_shapeN I c.
  Proof using .
    rewrite /pterm_shapeN. iIntros "H".
    iDestruct "H" as (v γc γm dep i sw) "(%Hp & #Hpin & #Hlb & Hfe & Hh)".
    iSplitR; [ by iExists v; iFrame "Hpin" | ].
    iExists v, γc, γm, dep, i, sw. iSplitR; [ by iPureIntro | ].
    by iFrame "Hpin Hlb Hfe Hh".
  Qed.

  Lemma pterm_payN_taint (v : era_pins) (I : list (bv 8)) :
    era_pin γ (S gen_id) v -∗ T -∗ pterm_payN I.
  Proof using .
    iIntros "#Hpin #HT". rewrite /pterm_payN. iLeft.
    rewrite /UkShFork.ushf_wq. iRight.
    iApply (pipes_Hcltaint g I 0%nat v with "Hpin HT").
  Qed.

  Definition pterm_wcN (I : list (bv 8)) (p : nat) : iProp Σ :=
    (Wcf I p ∨ (⌜(p < 3)%nat⌝ ∗ pterm_shapeN I (5 + p)%nat)
     ∨ (⌜p = 0%nat⌝ ∗ pdone_shapeN I))%I.

  Lemma pterm_wcN_of (I : list (bv 8)) (p : nat) : Wcf I p -∗ pterm_wcN I p.
  Proof using . iIntros "H". rewrite /pterm_wcN. by iLeft. Qed.

  Lemma pterm_wcN_3 (I : list (bv 8)) : pterm_wcN I 3%nat -∗ Wcf I 3%nat.
  Proof using .
    rewrite /pterm_wcN. iIntros "[H | [[%Hlt _] | [%Hz _]]]"; [ iExact "H" | lia | lia ].
  Qed.

  Lemma pterm_wqN_pay (I : list (bv 8)) :
    UkShFork.ushf_wq pterm_wcN I ⊣⊢ pterm_payN I.
  Proof using .
    rewrite /pterm_payN /UkShFork.ushf_wq /pterm_wcN. iSplit.
    - iIntros "[[H | [[%Hlt _] | [%Hz _]]] | [H | [[_ H] | [_ H]]]]".
      + iLeft. by iLeft.
      + exfalso. lia.
      + exfalso. lia.
      + iLeft. by iRight.
      + iRight. iLeft. rewrite Nat.add_0_r. iExact "H".
      + iRight. iRight. iExact "H".
    - iIntros "[[H | H] | [H | H]]".
      + iLeft. by iLeft.
      + iRight. by iLeft.
      + iRight. iRight. iLeft. iSplitR; [ iPureIntro; lia | ].
        rewrite Nat.add_0_r. iExact "H".
      + iRight. iRight. iRight. iSplitR; [ by iPureIntro | ]. iExact "H".
  Qed.

  Lemma pterm_wbN_wc (I : list (bv 8)) : ⊢ Wbf I -∗ pterm_wcN I 0%nat.
  Proof using .
    iIntros "H". iApply pterm_wcN_of. iApply (pipes_Hwbwc g I with "H").
  Qed.

  Lemma pterm_wcN_blk_line (I : list (bv 8)) :
    ⊢ pterm_wcN I 3%nat -∗ pterm_wcN I 0%nat.
  Proof using .
    iIntros "H". iApply pterm_wcN_of.
    iApply (pipes_Hwbl g I with "[H]"). iApply (pterm_wcN_3 I with "H").
  Qed.

  Lemma pterm_wcpN_3 (l : list fdstate) (I : list (bv 8)) :
    UkSh.ush_wcp pterm_wcN Wbf l I 3%nat -∗ UkSh.ush_wcp Wcf Wbf l I 3%nat.
  Proof using .
    rewrite /UkSh.ush_wcp. iIntros "[[%Hrow Hc] | [%Hcl Hb]]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iApply (pterm_wcN_3 I with "Hc").
    - exfalso. destruct Hcl as [_ Hlt]. lia.
  Qed.

  Lemma pterm_wcpN_of (l : list fdstate) (I : list (bv 8)) (p : nat) :
    UkSh.ush_wcp Wcf Wbf l I p -∗ UkSh.ush_wcp pterm_wcN Wbf l I p.
  Proof using .
    rewrite /UkSh.ush_wcp. iIntros "[[%Hrow Hc] | [%Hcl Hb]]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iApply (pterm_wcN_of I p with "Hc").
    - iRight. iFrame "Hb". by iPureIntro.
  Qed.

  Lemma pterm_shapeN_inp (I : list (bv 8)) (c : nat) :
    pterm_shapeN I c -∗
    pterm_shapeN I c ∗ (∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I).
  Proof using .
    rewrite /pterm_shapeN. iIntros "H".
    iDestruct "H" as (v γc γm dep i sw) "(%Hp & #Hpin & #Hlb & Hfe & Hh)".
    iSplitR "".
    - iExists v, γc, γm, dep, i, sw. iSplitR; [ by iPureIntro | ].
      by iFrame "Hpin Hlb Hfe Hh".
    - iExists v. by iFrame "Hpin Hlb".
  Qed.

  Lemma pterm_wcN_inp_of
      (Hwcf : forall (I : list (bv 8)) (p : nat),
         ⊢ Wcf I p -∗ Wcf I p
           ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T))
      (I : list (bv 8)) (p : nat) :
    ⊢ pterm_wcN I p -∗ pterm_wcN I p
      ∗ ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ inp_lb v I) ∨ T).
  Proof using .
    rewrite {1}/pterm_wcN. iIntros "[Hc | [[%Hlt Hsh] | [%Hz Hsh]]]".
    - iDestruct (Hwcf I p with "Hc") as "[Hc $]".
      iApply (pterm_wcN_of I p with "Hc").
    - iDestruct (pterm_shapeN_inp I (5 + p)%nat with "Hsh") as "[Hsh Hi]".
      iSplitR "Hi"; [ | by iLeft ].
      rewrite /pterm_wcN. iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExact "Hsh".
    - rewrite /pdone_shapeN.
      iDestruct "Hsh" as (v γc γm dep) "(%Hp & #Hpin & #Hlb & Hrest)".
      iSplitR "".
      + rewrite /pterm_wcN. iRight. iRight. iSplitR; [ by iPureIntro | ].
        iExists v, γc, γm, dep. iSplitR; [ by iPureIntro | ]. by iFrame "Hpin Hlb Hrest".
      + iLeft. iExists v. by iFrame "Hpin Hlb".
  Qed.

  Context (N : uk_names Σ).
  Context (γp : gname).
  Context (Pm : list (bv 8) -> iProp Σ).

  Lemma pterm_poswN_3 (l : list fdstate) (ws : list (list (bv 8))) :
    UkSh.ush_posw N γp T pterm_wcN Wbf Pm l ws -∗
    UkSh.ush_posw N γp T Wcf Wbf Pm l ws.
  Proof using .
    rewrite /UkSh.ush_posw. iIntros "[H | H]"; [| iRight; iExact "H" ].
    iDestruct "H" as (I) "(%Hpure & Hpm & Hc)". iLeft. iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    iApply (pterm_wcpN_3 l I with "Hc").
  Qed.

  Lemma pterm_posbN_of (l : list fdstate) (p : nat) :
    UkSh.ush_posb N γp T Wcf Wbf Pm l p -∗
    UkSh.ush_posb N γp T pterm_wcN Wbf Pm l p.
  Proof using .
    rewrite /UkSh.ush_posb. iIntros "[H | H]"; [| iRight; iExact "H" ].
    iDestruct "H" as (I) "(%Hr & Hpm & Hc)". iLeft. iExists I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    iApply (pterm_wcpN_of l I p with "Hc").
  Qed.

  Lemma pterm_posbN_of_shape (l : list fdstate) (I : list (bv 8)) :
    UkSh.ush_fd0c l /\ UkSh.ush_fd1p l /\ UkSh.ush_fd2p l ->
    rest_of I = [] ->
    Pm I -∗ pterm_shapeN I 5%nat -∗
    UkSh.ush_posb N γp T pterm_wcN Wbf Pm l 0%nat.
  Proof using .
    intros Hrow Hrest. iIntros "Hpm Hsh". rewrite /UkSh.ush_posb.
    iLeft. iExists I. iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
    rewrite /pterm_wcN. iRight. iLeft. iSplitR; [ iPureIntro; lia | ].
    rewrite Nat.add_0_r. iExact "Hsh".
  Qed.

  Lemma pterm_posbN_of_done (l : list fdstate) (I : list (bv 8)) :
    UkSh.ush_fd0c l /\ UkSh.ush_fd1p l /\ UkSh.ush_fd2p l ->
    rest_of I = [] ->
    Pm I -∗ pdone_shapeN I -∗
    UkSh.ush_posb N γp T pterm_wcN Wbf Pm l 0%nat.
  Proof using .
    intros Hrow Hrest. iIntros "Hpm Hsh". rewrite /UkSh.ush_posb.
    iLeft. iExists I. iSplitR; [ by iPureIntro | ]. iFrame "Hpm".
    rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
    rewrite /pterm_wcN. iRight. iRight. iSplitR; [ by iPureIntro | ]. iExact "Hsh".
  Qed.

  (* =================================================================== *)
  (*  S2  THE READ AFTER A TERMINAL ROUND IS THE TAINT                    *)
  (* =================================================================== *)
  Definition pterm_read_lawN : Prop :=
    forall I l : list (bv 8),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ pterm_shapeN I 7%nat ={⊤}=∗
        Pm (I ++ l ++ [wl_nl])%list ∗ T.

  Lemma pterm_read_lawN_of :
    (forall I' : list (bv 8),
       ⊢ Pm I' -∗ Pm I'
         ∗ (∃ v : era_pins, era_pin γ (S gen_id) v
                            ∗ gwc_rres pipes_lmE (pipes_params g) v I')) ->
    pterm_read_lawN.
  Proof using .
    intros Hpm I l Hnl. iIntros "Hpm Hsh".
    iDestruct (Hpm (I ++ l ++ [wl_nl])%list with "Hpm") as "[Hpm Hv]".
    iDestruct "Hv" as (v') "[#Hpin' #Hres]".
    rewrite /pterm_shapeN.
    iDestruct "Hsh" as (v γc γm dep i sw) "(%Hp & #Hpin & _ & Hfe & _)".
    destruct Hp as (_ & _ & _ & _ & Hpos).
    iDestruct (era_pin_agree with "Hpin' Hpin") as %->.
    iModIntro. iFrame "Hpm".
    rewrite /pwc_fork_exitN. iDestruct "Hfe" as "(_ & _ & _ & [#Hfz | #HT])";
      [| iExact "HT"].
    iExFalso. rewrite /gwc_rres.
    iDestruct "Hres" as (ps0 cs0 s0) "(%Hrd & _ & _ & #Hcs0 & _)".
    destruct Hrd as (_ & _ & _ & Hle).
    assert (Hrl : removelast (I ++ l ++ [wl_nl]) = (I ++ l)%list).
    { rewrite app_assoc. apply epu_removelast_snoc. }
    rewrite Hrl in Hle.
    pose proof (nlines_app_le I l) as Hmono.
    iApply (cs_frozen_at_lb_absurd v (nlines I - 1)%nat cs0
              ltac:(lia) with "Hfz Hcs0").
  Qed.

  Lemma pterm_wcN_read_of :
    pterm_read_lawN ->
    (forall I l : list (bv 8),
       wl_nl ∉ l ->
       ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ Wcf I 2%nat ={⊤}=∗
         Pm (I ++ l ++ [wl_nl])%list ∗ Wcf (I ++ l ++ [wl_nl])%list 3%nat) ->
    forall I l : list (bv 8),
      wl_nl ∉ l ->
      ⊢ Pm (I ++ l ++ [wl_nl])%list -∗ pterm_wcN I 2%nat ={⊤}=∗
        Pm (I ++ l ++ [wl_nl])%list ∗ pterm_wcN (I ++ l ++ [wl_nl])%list 3%nat.
  Proof using .
    intros Hterm Hlanded I l Hnl. iIntros "Hpm Hc".
    rewrite {1}/pterm_wcN. iDestruct "Hc" as "[Hc | [[_ Hsh] | [%Hz _]]]"; [| | lia].
    - iMod (Hlanded I l Hnl with "Hpm Hc") as "[$ Hw]". iModIntro.
      iApply (pterm_wcN_of _ 3%nat with "Hw").
    - iDestruct (pterm_shapeN_pin I 7%nat with "Hsh") as "[Hpv Hsh]".
      iDestruct "Hpv" as (v) "#Hpin".
      iMod (Hterm I l Hnl with "Hpm Hsh") as "[$ #HT]". iModIntro.
      iApply (pterm_wcN_of _ 3%nat).
      iApply (pipes_Hcltaint g (I ++ l ++ [wl_nl])%list 3%nat v with "Hpin HT").
  Qed.
End UkShPipesFork.

#[global] Typeclasses Opaque pipes_Wcl_at.
#[global] Typeclasses Opaque pipes_Wbl_at.
#[global] Typeclasses Opaque pterm_shapeN.
#[global] Typeclasses Opaque pterm_payN.
#[global] Typeclasses Opaque pterm_wcN.

(* ===================================================================== *)
(*  S3  THE TWO PROMPT BYTES AT THE TERMINAL ARM                          *)
(* ===================================================================== *)
Section UkShPipesForkPrompt.
  Context {Σ : gFunctors}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !pipeOutG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.
  Context `{PS : uprogSG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{!uartGhostG Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclE g).

  Local Notation Wcf := (pipes_Wcl_at g).
  Local Notation lE I := (lineN fcE adm_echo I).

  Lemma alt_forkc_prompt (p : nat) (b : bv 8) :
    u_prompt !! p = Some b -> alt_forkc !! (5 + p)%nat = Some b.
  Proof using.
    intros Hb. rewrite alt_forkc_fork lookup_app_r; [| rewrite dg_fork_b_len; lia].
    by rewrite dg_fork_b_len Nat.add_sub_swap // Nat.sub_diag Nat.add_0_l.
  Qed.

  Lemma pterm_prompt_stepN (I : list (bv 8)) :
    ⊢ UShPanic.prompt_step (fun p : nat => pterm_shapeN g I (5 + p)%nat).
  Proof using Hcons.
    rewrite /UShPanic.prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hsh HΦ".
    rewrite /pterm_shapeN.
    iDestruct "Hsh" as (v γc γm dep i sw) "(%Hpp & #Hpin & #Hlb & Hfe & Hh)".
    destruct Hpp as (Hdtl & Ha & Hl & Hi & Hpos).
    iApply (pipesN_prompt_at g fcE adm_echo pipes_lm_echo_laws Hcons fc_none_ok v I Ha Hl
              pnsN (S gen_id) i γc γm dep Hdtl sw (5 + p)%nat b Φ
              ltac:(solve_ndisj) ltac:(apply wids_elem; lia) ltac:(lia)
              (alt_forkc_prompt p b Hb)
              with "Hfe Hh [HΦ]").
    { intros x Hx. rewrite /heldN elem_of_list_fmap in Hx.
      destruct Hx as (j & -> & Hj). apply elem_of_seq in Hj.
      cbn [fst]. apply wids_elem. lia. }
    iIntros "Hfe Hh". iApply "HΦ".
    iExists v, γc, γm, dep, i, sw. iSplitR; [ by iPureIntro | ].
    rewrite (_ : (5 + S p)%nat = S (5 + p)); [| lia].
    by iFrame "Hpin Hlb Hfe Hh".
  Qed.

  Lemma pterm_prompt_armN (Np : uk_names Σ) (I : list (bv 8))
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    shk_rodata (ukn_t Np) -∗
    UkSh.ksh_w (PS := uprogSG_free) Np (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd Np) l ∗ pterm_shapeN g I 5%nat)
      (UserFd.ustd (ukn_fd Np) l ∗ pterm_shapeN g I 7%nat).
  Proof using Hcons.
    intros Hl2. iIntros "#Hro".
    iPoseProof (pterm_prompt_stepN I) as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
              (fun p : nat => pterm_shapeN g I (5 + p)%nat) l rb Hl2
              with "Hst Hro").
  Qed.
  (* THE COMMITTED ROUND'S PROMPT: its first byte files the block the
     family hands back, and is then the filing link's [$]; its second is
     the landed space at the record *)
  Definition pdone_fam (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => pdone_shapeN g I
    | S _ => pipes_Wcl_at g I p
    end.

  Lemma pdone_prompt_stepN (I : list (bv 8)) :
    ⊢ UShPanic.prompt_step (pdone_fam I).
  Proof using Hcons.
    rewrite /UShPanic.prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hsh HΦ".
    assert (Hbt : b = u_prompt !!! p)
      by (symmetry; exact (list_lookup_total_correct u_prompt p b Hb)).
    iAssert (pipes_links g) as "#Hlk"; [by iApply pipes_links_holds |].
    destruct p as [| [| p]]; [ | | exfalso; lia ].
    - (* the `$': file, then the filing link *)
      cbn [pdone_fam]. rewrite /pdone_shapeN.
      iDestruct "Hsh" as (v γc γm dep) "(%Hpp & #Hpin & #Hlb & #Hinv & Hall)".
      destruct Hpp as (Hdtl & Ha & Hl).
      iDestruct (big_sepL_exist_fun [] _ _ (wids_NoDup _) with "Hall") as (sw) "Hall".
      iDestruct (big_sepL_sep with "Hall") as "[Hc Hrest]".
      iDestruct (big_sepL_sep with "Hrest") as "[Hm Hterm]".
      iDestruct (big_sepL_pure_1 with "Hterm") as %Hterm.
      rewrite /out_link. iIntros (o H) "#Hlbo Hres".
      iMod (pipesN_file g fcE adm_echo fc_none_ok v I Ha Hl (⊤ ∖ ↑uartN Uart0) pnsN
              (S gen_id) γc γm termw (tokN fcE (lE I)) dep Hdtl sw
              ltac:(solve_ndisj)
              ltac:(intros w Hw; apply elem_of_list_lookup in Hw as [j Hj];
                    exact (Hterm j w Hj))
              with "Hinv [Hc Hm]") as (pre) "[HPW %Hbl]".
      { iApply big_sepL_sep. iFrame "Hc Hm". }
      iPoseProof (pipes_X_dollar g (S gen_id) v I b Φ Hbt with "Hpin Hlk [HPW] [HΦ]")
        as "Hol".
      { rewrite /pipes_X. iExists pre. iFrame "HPW". by iPureIntro. }
      { iIntros "Hc". iApply "HΦ". cbn [pdone_fam].
        rewrite /pipes_Wcl_at /lk_lcred. iExists v. iFrame "Hpin".
        rewrite (lk_lpr_1 (pipes_link_inst_at g)). iExact "Hc". }
      rewrite /out_link. iApply ("Hol" $! o H with "Hlbo Hres").
    - (* the space: the landed step *)
      cbn [pdone_fam]. rewrite /pipes_Wcl_at /lk_lcred.
      iDestruct "Hsh" as (v) "[#Hpin Hc]".
      rewrite (lk_lpr_1 (pipes_link_inst_at g)).
      iApply (lk_prompt_space_t (pipes_link_inst_at g) (S gen_id) v I b Φ Hbt
                with "Hpin Hlk Hc [HΦ]").
      iIntros "Hc". iApply "HΦ". cbn [pdone_fam].
      rewrite /pipes_Wcl_at /lk_lcred. iExists v. iFrame "Hpin".
      rewrite (lk_lpr_2 (pipes_link_inst_at g)). iExact "Hc".
  Qed.

  Lemma pdone_prompt_armN (Np : uk_names Σ) (I : list (bv 8))
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    shk_rodata (ukn_t Np) -∗
    UkSh.ksh_w (PS := uprogSG_free) Np (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd Np) l ∗ pdone_shapeN g I)
      (UserFd.ustd (ukn_fd Np) l ∗ pipes_Wcl_at g I 2%nat).
  Proof using Hcons.
    intros Hl2. iIntros "#Hro".
    iPoseProof (pdone_prompt_stepN I) as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
              (pdone_fam I) l rb Hl2 with "Hst Hro").
  Qed.
End UkShPipesForkPrompt.
