(* ===================================================================== *)
(*  PipeBothN.v -- THE N-WRITER CONSOLE FAMILY (design:                  *)
(*  claude-notes/design/pipes-general.md SS2.2, cut C5).                 *)
(*                                                                       *)
(*  [PipeBoth.blk2_inv]'s family, over any finite set of writers [ws] of  *)
(*  an abstract index type [W], and over an ABSTRACT claim: the family    *)
(*  reads the console claim only through the round's credential          *)
(*  [PW k pre tm] (the claim's round ledger at the merged bytes [pre] and *)
(*  the terminal flag [tm]) and ONE claim obligation [eclN] -- the four   *)
(*  landed obligations [pblk2_ecl_L/_R/_L_t/_R_t] in one, since a byte    *)
(*  is a byte whoever writes it.  [PipeOutN] instantiates both at the     *)
(*  generic claim over [PipesDisc.pipes_lm].                             *)
(*                                                                       *)
(*  THE STATE.  [md w] is writer [w]'s source once it has FIRED (its     *)
(*  mode, fixed at its first byte or at a silent exit), [sel] names the   *)
(*  writer of every byte on the wire, and the block so far is             *)
(*  [PipeBothNPure.pendN md sel].  Each writer holds HALF of its cursor   *)
(*  [wcurN] and of its mode [wmodeN]; the family holds the other halves   *)
(*  and, for every COMMITTED writer (one that has written, or has fixed   *)
(*  the empty source), its DEPOSIT [dep w s] -- the landed [XL]/[YR].     *)
(*                                                                       *)
(*  THE PURE INVARIANT.  While the round is not terminal the committed    *)
(*  sources, every uncommitted writer read as SILENT, ARE a complete run  *)
(*  of the model ([PipeBothNPure.runS]; so they are compatible,           *)
(*  [compatN]), so the block so far completes to one of                   *)
(*  its blocks ([pendN_complete]) and the claim's witness for the next    *)
(*  byte is DERIVED here, not supplied.  A writer COMMITS at its first    *)
(*  byte ([blkN_fire]) or at a silent exit ([blkN_silence]), and that is  *)
(*  where the exclusions of design SS2.2 are spent, in the landed shape   *)
(*  [□ (X -∗ Y ={Eex}=∗ False)]: the committer's premise names, for every *)
(*  family state its commit would make incompatible, a committed writer  *)
(*  whose deposit refutes its own.  A terminal round (a fork failure:     *)
(*  a writer whose source [TERM] flags has written) keeps the invariant   *)
(*  [TOK] instead (a commit there may be refuted the same way), and a     *)
(*  byte may read the halves of other writers its writer holds            *)
(*  ([blkN_cstep_h]: the prompt after the waited stages).  At the         *)
(*  pipeline [TOK] and the terminal witness are [PipeBothNPure.tokN] and  *)
(*  [tokN_blocks], discharged in [PipeOutN].                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ConsLog.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import PipeBothNPure.
(* stdpp's list names over the ones the Stdlib import above re-exports *)
From stdpp Require Import list.
Local Open Scope list_scope.

Section blkN.
  Context {Σ : gFunctors} `{HRg : !riscvGS Σ}.
  Context `{!ghost_varG Σ nat} `{!ghost_varG Σ (option (list (bv 8)))}.
  Context {W : Type} `{EqW : !EqDecision W}.
  (* the committed writers, at this family's writer type *)
  Local Notation cmtN := (@PipeBothNPure.cmtN W EqW).
  Local Notation rmd := (@PipeBothNPure.rmd W EqW).
  (* THE WRITERS, each once *)
  Context (ws : list W) (Hnd : stdpp.base.NoDup ws).
  (* THE CLAIM, as the port reads it *)
  Context (CL : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = CL).
  (* THE MODEL: the complete runs, as source vectors *)
  Context (RUN : (W -> list (bv 8)) -> Prop).
  (* THE ROUND'S CLAIM CREDENTIAL at the merged bytes and the flag, and
     what a terminal byte hands the writer (the frozen resolution) *)
  Context (PW : nat -> list (bv 8) -> bool -> iProp Σ).
  Context (PW_tl : forall k pre tm, Timeless (PW k pre tm)).
  Context (TK : nat -> iProp Σ) (TK_pers : forall k, Persistent (TK k)).
  (* WHAT THE CLAIM ASKS OF A BLOCK at each flag; the non-terminal one is
     implied by the model's blocks *)
  Context (WIT : bool -> list (bv 8) -> Prop).
  Context (HWIT : forall pre bl, blkN ws RUN bl -> pre `prefix_of` bl -> WIT false pre).
  (* THE TERMINAL SOURCES, and the caller's invariant of a terminal round *)
  Context (TERM : W -> list (bv 8) -> bool).
  Context (TOK : (W -> option (list (bv 8))) -> list W -> Prop).
  (* THE DEPOSITS *)
  Context (dep : W -> list (bv 8) -> iProp Σ).
  Context (dep_tl : forall w s, Timeless (dep w s)).

  Lemma chist_at0_N (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = CL kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ================================================================= *)
  (*  1.  THE PURE STATE                                               *)
  (* ================================================================= *)

  (* the round is terminal once a terminal source has put a byte on the
     wire (the landed [tmb]: mode 3 at [c2 > 0]) *)
  Definition tmN (md : W -> option (list (bv 8))) (sel : list W) : bool :=
    existsb (fun w => TERM w (srcN md w)) sel.

  (* the committed writers and their sources: [PipeBothNPure.cmtN] /
     [PipeBothNPure.rmd] *)

  Definition invN (md : W -> option (list (bv 8))) (sel : list W) : Prop :=
    (tmN md sel = false -> runS RUN (rmd md sel))
    /\ (tmN md sel = true -> TOK md sel).

  Definition famN (md : W -> option (list (bv 8))) (sel : list W) : Prop :=
    (forall x, x ∈ sel -> x ∈ ws)
    /\ (forall x, md x <> None -> x ∈ ws)
    /\ sel_firedN md sel
    /\ sel_wfN (srcN md) sel
    /\ invN md sel.

  (* ---- the flag's laws ---- *)
  Lemma tmN_snoc md sel w : tmN md (sel ++ [w]) = tmN md sel || TERM w (srcN md w).
  Proof using. rewrite /tmN existsb_app /=. by rewrite orb_false_r. Qed.

  Lemma tmN_snoc_in md sel w : w ∈ sel -> tmN md (sel ++ [w]) = tmN md sel.
  Proof using.
    intros Hw. rewrite tmN_snoc. destruct (TERM w (srcN md w)) eqn:Ht;
      [| by rewrite orb_false_r].
    assert (Hs : tmN md sel = true).
    { rewrite /tmN existsb_exists. exists w. split; [by apply list_elem_of_In | exact Ht]. }
    by rewrite Hs.
  Qed.

  Lemma tmN_ext md md' sel :
    (forall x, x ∈ sel -> md' x = md x) -> tmN md' sel = tmN md sel.
  Proof using.
    intros Hx. rewrite /tmN. induction sel as [| y s IH]; [reflexivity |].
    cbn [existsb]. rewrite /srcN (Hx y (list_elem_of_here y s)).
    f_equal. apply IH. intros x Hin. apply Hx. by apply list_elem_of_further.
  Qed.

  (* ---- the committed sources' laws ---- *)
  Lemma compatN_ext md md' : (forall x, md' x = md x) -> compatN RUN md -> compatN RUN md'.
  Proof using.
    intros Hx (src & Hr & Hag). exists src. split; [exact Hr |].
    intros w s Hs. apply Hag. by rewrite -Hx.
  Qed.

  Lemma rmd_in md sel x : x ∈ sel -> rmd md sel x = md x.
  Proof using. intros Hx. rewrite /rmd /cmtN bool_decide_true; [done | by left]. Qed.

  Lemma sel_firedN_rmd md sel : sel_firedN md sel -> sel_firedN (rmd md sel) sel.
  Proof using. intros Hf x Hx. rewrite rmd_in; [exact (Hf x Hx) | exact Hx]. Qed.

  Lemma srcN_rmd md sel x : x ∈ sel -> srcN (rmd md sel) x = srcN md x.
  Proof using. intros Hx. by rewrite /srcN rmd_in. Qed.

  Lemma sel_wfN_rmd md sel : sel_wfN (srcN md) sel -> sel_wfN (srcN (rmd md sel)) sel.
  Proof using.
    clear TERM TOK. (* unused; else Rocq counts it as used (asks for Proof using … TERM TOK) *)
    intros Hwf x. destruct (decide (x ∈ sel)) as [Hx | Hx].
    - rewrite srcN_rmd; [apply Hwf | exact Hx].
    - rewrite (cntN_nil_notin sel x Hx). lia.
  Qed.

  Lemma pendN_rmd md sel : pendN (rmd md sel) sel = pendN md sel.
  Proof using.
    rewrite /pendN. apply mergeN_local. intros x Hx. by rewrite srcN_rmd.
  Qed.

  (* THE NON-TERMINAL WITNESS, DERIVED: a compatible family's block is
     what the claim asks of a non-terminal byte *)
  Lemma witN_nt md sel :
    famN md sel -> compatN RUN (rmd md sel) -> WIT false (pendN md sel).
  Proof using Hnd HWIT.
    intros (Hin & _ & Hfd & Hwf & _) Hc.
    destruct (pendN_complete ws RUN (rmd md sel) sel Hnd Hin (sel_firedN_rmd md sel Hfd)
                (sel_wfN_rmd md sel Hwf) Hc) as (bl & Hb & Hp).
    rewrite pendN_rmd in Hp. exact (HWIT _ bl Hb Hp).
  Qed.

  (* ---- the fire's pure step: writer [w], unfired and unwritten, fixes
       [s] and writes its first byte ---- *)
  Lemma cmtN_fire md sel w s x :
    x <> w -> cmtN (mdupd md w s) (sel ++ [w]) x = cmtN md sel x.
  Proof using.
    intros Hne. rewrite /cmtN /mdupd decide_False; [| exact Hne].
    apply bool_decide_ext. rewrite elem_of_app list_elem_of_singleton.
    split; [intros [[Hx | Hx] | Hx]; [by left | by destruct (Hne Hx) | by right]
           | intros [Hx | Hx]; [by left; left | by right]].
  Qed.

  Lemma cmtN_fire_self md sel w s : cmtN (mdupd md w s) (sel ++ [w]) w = true.
  Proof using.
    rewrite /cmtN bool_decide_true; [done |]. left. apply elem_of_app. right.
    by apply list_elem_of_singleton.
  Qed.

  Lemma cmtN_step md sel w x : w ∈ sel -> cmtN md (sel ++ [w]) x = cmtN md sel x.
  Proof using.
    intros Hw. rewrite /cmtN. apply bool_decide_ext.
    rewrite elem_of_app list_elem_of_singleton.
    split; [intros [[Hx | ->] | Hx]; [by left | by left | by right]
           | intros [Hx | Hx]; [by left; left | by right]].
  Qed.

  Lemma cmtN_silence md sel w x :
    x <> w -> cmtN (mdupd md w []) sel x = cmtN md sel x.
  Proof using. intros Hne. by rewrite /cmtN /mdupd decide_False. Qed.

  Lemma cmtN_silence_self md sel w : cmtN (mdupd md w []) sel w = true.
  Proof using. rewrite /cmtN /mdupd decide_True; [| done]. rewrite bool_decide_true; [done | by right]. Qed.

  (* ================================================================= *)
  (*  2.  THE GHOSTS, AND THE FAMILY                                    *)
  (* ================================================================= *)

  Definition wcurN (γc : W -> gname) (w : W) (q : Qp) (c : nat) : iProp Σ :=
    ghost_var_frac (γc w) q c.
  Definition wmodeN (γm : W -> gname) (w : W) (q : Qp)
      (o : option (list (bv 8))) : iProp Σ :=
    ghost_var_frac (γm w) q o.

  Global Instance wcurN_timeless γc w q c : Timeless (wcurN γc w q c).
  Proof using. rewrite /wcurN. apply _. Qed.
  Global Instance wmodeN_timeless γm w q o : Timeless (wmodeN γm w q o).
  Proof using. rewrite /wmodeN. apply _. Qed.

  (* ONE WRITER'S SHARE OF THE FAMILY *)
  Definition wstN (γc γm : W -> gname) (md : W -> option (list (bv 8)))
      (sel : list W) (w : W) : iProp Σ :=
    (wcurN γc w (1/2) (cntN sel w) ∗ wmodeN γm w (1/2) (md w)
     ∗ (if cmtN md sel w then dep w (srcN md w) else emp))%I.

  Global Instance wstN_timeless γc γm md sel w : Timeless (wstN γc γm md sel w).
  Proof using dep_tl.
    rewrite /wstN. apply bi.sep_timeless; [apply _ |].
    apply bi.sep_timeless; [apply _ |]. destruct (cmtN md sel w); apply _.
  Qed.

  (* THE DONE ARM: every cursor, parked whole *)
  Definition blkN_done (γc : W -> gname) : iProp Σ :=
    [∗ list] w ∈ ws, ∃ c : nat, wcurN γc w 1 c.

  Definition blkN_body (k : nat) (γc γm : W -> gname) : iProp Σ :=
    ((∃ (md : W -> option (list (bv 8))) (sel : list W),
        PW k (pendN md sel) (tmN md sel)
        ∗ ([∗ list] w ∈ ws, wstN γc γm md sel w)
        ∗ ⌜famN md sel⌝)
     ∨ blkN_done γc)%I.

  Global Instance blkN_body_timeless k γc γm : Timeless (blkN_body k γc γm).
  Proof using PW_tl dep_tl.
    rewrite /blkN_body. apply bi.or_timeless; [| apply _].
    apply bi.exist_timeless; intro md. apply bi.exist_timeless; intro sel.
    apply bi.sep_timeless; [apply PW_tl |]. apply bi.sep_timeless; [| apply _].
    apply big_sepL_timeless. intros. apply _.
  Qed.

  Definition blkN_inv (N : namespace) (k : nat) (γc γm : W -> gname) : iProp Σ :=
    inv N (blkN_body k γc γm).

  Global Instance blkN_inv_persistent N k γc γm : Persistent (blkN_inv N k γc γm).
  Proof using. rewrite /blkN_inv. apply _. Qed.

  (* THE CLAIM'S ONE OBLIGATION: a byte of the round, at any flag *)
  Definition eclN : iProp Σ :=
    (□ ∀ (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
         (pre : list (bv 8)) (b : bv 8) (tm tm' : bool),
        ⌜tm = true -> tm' = true⌝ -∗ ⌜WIT tm' (pre ++ [b])⌝ -∗
        PW k pre tm -∗ CL k ho H ==∗
          CL k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ PW k (pre ++ [b]) tm' ∗ (⌜tm' = false⌝ ∨ TK k))%I.

  Global Instance eclN_persistent : Persistent eclN.
  Proof using. rewrite /eclN. apply bi.intuitionistically_persistent. Qed.

  (* ---- one writer's share, framed across a step that is not its own ---- *)
  Lemma wstN_frame γc γm md sel md' sel' x :
    cntN sel' x = cntN sel x -> md' x = md x -> cmtN md' sel' x = cmtN md sel x ->
    wstN γc γm md sel x -∗ wstN γc γm md' sel' x.
  Proof using.
    intros H1 H2 H3. rewrite /wstN /srcN H1 H2 H3. by iIntros "$".
  Qed.

  Lemma big_wstN_step γc γm md sel md' sel' w :
    w ∈ ws ->
    (forall x, x <> w ->
       cntN sel' x = cntN sel x /\ md' x = md x /\ cmtN md' sel' x = cmtN md sel x) ->
    ([∗ list] x ∈ ws, wstN γc γm md sel x) -∗
    wstN γc γm md sel w
    ∗ (wstN γc γm md' sel' w -∗ [∗ list] x ∈ ws, wstN γc γm md' sel' x).
  Proof using Hnd.
    intros Hw Hfr. destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iIntros "Hb".
    iDestruct (big_sepL_lookup_acc_impl i w Hi with "Hb") as "[$ Hcl]".
    iIntros "Hw". iApply ("Hcl" $! (fun _ x => wstN γc γm md' sel' x) with "[] Hw").
    iModIntro. iIntros (j x Hj Hne) "Hx".
    assert (Hxw : x <> w).
    { intros ->. apply Hne. exact (NoDup_lookup ws j i w Hnd Hj Hi). }
    destruct (Hfr x Hxw) as (H1 & H2 & H3).
    iApply (wstN_frame γc γm md sel md' sel' x H1 H2 H3 with "Hx").
  Qed.

  (* a committed writer's deposit, read out of the family *)
  Lemma big_wstN_dep γc γm md sel w s :
    w ∈ ws -> cmtN md sel w = true -> md w = Some s ->
    ([∗ list] x ∈ ws, wstN γc γm md sel x) -∗ dep w s.
  Proof using.
    intros Hw Hc Hs. destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iIntros "Hb". iDestruct (big_sepL_lookup _ _ i w Hi with "Hb") as "(_ & _ & Hd)".
    rewrite Hc /srcN Hs. iExact "Hd".
  Qed.

  (* a writer's cursor half refutes the DONE arm *)
  Lemma blkN_done_not γc w q c :
    w ∈ ws -> wcurN γc w q c -∗ blkN_done γc -∗ False.
  Proof using.
    intros Hw. destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iIntros "H1 Hd". iDestruct (big_sepL_lookup _ _ i w Hi with "Hd") as (c') "H2".
    rewrite /wcurN. iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    exfalso. apply (Qp.not_add_le_r q 1). exact Hq.
  Qed.

  (* ================================================================= *)
  (*  3.  THE ENTRY                                                     *)
  (* ================================================================= *)

  Lemma ghost_vars_alloc {A : Type} `{!ghost_varG Σ A} (l : list W) (a : A) :
    stdpp.base.NoDup l ->
    ⊢ |==> ∃ γ : W -> gname,
        [∗ list] w ∈ l, ghost_var_frac (γ w) (1/2) a ∗ ghost_var_frac (γ w) (1/2) a.
  Proof using EqW.
    induction l as [| x l IH]; intros Hl.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hl as [Hx Hl].
      iMod (IH Hl) as (γ') "Hl".
      iMod (ghost_var_alloc a) as (γx) "Hx".
      iDestruct (ghost_var_split γx a (1/2) (1/2) with "[Hx]") as "[Hx1 Hx2]";
        [by rewrite Qp.half_half |].
      iModIntro. iExists (fun w => if decide (w = x) then γx else γ' w).
      rewrite big_sepL_cons. rewrite decide_True; [| done]. iFrame "Hx1 Hx2".
      iApply (big_sepL_impl with "Hl"). iModIntro. iIntros (j y Hj) "Hy".
      assert (Hyx : y <> x).
      { intros ->. apply Hx. exact (list_elem_of_lookup_2 _ _ _ Hj). }
      rewrite decide_False; [| exact Hyx]. iExact "Hy".
  Qed.

  (* THE ROUND'S LEND: the family at the empty block, every writer's two
     halves handed out *)
  Lemma blkN_alloc (E : coPset) (N : namespace) (k : nat) :
    runS RUN (fun _ => None) ->
    PW k [] false ={E}=∗
    ∃ γc γm : W -> gname,
      blkN_inv N k γc γm
      ∗ [∗ list] w ∈ ws, wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None.
  Proof using Hnd.
    intros Hr0. iIntros "HPW".
    iMod (ghost_vars_alloc (A := nat) ws 0 Hnd) as (γc) "Hc".
    iMod (ghost_vars_alloc (A := option (list (bv 8))) ws None Hnd) as (γm) "Hm".
    iDestruct (big_sepL_sep_2 with "Hc Hm") as "Hcm".
    iAssert (([∗ list] w ∈ ws, wstN γc γm (fun _ => None) [] w)
             ∗ [∗ list] w ∈ ws, wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None)%I
      with "[Hcm]" as "[Hfam Hout]".
    { rewrite -big_sepL_sep. iApply (big_sepL_impl with "Hcm"). iModIntro.
      iIntros (j w _) "[[Hc1 Hc2] [Hm1 Hm2]]". rewrite /wstN /wcurN /wmodeN.
      cbn [cntN]. rewrite /cmtN bool_decide_false; last first.
      { intros [Hin | Hq]; [by apply elem_of_nil in Hin | discriminate Hq]. }
      iFrame. }
    iMod (inv_alloc N E (blkN_body k γc γm) with "[HPW Hfam]") as "#Hinv".
    { iNext. rewrite /blkN_body. iLeft. iExists (fun _ => None), [].
      rewrite /pendN /tmN. cbn [mergeN existsb]. iFrame "HPW Hfam".
      iPureIntro. split_and!.
      - intros x Hx. by apply elem_of_nil in Hx.
      - intros x Hx. by destruct (Hx eq_refl).
      - intros x Hx. by apply elem_of_nil in Hx.
      - intros x. cbn [cntN]. lia.
      - split; [| discriminate]. intros _.
        apply (runS_ext RUN (fun _ => None)); [| exact Hr0].
        intros w. rewrite /rmd. by destruct (cmtN _ _ w). }
    iModIntro. iExists γc, γm. iFrame "Hinv Hout".
  Qed.

  (* ================================================================= *)
  (*  4.  THE FIRE: a writer's first byte fixes its source and commits  *)
  (* ================================================================= *)

  (* the fire's premise: every family state it could meet either stays
     compatible under the commit, or holds a committed writer whose
     deposit refutes this one's; at a terminal step, the caller's
     invariant and the claim's witness *)
  Definition fire_okN (w : W) (s : list (bv 8))
      (EXCL : W -> list (bv 8) -> Prop) : Prop :=
    forall md sel, famN md sel -> md w = None -> w ∉ sel ->
      (tmN (mdupd md w s) (sel ++ [w]) = false ->
         runS RUN (rmd (mdupd md w s) (sel ++ [w]))
         \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s')
      /\ (tmN (mdupd md w s) (sel ++ [w]) = true ->
            (TOK (mdupd md w s) (sel ++ [w])
             /\ WIT true (pendN (mdupd md w s) (sel ++ [w])))
            \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s').

  Lemma blkN_fire (N : namespace) (Eex : coPset) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (b : bv 8)
      (EXCL : W -> list (bv 8) -> Prop) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    w ∈ ws -> s !! 0%nat = Some b ->
    fire_okN w s EXCL ->
    □ (∀ w' s', ⌜EXCL w' s'⌝ -∗ dep w' s' -∗ dep w s ={Eex}=∗ False) -∗
    eclN -∗ blkN_inv N k γc γm -∗
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ dep w s -∗
    (wcurN γc w (1/2) 1 -∗ wmodeN γm w (1/2) (Some s)
     -∗ (⌜TERM w s = false⌝ ∨ TK k) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns HEx Hw Hb Hok.
    iIntros "#Hex #Hecl #Hinv HcW HmW Hdep HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !chist_at0_N.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blkN_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not γc w with "HcW Hdone") as %[]. exact Hw. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    (* the writer's own share: cursor 0, unfired *)
    destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iAssert (⌜cntN sel w = 0%nat /\ md w = None⌝)%I as %[Hc0 Hmw].
    { iDestruct (big_sepL_lookup _ _ i w Hi with "Hb") as "(Hc & Hm & _)".
      rewrite /wcurN /wmodeN.
      iDestruct (ghost_var_agree with "HcW Hc") as %Hc.
      iDestruct (ghost_var_agree with "HmW Hm") as %Hm. by iPureIntro. }
    assert (Hwsel : w ∉ sel).
    { intros Hx. apply cntN_elem in Hx. exact (Hx Hc0). }
    set (md' := mdupd md w s). set (sel' := sel ++ [w]).
    destruct (Hok md sel Hfam Hmw Hwsel) as [Hnt Ht].
    (* the flag after the byte, and the block *)
    assert (Htm : tmN md' sel' = tmN md sel || TERM w s).
    { rewrite /sel' tmN_snoc. rewrite /md' (tmN_ext md (mdupd md w s) sel);
        [| intros x Hx; rewrite /mdupd decide_False; [done | intros ->; exact (Hwsel Hx)]].
      by rewrite srcN_mdupd_self. }
    assert (Hwf' : sel_wfN (srcN md') sel) by exact (sel_wfN_mdupd md sel w s Hwsel Hwf).
    assert (Hpend : pendN md' sel' = pendN md sel ++ [b]).
    { rewrite /sel' (pendN_snoc md' sel w s b Hwf'); [| by rewrite /md' /mdupd decide_True | by rewrite Hc0].
      by rewrite /md' pendN_mdupd. }
    (* WHICH CASE: compatible, excluded, or terminal *)
    destruct (tmN md' sel') eqn:Htm'.
    - (* THE TERMINAL BYTE: at the invariant, or refuted *)
      destruct (Ht Htm') as [[Htok Hwit] | (w' & s' & Hcw' & Hmw' & Hx)]; last first.
      { (* AN EXCLUDED PAIR, as at a non-terminal byte *)
        assert (Hw' : w' ∈ ws) by (apply Hmin; rewrite Hmw'; discriminate).
        iDestruct (big_wstN_dep γc γm md sel w' s' Hw' Hcw' Hmw' with "Hb") as "Hd'".
        iMod (fupd_mask_subseteq Eex) as "_"; [exact HEx |].
        iMod ("Hex" $! w' s' with "[%] Hd' Hdep") as "[]". exact Hx. }
      iMod ("Hecl" $! k (default [] o) H (pendN md sel) b (tmN md sel) true
              with "[%] [%] HPW Hres") as "(Hres & HPW & #HTK)".
      { by intros _. }
      { rewrite -Hpend. exact Hwit. }
      iDestruct (big_wstN_step γc γm md sel md' sel' w Hw with "Hb") as "[Hw Hcl]".
      { intros x Hne. split; [rewrite /sel' cntN_other_snoc; [done | exact Hne] |].
        split; [by rewrite /md' /mdupd decide_False |]. by rewrite /md' /sel' cmtN_fire. }
      iDestruct "Hw" as "(Hc & Hm & _)". rewrite /wcurN /wmodeN.
      iMod (ghost_var_update_halves 1%nat with "HcW Hc") as "[HcW Hc]".
      iMod (ghost_var_update_halves (Some s) with "HmW Hm") as "[HmW Hm]".
      iMod ("Hclose" with "[HPW Hc Hm Hdep Hcl]") as "_".
      { iNext. rewrite /blkN_body. iLeft. iExists md', sel'. rewrite Htm' Hpend.
        iFrame "HPW". iSplitL "Hc Hm Hdep Hcl".
        - iApply "Hcl". rewrite /wstN /wcurN /wmodeN /sel' cntN_self_snoc Hc0.
          rewrite /md' cmtN_fire_self srcN_mdupd_self /mdupd decide_True; [| done].
          iFrame.
        - iPureIntro. split_and!.
          + intros x Hx. apply elem_of_app in Hx as [Hx | Hx]; [exact (Hin x Hx) |].
            apply list_elem_of_singleton in Hx as ->. exact Hw.
          + intros x Hx. rewrite /md' /mdupd in Hx. case_decide as Hq; [subst x; exact Hw |].
            exact (Hmin x Hx).
          + apply sel_firedN_snoc; [exact (sel_firedN_mdupd md sel w s Hfd) |].
            rewrite /md' /mdupd decide_True; [by eexists | done].
          + apply (sel_wfN_fired_snoc md' sel w s Hwf'); [by rewrite /md' /mdupd decide_True |].
            rewrite Hc0. apply lookup_lt_Some in Hb. exact Hb.
          + split; [by rewrite Htm' | intros _; exact Htok]. }
      iModIntro. iExists o. rewrite chist_at0_N. iFrame "Hlb Hres".
      iApply ("HΦ" with "HcW HmW").
      iDestruct "HTK" as "[%Hf | #HTK']"; [discriminate Hf | by iRight].
    - (* THE NON-TERMINAL BYTE: compatible, or refuted *)
      destruct (Hnt Htm') as [Hcomp | (w' & s' & Hcw' & Hmw' & Hx)]; last first.
      { (* AN EXCLUDED PAIR: the committed writer's deposit meets this one *)
        assert (Hw' : w' ∈ ws) by (apply Hmin; rewrite Hmw'; discriminate).
        iDestruct (big_wstN_dep γc γm md sel w' s' Hw' Hcw' Hmw' with "Hb") as "Hd'".
        iMod (fupd_mask_subseteq Eex) as "_"; [exact HEx |].
        iMod ("Hex" $! w' s' with "[%] Hd' Hdep") as "[]". exact Hx. }
      assert (Hfam' : famN md' sel').
      { split_and!.
        - intros x Hx. apply elem_of_app in Hx as [Hx | Hx]; [exact (Hin x Hx) |].
          apply list_elem_of_singleton in Hx as ->. exact Hw.
        - intros x Hx. rewrite /md' /mdupd in Hx. case_decide as Hq; [subst x; exact Hw |].
          exact (Hmin x Hx).
        - apply sel_firedN_snoc; [exact (sel_firedN_mdupd md sel w s Hfd) |].
          rewrite /md' /mdupd decide_True; [by eexists | done].
        - apply (sel_wfN_fired_snoc md' sel w s Hwf'); [by rewrite /md' /mdupd decide_True |].
          rewrite Hc0. apply lookup_lt_Some in Hb. exact Hb.
        - split; [intros _; exact Hcomp | by rewrite Htm']. }
      assert (Hwit : WIT false (pendN md sel ++ [b])).
      { rewrite -Hpend. exact (witN_nt md' sel' Hfam' (compatN_of_runS _ _ Hcomp)). }
      assert (Htm0 : tmN md sel = false).
      { destruct (tmN md sel); [| done]. cbn in Htm. congruence. }
      assert (HTw : TERM w s = false).
      { rewrite Htm0 in Htm. cbn in Htm. congruence. }
      iMod ("Hecl" $! k (default [] o) H (pendN md sel) b (tmN md sel) false
              with "[%] [%] HPW Hres") as "(Hres & HPW & _)".
      { rewrite Htm0. by intros ?. }
      { exact Hwit. }
      iDestruct (big_wstN_step γc γm md sel md' sel' w Hw with "Hb") as "[Hw Hcl]".
      { intros x Hne. split; [rewrite /sel' cntN_other_snoc; [done | exact Hne] |].
        split; [by rewrite /md' /mdupd decide_False |]. by rewrite /md' /sel' cmtN_fire. }
      iDestruct "Hw" as "(Hc & Hm & _)". rewrite /wcurN /wmodeN.
      iMod (ghost_var_update_halves 1%nat with "HcW Hc") as "[HcW Hc]".
      iMod (ghost_var_update_halves (Some s) with "HmW Hm") as "[HmW Hm]".
      iMod ("Hclose" with "[HPW Hc Hm Hdep Hcl]") as "_".
      { iNext. rewrite /blkN_body. iLeft. iExists md', sel'. rewrite Htm' Hpend.
        iFrame "HPW". iSplitL "Hc Hm Hdep Hcl"; [| by iPureIntro].
        iApply "Hcl". rewrite /wstN /wcurN /wmodeN /sel' cntN_self_snoc Hc0.
        rewrite /md' cmtN_fire_self srcN_mdupd_self /mdupd decide_True; [| done].
        iFrame. }
      iModIntro. iExists o. rewrite chist_at0_N. iFrame "Hlb Hres".
      iApply ("HΦ" with "HcW HmW"). by iLeft.
  Qed.

  (* ================================================================= *)
  (*  5.  A FURTHER BYTE                                                *)
  (* ================================================================= *)

  (* the step's premise: only a terminal round asks anything *)
  Definition cstep_okN (w : W) (s : list (bv 8)) (c : nat) : Prop :=
    forall md sel, famN md sel -> md w = Some s -> cntN sel w = c ->
      tmN md sel = true ->
      TOK md (sel ++ [w]) /\ WIT true (pendN md (sel ++ [w])).

  Lemma blkN_cstep (N : namespace) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (c : nat) (b : bv 8) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    w ∈ ws -> (0 < c)%nat -> s !! c = Some b ->
    cstep_okN w s c ->
    eclN -∗ blkN_inv N k γc γm -∗
    wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) -∗
    (wcurN γc w (1/2) (S c) -∗ wmodeN γm w (1/2) (Some s)
     -∗ (⌜TERM w s = false⌝ ∨ TK k) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns Hw Hc Hb Hok.
    iIntros "#Hecl #Hinv HcW HmW HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !chist_at0_N.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blkN_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not γc w with "HcW Hdone") as %[]. exact Hw. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iAssert (⌜cntN sel w = c /\ md w = Some s⌝)%I as %[Hcw Hmw].
    { iDestruct (big_sepL_lookup _ _ i w Hi with "Hb") as "(Hc & Hm & _)".
      rewrite /wcurN /wmodeN.
      iDestruct (ghost_var_agree with "HcW Hc") as %Hc'.
      iDestruct (ghost_var_agree with "HmW Hm") as %Hm. by iPureIntro. }
    assert (Hwsel : w ∈ sel) by (apply cntN_elem; lia).
    set (sel' := sel ++ [w]).
    assert (Htm : tmN md sel' = tmN md sel) by exact (tmN_snoc_in md sel w Hwsel).
    assert (Hpend : pendN md sel' = pendN md sel ++ [b]).
    { apply (pendN_snoc md sel w s b Hwf Hmw). by rewrite Hcw. }
    assert (Hwf' : sel_wfN (srcN md) sel').
    { apply (sel_wfN_fired_snoc md sel w s Hwf Hmw). rewrite Hcw.
      apply lookup_lt_Some in Hb. exact Hb. }
    assert (Hcmt : forall x, cmtN md sel' x = cmtN md sel x)
      by (intros x; exact (cmtN_step md sel w x Hwsel)).
    assert (Hrmd : forall x, rmd md sel' x = rmd md sel x)
      by (intros x; by rewrite /rmd Hcmt).
    assert (Hfam' : famN md sel').
    { split_and!.
      - intros x Hx. apply elem_of_app in Hx as [Hx | Hx]; [exact (Hin x Hx) |].
        apply list_elem_of_singleton in Hx as ->. exact Hw.
      - exact Hmin.
      - apply sel_firedN_snoc; [exact Hfd | rewrite Hmw; by eexists].
      - exact Hwf'.
      - split.
        + intros Hf. rewrite Htm in Hf.
          apply (runS_ext RUN (rmd md sel)); [intros x; by rewrite Hrmd |].
          exact (proj1 Hinvn Hf).
        + intros Ht. rewrite Htm in Ht. exact (proj1 (Hok md sel Hfam Hmw Hcw Ht)). }
    assert (Hwit : WIT (tmN md sel) (pendN md sel ++ [b])).
    { rewrite -Hpend. destruct (tmN md sel) eqn:Ht.
      - exact (proj2 (Hok md sel Hfam Hmw Hcw Ht)).
      - apply (witN_nt md sel' Hfam'). apply compatN_of_runS.
        apply (runS_ext RUN (rmd md sel)); [intros x; by rewrite Hrmd |].
        exact (proj1 Hinvn Ht). }
    assert (HTw : TERM w s = true -> tmN md sel = true).
    { intros HT. rewrite /tmN existsb_exists. exists w.
      split; [by apply list_elem_of_In | by rewrite /srcN Hmw]. }
    iMod ("Hecl" $! k (default [] o) H (pendN md sel) b (tmN md sel) (tmN md sel)
            with "[%] [%] HPW Hres") as "(Hres & HPW & #HTK)".
    { done. }
    { exact Hwit. }
    iDestruct (big_wstN_step γc γm md sel md sel' w Hw with "Hb") as "[Hw Hcl]".
    { intros x Hne. split; [rewrite /sel' cntN_other_snoc; [done | exact Hne] |].
      split; [done | exact (Hcmt x)]. }
    iDestruct "Hw" as "(Hc & Hm & Hd)". rewrite /wcurN.
    iMod (ghost_var_update_halves (S c) with "HcW Hc") as "[HcW Hc]".
    iMod ("Hclose" with "[HPW Hc Hm Hd Hcl]") as "_".
    { iNext. rewrite /blkN_body. iLeft. iExists md, sel'. rewrite Htm Hpend.
      iFrame "HPW". iSplitL "Hc Hm Hd Hcl"; [| by iPureIntro].
      iApply "Hcl". rewrite /wstN /wcurN /sel' cntN_self_snoc Hcw (Hcmt w).
      iFrame. }
    iModIntro. iExists o. rewrite chist_at0_N. iFrame "Hlb Hres".
    iApply ("HΦ" with "HcW HmW").
    destruct (TERM w s) eqn:HT; [| by iLeft].
    iDestruct "HTK" as "[%Hf | $]". exfalso. rewrite (HTw eq_refl) in Hf. discriminate.
  Qed.

  (* ---- A BYTE WITH OTHER WRITERS' HALVES IN HAND.  What a writer knows
       of the others is exactly the halves it holds: each one's cursor and
       mode, agreed with the family.  The terminal round's PROMPT is such a
       byte -- the main loop writes it after its waits, holding the waited
       stages' halves, which is what orders it after them. ---- *)

  (* the halves [hs] (writer, source, cursor) agree with the family *)
  Lemma big_wstN_held γc γm md sel (hs : list (W * list (bv 8) * nat)) :
    (forall x, x ∈ hs -> x.1.1 ∈ ws) ->
    ([∗ list] w ∈ ws, wstN γc γm md sel w) -∗
    ([∗ list] x ∈ hs, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2)) -∗
    ⌜forall x, x ∈ hs -> md x.1.1 = Some x.1.2 /\ cntN sel x.1.1 = x.2⌝.
  Proof using.
    induction hs as [| x hs IH]; intros Hin.
    - iIntros "_ _". iPureIntro. intros x Hx. by apply elem_of_nil in Hx.
    - iIntros "Hb [[Hc Hm] Hh]".
      destruct (list_elem_of_lookup_1 ws x.1.1 (Hin x (list_elem_of_here x hs))) as (i & Hi).
      iAssert (⌜md x.1.1 = Some x.1.2 /\ cntN sel x.1.1 = x.2⌝)%I as %Hx.
      { iDestruct (big_sepL_lookup _ _ i _ Hi with "Hb") as "(Hc' & Hm' & _)".
        rewrite /wcurN /wmodeN.
        iDestruct (ghost_var_agree with "Hc Hc'") as %Hc.
        iDestruct (ghost_var_agree with "Hm Hm'") as %Hm. by iPureIntro. }
      iDestruct (IH (fun y Hy => Hin y (list_elem_of_further _ _ _ Hy)) with "Hb Hh") as %Hr.
      iPureIntro. intros y Hy. apply elem_of_cons in Hy as [-> | Hy]; [exact Hx | exact (Hr y Hy)].
  Qed.

  Definition cstep_okNh (w : W) (s : list (bv 8)) (c : nat)
      (hs : list (W * list (bv 8) * nat)) : Prop :=
    forall md sel, famN md sel -> md w = Some s -> cntN sel w = c ->
      (forall x, x ∈ hs -> md x.1.1 = Some x.1.2 /\ cntN sel x.1.1 = x.2) ->
      tmN md sel = true ->
      TOK md (sel ++ [w]) /\ WIT true (pendN md (sel ++ [w])).

  (* [blkN_cstep] with the halves [hs] in hand: the step's premise may
     read their cursors and modes, and the halves come back untouched *)
  Lemma blkN_cstep_h (N : namespace) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (c : nat) (b : bv 8)
      (hs : list (W * list (bv 8) * nat)) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    w ∈ ws -> (0 < c)%nat -> s !! c = Some b ->
    (forall x, x ∈ hs -> x.1.1 ∈ ws) ->
    cstep_okNh w s c hs ->
    eclN -∗ blkN_inv N k γc γm -∗
    wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) -∗
    ([∗ list] x ∈ hs, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2)) -∗
    (wcurN γc w (1/2) (S c) -∗ wmodeN γm w (1/2) (Some s)
     -∗ ([∗ list] x ∈ hs, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2))
     -∗ (⌜TERM w s = false⌝ ∨ TK k) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns Hw Hc Hb Hhin Hok.
    iIntros "#Hecl #Hinv HcW HmW Hh HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !chist_at0_N.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blkN_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not γc w with "HcW Hdone") as %[]. exact Hw. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iAssert (⌜cntN sel w = c /\ md w = Some s⌝)%I as %[Hcw Hmw].
    { iDestruct (big_sepL_lookup _ _ i w Hi with "Hb") as "(Hc & Hm & _)".
      rewrite /wcurN /wmodeN.
      iDestruct (ghost_var_agree with "HcW Hc") as %Hc'.
      iDestruct (ghost_var_agree with "HmW Hm") as %Hm. by iPureIntro. }
    iAssert (⌜forall x, x ∈ hs -> md x.1.1 = Some x.1.2 /\ cntN sel x.1.1 = x.2⌝)%I
      as %Hheld.
    { iApply (big_wstN_held γc γm md sel hs Hhin with "Hb Hh"). }
    assert (Hwsel : w ∈ sel) by (apply cntN_elem; lia).
    set (sel' := sel ++ [w]).
    assert (Htm : tmN md sel' = tmN md sel) by exact (tmN_snoc_in md sel w Hwsel).
    assert (Hpend : pendN md sel' = pendN md sel ++ [b]).
    { apply (pendN_snoc md sel w s b Hwf Hmw). by rewrite Hcw. }
    assert (Hwf' : sel_wfN (srcN md) sel').
    { apply (sel_wfN_fired_snoc md sel w s Hwf Hmw). rewrite Hcw.
      apply lookup_lt_Some in Hb. exact Hb. }
    assert (Hcmt : forall x, cmtN md sel' x = cmtN md sel x)
      by (intros x; exact (cmtN_step md sel w x Hwsel)).
    assert (Hrmd : forall x, rmd md sel' x = rmd md sel x)
      by (intros x; by rewrite /rmd Hcmt).
    assert (Hfam' : famN md sel').
    { split_and!.
      - intros x Hx. apply elem_of_app in Hx as [Hx | Hx]; [exact (Hin x Hx) |].
        apply list_elem_of_singleton in Hx as ->. exact Hw.
      - exact Hmin.
      - apply sel_firedN_snoc; [exact Hfd | rewrite Hmw; by eexists].
      - exact Hwf'.
      - split.
        + intros Hf. rewrite Htm in Hf.
          apply (runS_ext RUN (rmd md sel)); [intros x; by rewrite Hrmd |].
          exact (proj1 Hinvn Hf).
        + intros Ht. rewrite Htm in Ht. exact (proj1 (Hok md sel Hfam Hmw Hcw Hheld Ht)). }
    assert (Hwit : WIT (tmN md sel) (pendN md sel ++ [b])).
    { rewrite -Hpend. destruct (tmN md sel) eqn:Ht.
      - exact (proj2 (Hok md sel Hfam Hmw Hcw Hheld Ht)).
      - apply (witN_nt md sel' Hfam'). apply compatN_of_runS.
        apply (runS_ext RUN (rmd md sel)); [intros x; by rewrite Hrmd |].
        exact (proj1 Hinvn Ht). }
    assert (HTw : TERM w s = true -> tmN md sel = true).
    { intros HT. rewrite /tmN existsb_exists. exists w.
      split; [by apply list_elem_of_In | by rewrite /srcN Hmw]. }
    iMod ("Hecl" $! k (default [] o) H (pendN md sel) b (tmN md sel) (tmN md sel)
            with "[%] [%] HPW Hres") as "(Hres & HPW & #HTK)".
    { done. }
    { exact Hwit. }
    iDestruct (big_wstN_step γc γm md sel md sel' w Hw with "Hb") as "[Hw Hcl]".
    { intros x Hne. split; [rewrite /sel' cntN_other_snoc; [done | exact Hne] |].
      split; [done | exact (Hcmt x)]. }
    iDestruct "Hw" as "(Hc & Hm & Hd)". rewrite /wcurN.
    iMod (ghost_var_update_halves (S c) with "HcW Hc") as "[HcW Hc]".
    iMod ("Hclose" with "[HPW Hc Hm Hd Hcl]") as "_".
    { iNext. rewrite /blkN_body. iLeft. iExists md, sel'. rewrite Htm Hpend.
      iFrame "HPW". iSplitL "Hc Hm Hd Hcl"; [| by iPureIntro].
      iApply "Hcl". rewrite /wstN /wcurN /sel' cntN_self_snoc Hcw (Hcmt w).
      iFrame. }
    iModIntro. iExists o. rewrite chist_at0_N. iFrame "Hlb Hres".
    iApply ("HΦ" with "HcW HmW Hh").
    destruct (TERM w s) eqn:HT; [| by iLeft].
    iDestruct "HTK" as "[%Hf | $]". exfalso. rewrite (HTw eq_refl) in Hf. discriminate.
  Qed.

  (* ================================================================= *)
  (*  6.  A SILENT EXIT: the writer fixes the empty source and commits   *)
  (* ================================================================= *)

  Definition silence_okN (w : W) (EXCL : W -> list (bv 8) -> Prop) : Prop :=
    forall md sel, famN md sel -> md w = None -> w ∉ sel ->
      (tmN md sel = false ->
         runS RUN (rmd (mdupd md w []) sel)
         \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s')
      /\ (tmN md sel = true ->
            TOK (mdupd md w []) sel
            \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s').

  Lemma blkN_silence (E : coPset) (N : namespace) (Eex : coPset) (k : nat)
      (γc γm : W -> gname) (w : W) (EXCL : W -> list (bv 8) -> Prop) :
    (↑N : coPset) ⊆ E -> Eex ⊆ (E ∖ ↑N : coPset) ->
    w ∈ ws -> silence_okN w EXCL ->
    □ (∀ w' s', ⌜EXCL w' s'⌝ -∗ dep w' s' -∗ dep w [] ={Eex}=∗ False) -∗
    blkN_inv N k γc γm -∗
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ dep w [] ={E}=∗
    wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) (Some []).
  Proof using Hnd PW_tl dep_tl.
    intros HN HEx Hw Hok.
    iIntros "#Hex #Hinv HcW HmW Hdep".
    iMod (inv_acc _ N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blkN_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not γc w with "HcW Hdone") as %[]. exact Hw. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi).
    iAssert (⌜cntN sel w = 0%nat /\ md w = None⌝)%I as %[Hc0 Hmw].
    { iDestruct (big_sepL_lookup _ _ i w Hi with "Hb") as "(Hc & Hm & _)".
      rewrite /wcurN /wmodeN.
      iDestruct (ghost_var_agree with "HcW Hc") as %Hc.
      iDestruct (ghost_var_agree with "HmW Hm") as %Hm. by iPureIntro. }
    assert (Hwsel : w ∉ sel).
    { intros Hx. apply cntN_elem in Hx. exact (Hx Hc0). }
    set (md' := mdupd md w []).
    destruct (Hok md sel Hfam Hmw Hwsel) as [Hnt Ht].
    assert (Htm : tmN md' sel = tmN md sel).
    { apply tmN_ext. intros x Hx. rewrite /md' /mdupd decide_False; [done |].
      intros ->. exact (Hwsel Hx). }
    assert (Hpend : pendN md' sel = pendN md sel) by exact (pendN_mdupd md sel w [] Hwsel).
    assert (Hcase : invN md' sel
                    \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s').
    { destruct (tmN md sel) eqn:Htm0.
      - destruct (Ht eq_refl) as [Htok | Hx]; [left | right; exact Hx]. split.
        + intros Hq. rewrite Htm in Hq. discriminate Hq.
        + intros _. exact Htok.
      - destruct (Hnt eq_refl) as [Hcomp | Hx]; [left | right; exact Hx].
        split; [intros _; exact Hcomp |].
        intros Hq. rewrite Htm in Hq. discriminate Hq. }
    destruct Hcase as [Hinv' | (w' & s' & Hcw' & Hmw' & Hx)]; last first.
    { (* AN EXCLUDED PAIR *)
      assert (Hw' : w' ∈ ws) by (apply Hmin; rewrite Hmw'; discriminate).
      iDestruct (big_wstN_dep γc γm md sel w' s' Hw' Hcw' Hmw' with "Hb") as "Hd'".
      iMod (fupd_mask_subseteq Eex) as "_"; [exact HEx |].
      iMod ("Hex" $! w' s' with "[%] Hd' Hdep") as "[]". exact Hx. }
    iDestruct (big_wstN_step γc γm md sel md' sel w Hw with "Hb") as "[Hw Hcl]".
    { intros x Hne. split; [done |].
      split; [by rewrite /md' /mdupd decide_False |]. by rewrite /md' cmtN_silence. }
    iDestruct "Hw" as "(Hc & Hm & _)". rewrite /wmodeN.
    iMod (ghost_var_update_halves (Some []) with "HmW Hm") as "[HmW Hm]".
    iMod ("Hclose" with "[HPW Hc Hm Hdep Hcl]") as "_".
    { iNext. rewrite /blkN_body. iLeft. iExists md', sel. rewrite Htm Hpend.
      iFrame "HPW". iSplitL "Hc Hm Hdep Hcl".
      - iApply "Hcl". rewrite /wstN /wmodeN.
        rewrite /md' cmtN_silence_self srcN_mdupd_self /mdupd decide_True; [| done].
        iFrame.
      - iPureIntro. split_and!.
        + exact Hin.
        + intros x Hx. rewrite /md' /mdupd in Hx. case_decide as Hq; [subst x; exact Hw |].
          exact (Hmin x Hx).
        + exact (sel_firedN_mdupd md sel w [] Hfd).
        + exact (sel_wfN_mdupd md sel w [] Hwsel Hwf).
        + exact Hinv'. }
    iModIntro. iFrame "HcW HmW".
  Qed.

  (* ================================================================= *)
  (*  7.  THE FILING: at the prompt, every half back                     *)
  (* ================================================================= *)

  (* THE ROUND TAKES THE FAMILY BACK AND FILES: every writer has fired and
     written its whole source, no source is terminal -- and then the block
     IS one of the model's, and the claim's credential comes out at the
     flag [false], which is what the filing step asks.  The family is
     DONE: every cursor is parked whole. *)
  Lemma blkN_file (E : coPset) (N : namespace) (k : nat) (γc γm : W -> gname)
      (sw : W -> list (bv 8)) :
    (↑N : coPset) ⊆ E -> ws <> [] ->
    (forall w, w ∈ ws -> TERM w (sw w) = false) ->
    blkN_inv N k γc γm -∗
    ([∗ list] w ∈ ws, wcurN γc w (1/2) (length (sw w))
                       ∗ wmodeN γm w (1/2) (Some (sw w))) ={E}=∗
    ∃ pre : list (bv 8), PW k pre false ∗ ⌜blkN ws RUN pre⌝.
  Proof using Hnd HWIT PW_tl dep_tl.
    intros HN Hne HT. iIntros "#Hinv Hall".
    iMod (inv_acc _ N _ HN with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as ">Hin". rewrite {1}/blkN_body.
    iDestruct "Hin" as "[Hfam | Hdone]"; last first.
    { destruct ws as [| w0 ws'] eqn:Hws; [by destruct (Hne eq_refl) |].
      assert (Hw0 : w0 ∈ ws) by (rewrite Hws; apply list_elem_of_here).
      assert (Hi0 : ws !! 0%nat = Some w0) by (by rewrite Hws).
      rewrite -Hws.
      iDestruct (big_sepL_lookup_acc _ _ 0%nat w0 Hi0 with "Hall") as "[[Hc0 _] _]".
      iDestruct (blkN_done_not γc w0 with "Hc0 Hdone") as %[]. exact Hw0. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    iDestruct (big_sepL_sep_2 with "Hall Hb") as "Hab".
    iAssert ([∗ list] w ∈ ws, wcurN γc w 1 (cntN sel w)
               ∗ ⌜md w = Some (sw w) /\ cntN sel w = length (sw w)⌝)%I
      with "[Hab]" as "Hab".
    { iApply (big_sepL_impl with "Hab"). iModIntro.
      iIntros (j w _) "[[Hc1 Hm1] (Hc2 & Hm2 & _)]". rewrite /wcurN /wmodeN.
      iDestruct (ghost_var_agree with "Hc1 Hc2") as %Hc.
      iDestruct (ghost_var_agree with "Hm1 Hm2") as %Hm.
      rewrite Hc. iCombine "Hc1 Hc2" as "Hc". rewrite ?Qp.half_half. iFrame "Hc".
      iPureIntro. split; [by rewrite Hm | done]. }
    iDestruct (big_sepL_sep with "Hab") as "[Hcur Hp]".
    iDestruct (big_sepL_pure_1 with "Hp") as %Hp.
    assert (Hall : forall w, w ∈ ws -> md w = Some (sw w) /\ cntN sel w = length (sw w)).
    { intros w Hw. destruct (list_elem_of_lookup_1 ws w Hw) as (i & Hi). exact (Hp i w Hi). }
    assert (Htm : tmN md sel = false).
    { apply not_true_iff_false. rewrite /tmN existsb_exists. intros (x & Hx & Ht).
      apply list_elem_of_In in Hx. pose proof (Hin x Hx) as Hxw.
      destruct (Hall x Hxw) as [Hmx _]. rewrite /srcN Hmx /= (HT x Hxw) in Ht. discriminate Ht. }
    pose proof (compatN_of_runS _ _ (proj1 Hinvn Htm)) as Hcomp.
    assert (Hblk : blkN ws RUN (pendN md sel)).
    { rewrite -pendN_rmd. apply (pendN_file ws RUN (rmd md sel) sel Hnd Hin); [| exact Hcomp].
      intros w Hw. destruct (Hall w Hw) as [Hmw Hcw]. exists (sw w).
      split; [| exact Hcw]. rewrite /rmd /cmtN bool_decide_true; [exact Hmw |].
      destruct (sw w) as [| x s] eqn:Hsw; [right; exact Hmw |]. left. apply cntN_elem.
      rewrite Hcw. cbn [length]. lia. }
    iMod ("Hclose" with "[Hcur]") as "_".
    { iNext. rewrite /blkN_body. iRight. rewrite /blkN_done.
      iApply (big_sepL_impl with "Hcur"). iModIntro. iIntros (j w _) "Hc".
      by iExists (cntN sel w). }
    iModIntro. iExists (pendN md sel). rewrite Htm. iFrame "HPW". iPureIntro. exact Hblk.
  Qed.

  (* ================================================================= *)
  (*  8.  THE TERMINAL ROUND (generalising [PipeBoth.pwc_fork_exit] and  *)
  (*      [pprompt_dollar_fork] / [pprompt_space_fork])                  *)
  (* ================================================================= *)

  (* what the writer of a TERMINAL source (sh node k's fork panic, whose
     source carries the main loop's prompt after it, as [alt_forkc] does)
     hands back at its exit: the family, its own two halves and the
     frozen resolution -- the round is never filed *)
  Definition pwc_fork_exitN (N : namespace) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (c : nat) : iProp Σ :=
    (blkN_inv N k γc γm ∗ wcurN γc w (1/2) c ∗ wmodeN γm w (1/2) (Some s) ∗ TK k)%I.

  (* THE TERMINAL FIRE: the panic's first byte *)
  Lemma blkN_fire_t (N : namespace) (Eex : coPset) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (b : bv 8)
      (EXCL : W -> list (bv 8) -> Prop) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    w ∈ ws -> s !! 0%nat = Some b -> TERM w s = true ->
    fire_okN w s EXCL ->
    □ (∀ w' s', ⌜EXCL w' s'⌝ -∗ dep w' s' -∗ dep w s ={Eex}=∗ False) -∗
    eclN -∗ blkN_inv N k γc γm -∗
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ dep w s -∗
    (pwc_fork_exitN N k γc γm w s 1 -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns HEx Hw Hb HT Hok.
    iIntros "#Hex #Hecl #Hinv HcW HmW Hdep HΦ".
    iApply (blkN_fire N Eex k γc γm w s b EXCL Φ Hns HEx Hw Hb Hok
              with "Hex Hecl Hinv HcW HmW Hdep").
    iIntros "HcW HmW [%Hf | #HTK]"; [by rewrite HT in Hf |].
    iApply "HΦ". rewrite /pwc_fork_exitN. iFrame "Hinv HcW HmW HTK".
  Qed.

  (* THE TERMINAL ROUND'S LATER BYTES at the terminal writer's own cursor:
     the rest of the panic, and -- one process later, at the same cursor --
     the main loop's prompt *)
  Lemma pprompt_forkN (N : namespace) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (c : nat) (b : bv 8) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    w ∈ ws -> (0 < c)%nat -> s !! c = Some b ->
    cstep_okN w s c ->
    eclN -∗ pwc_fork_exitN N k γc γm w s c -∗
    (pwc_fork_exitN N k γc γm w s (S c) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns Hw Hc Hb Hok.
    iIntros "#Hecl (#Hinv & HcW & HmW & #HTK) HΦ".
    iApply (blkN_cstep N k γc γm w s c b Φ Hns Hw Hc Hb Hok with "Hecl Hinv HcW HmW").
    iIntros "HcW HmW _". iApply "HΦ". rewrite /pwc_fork_exitN. iFrame "Hinv HcW HmW HTK".
  Qed.

  (* ...AND THE MAIN LOOP'S PROMPT with the waited stages' halves in hand
     (their exit payloads): what orders the prompt after them *)
  Lemma pprompt_forkN_h (N : namespace) (k : nat) (γc γm : W -> gname)
      (w : W) (s : list (bv 8)) (c : nat) (b : bv 8)
      (hs : list (W * list (bv 8) * nat)) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    w ∈ ws -> (0 < c)%nat -> s !! c = Some b ->
    (forall x, x ∈ hs -> x.1.1 ∈ ws) ->
    cstep_okNh w s c hs ->
    eclN -∗ pwc_fork_exitN N k γc γm w s c -∗
    ([∗ list] x ∈ hs, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2)) -∗
    (pwc_fork_exitN N k γc γm w s (S c)
     -∗ ([∗ list] x ∈ hs, wcurN γc x.1.1 (1/2) x.2 ∗ wmodeN γm x.1.1 (1/2) (Some x.1.2))
     -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hnd HWIT PW_tl dep_tl TK_pers.
    intros Hns Hw Hc Hb Hhin Hok.
    iIntros "#Hecl (#Hinv & HcW & HmW & #HTK) Hh HΦ".
    iApply (blkN_cstep_h N k γc γm w s c b hs Φ Hns Hw Hc Hb Hhin Hok
              with "Hecl Hinv HcW HmW Hh").
    iIntros "HcW HmW Hh _". iApply ("HΦ" with "[HcW HmW] Hh").
    rewrite /pwc_fork_exitN. iFrame "Hinv HcW HmW HTK".
  Qed.

  (* a STRAY's byte in a terminal round, and every other writer's, is
     [blkN_cstep] itself: the flag decides the witness, not the writer *)
End blkN.
