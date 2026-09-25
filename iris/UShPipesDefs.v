(* ===================================================================== *)
(* UShPipesDefs.v -- THE N-STAGE ROUND'S NAMES, DEPOSITS AND PAYLOADS    *)
(* (design claude-notes/design/pipes-general.md SS1.1, SS1.3, SS2.2; cut  *)
(* C7).                                                                  *)
(*                                                                        *)
(* What the right spine's node law ([UkShPipesRound.                      *)
(* wp_kshr_runcmd_pipes_law_g]) is instantiated at, as data: the round's  *)
(* pipes [P k] (named before the walk, so a payload may name them), two   *)
(* ONE-SHOTS per node ([gF k]: the right child was forked; [gG k]: the    *)
(* left one was), the family's DEPOSITS [pdep] and EXCLUSIONS [EXf]       *)
(* (design SS2.2's three kinds -- content against an exec failure through *)
(* the flow chain, and the structural ones through the one-shots), the    *)
(* node payloads [Qc], and the family's accessors the node needs.         *)
(*                                                                        *)
(* THE DEPOSITS (design SS2.2).  A writer's nonempty source deposits the  *)
(* SHOTS of the forks that made it ([shotsF]/[gG]); a panic of sh node k  *)
(* deposits the PENDING one-shots of the forks it never made; a FAILED    *)
(* stage k ([PipesFire.fail_src]: its exec, or the [cat f] producer's     *)
(* refused open) deposits its untouched write permit on [P k]; the        *)
(* content writer deposits a byte of EVERY pipe of the chain (the flow    *)
(* chain is run at its first byte).  Every exclusion the family spends is *)
(* then a pair of deposits that refute each other ([pexcl_*]).            *)
(*                                                                        *)
(* THE REFUSED OPEN'S DEPOSIT (C9d'), [wcur (P 0) 0], is the write       *)
(* permit of the [cat f] process's own pipe end, and the report that      *)
(* spends it is written on the console: one device number is bound to     *)
(* both descriptors ([ProgTree.DProd], [ProgTreePipes.                     *)
(* cat_file_prod_conforms]), the report chosen only while the pipe is     *)
(* untouched, and [UkCatFIface]'s device pays the deposit at the report's *)
(* first byte out of the permit it holds.  [UShCatFStage] pays            *)
(* [UShPipesStage.stage_catf]'s premise at the lend with the deed.        *)
(*                                                                        *)
(* THE PAYLOADS (design SS1.1's sketch, made exact).  A node's two        *)
(* children pay [Qc k] -- the taint, or the SIDE-TAGGED report of the     *)
(* left stage ([lrep]) or of the suffix ([rrep]).  A suffix reports its   *)
(* read outcome on the pipe above it and every one of its writers at its *)
(* FINAL state ([wfin]), the content writer possibly mid-line with the    *)
(* CHAIN fact that its cursor is what the suffix read ([chain]) -- or the *)
(* TERMINAL shape ([sufT]): a node's fork panic at cursor 5 and the       *)
(* waited stages above it.                                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions csum excl agree.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import WpUart.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs FdSlots UserFd.
Require Import LineWords EchoDisc EchoOut AppEcho.
Require Import LineModel.
Require Import PipeOut PipeDisc.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN GenOut PipeOutN PipesView.
Require Import PipeNames PipeProto.
Require Import AppCfg AppInv.
Require Import ProgTree.
Require Import CtxIdDefs.
Require Import UkPipesIface.
Require Import PipesFire.
Require GrepFilt.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  PURE: the writers, the diagnostics, the exclusions -- [PipesFire]  *)
(* ===================================================================== *)

(* the chain of the content writer: its cursor is what the suffix read *)
Definition chain (L : list (bv 8)) (ro : rd_out) (oc : option nat) : Prop :=
  forall c, oc = Some c -> ro = RdEof (take c L).

(* a middle filter stage's two ends: what it wrote whole is what its
   filter owes for what it read to end of file (grep-pipes SS3.4; cat's
   is the copier, [W = D]) *)
Definition filterer (F : filt) (ro : rd_out) (wo : wr_out) : Prop :=
  forall W, wo = WrAll W -> exists D, ro = RdEof D /\ W = fapp F D.

(* ...and what a reader read of the line is a prefix of it *)
Definition rd_pre (L : list (bv 8)) (ro : rd_out) : Prop :=
  forall D, ro = RdEof D -> D `prefix_of` L.

(* the flow chain's pipe indices (outside the section: [lia] there reads
   the section's context) *)
Lemma flow_down_nil (i : nat) : ~ (1 <= i <= 0)%nat.
Proof using. lia. Qed.
Lemma flow_down_idx (i j : nat) : (1 <= i <= S j)%nat -> i <> S j -> (1 <= i <= j)%nat.
Proof using. lia. Qed.

(* ===================================================================== *)
(*  1.  THE ROUND                                                         *)
(* ===================================================================== *)

Section UShPipesDefs.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  (* [UkPipesIface]'s pin of the family's cursor camera *)
  #[local] Existing Instance eo_turn | 0.

  (* THE ROUND'S CLAIM at a line model with a pipeline view (cut C9c') *)
  Context (g : pipe_gn).
  Context (LM : lmodel) (PV : pview LM) (CP : gen_cparams LM) (sd : lm_st LM).
  Context (WA : gen_wa LM CP sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT CP).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g LM CP sd WA).
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st LM) (lR : pline').
  Hypothesis HlR : pv_line PV (lineV LM I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc PV sR).
  Context (Hadmit : pns_admV PV lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)).
  (* THE PRODUCER at the head of the line (echo, or [cat f]): its failures
     ([PipesFire.fail_src]) and whether it may halt *)
  Context (pr : producer).
  (* WHAT THE PRODUCER BORROWS AND HANDS BACK (C9f2): node 0 lends it to
     its left child beside [echo_raw], and the left report returns it --
     the [cat f] producer's deed; [True] for echo *)
  Context (Rd : iProp Σ).
  Context (γc γm : wid -> gname).
  (* THE ROUND'S NAMES, fixed before the walk: node [k]'s pipe, and the two
     one-shots of its two forks *)
  Context (P : nat -> pnames) (gF gG : nat -> gname).

  Local Notation fcR := (pv_fc PV sR).
  Local Notation nc := (lcats lR).
  Local Notation wsN := (wids nc).
  Local Notation RUNN := (runN fcR lR).
  Local Notation PWN := (pwc_blkV g LM (gcPIN CP) (gcW CP) T v I sR).
  Local Notation WITN := (pwitV LM I sR).
  Local Notation TOKN := (tokN fcR lR).

  (* ---- the one-shots ---- *)
  Definition osP (γo : gname) : iProp Σ := own γo (Cinl (Excl ()) : pipe_roR).
  Definition osS (γo : gname) : iProp Σ := own γo (Cinr (to_agree ()) : pipe_roR).

  Global Instance osP_timeless γo : Timeless (osP γo).
  Proof using . rewrite /osP. apply _. Qed.
  Global Instance osS_timeless γo : Timeless (osS γo).
  Proof using . rewrite /osS. apply _. Qed.
  Global Instance osS_persistent γo : Persistent (osS γo).
  Proof using . rewrite /osS. apply _. Qed.

  Lemma os_excl (γo : gname) : osP γo -∗ osS γo -∗ False.
  Proof using .
    rewrite /osP /osS. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %Hv.
  Qed.

  Lemma os_shoot (γo : gname) : osP γo ==∗ osS γo.
  Proof using .
    rewrite /osP /osS. iIntros "H".
    iApply (own_update with "H"). apply cmra_update_exclusive. done.
  Qed.

  Lemma os_alloc : ⊢ |==> ∃ γo, osP γo.
  Proof using . rewrite /osP. iApply own_alloc. done. Qed.

  (* the shots of the right forks above node [k] *)
  Definition shotsF (k : nat) : iProp Σ := [∗ list] j ∈ seq 0 k, osS (gF j).

  Global Instance shotsF_persistent k : Persistent (shotsF k).
  Proof using . rewrite /shotsF. apply _. Qed.
  Global Instance shotsF_timeless k : Timeless (shotsF k).
  Proof using . rewrite /shotsF. apply _. Qed.

  Lemma shotsF_at (k j : nat) : (j < k)%nat -> shotsF k -∗ osS (gF j).
  Proof using L P gG.
    intros Hj. iIntros "H". rewrite /shotsF.
    iApply (big_sepL_elem_of with "H"). apply elem_of_seq. lia.
  Qed.

  Lemma shotsF_snoc (k : nat) : shotsF k -∗ osS (gF k) -∗ shotsF (S k).
  Proof using .
    iIntros "H1 H2". rewrite /shotsF seq_S big_sepL_app big_sepL_singleton.
    iFrame "H1 H2".
  Qed.

  (* the bytes of every pipe of the chain *)
  Definition pws_all : iProp Σ := [∗ list] j ∈ seq 0 nc, pws_lb (P j) (take 1 L).

  (* ---- THE DEPOSITS ---- *)
  Definition pdep_ne (w : wid) (s : list (bv 8)) : iProp Σ :=
    match w with
    | WSh k =>
        shotsF k
        ∗ (if bool_decide (s = dg_pipe_b) then osP (gF k) ∗ osP (gG k)
           else if bool_decide (s = alt_forkc) then osP (gF k) else True)
    | WLeft k =>
        shotsF k ∗ osS (gG k)
        ∗ (if bool_decide (fail_src pr (lfilts lR) k s) then wcur (P k) 0 else True)
    | WLast =>
        (* the content: a byte of every pipe, and every filter of the
           line passing it (grep-pipes SS3.3) *)
        shotsF nc ∗ (if bool_decide (s = L) then (pws_all ∗ ⌜passes (lfilts lR) L⌝) ∨ ⌜L = ldg (lfilts lR)⌝
                     else True)
    end%I.

  (* ...and a source no process commits deposits nothing payable *)
  Definition pdep (w : wid) (s : list (bv 8)) : iProp Σ :=
    if bool_decide (s = []) then True%I
    else if bool_decide (fire_src fcR pr (lfilts lR) L w s) then pdep_ne w s else False%I.

  Global Instance pdep_timeless w s : Timeless (pdep w s).
  Proof using .
    rewrite /pdep /pdep_ne. case_bool_decide; [apply _ |]. case_bool_decide; [| apply _].
    destruct w as [k | k |]; repeat case_bool_decide; apply _.
  Qed.

  Lemma pdep_unfold (w : wid) (s : list (bv 8)) :
    s <> [] -> fire_src fcR pr (lfilts lR) L w s -> pdep w s = pdep_ne w s.
  Proof using . intros Hs Hf. by rewrite /pdep bool_decide_false // bool_decide_true. Qed.

  Lemma pdep_gsrc (w : wid) (s : list (bv 8)) : gsrc fcR pr (lfilts lR) L w s -> pdep w s ⊢ False.
  Proof using .
    intros [Hs Hf]. rewrite /pdep bool_decide_false; [| exact Hs].
    rewrite bool_decide_false; [| exact Hf]. iIntros "[]".
  Qed.

  (* a deposit, read at a source some process commits, or refuted *)
  Lemma pdep_cases (w : wid) (s : list (bv 8)) :
    s <> [] -> pdep w s ⊢ ⌜fire_src fcR pr (lfilts lR) L w s⌝ ∗ pdep_ne w s.
  Proof using .
    intros Hs. destruct (decide (fire_src fcR pr (lfilts lR) L w s)) as [Hf | Hf].
    - rewrite (pdep_unfold w s Hs Hf). iIntros "$". done.
    - iIntros "H". iDestruct (pdep_gsrc w s (conj Hs Hf) with "H") as "[]".
  Qed.

  Lemma pdep_nil (w : wid) : ⊢ pdep w [].
  Proof using . rewrite /pdep bool_decide_true; done. Qed.

  Lemma panic_src_ne (s : list (bv 8)) : panic_src s -> s <> [].
  Proof using . intros [-> | ->]; vm_compute; discriminate. Qed.

  (* a panic's deposit: the pending right shot, and the left one at a pipe
     panic *)
  Lemma pdep_sh_pend (j : nat) (s : list (bv 8)) :
    panic_src s ->
    pdep (WSh j) s ⊢ shotsF j ∗ osP (gF j) ∗ (⌜s = dg_pipe_b⌝ -∗ osP (gG j)).
  Proof using .
    intros Hs. rewrite (pdep_unfold (WSh j) s (panic_src_ne s Hs) Hs) /pdep_ne.
    iIntros "[$ H]". destruct Hs as [-> | ->].
    - rewrite bool_decide_true; [| done]. iDestruct "H" as "[$ $]". auto.
    - rewrite bool_decide_false; [| exact (not_eq_sym dg_pipe_ne_fork)].
      rewrite bool_decide_true; [| done]. iFrame "H".
      iIntros (Hq). exfalso. exact (dg_pipe_ne_fork (eq_sym Hq)).
  Qed.

  (* a nonempty source's deposit carries the shots of its forks *)
  Lemma pdep_left_shots (j : nat) (s : list (bv 8)) :
    s <> [] -> pdep (WLeft j) s ⊢ shotsF j ∗ osS (gG j).
  Proof using .
    intros Hs. iIntros "H". iDestruct (pdep_cases _ _ Hs with "H") as "[_ H]".
    rewrite /pdep_ne. iDestruct "H" as "($ & $ & _)".
  Qed.

  Lemma pdep_sh_shots (j : nat) (s : list (bv 8)) :
    s <> [] -> pdep (WSh j) s ⊢ shotsF j.
  Proof using .
    intros Hs. iIntros "H". iDestruct (pdep_cases _ _ Hs with "H") as "[_ H]".
    rewrite /pdep_ne. iDestruct "H" as "($ & _)".
  Qed.

  Lemma pdep_last_shots (s : list (bv 8)) :
    s <> [] -> pdep WLast s ⊢ shotsF nc.
  Proof using .
    intros Hs. iIntros "H". iDestruct (pdep_cases _ _ Hs with "H") as "[_ H]".
    rewrite /pdep_ne. iDestruct "H" as "($ & _)".
  Qed.

  (* ---- the invariant of a pipe of the chain, at its flow parameter:
          the filter of the stage that writes it ([lfilt]) must pass the
          line (grep-pipes SS3.3) ---- *)
  Definition prevP (j : nat) : option pnames :=
    match j with O => None | S j' => Some (P j') end.

  Definition pflow (j : nat) : iProp Σ := flowF L (fapp (lfilt lR j)) (prevP j).

  Global Instance pflow_persistent j : Persistent (pflow j).
  Proof using . rewrite /pflow. apply _. Qed.
  Global Instance pflow_timeless j : Timeless (pflow j).
  Proof using . rewrite /pflow. apply _. Qed.

  (* at a cat stage the parameter is the landed one plus a trivial pass *)
  Lemma pflow_cat (j : nat) : lfilt lR (S j) = FCat -> pflow (S j) = flowF L (fapp FCat) (Some (P j)).
  Proof using . intros HF. rewrite /pflow HF. reflexivity. Qed.

  Definition pinv (j : nat) : iProp Σ :=
    ∃ γp : pipe_names, pipe_invU (P j) γp L (pflow j).

  Global Instance pinv_persistent j : Persistent (pinv j).
  Proof using . rewrite /pinv. apply _. Qed.

  (* a byte in pipe [j] is a byte in every pipe above it, and every filter
     that wrote one of them passes the line *)
  Lemma flow_down (j : nat) :
    L <> [] ->
    ([∗ list] i ∈ seq 0 (S j), pinv i) -∗ pws_lb (P j) (take 1 L) ={↑pipeN}=∗
    ([∗ list] i ∈ seq 0 (S j), pws_lb (P i) (take 1 L))
    ∗ ⌜forall i, (1 <= i <= j)%nat -> fapp (lfilt lR i) L = L⌝.
  Proof using .
    intros HL. induction j as [| j IH]; iIntros "#Hinvs #Hlb".
    - iModIntro. iSplitL; [| iPureIntro; intros i Hi; exfalso; exact (flow_down_nil i Hi)].
      cbn. iFrame "Hlb".
    - rewrite !(seq_S (S j)) !big_sepL_app !big_sepL_singleton !Nat.add_0_l.
      iDestruct "Hinvs" as "[Hinvs Hi]". iDestruct "Hi" as (γp) "Hi".
      iMod (flow_step (↑pipeN) (P (S j)) γp L (pflow (S j))
              ltac:(reflexivity) HL with "Hi Hlb") as "#HU".
      iEval (rewrite /pflow; cbn [prevP flowF]) in "HU".
      iDestruct "HU" as "[#Hlb' %Hg]".
      iMod (IH with "Hinvs Hlb'") as "[#Hall %Hps]". iModIntro. iFrame "Hall Hlb".
      iPureIntro. intros i Hi. destruct (decide (i = S j)) as [-> | Hne]; [exact Hg |].
      apply Hps. exact (flow_down_idx i j Hi Hne).
  Qed.

  (* THE CONTENT WRITER'S DEPOSIT, at its first byte, from the last
     stage's own pass *)
  Lemma pdep_last_of_lb :
    L <> [] -> (0 < nc)%nat ->
    shotsF nc -∗ ([∗ list] i ∈ seq 0 nc, pinv i) -∗
    □ (pws_lb (P (nc - 1)) (take 1 L) -∗ ⌜fapp (lfilt lR nc) L = L⌝
       ={↑pipeN}=∗ pdep WLast L ∗ ⌜passes (lfilts lR) L⌝).
  Proof using GEN.
    intros HL Hn.
    assert (Hnc : exists m, nc = S m) by (exists (nc - 1)%nat; lia).
    destruct Hnc as [m Hm]. rewrite Hm.
    replace (S m - 1)%nat with m by lia.
    iIntros "#Hs #Hinvs !> #Hlb %Hlast".
    iMod (flow_down m HL with "Hinvs Hlb") as "[Hall %Hps]".
    assert (Hpass : passes (lfilts lR) L).
    { rewrite /passes Forall_lookup. intros i F Hi.
      assert (Hlen : length (lfilts lR) = S m) by (rewrite -lcats_lfilts; exact Hm).
      pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
      assert (HF : lfilt lR (S i) = F).
      { rewrite /lfilt. replace (S i - 1)%nat with i by lia. exact (nth_lookup_Some _ _ _ _ Hi). }
      rewrite -HF. destruct (decide (i = m)) as [-> | Hne]; [exact Hlast |]. apply Hps. lia. }
    iModIntro.
    rewrite (pdep_unfold WLast L HL (or_introl (conj eq_refl (conj HL Hpass)))) /pdep_ne bool_decide_true; [| done].
    rewrite /pws_all Hm. iSplitL; [| by iPureIntro]. iFrame "Hs". iLeft. iFrame "Hall". by iPureIntro.
  Qed.

  (* ---- THE EXCLUSIONS, REFUTED BY THE DEPOSITS ---- *)
  Lemma pexcl_sh (k : nat) (s : list (bv 8)) :
    (k < nc)%nat -> panic_src s ->
    ⊢ □ (∀ w' s', ⌜EXf fcR pr (lfilts lR) nc L (WSh k) s w' s'⌝ -∗ pdep w' s' -∗ pdep (WSh k) s
                  ={↑pipeN}=∗ False).
  Proof using .
    intros Hk Hs. iIntros "!>" (w' s' Hx) "Hd' Hd".
    destruct Hx as [Hg | Hx]; [iDestruct (pdep_gsrc w' s' Hg with "Hd'") as "[]" |].
    iDestruct (pdep_sh_pend k s Hs with "Hd") as "(#Hsk & HF & HG)".
    destruct Hx as [(j & -> & Hj & Hjk & Hs') | [(j & -> & Hj & Hc & Hne) | (-> & Hne)]].
    - iDestruct (pdep_sh_pend j s' Hs' with "Hd'") as "(#Hsj & HF' & _)".
      destruct (decide (j < k)%nat) as [Hlt | Hge].
      + iDestruct (shotsF_at k j Hlt with "Hsk") as "HS".
        iDestruct (os_excl with "HF' HS") as %[].
      + iDestruct (shotsF_at j k ltac:(lia) with "Hsj") as "HS".
        iDestruct (os_excl with "HF HS") as %[].
    - iDestruct (pdep_left_shots j s' Hne with "Hd'") as "[#Hsj #HGj]".
      case_bool_decide as Hp.
      + destruct (decide (j = k)) as [-> | Hjk].
        * iDestruct ("HG" with "[//]") as "HG".
          iDestruct (os_excl with "HG HGj") as %[].
        * iDestruct (shotsF_at j k ltac:(lia) with "Hsj") as "HS".
          iDestruct (os_excl with "HF HS") as %[].
      + iDestruct (shotsF_at j k ltac:(lia) with "Hsj") as "HS".
        iDestruct (os_excl with "HF HS") as %[].
    - iDestruct (pdep_last_shots s' Hne with "Hd'") as "#Hsn".
      iDestruct (shotsF_at nc k Hk with "Hsn") as "HS".
      iDestruct (os_excl with "HF HS") as %[].
  Qed.

  Lemma pexcl_left (k : nat) (s : list (bv 8)) :
    (k < nc)%nat -> s <> [] ->
    pinv k -∗
    □ (∀ w' s', ⌜EXf fcR pr (lfilts lR) nc L (WLeft k) s w' s'⌝ -∗ pdep w' s' -∗ pdep (WLeft k) s
                ={↑pipeN}=∗ False).
  Proof using .
    intros Hk Hs. iIntros "#Hinv !>" (w' s' Hx) "Hd' Hd".
    destruct Hx as [Hg | Hx]; [iDestruct (pdep_gsrc w' s' Hg with "Hd'") as "[]" |].
    destruct Hx as [(j & -> & Hj & Hc) | (Hfl & -> & -> & HL & HLx)].
    - iDestruct (pdep_left_shots k s Hs with "[Hd]") as "[#Hsk #HGk]"; [iExact "Hd" |].
      assert (Hs' : panic_src s') by (destruct Hc as [[_ ->] | [_ ->]]; [left | right]; done).
      iDestruct (pdep_sh_pend j s' Hs' with "Hd'") as "(_ & HF & HG)".
      destruct Hc as [[Hjk ->] | [Hjk ->]].
      + destruct (decide (j = k)) as [-> | Hne].
        * iDestruct ("HG" with "[//]") as "HG".
          iDestruct (os_excl with "HG HGk") as %[].
        * iDestruct (shotsF_at k j ltac:(lia) with "Hsk") as "HS".
          iDestruct (os_excl with "HF HS") as %[].
      + iDestruct (shotsF_at k j Hjk with "Hsk") as "HS".
        iDestruct (os_excl with "HF HS") as %[].
    - (* THE CONTENT AGAINST THE FAILURE (an exec failure, or the [cat f]
         producer's refused open): the flow chain's byte of pipe [k]
         against the failed stage's untouched permit on it *)
      rewrite (pdep_unfold (WLeft k) s Hs (or_introl Hfl)) /pdep_ne bool_decide_true; [| done].
      iDestruct "Hd" as "(_ & _ & Hw)".
      iDestruct (pdep_cases WLast L HL with "Hd'") as "[_ Hd']".
      rewrite /pdep_ne bool_decide_true; [| done].
      iDestruct "Hd'" as "(_ & [[Hall _] | %Hq])"; [| by destruct (HLx Hq)].
      rewrite /pws_all.
      iDestruct (big_sepL_elem_of _ _ k with "Hall") as "Hlb";
        [apply elem_of_seq; lia |].
      iDestruct "Hinv" as (γp) "Hinv".
      iDestruct (pipe_excl_wtok_lbU (↑pipeN) (P k) γp L (pflow k)
                   ltac:(reflexivity) HL with "Hinv") as "#Hex".
      iApply ("Hex" with "Hw Hlb").
  Qed.

  Lemma pexcl_last (s : list (bv 8)) :
    s <> [] ->
    ([∗ list] i ∈ seq 0 nc, pinv i) -∗
    □ (∀ w' s', ⌜EXf fcR pr (lfilts lR) nc L WLast s w' s'⌝ -∗ pdep w' s' -∗ pdep WLast s
                ={↑pipeN}=∗ False).
  Proof using .
    intros Hs. iIntros "#Hinvs !>" (w' s' Hx) "Hd' Hd".
    destruct Hx as [Hg | Hx]; [iDestruct (pdep_gsrc w' s' Hg with "Hd'") as "[]" |].
    destruct Hx as [(j & -> & Hj & Hs') | (-> & HL & HLx & j & -> & Hj & Hfl)].
    - iDestruct (pdep_sh_pend j s' Hs' with "Hd'") as "(_ & HF & _)".
      iDestruct (pdep_last_shots s Hs with "Hd") as "#Hsn".
      iDestruct (shotsF_at nc j Hj with "Hsn") as "HS".
      iDestruct (os_excl with "HF HS") as %[].
    - iDestruct (pdep_cases WLast L HL with "Hd") as "[_ Hd]".
      rewrite /pdep_ne bool_decide_true; [| done].
      iDestruct "Hd" as "(_ & [[Hall _] | %Hq])"; [| by destruct (HLx Hq)].
      rewrite (pdep_unfold (WLeft j) s' (fail_src_ne pr (lfilts lR) j s' Hfl) (or_introl Hfl)) /pdep_ne bool_decide_true; [| done].
      iDestruct "Hd'" as "(_ & _ & Hw)".
      rewrite /pws_all.
      iDestruct (big_sepL_elem_of _ _ j with "Hall") as "Hlb";
        [apply elem_of_seq; lia |].
      iDestruct (big_sepL_elem_of _ _ j with "Hinvs") as "Hinv";
        [apply elem_of_seq; lia |].
      iDestruct "Hinv" as (γp) "Hinv".
      iDestruct (pipe_excl_wtok_lbU (↑pipeN) (P j) γp L (pflow j)
                   ltac:(reflexivity) HL with "Hinv") as "#Hex".
      iApply ("Hex" with "Hw Hlb").
  Qed.

  (* ---- THE FAMILY, at the round ---- *)
  Local Notation FAM := (blkN_inv wsN RUNN PWN termw TOKN pdep pnsN (S gen_id) γc γm).

  (* A WRITER'S KIT from its firing premise and the refutation of its
     exclusions; the step premise is [PipeOutN.cstep_okN_tok] at any
     writer that is not a node's (no prompt byte is its) *)
  Lemma pkit_of (w : wid) (s : list (bv 8)) :
    (forall k, w <> WSh k) ->
    fire_okN wsN RUNN WITN termw TOKN w s (EXf fcR pr (lfilts lR) nc L w s) ->
    □ (∀ w' s', ⌜EXf fcR pr (lfilts lR) nc L w s w' s'⌝ -∗ pdep w' s' -∗ pdep w s ={↑pipeN}=∗ False) -∗
    pns_kit LM PV I sR lR termw TOKN pdep w s.
  Proof using HlR Hadmit.
    intros Hnsh Hok. iIntros "#Hex". rewrite /pns_kit. iSplit.
    - iExists (EXf fcR pr (lfilts lR) nc L w s). iSplitR; [by iPureIntro | iExact "Hex"].
    - iPureIntro. intros c [Hc Hlt].
      apply (cstep_okV_tok LM PV I sR lR HlR Hadmit w s c Hc Hlt).
      intros k Hk. by destruct (Hnsh k Hk).
  Qed.

  (* SILENCE: an unfired writer commits the empty source *)
  Lemma fam_silence (E : coPset) (w : wid) :
    ↑pnsN ⊆ E -> w ∈ wsN -> silence_okN wsN RUNN termw TOKN w (fun _ _ => False) ->
    FAM -∗ wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None ={E}=∗
    wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) (Some []).
  Proof using HlR Hadmit Hcons Hfc Hplok.
    intros HE Hw Hok. iIntros "#Hinv Hc Hm".
    iApply (blkN_silence wsN (wids_NoDup _) RUNN PWN (PWN_tl g LM CP v I sR)
              termw TOKN pdep pdep_timeless E pnsN ∅ (S gen_id) γc γm w
              (fun _ _ => False) HE ltac:(set_solver) Hw Hok with "[] Hinv Hc Hm []").
    - iIntros "!>" (w' s' []).
    - iApply pdep_nil.
  Qed.

  (* A COMMITTED WRITER'S DEPOSIT, peeked at through the family: its halves
     say it has written, so the family holds its deposit *)
  Lemma fam_peek (E : coPset) (w : wid) (s : list (bv 8)) (c : nat) (Φ : iProp Σ) :
    ↑pnsN ⊆ E -> w ∈ wsN -> (0 < c)%nat ->
    FAM -∗ wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) -∗
    (pdep w s ={E ∖ ↑pnsN}=∗ pdep w s ∗ Φ) ={E}=∗
    wcurN γc w (1/2) c ∗ wmodeN γm w (1/2) (Some s) ∗ Φ.
  Proof using .
    intros HE Hw Hc. iIntros "#Hinv Hcw Hmw Hacc".
    rewrite /blkN_inv. iInv "Hinv" as ">Hb" "Hclose".
    rewrite {1}/blkN_body. iDestruct "Hb" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not wsN γc w (1/2) c Hw with "Hcw Hdone") as %[]. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    destruct (elem_of_list_lookup_1 wsN w Hw) as (i & Hi).
    iDestruct (big_sepL_lookup_acc _ _ i w Hi with "Hb") as "[Hw Hcl]".
    rewrite {1}/wstN. iDestruct "Hw" as "(Hc' & Hm' & Hd)".
    rewrite /wcurN /wmodeN.
    iDestruct (ghost_var_agree with "Hcw Hc'") as %Hcnt.
    iDestruct (ghost_var_agree with "Hmw Hm'") as %Hmd.
    assert (Hcmt : cmtN md sel w = true).
    { rewrite /cmtN bool_decide_true; [done |]. left. apply cntN_elem. lia. }
    rewrite Hcmt /srcN -Hmd /=.
    iMod ("Hacc" with "Hd") as "[Hd HΦ]".
    iMod ("Hclose" with "[HPW Hc' Hm' Hd Hcl]") as "_".
    { iNext. rewrite /blkN_body. iLeft. iExists md, sel. iFrame "HPW".
      iSplitL; [| by iPureIntro].
      iApply "Hcl". rewrite /wstN /wcurN /wmodeN Hcmt /srcN -Hmd /=. iFrame. }
    iModIntro. iFrame.
  Qed.

  (* ...and the cursor never passes the source *)
  Lemma fam_cur_le (E : coPset) (w : wid) (s : list (bv 8)) (c : nat) :
    ↑pnsN ⊆ E -> w ∈ wsN ->
    FAM -∗ wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) ={E}=∗
    ⌜(c <= length s)%nat⌝ ∗ wcurN γc w (1/2) c ∗ wmodeN γm w (1/2) (Some s).
  Proof using .
    intros HE Hw. iIntros "#Hinv Hcw Hmw".
    rewrite /blkN_inv. iInv "Hinv" as ">Hb" "Hclose".
    rewrite {1}/blkN_body. iDestruct "Hb" as "[Hfam | Hdone]"; last first.
    { iDestruct (blkN_done_not wsN γc w (1/2) c Hw with "Hcw Hdone") as %[]. }
    iDestruct "Hfam" as (md sel) "(HPW & Hb & %Hfam)".
    destruct (elem_of_list_lookup_1 wsN w Hw) as (i & Hi).
    iDestruct (big_sepL_lookup_acc _ _ i w Hi with "Hb") as "[Hw Hcl]".
    rewrite {1}/wstN. iDestruct "Hw" as "(Hc' & Hm' & Hd)".
    rewrite /wcurN /wmodeN.
    iDestruct (ghost_var_agree with "Hcw Hc'") as %Hcnt.
    iDestruct (ghost_var_agree with "Hmw Hm'") as %Hmd.
    pose proof Hfam as (_ & _ & _ & Hwf & _).
    pose proof (Hwf w) as Hle. rewrite /srcN -Hmd /= in Hle.
    iMod ("Hclose" with "[HPW Hc' Hm' Hd Hcl]") as "_".
    { iNext. rewrite /blkN_body. iLeft. iExists md, sel. iFrame "HPW".
      iSplitL; [| by iPureIntro].
      iApply "Hcl". rewrite /wstN /wcurN /wmodeN. iFrame. }
    iModIntro. iFrame "Hcw Hmw". iPureIntro. lia.
  Qed.

  (* ================================================================= *)
  (*  THE PAYLOADS                                                      *)
  (* ================================================================= *)

  (* a writer at its FINAL state: unfired, or its whole source written
     (and no fork line: the round is not terminal at it) *)
  Definition wfin (w : wid) : iProp Σ :=
    ∃ o, pns_wfin γc γm w o ∗ ⌜forall s, o = Some s -> termw w s = false⌝.
  (* ...and COMMITTED: what the filing takes *)
  Definition wdone (w : wid) : iProp Σ :=
    ∃ s, pns_wfin γc γm w (Some s) ∗ ⌜termw w s = false⌝.

  (* the content writer: final, or mid-line at [c] (the chain says where) *)
  Definition wlast (oc : option nat) : iProp Σ :=
    match oc with
    | None => wfin WLast
    | Some c => wcurN γc WLast (1/2) c ∗ wmodeN γm WLast (1/2) (Some L)
                ∗ ⌜(0 < c <= length L)%nat⌝
    end%I.

  (* the writers of the suffix from stage [j]: sh node [j]'s, its left
     stage's, and so on down to the last cat *)
  Definition wsub (j : nat) : list wid := wids_from j (nc - j).
  Definition wst (w : wid) : iProp Σ :=
    match w with WLast => True | _ => wdone w end%I.

  (* THE SUFFIX'S REPORT at its read outcome: every writer final and the
     content writer's chain -- or the TERMINAL shape: node [i]'s fork line
     on the wire up to its prompt (the frozen resolution with it), and the
     stages the nodes between [j] and [i] waited for *)
  Definition sufN (j : nat) (ro : rd_out) : iProp Σ :=
    ∃ oc, ⌜chain L ro oc⌝ ∗ wlast oc ∗ [∗ list] w ∈ wsub j, wst w.
  Definition terT (i : nat) : iProp Σ :=
    wcurN γc (WSh i) (1/2) 5 ∗ wmodeN γm (WSh i) (1/2) (Some alt_forkc) ∗ ptkV T v I (S gen_id).
  Definition sufT (j : nat) : iProp Σ :=
    ∃ i, ⌜(j <= i < nc)%nat⌝ ∗ terT i ∗ [∗ list] j' ∈ seq j (i - j), wdone (WLeft j').
  Definition suf (j : nat) (ro : rd_out) : iProp Σ := sufN j ro ∨ sufT j.

  (* A NODE'S TWO CHILDREN'S REPORTS.  The right one: the suffix below the
     node's pipe [P k], at the outcome of its reader end.  The left one:
     the stage's writer final, and -- unless its exec failed -- its write
     outcome on [P k] and, below the producer, its read outcome on the pipe
     above (a prefix of the line), which it filtered. *)
  Definition rrep (j : nat) : iProp Σ :=
    ∃ ro, rd_final (P (j - 1)) ro ∗ suf j ro.
  Definition lrep (k : nat) : iProp Σ :=
    ∃ o, pns_wfin γc γm (WLeft k) o
      ∗ (⌜exists s, o = Some s /\ fail_src pr (lfilts lR) k s⌝
         ∨ ∃ wo, wr_final (P k) L wo
             ∗ match k with
               | O => ⌜forall D, wo = WrAll D -> D = L⌝
               | S k' => ∃ ro, rd_final (P k') ro ∗ ⌜filterer (lfilt lR (S k')) ro wo /\ rd_pre L ro⌝
               end).

  (* the producer's loan, back beside the left report of node 0 *)
  Definition lrd (k : nat) : iProp Σ := match k with O => Rd | S _ => True end%I.

  Lemma lrd_S (k : nat) : ⊢ lrd (S k).
  Proof using . rewrite /lrd. done. Qed.

  (* THE PAYMENT node [k]'s children owe, side-tagged at its pipe *)
  Definition QcK (k : nat) : iProp Σ := (T ∨ pipe_Qc (P k) (lrd k ∗ lrep k) (rrep (S k)))%I.

  (* THE ROUND'S: what the forked sh running the whole line pays the main
     loop -- every writer committed and exhausted (the filing's input) with
     the producer's loan back, or the terminal round (the prompt's; a
     stray producer may still hold the loan, review B3) *)
  Definition Qtop : iProp Σ :=
    (T ∨ (([∗ list] w ∈ wsN, wdone w) ∗ Rd)
       ∨ (∃ i, ⌜(i < nc)%nat⌝ ∗ terT i ∗ [∗ list] j ∈ seq 0 i, wdone (WLeft j)))%I.

  Global Instance pns_wfin_timeless w o : Timeless (pns_wfin γc γm w o).
  Proof using . rewrite /pns_wfin. destruct o; apply _. Qed.
  Global Instance wfin_timeless w : Timeless (wfin w).
  Proof using . rewrite /wfin. apply _. Qed.
  Global Instance wdone_timeless w : Timeless (wdone w).
  Proof using . rewrite /wdone. apply _. Qed.
  Global Instance wlast_timeless oc : Timeless (wlast oc).
  Proof using . rewrite /wlast. destruct oc; apply _. Qed.
  Global Instance wst_timeless w : Timeless (wst w).
  Proof using . rewrite /wst. destruct w; apply _. Qed.
  Global Instance ptkV_timeless0 k : Timeless (ptkV T v I k).
  Proof using . rewrite /ptkV. apply _. Qed.
  Global Instance terT_timeless i : Timeless (terT i).
  Proof using . rewrite /terT. apply _. Qed.
  Global Instance sufN_timeless j ro : Timeless (sufN j ro).
  Proof using . rewrite /sufN. apply _. Qed.
  Global Instance sufT_timeless j : Timeless (sufT j).
  Proof using . rewrite /sufT. apply _. Qed.
  Global Instance suf_timeless j ro : Timeless (suf j ro).
  Proof using . rewrite /suf. apply _. Qed.
  Global Instance rd_final_timeless0 pn ro : Timeless (rd_final pn ro).
  Proof using . rewrite /rd_final. destruct ro; apply _. Qed.
  Global Instance wr_final_timeless0 pn wo : Timeless (wr_final pn L wo).
  Proof using . rewrite /wr_final. destruct wo; apply _. Qed.
  Global Instance rrep_timeless j : Timeless (rrep j).
  Proof using . rewrite /rrep. apply _. Qed.
  Global Instance lrep_timeless k : Timeless (lrep k).
  Proof using . rewrite /lrep. destruct k; apply _. Qed.
  Global Instance lrd_timeless `{!Timeless Rd} k : Timeless (lrd k).
  Proof using . rewrite /lrd. destruct k; apply _. Qed.
  Global Instance QcK_timeless `{!Timeless Rd} k : Timeless (QcK k).
  Proof using . rewrite /QcK /pipe_Qc. apply _. Qed.
  Global Instance Qtop_timeless `{!Timeless Rd} : Timeless Qtop.
  Proof using . rewrite /Qtop. apply _. Qed.
End UShPipesDefs.

(* ===================================================================== *)
(*  THE ROUND'S FIRING PREMISE, DISCHARGED FROM THE RUN MODEL             *)
(* ===================================================================== *)

(* the committed sources after a first byte: the old vector, updated *)
Lemma cmtN_fire_wid (md : wid -> option bytes) (sel : list wid) (w : wid) (s : bytes) (x : wid) :
  x <> w -> cmtN (mdupd md w s) (sel ++ [w]) x = cmtN md sel x.
Proof using.
  intros Hne. rewrite /cmtN /mdupd decide_False; [| exact Hne].
  apply bool_decide_ext. rewrite elem_of_app elem_of_list_singleton. tauto.
Qed.

Lemma vsrc_fire (md : wid -> option bytes) (sel : list wid) (w : wid) (s : bytes)
    (src : wid -> bytes) :
  w ∉ sel -> (forall x, src x = default [] (rmd md sel x)) ->
  forall x, vupd src w s x = default [] (rmd (mdupd md w s) (sel ++ [w]) x).
Proof using.
  intros Hws Hs x. unfold vupd. case_decide as Hxw.
  - subst x. rewrite /rmd /cmtN bool_decide_true; [| left; set_solver].
    rewrite /mdupd decide_True //.
  - rewrite Hs /rmd (cmtN_fire_wid md sel w s x Hxw) /mdupd decide_False //.
Qed.

(* a nonempty committed entry of the vector is a committed writer *)
Lemma ex_of_src (md : wid -> option bytes) (sel : list wid) (src : wid -> bytes)
    (EX : wid -> bytes -> Prop) :
  (forall x, src x = default [] (rmd md sel x)) ->
  (exists w', src w' <> [] /\ EX w' (src w')) ->
  exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EX w' s'.
Proof using.
  intros Hs (w' & Hnz & Hex). rewrite Hs in Hnz Hex. revert Hnz Hex. rewrite /rmd.
  destruct (cmtN md sel w') eqn:Hc; [| cbn; intros Hq; by destruct Hq].
  destruct (md w') as [s' |] eqn:Hm; [| cbn; intros Hq; by destruct Hq].
  intros _ Hex. by exists w', s'.
Qed.

Section fire_glue.
  Context (LM : lmodel) (PV : pview LM) (I : list (bv 8)) (sR : lm_st LM) (lR : pline').
  Hypothesis HlR : pv_line PV (lineV LM I) = Some lR.
  Context (Ha : pns_admV PV lR).
  Local Notation fc := (pv_fc PV sR).
  (* the line: its producer [pr] (echo, or [cat f]) and its filter stages
     [fs]; its content one line (the union's every content is) *)
  Context (pr : producer) (fs : list filt) (Hn : fs <> []).
  Context (Hline : lR = LPipes pr fs).
  Local Notation L := (prod_content fc pr).
  Hypothesis HL1 : GrepFilt.oneline L.

  (* THE FIRING PREMISE: every commit a process of the round makes is
     admitted by the run model, or refuted by a committed deposit *)
  Lemma pipes_fire_ok (w : wid) (s : list (bv 8)) :
    w ∈ wids (lcats (lR)) -> fire_src fc pr (lfilts lR) L w s ->
    fire_okN (wids (lcats (lR))) (runN fc (lR)) (pwitV LM I sR)
      termw (tokN fc (lR)) w s (EXf fc pr (lfilts lR) (lcats (lR)) L w s).
  Proof using HlR Ha Hline Hn HL1.
    intros Hwin Hf.
    assert (Hfs : lfilts lR = fs) by (rewrite Hline; reflexivity).
    assert (Hnc : lcats (lR) = length fs) by (rewrite Hline; reflexivity).
    rewrite Hfs in Hf |- *. rewrite Hnc in Hwin.
    apply (fire_okV_tok LM PV I sR lR HlR Ha w s _ (fire_src_ne fc pr fs w s Hf)).
    - intros md sel Hfam Hmw Hws Htm. rewrite Hnc.
      pose proof Hfam as (_ & _ & _ & _ & Hinv).
      assert (Htm' : tmN termw (mdupd md w s) sel = tmN termw md sel).
      { apply tmN_ext. intros x Hx. rewrite /mdupd decide_False //. intros ->. exact (Hws Hx). }
      rewrite tmN_snoc Htm' srcN_mdupd_self in Htm. apply orb_false_iff in Htm as [Htm0 Hw0].
      destruct Hinv as [Hrun _]. destruct (Hrun Htm0) as (src & Hr & Hsrc).
      rewrite Hline in Hr. pose proof (run_real fc pr fs Hn HL1 src Hr) as Hre.
      assert (Hsw : src w = []) by (rewrite Hsrc /rmd Hmw; by destruct (cmtN md sel w)).
      destruct (fire_nt fc pr fs Hn src w s Hre Hsw Hwin Hf Hw0) as [Hre' | Hx].
      + left. exists (vupd src w s). split; [rewrite Hline; exact (real_run fc pr fs Hn HL1 _ Hre') |].
        exact (vsrc_fire md sel w s src Hws Hsrc).
      + right. exact (ex_of_src md sel src (EXf fc pr fs (length fs) L w s) Hsrc Hx).
    - intros md sel Hfam Hmw Hws Htm. rewrite Hnc.
      pose proof Hfam as (_ & Hmin & _ & _ & Hinv).
      assert (Htm' : tmN termw (mdupd md w s) sel = tmN termw md sel).
      { apply tmN_ext. intros x Hx. rewrite /mdupd decide_False //. intros ->. exact (Hws Hx). }
      rewrite tmN_snoc Htm' srcN_mdupd_self in Htm.
      destruct (tmN termw md sel) eqn:Htm0.
      + destruct Hinv as [_ Htok]. destruct (Htok Htm0) as [(src & Hr & Hsrc) _].
        rewrite Hline in Hr. destruct (terms_realT fc pr fs src Hr) as [i Hi].
        assert (Hsw : src w = []) by (rewrite Hsrc /rmd Hmw; by destruct (cmtN md sel w)).
        destruct (fire_t2 fc pr fs src i w s Hi Hsw Hwin Hf) as [Hi' | Hx].
        * left. exists (vupd src w s).
          split; [rewrite Hline; exact (realT_terms fc pr fs Hn _ i Hi') |].
          exact (vsrc_fire md sel w s src Hws Hsrc).
        * right. exact (ex_of_src md sel src (EXf fc pr fs (length fs) L w s) Hsrc Hx).
      + cbn [orb] in Htm.
        destruct Hinv as [Hrun _]. destruct (Hrun Htm0) as (src & Hr & Hsrc).
        rewrite Hline in Hr. pose proof (run_real fc pr fs Hn HL1 src Hr) as Hre.
        assert (Hsw : src w = []) by (rewrite Hsrc /rmd Hmw; by destruct (cmtN md sel w)).
        assert (Hdom : forall x, x ∉ wids (length fs) -> src x = []).
        { intros x Hx. rewrite Hsrc /rmd. destruct (cmtN md sel x); [| done].
          destruct (md x) eqn:Hmx; [| done]. exfalso. apply Hx. rewrite -Hnc.
          apply Hmin. by rewrite Hmx. }
        destruct w as [k | k |]; cbn [termw] in Htm; try discriminate Htm.
        apply bool_decide_eq_true in Htm. subst s.
        assert (Hk : (k < length fs)%nat) by (rewrite wids_elem in Hwin; exact Hwin).
        destruct (fire_t1 fc pr fs src k Hre Hdom Hsw Hk) as [HT | Hx].
        * left. exists (vupd src (WSh k) alt_forkc).
          split; [rewrite Hline; exact (realT_terms fc pr fs Hn _ k HT) |].
          exact (vsrc_fire md sel (WSh k) alt_forkc src Hws Hsrc).
        * right. exact (ex_of_src md sel src (EXf fc pr fs (length fs) L (WSh k) alt_forkc) Hsrc Hx).
  Qed.
End fire_glue.
