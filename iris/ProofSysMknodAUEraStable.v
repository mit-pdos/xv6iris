(* ProofSysMknodAUEraStable.v -- the mknod stable corollary, DERIVED from
   the AU form and nothing else: [SYSMKNOD_AU_ERA -> SYSMKNOD_AU_ERA_STABLE].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the mknod AU
   prover's follow-on).  [SpecSysMknodAU]'s header is explicit that the
   stable form is owed "FROM the AU form + agreement, never as a second
   walk", and this file is that: NO instruction is stepped, no invariant is
   opened, and the syscall-level half is [ProofSysWriteAUStable]'s assembly
   with one more binder.

   ==== WHAT THE DERIVATION SPENDS, AND WHERE ===========================

   1. THE WALK PREMISE IS DISCHARGED, NOT PASSED ON ([mkr_walk_triv]).  The
      stable client owes no cursor: instantiate [P] and [Pmiss] at [True]
      and [mknod_walk_pre_era]'s one-shot is provable outright -- every
      [ax_hop] at a trivial cursor is [⊢]-derivable, whatever the fetched
      string turns out to be.  This is what collapses the -1 arm's
      three-way fold to two: "the walk died at hop k" and "nothing
      fs-visible happened" both hand back exactly the bundle.

   2. THE PINS ARE SPENT AT THE FIRE INSTANTS, TWICE ([mkr_acre_compose] /
      [mkr_dlookup_compose]).  This is [FsAbsMknodFire]'s [_at_pinned] pair
      at a chain rather than at one row, and it is where the DISCARDED
      flavour of [mkr_pin] pays for itself: the same bundle is copied into
      BOTH commits, so neither arm can strand it (see the statement file's
      note beside [mkr_pin]).  Agreement itself is [mkf_auth_nview], one
      chain element at a time ([mkr_chain_at]), lifted to the whole run by
      a pure transfer ([mkr_arun_view]): a run through the client's
      remembered view whose every visited row still reads its remembered
      value IS a run through the live view.

   3. THE REFUNDS ARE WEAKENED BACK ([mkr_dlookup_forget] /
      [mkr_acre_forget]).  The arms hand back the commit the syscall did
      not fire, and it is a closure at the ENRICHED receipt; the
      enrichment is a conjunct, so it is dropped and the client gets its
      own [Φok]/[Φex] commit back rather than a stronger-looking one it
      did not ask for.

   ==== THE MEASURED SHAPE: ONE LEMMA PER ARM ===========================

   [FsAbsReadFire]'s trap, taken at face value and it was the right call:
   the two arms are cut at the disjunction ([mkr_ok_arm] / [mkr_fail_arm])
   and joined in three lines, because a single two-arm entailment makes
   the kernel check the stable arms' unfolding twice over at [Qed].

   BINDERS: [SpecSysMknodAUEra]'s section list VERBATIM. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import ProcInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsTree.
Require Import FsStateDefs.
Require Import FsAbsMknodFire.
Require Import SpecCreateAU.
Require Import SpecSysMknodAUEra.
Require Import FsAbs.            (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  0.  THE PURE HALF                                                     *)
(* ===================================================================== *)

(* the one index fact the chain's big-op needs, and it is definitional *)
Lemma mkr_lookup_total_tail (ds : list Z) (j : nat) :
  ds !!! S j = (tail ds) !!! j.
Proof. by destruct ds. Qed.

(* A RUN TRANSPORTS ALONG AGREEMENT.  Every directory the client's run
   visits is one of its pinned rows, and a pinned row reads the same in
   both views, so each [astep] answers the same -- the LAST inum is not
   visited and needs no pin, which is exactly why the parent stays
   unpinned. *)
Lemma mkr_arun_view (av avc : aview) (root : Z) (ps : list fname)
    (ds : list Z) :
  arun avc root ps ds ->
  (forall j, (j < length ps)%nat -> av !! (ds !!! j) = avc !! (ds !!! j)) ->
  arun av root ps ds.
Proof.
  intros Hr. induction Hr as [d | d c s ps' ds' Hstep Hr' IH]; intros Hall.
  - constructor.
  - assert (Hd : av !! d = avc !! d).
    { apply (Hall 0%nat). simpl. lia. }
    apply (ARun_cons av d c s ps' ds').
    + rewrite /astep /aents Hd. exact Hstep.
    + apply IH. intros j Hj.
      exact (Hall (S j) ltac:(simpl; lia)).
Qed.

Section MknodStable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  AGREEMENT AT THE INSTANT                                        *)
  (* =================================================================== *)

  Lemma mkr_chain_at Γ (I : gmap Z fs_node) (avc : aview) (ds : list Z)
      (ps : list fname) (j : nat) :
    (j < length ps)%nat ->
    ghost_map_auth (γtop Γ) (1/2) I -∗ mkr_chain Γ avc ds ps -∗
      ⌜abs_view I !! (ds !!! j) = avc !! (ds !!! j)⌝.
  Proof.
    intros Hj. iIntros "Ha Hc".
    destruct (lookup_lt_is_Some_2 ps j Hj) as [s Hs].
    rewrite /mkr_chain.
    iDestruct (big_sepL_lookup _ ps j s Hs with "Hc") as "Hp".
    iDestruct "Hp" as (a) "[%Hav Hn]".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hi.
    iPureIntro. by rewrite Hi Hav.
  Qed.

  (* ...AND THE RUN, WHOLE.  The [∀ j] lives inside the assertion so the
     authority is used once, in a proof parametric in [j]; the conclusion
     is pure, so nothing is spent. *)
  Lemma mkr_chain_run Γ (I : gmap Z fs_node) (avc : aview) (root : Z)
      (ps : list fname) (ds : list Z) :
    arun avc root ps ds ->
    ghost_map_auth (γtop Γ) (1/2) I -∗ mkr_chain Γ avc ds ps -∗
      ⌜arun (abs_view I) root ps ds⌝.
  Proof.
    intros Hr. iIntros "Ha #Hc".
    iAssert (∀ j : nat, ⌜(j < length ps)%nat ->
               abs_view I !! (ds !!! j) = avc !! (ds !!! j)⌝)%I as %Hall.
    { iIntros (j). destruct (decide (j < length ps)%nat) as [Hlt | Hge].
      - by iDestruct (mkr_chain_at Γ I avc ds ps j Hlt with "Ha Hc") as %Hj.
      - iPureIntro. lia. }
    iPureIntro. exact (mkr_arun_view _ _ _ _ _ Hr Hall).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1a.  THE ASK IS REACHABLE: the landed package pays for it          *)
  (* ------------------------------------------------------------------ *)

  (* A client holding [FsAbsPins.apr_pins] -- the pin-returning bundle at a
     fraction -- buys the persistent one with a ghost update and nothing
     else.  What it gives up is the fraction, i.e. the ABILITY TO RETAG
     those directories ever again, which is the whole price of the word
     "stable" here; what it gets is a bundle no arm of this contract can
     strand.  The parent is not in the list, so the price is not paid on
     the row this syscall writes. *)
  Lemma mkr_pin_persist Γ (avc : aview) (q : Qp) (d : Z) (a : anode) :
    avc !! d = Some a -> nview Γ q d a ==∗ mkr_pin Γ avc d.
  Proof.
    intros Hav. rewrite /nview /nview_dq /top_frag_q /mkr_pin.
    iIntros "H". iDestruct "H" as (n) "[Hf %Hab]".
    iMod (ghost_map_elem_persist with "Hf") as "Hf".
    iModIntro. iExists a. iSplitR; [by iPureIntro |].
    iExists n. by iFrame.
  Qed.

  Lemma mkr_chain_of_pins Γ (q : Qp) (avc : aview) (ds : list Z)
      (ps : list fname) :
    apr_pins Γ q avc ds ps ==∗ mkr_chain Γ avc ds ps.
  Proof.
    rewrite /apr_pins /mkr_chain. iIntros "H".
    iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!>" (jj s Hjj) "Hp". rewrite /apn_pin.
    iDestruct "Hp" as (a) "[%Hav Hn]".
    by iApply (mkr_pin_persist Γ avc q _ a Hav with "Hn").
  Qed.

  (* =================================================================== *)
  (*  2.  THE TWO COMMITS, COMPOSED AND WEAKENED BACK                     *)
  (* =================================================================== *)

  Lemma mkr_acre_compose Γ (E : coPset) (c : absnode) (avc : aview)
      (root : Z) (ps : list fname) (ds : list Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    arun avc root ps ds ->
    mkr_chain Γ avc ds ps -∗ acre_commit_at Γ E c Φ -∗
      acre_commit_at Γ E c (mkr_recv root ps ds Φ).
  Proof.
    intros Hr. iIntros "#Hc Hcm". rewrite /acre_commit_at.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iDestruct (mkr_chain_run Γ I avc root ps ds Hr with "Ha Hc") as %Hrun.
    iMod ("Hcm" $! I d i nm ents nl with "[//] Ha") as "(Ha & Hstep & Hph2)".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'".
    iMod ("Hph2" $! I' with "[//] Ha'") as "[Ha' HΦ]".
    iModIntro. iFrame "Ha'". rewrite /mkr_recv.
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  Lemma mkr_dlookup_compose Γ (E : coPset) (avc : aview) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    arun avc root ps ds ->
    mkr_chain Γ avc ds ps -∗ dlookup_commit_at Γ E Φ -∗
      dlookup_commit_at Γ E (mkr_recv root ps ds Φ).
  Proof.
    intros Hr. iIntros "#Hc Hcm". rewrite /dlookup_commit_at.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iDestruct (mkr_chain_run Γ I avc root ps ds Hr with "Ha Hc") as %Hrun.
    iMod ("Hcm" $! I d i nm ents nl with "[//] [//] Ha") as "[Ha HΦ]".
    iModIntro. iFrame "Ha". rewrite /mkr_recv.
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  Lemma mkr_dlookup_forget Γ (E : coPset) (root : Z) (ps : list fname)
      (ds : list Z) (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    dlookup_commit_at Γ E (mkr_recv root ps ds Φ) -∗ dlookup_commit_at Γ E Φ.
  Proof.
    iIntros "Hcm". rewrite /dlookup_commit_at.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iMod ("Hcm" $! I d i nm ents nl with "[//] [//] Ha") as "[Ha HΦ]".
    rewrite /mkr_recv. iDestruct "HΦ" as "[_ HΦ]". iModIntro. by iFrame.
  Qed.

  Lemma mkr_acre_forget Γ (E : coPset) (c : absnode) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    acre_commit_at Γ E c (mkr_recv root ps ds Φ) -∗ acre_commit_at Γ E c Φ.
  Proof.
    iIntros "Hcm". rewrite /acre_commit_at.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iMod ("Hcm" $! I d i nm ents nl with "[//] Ha") as "(Ha & Hstep & Hph2)".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'".
    iMod ("Hph2" $! I' with "[//] Ha'") as "[Ha' HΦ]".
    rewrite /mkr_recv. iDestruct "HΦ" as "[_ HΦ]". iModIntro. by iFrame.
  Qed.

  (* =================================================================== *)
  (*  3.  THE WALK, OWED NOTHING                                          *)
  (* =================================================================== *)

  Lemma mkr_hop_triv (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (k : nat) (s : fname) :
    ⊢ ax_hop F (fun _ _ => True%I) (fun _ _ => True%I) k s.
  Proof.
    rewrite /ax_hop. iIntros (d ents dqv) "_ HF". iModIntro. iFrame "HF".
    by destruct (ents !! s).
  Qed.

  Lemma mkr_walk_triv (γfs : fs_names) (cw : Z) :
    ⊢ mknod_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /mknod_walk_pre_era. iIntros (pl r) "%Hs". iModIntro.
    iSplitR; [done |]. rewrite /ax_hops_from.
    iApply big_sepL_intro. iIntros "!>" (j s Hj). iApply mkr_hop_triv.
  Qed.

  (* =================================================================== *)
  (*  4.  THE ARMS.  ONE LEMMA PER ARM (the read lane's measured cut)     *)
  (* =================================================================== *)

  Lemma mkr_ok_arm Γ (ma mi : Z) (root : Z) (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :
    mknod_post_ok_era Γ ma mi (fun _ _ => True%I)
      (mkr_recv root ps ds Φok) (mkr_recv root ps ds Φex)
    ⊢ mknod_stable_ok_era Γ ma mi root ps ds Φok Φex.
  Proof.
    rewrite /mknod_post_ok_era /mknod_stable_ok_era /cau_ok.
    iIntros "H". iDestruct "H" as (pl i) "[%Hi H]".
    iDestruct "H" as (av d nm ents nl) "(%Hlast & %Hpre & _ & Hcm & HΦ)".
    iEval (rewrite /mkr_recv) in "HΦ". iDestruct "HΦ" as "[%Hrun HΦ]".
    iExists pl, av, d, i, nm, ents, nl.
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitL "Hcm"; [iApply (mkr_dlookup_forget with "Hcm") | iExact "HΦ"].
  Qed.

  Lemma mkr_fail_arm Γ (γfs : fs_names) (cw : Z) (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :
    mknod_post_fail_era Γ γfs cw ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (mkr_recv root ps ds Φok) (mkr_recv root ps ds Φex)
    ⊢ mknod_stable_fail_era Γ ma mi root ps ds Φok Φex.
  Proof.
    rewrite /mknod_post_fail_era /mknod_stable_fail_era /mknod_au_pre_era
            /cau_fail.
    iIntros "[(_ & Hacre & Hdl) | H]".
    { iLeft. iSplitL "Hacre".
      - iApply (mkr_acre_forget with "Hacre").
      - iApply (mkr_dlookup_forget with "Hdl"). }
    iDestruct "H" as (pl) "[(_ & Hacre & Hdl) | H]".
    { iLeft. iSplitL "Hacre".
      - iApply (mkr_acre_forget with "Hacre").
      - iApply (mkr_dlookup_forget with "Hdl"). }
    iDestruct "H" as (d) "(_ & Hacre & [H | Hdl])".
    - iRight. iDestruct "H" as (av i nm ents nl) "(%Hlast & %Hd & %Hnm & HΦ)".
      iEval (rewrite /mkr_recv) in "HΦ". iDestruct "HΦ" as "[%Hrun HΦ]".
      iExists pl, av, d, i, nm, ents, nl.
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitL "Hacre"; [iApply (mkr_acre_forget with "Hacre") | iExact "HΦ"].
    - iLeft. iSplitL "Hacre".
      + iApply (mkr_acre_forget with "Hacre").
      + iApply (mkr_dlookup_forget with "Hdl").
  Qed.

  Lemma mkr_arms Γ (γfs : fs_names) (cw : Z) (ma mi : Z) (root : Z)
      (ps : list fname) (ds : list Z)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) (r : mword 64) :
    mknod_arms_era Γ γfs cw ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (mkr_recv root ps ds Φok) (mkr_recv root ps ds Φex) r
    ⊢ mknod_stable_arms_era Γ ma mi root ps ds Φok Φex r.
  Proof.
    rewrite /mknod_arms_era /mknod_stable_arms_era.
    iIntros "[[%Hr Hok] | [%Hr Hfail]]".
    - iLeft. iSplitR; [by iPureIntro |]. iApply (mkr_ok_arm with "Hok").
    - iRight. iSplitR; [by iPureIntro |]. iApply (mkr_fail_arm with "Hfail").
  Qed.

End MknodStable.

(* ===================================================================== *)
(*  5.  THE FUNCTOR                                                       *)
(* ===================================================================== *)

Module SysMknodAUEraStable (M : SYSMKNOD_AU_ERA) : SYSMKNOD_AU_ERA_STABLE.

Section ProofStable.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_sys_mknod_au_era_stable
      (γf : gname) (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64) (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64) (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (root : Z) (avc : aview) (ds : list Z) (ps : list fname)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
    : wp_sys_mknod_au_era_stable_body γf gs j gl pd pav pu ns dqb dqs dqbs
        dqn v0 v1 v2 pid U m K eb b lks root avc ds ps Φok Φex.
  Proof.
    pose proof (M.wp_sys_mknod_au_era γf gs j gl pd pav pu ns dqb dqs dqbs
                  dqn v0 v1 v2 pid U m K eb b lks
                  (fun _ _ => True%I) (fun _ _ => True%I)
                  (mkr_recv root ps ds Φok) (mkr_recv root ps ds Φex)) as HW.
    cbv beta delta [wp_sys_mknod_au_era_body wp_sys_mknod_au_era_frame] in HW.
    cbv beta delta [wp_sys_mknod_au_era_stable_body wp_sys_mknod_au_era_frame].
    intros Gfs ma mi Hrun pcE pj ret_tgt
           HK Hdev Hnib Hlgeom Hsize Hbm0 Hbmcov Hbmlog Hist Hcovb Hbmgeo
           Hireg Hni1 Hni2 Hni3 Hush Hprk Hnsb Hj Hgl Heb Ha0 Ha1 Ha2.
    iIntros "Hcg Hown Htcsr Hclaim Htext Hdata Hpc Hpenv Hbio Hlog Hseam
             Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hesc Hslks Hiregi Hropen
             Hsbn Hsbi Hsbs Hsbb Hbmres Hkenv Hprocs Hiref Hpriv
             (#Hchain & Hacre & Hdl) Hcont".
    iApply (HW HK Hdev Hnib Hlgeom Hsize Hbm0 Hbmcov Hbmlog Hist Hcovb
              Hbmgeo Hireg Hni1 Hni2 Hni3 Hush Hprk Hnsb Hj Hgl Heb
              Ha0 Ha1 Ha2
              with "Hcg Hown Htcsr Hclaim Htext Hdata Hpc Hpenv Hbio Hlog
                    Hseam Hgen Hdev Hgeo Hdlk Hbsl Hitab Hitinv Hesc Hslks
                    Hiregi Hropen Hsbn Hsbi Hsbs Hsbb Hbmres Hkenv Hprocs
                    Hiref Hpriv [Hacre Hdl]").
    (* ---- THE BUNDLE: the walk owed nothing, the commits are enriched ---- *)
    { rewrite /mknod_au_pre_era. iSplitR; [iApply mkr_walk_triv |].
      iSplitL "Hacre".
      - iApply (mkr_acre_compose _ _ _ avc root ps ds _ Hrun
                  with "Hchain Hacre").
      - iApply (mkr_dlookup_compose _ _ avc root ps ds _ Hrun
                  with "Hchain Hdl"). }
    iIntros (CID' Hch mf ns' P')
      "%Hcs %Hupt Hcg Hown Htcsr Hclaim Hpc Hbsl Hsbn Hsbi Hsbs Hsbb
       %Hns Hiref Hpriv Harms".
    iSpecialize ("Hcont" $! CID' with "[%]"); [exact Hch |].
    iApply ("Hcont" $! mf ns' P'
              with "[%] [%] Hcg Hown Htcsr Hclaim Hpc Hbsl Hsbn Hsbi Hsbs
                    Hsbb [%] Hiref Hpriv [Harms]").
    { exact Hcs. }
    { exact Hupt. }
    { exact Hns. }
    (* ---- THE ONLY REAL STEP AT THIS ALTITUDE ---- *)
    iApply (mkr_arms with "Harms").
  Qed.

End ProofStable.

End SysMknodAUEraStable.
