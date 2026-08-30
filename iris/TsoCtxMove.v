(* TsoCtxMove.v -- THE SAME-HART HAND-OFF (tso-port.md §0.43′; tso-machine-flip.md
   A6.128): moving a context-indexed fact between two RUNNING contexts on one
   hart, with both running tokens in hand.

   WHERE IT IS NEEDED.  swtch hands cells from the caller's thread to the
   target's with no fence between: the scheduler's [p->state = RUNNING] /
   [c->proc = p] stores are still in the hart's store buffer when the proc's
   [forkret]/[release] read them, and the parker's save-area stores are
   buffered when the scheduler resumes.  Store forwarding makes those reads
   correct on the hardware; in the logic that is the AUTHOR arm of
   [visibleb], which is what a context's DIRTY registration records.  So:

     - a CLEAN cell at ξ0 ([t ≤ B0 ≤ view]) is clean at ξ1 once ξ1's bound is
       raised to [max B1 B0] -- legal, both are under this hart's view
       ([TsoCtx.ctx_bound_raise]'s argument, paid with ξ0's own receipt);
     - a DIRTY cell at ξ0 (its key registered at ξ0, the message this hart's
       own) is REGISTERED at ξ1 with the same justification.  Registration is
       total because the dirty set is a monotone set authority whose
       membership is re-mintable (A6.128, [TsoGhost.dset_insert]): whether or
       not ξ1 already has the key, it gets the witness.

   The class [CtxMove R] is [TsoCtx.CtxMorph]'s twin for this crossing; its
   structural instances mirror [CtxMorph]'s.  Nothing here consults the
   interpretation: both premises are running tokens.

   WHY ITS OWN FILE: [TsoCtx.v] is under the whole tree; this is a derivation
   off its public unseal lemmas ([TsoCtxAbsorbLb] / [TsoCtxPark] precedent). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map mono_nat.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.

Section Move.
  Context `{!riscvGS Σ}.

  Local Lemma view_lb_max' (gv gl : gname) (h : agent) (K1 K2 : nat) :
    view_lb gv gl h K1 -∗ view_lb gv gl h K2 -∗ view_lb gv gl h (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2".
    destruct (Nat.le_ge_cases K1 K2) as [Hle|Hle].
    - rewrite (Nat.max_r _ _ Hle). iExact "H2".
    - rewrite (Nat.max_l _ _ Hle). iExact "H1".
  Qed.

  (* THE CLEAN HALF: a bound ξ0 has passed, ξ1 passes too -- ξ1's bound
     rises to ξ0's.  Both are under the hart's view, so the raised bound
     keeps [B ≤ K] with the joined receipt; ξ1's dirty justifications are
     monotone in the bound. *)
  Lemma ctx_move_floor `{CID : CpuId} (ξ0 ξ1 : CtxId) (lo : nat) :
    own_context ξ0 -∗ own_context ξ1 -∗ ctx_floor ξ0 lo ==∗
    own_context ξ0 ∗ own_context ξ1 ∗ ctx_floor ξ1 lo.
  Proof.
    rewrite !own_context_unseal /own_context_def.
    iIntros "(%B0 & %K0 & %W0 & %D0 & [Hb0 Hd0] & #HK0 & %HBK0 & #HW0 & %HDW0 & #Hoks0)
             (%B1 & %K1 & %W1 & %D1 & [Hb1 Hd1] & #HK1 & %HBK1 & #HW1 & %HDW1 & #Hoks1) #Hfl".
    iDestruct (llb_valid with "Hb0 Hfl") as %HloB0.
    iMod (mono_nat_own_update (Nat.max B1 B0) with "Hb1") as "[Hb1 #Hlb1]"; first lia.
    iDestruct (view_lb_max' _ _ _ K1 K0 with "HK1 HK0") as "#HKj".
    iAssert ([∗ set] k ∈ D1,
               dirty_ok logm_name (hart_agent cpu_id) (Nat.max B1 B0) k)%I as "#Hoks1'".
    { iApply (big_sepS_impl with "Hoks1"). iIntros "!>" (k _) "Hok".
      iApply (dirty_ok_mono with "Hok"). lia. }
    iModIntro.
    iSplitL "Hb0 Hd0".
    { iExists B0, K0, W0, D0. iFrame "Hb0 Hd0 HK0 HW0 Hoks0". by iPureIntro. }
    iSplitL "Hb1 Hd1".
    { iExists (Nat.max B1 B0), (Nat.max K1 K0), W1, D1.
      iFrame "Hb1 Hd1 HKj HW1 Hoks1'". iPureIntro. split; [lia | exact HDW1]. }
    rewrite /ctx_floor /llb. iLeft. iApply (mono_nat_lb_own_le with "Hlb1"). lia.
  Qed.

  (* THE CELL MOVES, EITHER ARM. *)
  Lemma ctx_move_pointsto `{CID : CpuId} `{KTR : !CurKtier} (ξ0 ξ1 : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    own_context ξ0 -∗ own_context ξ1 -∗ ctx_pointsto (KTR := KTR) ξ0 a dq v ==∗
    own_context ξ0 ∗ own_context ξ1 ∗ ctx_pointsto (KTR := KTR) ξ1 a dq v.
  Proof.
    iIntros "H0 H1 HP".
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iDestruct "HP" as "(%ppn & %t & #Hk & %Hc & %Hr & %Hpin & Hpt & Hts & Hbit)".
    iDestruct "Hbit" as "[#Hcl | #Hdt]".
    - (* clean: raise ξ1's bound to ξ0's *)
      iMod (ctx_move_floor ξ0 ξ1 t with "H0 H1 Hcl") as "(H0 & H1 & #Hfl1)".
      iModIntro. iFrame "H0 H1". iExists ppn, t. iFrame "Hk Hpt Hts".
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iLeft. iExact "Hfl1".
    - (* dirty: the key is ξ0's registration; look at its justification *)
      iEval (rewrite own_context_unseal /own_context_def) in "H0".
      iDestruct "H0" as "(%B0 & %K0 & %W0 & %D0 & [Hb0 Hd0] & #HK0 & %HBK0 & #HW0 & %HDW0 & #Hoks0)".
      iDestruct (dset_lookup with "Hd0 Hdt") as %HD0.
      iDestruct (big_sepS_elem_of _ _ _ HD0 with "Hoks0") as "#Hok0".
      pose proof (HDW0 _ HD0) as HtW0. simpl in HtW0.
      iDestruct "Hok0" as "[%HtB0 | #Hown]".
      + (* morally clean at ξ0: treat as clean *)
        simpl in HtB0.
        iDestruct (mono_nat_lb_own_get with "Hb0") as "#Hlb0".
        iAssert (ctx_floor ξ0 t) as "#Hfl0".
        { rewrite /ctx_floor /llb. iLeft. iApply (mono_nat_lb_own_le with "Hlb0"). lia. }
        iAssert (own_context ξ0) with "[Hb0 Hd0]" as "H0".
        { rewrite own_context_unseal /own_context_def.
          iExists B0, K0, W0, D0. iFrame "Hb0 Hd0 HK0 HW0 Hoks0". by iPureIntro. }
        iMod (ctx_move_floor ξ0 ξ1 t with "H0 H1 Hfl0") as "(H0 & H1 & #Hfl1)".
        iModIntro. iFrame "H0 H1". iExists ppn, t. iFrame "Hk Hpt Hts".
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
        iLeft. iExact "Hfl1".
      + (* this hart's own message: register at ξ1 *)
        iEval (rewrite own_context_unseal /own_context_def) in "H1".
        iDestruct "H1" as "(%B1 & %K1 & %W1 & %D1 & [Hb1 Hd1] & #HK1 & %HBK1 & #HW1 & %HDW1 & #Hoks1)".
        iMod (dset_insert _ D1 (t, pa_of ppn a) with "Hd1") as "[Hd1 #Hdt1]".
        iDestruct (llb_max with "HW1 HW0") as "#HW1'".
        iAssert ([∗ set] k ∈ D1 ∪ {[(t, pa_of ppn a)]},
                   dirty_ok logm_name (hart_agent cpu_id) B1 k)%I as "#Hoks1'".
        { destruct (decide ((t, pa_of ppn a) ∈ D1)) as [Hin | Hnin].
          - assert (Heq : D1 ∪ {[(t, pa_of ppn a)]} = D1) by set_solver.
            rewrite Heq. iExact "Hoks1".
          - rewrite (union_comm_L D1) big_sepS_insert; last exact Hnin.
            iSplit; [| iExact "Hoks1"]. rewrite /dirty_ok. iRight. iExact "Hown". }
        iModIntro. rewrite !own_context_unseal /own_context_def.
        iSplitL "Hb0 Hd0".
        { iExists B0, K0, W0, D0. iFrame "Hb0 Hd0 HK0 HW0 Hoks0". by iPureIntro. }
        iSplitL "Hb1 Hd1".
        { iExists B1, K1, (Nat.max W1 W0), (D1 ∪ {[(t, pa_of ppn a)]}).
          iFrame "Hb1 Hd1 HK1 HW1' Hoks1'". iPureIntro. split; [exact HBK1|].
          intros k Hk. apply elem_of_union in Hk as [Hk | Hk].
          - have := HDW1 _ Hk. lia.
          - apply elem_of_singleton in Hk. subst k. simpl. lia. }
        iExists ppn, t. iFrame "Hk Hpt Hts".
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iRight. iExact "Hdt1".
  Qed.

  (* The physical-tier byte ([TsoCtx.ctx_phys_pointsto]: the ledger pages --
     trapframes, kernel stacks) moves the same way; its seal has no ppn. *)
  Lemma ctx_move_phys_pointsto `{CID : CpuId} (ξ0 ξ1 : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    own_context ξ0 -∗ own_context ξ1 -∗ ctx_phys_pointsto ξ0 a dq v ==∗
    own_context ξ0 ∗ own_context ξ1 ∗ ctx_phys_pointsto ξ1 a dq v.
  Proof.
    iIntros "H0 H1 HP".
    rewrite !ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "HP" as "(%t & Hpt & Hts & Hbit)".
    iDestruct "Hbit" as "[#Hcl | #Hdt]".
    - iMod (ctx_move_floor ξ0 ξ1 t with "H0 H1 Hcl") as "(H0 & H1 & #Hfl1)".
      iModIntro. iFrame "H0 H1". iExists t. iFrame "Hpt Hts". iLeft. iExact "Hfl1".
    - iEval (rewrite own_context_unseal /own_context_def) in "H0".
      iDestruct "H0" as "(%B0 & %K0 & %W0 & %D0 & [Hb0 Hd0] & #HK0 & %HBK0 & #HW0 & %HDW0 & #Hoks0)".
      iDestruct (dset_lookup with "Hd0 Hdt") as %HD0.
      iDestruct (big_sepS_elem_of _ _ _ HD0 with "Hoks0") as "#Hok0".
      pose proof (HDW0 _ HD0) as HtW0. simpl in HtW0.
      iDestruct "Hok0" as "[%HtB0 | #Hown]".
      + simpl in HtB0.
        iDestruct (mono_nat_lb_own_get with "Hb0") as "#Hlb0".
        iAssert (ctx_floor ξ0 t) as "#Hfl0".
        { rewrite /ctx_floor /llb. iLeft. iApply (mono_nat_lb_own_le with "Hlb0"). lia. }
        iAssert (own_context ξ0) with "[Hb0 Hd0]" as "H0".
        { rewrite own_context_unseal /own_context_def.
          iExists B0, K0, W0, D0. iFrame "Hb0 Hd0 HK0 HW0 Hoks0". by iPureIntro. }
        iMod (ctx_move_floor ξ0 ξ1 t with "H0 H1 Hfl0") as "(H0 & H1 & #Hfl1)".
        iModIntro. iFrame "H0 H1". iExists t. iFrame "Hpt Hts". iLeft. iExact "Hfl1".
      + iEval (rewrite own_context_unseal /own_context_def) in "H1".
        iDestruct "H1" as "(%B1 & %K1 & %W1 & %D1 & [Hb1 Hd1] & #HK1 & %HBK1 & #HW1 & %HDW1 & #Hoks1)".
        iMod (dset_insert _ D1 (t, a) with "Hd1") as "[Hd1 #Hdt1]".
        iDestruct (llb_max with "HW1 HW0") as "#HW1'".
        iAssert ([∗ set] k ∈ D1 ∪ {[(t, a)]},
                   dirty_ok logm_name (hart_agent cpu_id) B1 k)%I as "#Hoks1'".
        { destruct (decide ((t, a) ∈ D1)) as [Hin | Hnin].
          - assert (Heq : D1 ∪ {[(t, a)]} = D1) by set_solver.
            rewrite Heq. iExact "Hoks1".
          - rewrite (union_comm_L D1) big_sepS_insert; last exact Hnin.
            iSplit; [| iExact "Hoks1"]. rewrite /dirty_ok. iRight. iExact "Hown". }
        iModIntro. rewrite !own_context_unseal /own_context_def.
        iSplitL "Hb0 Hd0".
        { iExists B0, K0, W0, D0. iFrame "Hb0 Hd0 HK0 HW0 Hoks0". by iPureIntro. }
        iSplitL "Hb1 Hd1".
        { iExists B1, K1, (Nat.max W1 W0), (D1 ∪ {[(t, a)]}).
          iFrame "Hb1 Hd1 HK1 HW1' Hoks1'". iPureIntro. split; [exact HBK1|].
          intros k Hk. apply elem_of_union in Hk as [Hk | Hk].
          - have := HDW1 _ Hk. lia.
          - apply elem_of_singleton in Hk. subst k. simpl. lia. }
        iExists t. iFrame "Hpt Hts". iRight. iExact "Hdt1".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The class and its structural instances -- [CtxMorph]'s mirror.    *)
  (* ---------------------------------------------------------------- *)
  Class CtxMove `{CID : CpuId} (R : CtxId → iProp Σ) :=
    ctx_move : ∀ ξ0 ξ1, own_context ξ0 -∗ own_context ξ1 -∗ R ξ0 ==∗
                        own_context ξ0 ∗ own_context ξ1 ∗ R ξ1.

  Global Instance ctx_move_const `{CID : CpuId} (P : iProp Σ) : CtxMove (λ _, P) | 100.
  Proof. iIntros (ξ0 ξ1) "H0 H1 HP !>". iFrame. Qed.

  Global Instance ctx_move_sep `{CID : CpuId} (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ0 ξ1) "H0 H1 [HR1 HR2]".
    iMod (ctx_move with "H0 H1 HR1") as "(H0 & H1 & HR1)".
    iMod (ctx_move with "H0 H1 HR2") as "(H0 & H1 & HR2)".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_move_exist `{CID : CpuId} {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMove (Φ x)) → CtxMove (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ0 ξ1) "H0 H1 (%x & HR)".
    iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
    iModIntro. iFrame "H0 H1". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_move_big_sepL `{CID : CpuId} {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMove (Φ i x)) → CtxMove (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 [HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH (λ i y, Φ (S i) y) _ ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame.
  Qed.

  Global Instance ctx_move_big_sepM `{CID : CpuId} `{Countable K} {A} (m : gmap K A)
      (Φ : K → A → CtxId → iProp Σ) :
    (∀ k x, CtxMove (Φ k x)) → CtxMove (λ ξ, [∗ map] k ↦ x ∈ m, Φ k x ξ)%I.
  Proof.
    intros HΦ. induction m as [|k x m Hk IH] using map_ind.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". rewrite big_sepM_empty. by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 HR".
      iDestruct (big_sepM_insert _ _ _ _ Hk with "HR") as "[HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame "H0 H1". rewrite (big_sepM_insert _ _ _ _ Hk). iFrame.
  Qed.

  Global Instance ctx_move_big_sepS `{CID : CpuId} `{Countable A} (X : gset A)
      (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMove (Φ x)) → CtxMove (λ ξ, [∗ set] x ∈ X, Φ x ξ)%I.
  Proof.
    intros HΦ. induction X as [|x X Hx IH] using set_ind_L.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". rewrite big_sepS_empty. by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 HR".
      iDestruct (big_sepS_insert _ _ _ Hx with "HR") as "[HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame "H0 H1". rewrite (big_sepS_insert _ _ _ Hx). iFrame.
  Qed.

  Global Instance ctx_move_or `{CID : CpuId} (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, R1 ξ ∨ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ0 ξ1) "H0 H1 [HR | HR]".
    - iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)". iModIntro. iFrame "H0 H1". by iLeft.
    - iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)". iModIntro. iFrame "H0 H1". by iRight.
  Qed.

  Global Instance ctx_move_if `{CID : CpuId} (b : bool) (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, if b then R1 ξ else R2 ξ)%I.
  Proof. intros H1 H2. destruct b; [exact H1 | exact H2]. Qed.

  Global Instance ctx_move_pointsto_inst `{CID : CpuId} (kt : ktier) a dq v :
    CtxMove (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof. iIntros (ξ0 ξ1) "H0 H1 HP". iApply (ctx_move_pointsto with "H0 H1 HP"). Qed.

  Global Instance ctx_move_floor_inst `{CID : CpuId} (lo : nat) :
    CtxMove (λ ξ, ctx_floor ξ lo).
  Proof. iIntros (ξ0 ξ1) "H0 H1 #Hfl". iApply (ctx_move_floor with "H0 H1 Hfl"). Qed.

  Global Instance ctx_move_word `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 8)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_move_word2 `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word2_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 2)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_move_word4 `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word4_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 4)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_move_phys_pointsto_inst `{CID : CpuId} a dq v :
    CtxMove (λ ξ, ctx_phys_pointsto ξ a dq v).
  Proof. intros ξ0 ξ1. apply ctx_move_phys_pointsto. Qed.

  Global Instance ctx_move_phys_word `{CID : CpuId} a dq w :
    CtxMove (λ ξ, ctx_phys_word_pointsto ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 8)
            (λ _ j ξ, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_phys_pointsto_inst _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

End Move.

(* THE DRIVER ([CtxMorphTac.ctx_morph_solve]'s mirror): [cur_ctx] unfolded
   first (a payload spelled with the ambient notations elaborates its cells
   at [@cur_ctx XI]), then the structural instances BY NAME down to the
   leaves; what it cannot decompose is left for the caller's own instances. *)
(* THE SOLVER IS SYNTACTIC.  Both the structural steps and the leaves are
   dispatched on the head symbol of the body: an [apply ctx_move_sep] (or
   [apply ctx_move_pointsto_inst]) against a NAMED predicate (say
   [proc_dormant_noctx (XI := ξ) pa st], or a ghost [own]) makes the
   unifier δ-unfold the name and search its [∗]/[∃] spine against the
   lemma's pattern -- measured: SchedCtx's payload instance hung for 20
   minutes.  A named ξ-dependent leaf goes to instance search ([apply _])
   instead, where the consumer registers one [CtxMove] instance per named
   piece (SchedCtx, CpuOwnMove, SwtchCtx); a ξ-free body is a constant.
   [cur_ctx] is unfolded at every step: the notations ([↦ₘ], [↦₈]) hide it,
   and a name unfolded by the consumer's [rewrite /...] exposes fresh
   occurrences. *)
Ltac ctx_move_step :=
  try rewrite /cur_ctx; cbv beta;
  lazymatch goal with
  | |- CtxMove (λ _, ?body) => apply ctx_move_const
  | |- CtxMove (λ ξ, bi_exist _) => apply ctx_move_exist; intros ?
  | |- CtxMove (λ ξ, bi_sep _ _) => apply ctx_move_sep
  | |- CtxMove (λ ξ, bi_or _ _) => apply ctx_move_or
  | |- CtxMove (λ ξ, big_opL bi_sep _ _) => apply ctx_move_big_sepL; intros ? ?
  | |- CtxMove (λ ξ, big_opM bi_sep _ _) => apply ctx_move_big_sepM; intros ? ?
  | |- CtxMove (λ ξ, big_opS bi_sep _ _) => apply ctx_move_big_sepS; intros ?
  | |- CtxMove (λ ξ, if _ then _ else _) => apply ctx_move_if
  | |- CtxMove (λ ξ, ctx_pointsto ξ _ _ _) => apply ctx_move_pointsto_inst
  | |- CtxMove (λ ξ, ctx_floor ξ _) => apply ctx_move_floor_inst
  | |- CtxMove (λ ξ, ctx_word_pointsto ξ _ _ _) => apply ctx_move_word
  | |- CtxMove (λ ξ, ctx_word2_pointsto ξ _ _ _) => apply ctx_move_word2
  | |- CtxMove (λ ξ, ctx_word4_pointsto ξ _ _ _) => apply ctx_move_word4
  | |- CtxMove (λ ξ, ctx_phys_pointsto ξ _ _ _) => apply ctx_move_phys_pointsto_inst
  | |- CtxMove (λ ξ, ctx_phys_word_pointsto ξ _ _ _) => apply ctx_move_phys_word
  | |- _ => apply _
  end.
Ltac ctx_move_solve := repeat ctx_move_step.
