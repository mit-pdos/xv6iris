(* HartBarrier.v -- §6's BARRIER LEAF, at last
   (tso-machine-flip.md A6.5, ratified; A6.72 implements it).

   A6.5 ruled that the barrier stays a SILENT node -- so every register-only
   window keeps walking over fences it does not care about -- and that §6's
   leaf is a SEPARATE rule over the SAME node, for the proof that wants the
   drain's receipt:

     "A barrier walked by a silent stretch drains but DELIBERATELY PRODUCES
      NO RECEIPT; a barrier stepped by the leaf drains and mints one.  Two
      ways to step a fence, both sound, the proof picks -- and the LEAF IS
      THE ONLY PLACE A RECEIPT IS BORN, which is what keeps the receipt's
      meaning sharp."

   [HartLift.v:139] has named this file as missing since the lifting port.
   It is the honest home for an INTERP-SIDE GHOST STEP at a fence, which is
   what the canon pin's publication needs (A6.70/A6.71: the gate consumes
   [tso_interp_at], and the interp is in hand only inside a WP leaf).

   THE SHAPE, and why it is a bupd rather than a callback.  A memory leaf
   hands the client the bundle inside its own mask-changing fupd because the
   client must ANSWER the event (what value was read, was the write blocked).
   A barrier has no answer: the step is deterministic and state-preserving
   except for the view.  So this rule does the whole mask dance itself, and
   the client supplies only a BUPD over the bundle -- [pub_step] below --
   which the rule runs at the DRAINED view, with the receipt already minted.
   Nothing about the machine reaches the client but the two facts a
   publication needs.

   WHAT THE DRAIN ACTUALLY GIVES, and it is NOT the top of the log.  Under
   two logs (relaxed-ww.md §1.1) [fence_post] takes the floor to
   [max tv (own_pub h log dl)] -- the DRAIN position of the author's own
   last message -- so the client gets [own_pub h glog gdlog <= gtv cpu_id],
   not [length gdlog <= gtv cpu_id].  That is weaker and it is enough: what a
   publisher must show of a byte is that its message is drained under the
   bound, and a byte in the publisher's own context is either clean or its
   own message ([TsoGhost.dirty_ok]'s two arms).  Requiring the drain top
   would have needed a fact about OTHER agents that no client can hold.

   THE RELEASE FENCE BLOCKS (relaxed-ww.md §1.1): a fence with a W
   predecessor ([fence_rel]) is enabled only once every own store has
   drained -- the environment's drain thread does that -- and the leaf
   self-loops until then (Löb, premises intact, exactly as a blocked write
   does in [HartEvents]).  On the enabled arm the client ALSO gets
   [own_drained], which is the premise of every fence-bound ctx law
   ([TsoCtxLedger.ctx_stamp], [ctx_dom_to_stamped], [ctx_deposit]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartEvents.
From Stdlib Require List.
Require Import TsoMemPa.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* §1 THE PROJECTION AND THE RESUME, in [HartLift]'s own style: the caller  *)
(* names the node by a projection that returns a value it could write by    *)
(* hand, and never writes a continuation down (finding F8).                 *)
(* ---------------------------------------------------------------------- *)
Definition hbar_at {X : Type} (m : M X) : option barrier_kind :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option barrier_kind with
       | Interface.Barrier b => fun _ => Some b
       | _ => fun _ => None
       end) k
  | _ => None
  end.

Definition hbar_resume {X : Type} (m : M X) : M X :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> M X with
       | Interface.Barrier _ => fun k => k tt
       | _ => fun _ => m
       end) k
  | _ => m
  end.

Lemma hbar_at_inv {X : Type} (m : M X) (bk : barrier_kind) :
  hbar_at m = Some bk ->
  exists K, m = Interface.Next (Interface.Barrier bk) K /\ hbar_resume m = K tt.
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  injection Hn as <-. exists k. by split.
Qed.

Section barrier.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* §0 THE ENABLING CONDITION IS DECIDABLE: a bounded check over the     *)
  (* issue log that every own message sits in the drain log.  The leaves  *)
  (* decide the machine's arm with it.                                    *)
  (* ------------------------------------------------------------------ *)
  Global Instance own_drained_dec (h : agent) (log : list pwmsg) (dl : list nat) :
    Decision (own_drained h log dl).
  Proof.
    destruct (List.Forall_dec
                (fun i : nat => match log !! i with
                                | Some m => pm_tid m = h -> i ∈ dl
                                | None => True
                                end)
                (fun i => match log !! i as o
                                return Decision (match o with
                                                 | Some m => pm_tid m = h -> i ∈ dl
                                                 | None => True end) with
                          | Some m => _
                          | None => _
                          end)
                (seq 0 (length log))) as [Hf|Hnf].
    - left. intros i m Hi Htid.
      pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
      pose proof (proj1 (List.Forall_forall _ _) Hf i
                    (proj2 (List.in_seq (length log) 0 i) (conj (Nat.le_0_l _) Hlt)))
        as Hfi.
      rewrite Hi in Hfi. exact (Hfi Htid).
    - right. intros Hod. apply Hnf. apply List.Forall_forall. intros i _.
      destruct (log !! i) as [m|] eqn:Hm; [intros Htid; exact (Hod i m Hm Htid)|exact I].
      Unshelve. all: apply _.
  Defined.

  (* the machine's enabled arm, from the negation of the blocked one *)
  Lemma barrier_enabled_of_not (bk : barrier_kind) (h : agent) (log : list pwmsg)
      (dl : list nat) :
    ~ (fence_rel bk = true /\ ~ own_drained h log dl) ->
    fence_rel bk = false \/ own_drained h log dl.
  Proof.
    intros Hn. destruct (fence_rel bk) eqn:Hrel; [|by left].
    right. destruct (decide (own_drained h log dl)) as [Hd|Hd]; [exact Hd|].
    exfalso. exact (Hn (conj eq_refl Hd)).
  Qed.

  (* a draining kind has a W predecessor *)
  Lemma fence_drains_rel (bk : barrier_kind) :
    fence_drains bk = true -> fence_rel bk = true.
  Proof. destruct bk; simpl; congruence. Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 THE CLIENT'S OBLIGATION.  A ghost step against the live interp,   *)
  (* at the machine state the fence leaves behind and at THIS hart's      *)
  (* drained view, with the view's receipt already in hand.  Named        *)
  (* because it is the whole client-visible surface of the leaf: nothing  *)
  (* below [gstate] leaks, and a client that wants nothing writes         *)
  (* [pub_step_id].  The drain's THREE gifts: every own store has drained *)
  (* (the fence-bound ctx laws' premise), the hart's own last drain        *)
  (* position is under its floor, and the floor's receipt.                *)
  (* ------------------------------------------------------------------ *)
  Definition pub_step (P Q : iProp Σ) : iProp Σ :=
    (∀ g : gstate,
       ⌜own_drained (hart_agent cpu_id) g.(glog) g.(gdlog)⌝ -∗
       ⌜(own_pub (hart_agent cpu_id) g.(glog) g.(gdlog) <= g.(gtv) cpu_id)%nat⌝ -∗
       hart_view_lb (g.(gtv) cpu_id) -∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
       tso_interp_at riscv_eraGS g -∗ P ==∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
       tso_interp_at riscv_eraGS g ∗ Q)%I.

  (* the trivial one: a fence that publishes nothing still drains *)
  Lemma pub_step_id (P : iProp Σ) : ⊢ pub_step P P.
  Proof. iIntros (g) "_ _ _ $ $ $". done. Qed.

  (* ------------------------------------------------------------------ *)
  (* §2a THE SHARED SKELETON.  Every barrier leaf below is this one rule  *)
  (* with a different client: the machine's arm is decided, the blocked   *)
  (* arm self-loops (Löb), and on the enabled arm the client's fupd runs  *)
  (* at the post-fence floor and instruction view with the bundle already *)
  (* advanced and both receipts minted.  [Hen] is the enabled condition,  *)
  (* which is where a drain leaf reads [own_drained] off.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_barrier_core {X : Type} (C : M X -> M unit) (bk : barrier_kind)
      (m : M X) (P : iProp Σ) :
    mctx C ->
    hbar_at m = Some bk ->
    gen_cert -∗ P -∗
    (∀ σ img log dl tv itv hr V,
       ⌜fence_rel bk = false \/ own_drained (hart_agent cpu_id) log dl⌝ -∗
       ⌜V (hart_agent cpu_id) = tv⌝ -∗
       ⌜(tv <= length dl)%nat⌝ -∗
       ⌜(itv <= length dl)%nat⌝ -∗
       ⌜hr_bound hr (length dl)⌝ -∗
       TsoGhost.view_lb view_name dlen_name (hart_agent cpu_id)
         (fence_post (hart_agent cpu_id) log dl (fence_drains bk) (fence_acq bk)
            tv (hr_rv hr)) -∗
       hart_iview_lb_at cpu_id
         (if fence_ifetch bk
          then Nat.max itv (fence_post (hart_agent cpu_id) log dl true false tv (hr_rv hr))
          else itv) -∗
       mstate_interp σ -∗
       tso_interp_of riscv_eraGS img σ.(mem) log dl
         (vstep (hart_agent cpu_id)
            (fence_post (hart_agent cpu_id) log dl (fence_drains bk) (fence_acq bk)
               tv (hr_rv hr)) dl V) -∗
       P ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp σ ∗
            tso_interp_of riscv_eraGS img σ.(mem) log dl
              (vstep (hart_agent cpu_id)
                 (fence_post (hart_agent cpu_id) log dl (fence_drains bk) (fence_acq bk)
                    tv (hr_rv hr)) dl V) ∗
            WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj) "#Hcert HP H".
    destruct (hbar_at_inv _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.Barrier bk) (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.Barrier bk) K eq_refl)).
    rewrite Hg.
    iLöb as "IH".
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 dl0 tv0 itv0 hr0 r0 m'0 σ'0 log'0 dl'0 tv'0 itv'0 hr'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      destruct Hs as [(_ & _ & _ & _ & _ & _ & _ & _ & -> & ->)
                     |(_ & _ & _ & _ & _ & _ & _ & -> & ->)]; by split. }
    iIntros (σ oth rv img log dl tv itv hr V) "%Htv %Hitv %Hhr Hσ Hiv Hrv Htso".
    set (h := hart_agent cpu_id).
    destruct (decide (fence_rel bk = true /\ ~ own_drained h log dl)) as [Hblk|Hen'].
    - (* BLOCKED: a release fence waits for the hart's own stores to drain.
         Nothing moves; the premise is intact and Löb closes it. *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
      iExists (Interface.Next (Interface.Barrier bk) (fun v => C (K v))),
        σ, log, dl, tv, itv, hr, rv.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota. left.
        destruct Hblk as [Hrel Hnd]. split_and!; done. }
      iNext. iIntros (m' σ' log' dl' tv' itv' hr' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & _ & -> & -> & -> & -> & -> & -> & -> & ->) | (Hen & _)];
        [|exfalso; destruct Hblk as [Hrel Hnd];
          destruct Hen as [Hen|Hen]; [congruence|exact (Hnd Hen)]].
      iMod "Hclose" as "_". iModIntro. iFrame "Hσ Hiv Hrv".
      iSplitL "Htso".
      { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
      iApply ("IH" with "HP H").
    - (* ENABLED *)
      pose proof (barrier_enabled_of_not bk h log dl Hen') as Hen.
      destruct Hhr as (Hrvlen & Hcohlen).
      iDestruct (tso_interp_of_bound with "Htso") as %Hb.
      assert (Htvlen : (tv <= length dl)%nat) by (rewrite -Htv; apply Hb).
      set (tvn := fence_post h log dl (fence_drains bk) (fence_acq bk) tv (hr_rv hr)).
      set (itvn := if fence_ifetch bk
                   then Nat.max itv (fence_post h log dl true false tv (hr_rv hr))
                   else itv).
      assert (Hadv : (V h <= tvn)%nat).
      { rewrite Htv /tvn. apply fence_post_ge. }
      assert (Htop : (tvn <= length dl)%nat).
      { rewrite /tvn. apply fence_post_le; [exact Htvlen|exact Hrvlen]. }
      iMod (tso_interp_of_advance _ img σ.(mem) log dl V h tvn
              (fin_to_nat_lt cpu_id) Hadv Htop with "Htso") as "Htso".
      iDestruct (tso_interp_of_receipt_at riscv_eraGS img σ.(mem) log dl
                   (vstep h tvn dl V) h tvn (vstep_here h tvn dl V)
                   with "Htso") as "[Htso #Hrcpt]".
      iMod (hart_iview_auth_update cpu_id itv itvn with "Hiv") as "Hiv".
      { rewrite /itvn. case_match; lia. }
      iDestruct (hart_iview_lb_at_get with "Hiv") as "#Hilb".
      iMod ("H" $! σ img log dl tv itv hr V with "[//] [//] [//] [//] [//] Hrcpt Hilb Hσ Htso HP")
        as "Hk".
      iModIntro.
      iExists (C (K tt)), σ, log, dl, tvn, itvn, hr, rv.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota. right.
        split; [exact Hen|]. by split_and!. }
      iNext. iIntros (m' σ' log' dl' tv' itv' hr' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hrel & Hnd & _) | (_ & -> & -> & -> & -> & -> & -> & -> & ->)];
        [exfalso; destruct Hen as [Hen|Hen]; [congruence|exact (Hnd Hen)]|].
      iMod "Hk" as "(Hσ & Htso & HWP)". iModIntro.
      iFrame "Hσ Htso Hiv Hrv". rewrite -Hres. iExact "HWP".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE LEAF, at the WP over a context: the DRAIN leaf.               *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_barrier {X : Type} (C : M X -> M unit) (bk : barrier_kind)
      (m : M X) (P Q : iProp Σ) :
    mctx C ->
    hbar_at m = Some bk ->
    fence_drains bk = true ->
    gen_cert -∗ pub_step P Q -∗ P -∗
    ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hdrain) "#Hcert Hpub HP H".
    iApply (wp_hart_barrier_core C bk m (pub_step P Q ∗ P ∗
              ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)))%I
              HC Hproj with "Hcert [$Hpub $HP $H]").
    iIntros (σ img log dl tv itv hr V) "%Hen %Htv %Htvlen %Hitv %Hhr #Hrcpt _ Hσ Htso (Hpub & HP & H)".
    (* a draining fence has a W predecessor, so it is enabled only drained *)
    assert (Hod : own_drained (hart_agent cpu_id) log dl).
    { destruct Hen as [Hen|Hen]; [|exact Hen].
      rewrite (fence_drains_rel _ Hdrain) in Hen. discriminate Hen. }
    set (h := hart_agent cpu_id).
    set (tvn := fence_post h log dl (fence_drains bk) (fence_acq bk) tv (hr_rv hr)).
    assert (Hown : (own_pub h log dl <= tvn)%nat)
      by (rewrite /tvn Hdrain; apply fence_post_drain).
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    (* the bundle, re-read as a [gstate] fact -- A6.1a's bridge *)
    assert (Hpin' : forall h', (NCPU <= h')%nat -> vstep h tvn dl V h' = length dl).
    { intros h' Hh'. specialize (Hpin h' Hh'). exact Hpin. }
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl (vstep h tvn dl V)
               σ.(sregs) σ.(mdev) Hpin').
    iMod ("Hpub" $! (gs_of img σ.(mem) log dl (vstep h tvn dl V) σ.(sregs) σ.(mdev))
            with "[%] [%] [] Hmem Htso HP") as "(Hmem & Htso & HQ)".
    { cbn [glog gdlog gs_of]. exact Hod. }
    { cbn [glog gdlog gtv gs_of]. rewrite vstep_here. exact Hown. }
    { cbn [gtv gs_of]. rewrite vstep_here.
      rewrite hart_view_lb_unseal /hart_view_lb_def /view_name /dlen_name.
      iExact "Hrcpt". }
    rewrite -(tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl
                (vstep h tvn dl V) σ.(sregs) σ.(mdev) Hpin').
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iNext. iMod "Hclose" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso". iApply ("H" with "HQ").
  Qed.

  (* ================================================================== *)
  (* §3a THE PUBLICATION LEAF (relaxed-ww.md §2.3): keyed on [fence_rel], *)
  (* which `fence rw,w` -- release's fence -- satisfies and              *)
  (* [fence_drains] does not.  Its one gift is [own_drained]: every own   *)
  (* store has drained, which is the premise of the fence-bound ctx laws  *)
  (* ([TsoCtxLedger.ctx_stamp] / [ctx_dom_to_stamped] / [ctx_deposit]).  *)
  (* The client's step is a FUPD AT ⊤ rather than a bupd: the release     *)
  (* hook opens the lock's and the boxes' invariants there.               *)
  (* ================================================================== *)
  Definition rel_step (P Q : iProp Σ) : iProp Σ :=
    (∀ g : gstate,
       ⌜own_drained (hart_agent cpu_id) g.(glog) g.(gdlog)⌝ -∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
       tso_interp_at riscv_eraGS g -∗ P ={⊤}=∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
       tso_interp_at riscv_eraGS g ∗ Q)%I.

  Lemma rel_step_id (P : iProp Σ) : ⊢ rel_step P P.
  Proof. iIntros (g) "_ $ $ $". done. Qed.

  Lemma wp_hart_barrier_rel {X : Type} (C : M X -> M unit) (bk : barrier_kind)
      (m : M X) (P Q : iProp Σ) :
    mctx C ->
    hbar_at m = Some bk ->
    fence_rel bk = true ->
    gen_cert -∗ rel_step P Q -∗ P -∗
    ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hrel) "#Hcert Hpub HP H".
    iApply (wp_hart_barrier_core C bk m (rel_step P Q ∗ P ∗
              ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)))%I
              HC Hproj with "Hcert [$Hpub $HP $H]").
    iIntros (σ img log dl tv itv hr V) "%Hen %Htv %Htvlen %Hitv %Hhr #Hrcpt _ Hσ Htso (Hpub & HP & H)".
    assert (Hod : own_drained (hart_agent cpu_id) log dl).
    { destruct Hen as [Hen|Hen]; [congruence|exact Hen]. }
    set (h := hart_agent cpu_id).
    set (tvn := fence_post h log dl (fence_drains bk) (fence_acq bk) tv (hr_rv hr)).
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    assert (Hpin' : forall h', (NCPU <= h')%nat -> vstep h tvn dl V h' = length dl).
    { intros h' Hh'. specialize (Hpin h' Hh'). exact Hpin. }
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl (vstep h tvn dl V)
               σ.(sregs) σ.(mdev) Hpin').
    iMod ("Hpub" $! (gs_of img σ.(mem) log dl (vstep h tvn dl V) σ.(sregs) σ.(mdev))
            with "[%] Hmem Htso HP") as "(Hmem & Htso & HQ)".
    { cbn [glog gdlog gs_of]. exact Hod. }
    rewrite -(tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl
                (vstep h tvn dl V) σ.(sregs) σ.(mdev) Hpin').
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iNext. iMod "Hclose" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso". iApply ("H" with "HQ").
  Qed.

  Lemma swp_hart_barrier_rel {X : Type} (bk : barrier_kind) (m : M X)
      (Φ : X -> iProp Σ) (P Q : iProp Σ) :
    hbar_at m = Some bk ->
    fence_rel bk = true ->
    gen_cert -∗ rel_step P Q -∗ P -∗
    ▷ (Q -∗ swp (hbar_resume m) Φ) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hrel) "#Hcert Hpub HP H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_barrier_rel C bk m P Q HC Hproj Hrel
              with "Hcert Hpub HP [H Hcont]").
    iNext. iIntros "HQ".
    iApply (swp_use _ Φ C HC with "[H HQ] Hcont"). by iApply "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4 THE [swp] FORM -- the one every composed leaf actually uses.       *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_hart_barrier {X : Type} (bk : barrier_kind) (m : M X)
      (Φ : X -> iProp Σ) (P Q : iProp Σ) :
    hbar_at m = Some bk ->
    fence_drains bk = true ->
    gen_cert -∗ pub_step P Q -∗ P -∗
    ▷ (Q -∗ swp (hbar_resume m) Φ) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdrain) "#Hcert Hpub HP H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_barrier C bk m P Q HC Hproj Hdrain
              with "Hcert Hpub HP [H Hcont]").
    iNext. iIntros "HQ".
    iApply (swp_use _ Φ C HC with "[H HQ] Hcont"). by iApply "H".
  Qed.

  (* ================================================================== *)
  (* §5 THE NON-DRAINING SIBLING (A6.107, §0.36′ step 4).                 *)
  (*                                                                     *)
  (* MEASURED (A6.106): the only barrier on hart 0's boot arm is          *)
  (* `fence rw,w` at [main+0xac] -- [Barrier_RISCV_rw_w], whose           *)
  (* [fence_drains] is FALSE -- so §3's leaf does not apply there, and    *)
  (* the KPT publication has no site.  What the publication actually      *)
  (* needs from a fence is not the drain: it is ACCESS TO THE LIVE        *)
  (* INTERP, so that [KptPublish.kptree_publish_top] can mint the pin at  *)
  (* the log top.  That is strictly less than [pub_step], and this is it. *)
  (*                                                                     *)
  (* [ghost_step] is [pub_step] MINUS ITS GIFTS, and nothing else         *)
  (* changes: the view still moves to [fence_post], the state step is     *)
  (* the same, and the leaf below carries NO premise on [bk] at all.  So  *)
  (* it serves every barrier the model has (a release kind still waits    *)
  (* for the drain), and [pub_step_of_ghost_step] lets a draining site     *)
  (* keep using §3 unchanged.                                             *)
  (* ================================================================== *)
  Definition ghost_step (P Q : iProp Σ) : iProp Σ :=
    (∀ g : gstate,
       gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
       tso_interp_at riscv_eraGS g -∗ P ==∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
       tso_interp_at riscv_eraGS g ∗ Q)%I.

  Lemma ghost_step_id (P : iProp Σ) : ⊢ ghost_step P P.
  Proof. iIntros (g) "$ $ $". done. Qed.

  (* a client that wants nothing from the drain may be run by either leaf *)
  Lemma pub_step_of_ghost_step (P Q : iProp Σ) :
    ghost_step P Q -∗ pub_step P Q.
  Proof. iIntros "H" (g) "_ _ _ Hm Ht HP". iApply ("H" with "Hm Ht HP"). Qed.

  Lemma wp_hart_barrier_gs {X : Type} (C : M X -> M unit) (bk : barrier_kind)
      (m : M X) (P Q : iProp Σ) :
    mctx C ->
    hbar_at m = Some bk ->
    gen_cert -∗ ghost_step P Q -∗ P -∗
    ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj) "#Hcert Hpub HP H".
    iApply (wp_hart_barrier_core C bk m (ghost_step P Q ∗ P ∗
              ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)))%I
              HC Hproj with "Hcert [$Hpub $HP $H]").
    iIntros (σ img log dl tv itv hr V) "%Hen %Htv %Htvlen %Hitv %Hhr #Hrcpt _ Hσ Htso (Hpub & HP & H)".
    set (h := hart_agent cpu_id).
    set (tvn := fence_post h log dl (fence_drains bk) (fence_acq bk) tv (hr_rv hr)).
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    assert (Hpin' : forall h', (NCPU <= h')%nat -> vstep h tvn dl V h' = length dl).
    { intros h' Hh'. specialize (Hpin h' Hh'). exact Hpin. }
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl (vstep h tvn dl V)
               σ.(sregs) σ.(mdev) Hpin').
    iMod ("Hpub" $! (gs_of img σ.(mem) log dl (vstep h tvn dl V) σ.(sregs) σ.(mdev))
            with "Hmem Htso HP") as "(Hmem & Htso & HQ)".
    rewrite -(tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl
                (vstep h tvn dl V) σ.(sregs) σ.(mdev) Hpin').
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iNext. iMod "Hclose" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso". iApply ("H" with "HQ").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE FENCE.I LEAF (claude-notes/projects/icache.md).  [fence.i]      *)
  (* drains nothing on the data side ([fence_drains] is false), but it    *)
  (* has a W predecessor ([fence_rel]) -- it waits for the hart's stores  *)
  (* to drain -- and it raises this hart's INSTRUCTION view past its data *)
  (* view and its own last drain position ([RiscvLang.mnode_step]'s       *)
  (* Barrier arm): the one moment an instruction-view RECEIPT is honestly *)
  (* born.  The rule mints [hart_iview_lb_at cpu_id IK] at the raised     *)
  (* view and runs the client's ghost step with the bounds the stamp needs *)
  (* ([TsoCtxLedger.ctx_xstamp]: every own store drained, the hart's view  *)
  (* and its own last drain position both under [IK]) -- the [userret]    *)
  (* STEP 0 stamping of a process's executable pages is such a step.       *)
  (* ------------------------------------------------------------------ *)
  Definition ifence_step (P Q : iProp Σ) : iProp Σ :=
    (∀ (g : gstate) (IK : nat),
       ⌜own_drained (hart_agent cpu_id) g.(glog) g.(gdlog)⌝ -∗
       ⌜(g.(gtv) cpu_id <= IK)%nat⌝ -∗
       ⌜(own_pub (hart_agent cpu_id) g.(glog) g.(gdlog) <= IK)%nat⌝ -∗
       hart_iview_lb_at cpu_id IK -∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
       tso_interp_at riscv_eraGS g -∗ P ==∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
       tso_interp_at riscv_eraGS g ∗ Q)%I.

  Lemma ifence_step_id (P : iProp Σ) : ⊢ ifence_step P P.
  Proof. iIntros (g IK) "_ _ _ _ $ $ $". done. Qed.

  Lemma wp_hart_fence_i {X : Type} (C : M X -> M unit) (m : M X)
      (P Q : iProp Σ) :
    mctx C ->
    hbar_at m = Some Barrier_RISCV_i ->
    gen_cert -∗ ifence_step P Q -∗ P -∗
    ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj) "#Hcert Hstep HP H".
    iApply (wp_hart_barrier_core C Barrier_RISCV_i m (ifence_step P Q ∗ P ∗
              ▷ (Q -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)))%I
              HC Hproj with "Hcert [$Hstep $HP $H]").
    iIntros (σ img log dl tv itv hr V) "%Hen %Htv %Htvlen %Hitv %Hhr #Hrcpt #Hilb Hσ Htso (Hstep & HP & H)".
    assert (Hod : own_drained (hart_agent cpu_id) log dl).
    { destruct Hen as [Hen|Hen]; [discriminate Hen|exact Hen]. }
    set (h := hart_agent cpu_id).
    (* fence.i neither drains nor acquires on the data side: the floor stays *)
    set (itvn := Nat.max itv (fence_post h log dl true false tv (hr_rv hr))).
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    assert (Hpin' : forall h', (NCPU <= h')%nat -> vstep h tv dl V h' = length dl).
    { intros h' Hh'. specialize (Hpin h' Hh'). exact Hpin. }
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl (vstep h tv dl V)
               σ.(sregs) σ.(mdev) Hpin').
    iMod ("Hstep" $! (gs_of img σ.(mem) log dl (vstep h tv dl V) σ.(sregs) σ.(mdev)) itvn
            with "[%] [%] [%] Hilb Hmem Htso HP") as "(Hmem & Htso & HQ)".
    { cbn [glog gdlog gs_of]. exact Hod. }
    { cbn [gtv gs_of]. rewrite vstep_here /itvn /fence_post /=. lia. }
    { cbn [glog gdlog gs_of]. rewrite /itvn /h /fence_post /=. lia. }
    rewrite -(tso_interp_of_at_gs riscv_eraGS img σ.(mem) log dl
                (vstep h tv dl V) σ.(sregs) σ.(mdev) Hpin').
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iNext. iMod "Hclose" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso". iApply ("H" with "HQ").
  Qed.

  Lemma swp_hart_fence_i {X : Type} (m : M X) (Φ : X -> iProp Σ)
      (P Q : iProp Σ) :
    hbar_at m = Some Barrier_RISCV_i ->
    gen_cert -∗ ifence_step P Q -∗ P -∗
    ▷ (Q -∗ swp (hbar_resume m) Φ) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj) "#Hcert Hstep HP H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_fence_i C m P Q HC Hproj with "Hcert Hstep HP [H Hcont]").
    iNext. iIntros "HQ".
    iApply (swp_use _ Φ C HC with "[H HQ] Hcont"). by iApply "H".
  Qed.

  Lemma swp_hart_barrier_gs {X : Type} (bk : barrier_kind) (m : M X)
      (Φ : X -> iProp Σ) (P Q : iProp Σ) :
    hbar_at m = Some bk ->
    gen_cert -∗ ghost_step P Q -∗ P -∗
    ▷ (Q -∗ swp (hbar_resume m) Φ) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj) "#Hcert Hpub HP H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_barrier_gs C bk m P Q HC Hproj
              with "Hcert Hpub HP [H Hcont]").
    iNext. iIntros "HQ".
    iApply (swp_use _ Φ C HC with "[H HQ] Hcont"). by iApply "H".
  Qed.

  (* ================================================================== *)
  (* THE ACQUIRE LEAF (claude-notes/projects/relaxed-rr.md §4.2).           *)
  (*                                                                     *)
  (* A fence with an R→R edge ([fence_acq]: r,r / r,rw / rw,r / rw,rw /   *)
  (* fence.tso) raises this hart's FLOOR past its READ WATERMARK.  A       *)
  (* client holding a plain load's receipt [hart_rview_lb_at cpu_id K]     *)
  (* ("I have read at view K") therefore leaves with [hart_view_lb K]     *)
  (* ("my floor is at or past K"), which is what every later load and      *)
  (* every floor law consumes.  This is the ONE place the conversion is    *)
  (* honest: the leaf holds the watermark's counter on loan and the view   *)
  (* authority in the bundle at the same step, so [K <= rv <= tv'] is      *)
  (* read off the two authorities and the receipt is an inclusion.  A      *)
  (* client with several load receipts converts the largest.  The         *)
  (* continuation is under a LATER, as [wp_hart_barrier]'s is: a fence IS  *)
  (* a program step.  The kinds that also drain drain here too (the arm   *)
  (* is the machine's, and a release kind waits for the drain); a client   *)
  (* that wants the drain's receipt as well uses [wp_hart_barrier].        *)
  (* ================================================================== *)
  Lemma wp_hart_fence_acq {X : Type} (C : M X -> M unit) (bk : barrier_kind)
      (m : M X) (K : nat) :
    mctx C ->
    hbar_at m = Some bk ->
    fence_acq bk = true ->
    gen_cert -∗ hart_rview_lb_at cpu_id K -∗
    ▷ (hart_view_lb K -∗ WP (HartE gen_id cpu_id (C (hbar_resume m)) : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    iIntros (HC Hproj Hacq) "#Hcert #HK H".
    destruct (hbar_at_inv _ _ Hproj) as (Kc & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.Barrier bk) (fun v => C (Kc v)))
      by (rewrite Hm; exact (HC _ (Interface.Barrier bk) Kc eq_refl)).
    rewrite Hg.
    iLöb as "IH".
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 dl0 tv0 itv0 hr0 r0 m'0 σ'0 log'0 dl'0 tv'0 itv'0 hr'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      destruct Hs as [(_ & _ & _ & _ & _ & _ & _ & _ & -> & ->)
                     |(_ & _ & _ & _ & _ & _ & _ & -> & ->)]; by split. }
    iIntros (σ oth rv img log dl tv itv hr V) "%Htv %Hitv %Hhr Hσ Hiv Hrv Htso".
    set (h := hart_agent cpu_id).
    destruct (decide (fence_rel bk = true /\ ~ own_drained h log dl)) as [Hblk|Hen'].
    - (* blocked: self-loop *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
      iExists (Interface.Next (Interface.Barrier bk) (fun v => C (Kc v))),
        σ, log, dl, tv, itv, hr, rv.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota. left.
        destruct Hblk as [Hrel Hnd]. split_and!; done. }
      iNext. iIntros (m' σ' log' dl' tv' itv' hr' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(_ & _ & -> & -> & -> & -> & -> & -> & -> & ->) | (Hen & _)];
        [|exfalso; destruct Hblk as [Hrel Hnd];
          destruct Hen as [Hen|Hen]; [congruence|exact (Hnd Hen)]].
      iMod "Hclose" as "_". iModIntro. iFrame "Hσ Hiv Hrv".
      iSplitL "Htso".
      { rewrite -Htv. iApply (tso_interp_of_idle with "Htso"). }
      iApply ("IH" with "H").
    - pose proof (barrier_enabled_of_not bk h log dl Hen') as Hen.
      destruct Hhr as (Hrvlen & _).
      iDestruct (tso_interp_of_bound with "Htso") as %Hb.
      assert (Htvlen : (tv <= length dl)%nat) by (rewrite -Htv; apply Hb).
      (* the load's receipt sits under the watermark ... *)
      iDestruct (hart_rview_lb_at_valid with "Hrv HK") as %HKrv.
      set (tvn := fence_post h log dl (fence_drains bk) (fence_acq bk) tv (hr_rv hr)).
      assert (Hadv : (V h <= tvn)%nat).
      { rewrite Htv /tvn. apply fence_post_ge. }
      assert (Htop : (tvn <= length dl)%nat).
      { rewrite /tvn. apply fence_post_le; [exact Htvlen|exact Hrvlen]. }
      (* ... and the watermark under the floor the fence leaves behind *)
      assert (HKtvn : (K <= tvn)%nat).
      { rewrite /tvn Hacq.
        pose proof (fence_post_acq h log dl (fence_drains bk) tv (hr_rv hr)). lia. }
      iMod (tso_interp_of_advance _ img σ.(mem) log dl V h tvn
              (fin_to_nat_lt cpu_id) Hadv Htop with "Htso") as "Htso".
      iDestruct (tso_interp_of_receipt_at riscv_eraGS img σ.(mem) log dl
                   (vstep h tvn dl V) h tvn (vstep_here h tvn dl V)
                   with "Htso") as "[Htso #Hrcpt]".
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
      set (itvn := if fence_ifetch bk
                   then Nat.max itv (fence_post h log dl true false tv (hr_rv hr))
                   else itv).
      iExists (C (Kc tt)), σ, log, dl, tvn, itvn, hr, rv.
      iSplitR.
      { iPureIntro. rewrite /mnode_step. cbn beta iota. right.
        split; [exact Hen|]. by split_and!. }
      iNext. iIntros (m' σ' log' dl' tv' itv' hr' rv') "%Hstep".
      rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
      destruct Hstep as [(Hrel & Hnd & _) | (_ & -> & -> & -> & -> & -> & -> & -> & ->)];
        [exfalso; destruct Hen as [Hen|Hen]; [congruence|exact (Hnd Hen)]|].
      iMod "Hclose" as "_".
      iMod (hart_iview_auth_update cpu_id itv itvn with "Hiv") as "Hiv".
      { rewrite /itvn. case_match; lia. }
      iModIntro.
      iFrame "Hσ Htso Hiv Hrv".
      rewrite -Hres. iApply "H".
      rewrite hart_view_lb_unseal /hart_view_lb_def /view_name /dlen_name.
      iApply (TsoGhost.view_lb_le _ _ _ tvn K HKtvn with "Hrcpt").
  Qed.

  Lemma swp_hart_fence_acq {X : Type} (bk : barrier_kind) (m : M X)
      (Φ : X -> iProp Σ) (K : nat) :
    hbar_at m = Some bk ->
    fence_acq bk = true ->
    gen_cert -∗ hart_rview_lb_at cpu_id K -∗
    ▷ (hart_view_lb K -∗ swp (hbar_resume m) Φ) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hacq) "#Hcert #HK H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_fence_acq C bk m K HC Hproj Hacq with "Hcert HK [H Hcont]").
    iNext. iIntros "HV".
    iApply (swp_use _ Φ C HC with "[H HV] Hcont"). by iApply "H".
  Qed.

End barrier.
