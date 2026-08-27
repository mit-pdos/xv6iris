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
   Ztso [fence_post] takes the view to [max tv (own_pub h log)] -- the
   author's OWN last message -- so the client gets
   [own_pub h glog <= gtv cpu_id], not [length glog <= gtv cpu_id].  That is
   weaker and it is enough: what a publisher must show of a byte is that its
   timestamp is under the bound, and a byte in the publisher's own context is
   either clean under the token's bound or its own message
   ([TsoGhost.dirty_ok]'s two arms are exactly [visibleb]'s).  Requiring the
   log top would have needed [TsoMemPa.all_own] -- a fact about OTHER agents
   that no client can hold -- and A6.4's boot bracket is not needed here. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartEvents.
Require Import TsoMemPa TsoGhost.
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
  (* §2 THE CLIENT'S OBLIGATION.  A ghost step against the live interp,   *)
  (* at the machine state the fence leaves behind and at THIS hart's      *)
  (* drained view, with the view's receipt already in hand.  Named        *)
  (* because it is the whole client-visible surface of the leaf: nothing  *)
  (* below [gstate] leaks, and a client that wants nothing writes         *)
  (* [pub_step_id].                                                       *)
  (* ------------------------------------------------------------------ *)
  Definition pub_step (P Q : iProp Σ) : iProp Σ :=
    (∀ g : gstate,
       ⌜(own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat⌝ -∗
       hart_view_lb (g.(gtv) cpu_id) -∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
       tso_interp_at riscv_eraGS g -∗ P ==∗
       gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
       tso_interp_at riscv_eraGS g ∗ Q)%I.

  (* the trivial one: a fence that publishes nothing still drains *)
  Lemma pub_step_id (P : iProp Σ) : ⊢ pub_step P P.
  Proof. iIntros (g) "_ _ $ $ $". done. Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE LEAF, at the WP over a context.                               *)
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
    destruct (hbar_at_inv _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.Barrier bk) (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.Barrier bk) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    { intros oth0 h0 img0 σ0 log0 tv0 r0 m'0 σ'0 log'0 tv'0 r'0 Hs.
      rewrite /mnode_step in Hs. cbn beta iota in Hs.
      by destruct Hs as (_ & _ & _ & _ & ->). }
    iIntros (σ oth rv img log tv V) "%Htv Hσ Htso".
    iDestruct (tso_interp_of_bound with "Htso") as %Hb.
    iDestruct (tso_interp_of_pin with "Htso") as %Hpin.
    assert (Htvlen : (tv <= length log)%nat) by (rewrite -Htv; apply Hb).
    (* the drained view, and the two bounds it satisfies *)
    set (h := hart_agent cpu_id).
    set (tvn := fence_post h log (fence_drains bk) tv).
    assert (Hadv : (V h <= tvn)%nat).
    { rewrite Htv /tvn /fence_post Hdrain. lia. }
    assert (Htop : (tvn <= length log)%nat).
    { rewrite /tvn /fence_post Hdrain.
      pose proof (own_pub_le h log). lia. }
    assert (Hown : (own_pub h log <= tvn)%nat)
      by (rewrite /tvn /fence_post Hdrain; lia).
    iMod (tso_interp_of_advance _ img σ.(mem) log V h tvn
            (fin_to_nat_lt cpu_id) Hadv Htop with "Htso") as "Htso".
    iDestruct (tso_interp_of_receipt_at riscv_eraGS img σ.(mem) log
                 (vstep h tvn log V) h tvn (vstep_here h tvn log V)
                 with "Htso") as "[Htso #Hrcpt]".
    (* the bundle, re-read as a [gstate] fact -- A6.1a's bridge, the same
       one [HartMStore.wobl_ram_ledger] pays in both directions *)
    assert (Hpin' : forall h', (NCPU <= h')%nat -> vstep h tvn log V h' = length log).
    { intros h' Hh'. rewrite /vstep. case_decide as Hd.
      - exfalso. subst h'. rewrite /h /hart_agent in Hh'.
        pose proof (fin_to_nat_lt cpu_id). lia.
      - destruct (lt_dec h' NCPU); [lia | reflexivity]. }
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    rewrite (tso_interp_of_at_gs riscv_eraGS img σ.(mem) log (vstep h tvn log V)
               σ.(sregs) σ.(mdev) Hpin').
    iMod ("Hpub" $! (gs_of img σ.(mem) log (vstep h tvn log V)
                       σ.(sregs) σ.(mdev))
            with "[%] [] Hmem Htso HP") as "(Hmem & Htso & HQ)".
    { cbn [glog gtv gs_of]. rewrite vstep_here. exact Hown. }
    { cbn [gtv gs_of]. rewrite vstep_here.
      rewrite hart_view_lb_unseal /hart_view_lb_def /view_name /loglen_name.
      iExact "Hrcpt". }
    rewrite -(tso_interp_of_at_gs riscv_eraGS img σ.(mem) log
                (vstep h tvn log V) σ.(sregs) σ.(mdev) Hpin').
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iExists (C (K tt)), σ, log, tvn, rv.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota. by split_and!. }
    iNext. iIntros (m' σ' log' tv' rv') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (-> & -> & -> & -> & ->).
    iMod "Hclose" as "_". iModIntro.
    iFrame "Hri Hmem Hdev Htso".
    rewrite -Hres. iApply ("H" with "HQ").
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

End barrier.
