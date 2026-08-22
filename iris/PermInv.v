(* ====================================================================== *)
(* PermInv.v -- THE CRASH-PERMIT CHANNEL: the non-timeless transport that   *)
(* carries a client's logically-atomic write permit from the ENQUEUER to    *)
(* the DMA COMPLETION, and the receipt back.                                *)
(*                                                                          *)
(* (claude-notes/design/fs-log.md stage 4 item 2; the M5b option (a) of      *)
(*  claude-notes/completed/crash.md.)                                       *)
(*                                                                          *)
(* WHY A SECOND INVARIANT EXISTS AT ALL.  The natural home for the permit    *)
(* is the request slot the driver protocol already keys on                   *)
(* ([VirtioProto.slot_pend_res], the [vs_data] precedent).  It cannot go     *)
(* there: [WpUart.disk_inv_body] MUST be [Timeless] -- every driver site     *)
(* that opens it does so from inside an MMIO atomic-update accessor, where   *)
(* there is no step left to absorb a [▷] -- and a permit is a wand over an   *)
(* ARBITRARY [riscv_crash_pred], hence never timeless.  Saved propositions   *)
(* are not timeless either.  So the permit gets a channel of its own, with   *)
(* a TIMELESS ghost SKELETON: what rides the slot is the pure, discrete      *)
(* [perm_tok] (a [ghost_map] element), and the iProp it names lives here.    *)
(*                                                                          *)
(* THE THREE MOMENTS, and the [▷] discipline each one needs:                 *)
(*                                                                          *)
(*  - DEPOSIT ([perm_deposit], the enqueuer).  A plain fupd, no program step *)
(*    needed: the invariant's auth is timeless (so its [▷] strips inside the *)
(*    fupd), and the permit itself is only ADDED under the later             *)
(*    ([▷B ∗ P ⊢ ▷(B ∗ P)]).  The enqueuer never has to USE a permit.        *)
(*  - CONSUMPTION ([perm_consume], the disk thread).  Stated over the        *)
(*    ALREADY-STRIPPED body, because that is what the caller has:            *)
(*    [wp_disk_loop] opens [permN] in [wp_disk_step]'s FIRST (⊤→∅) leg and   *)
(*    the existing between-legs [iNext] strips it.  The permit is applied to *)
(*    the [▷]-BODY of [crash_inv] -- do NOT strip the crash predicate's      *)
(*    later, the permit's type takes it.                                     *)
(*  - COLLECTION ([perm_collect_body] / [perm_collect], the enqueuer after   *)
(*    its wake).  Identification of "which Q is mine" is by saved-prop       *)
(*    agreement, which costs ONE [▷]; opening the invariant costs a second   *)
(*    one unless the caller has a step.  Hence the two forms: the body-level *)
(*    one (a caller that already stripped the invariant, e.g. around a       *)
(*    program step) gets [▷ Q]; the fupd-level one gets [▷ ▷ Q].  Neither is *)
(*    avoidable: transporting an ARBITRARY iProp through a shared invariant  *)
(*    is exactly what a saved proposition costs.                             *)
(* ====================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map invariants saved_prop.
Require Import VirtioModel.   (* [disk_wr]/[wr_apply]: the write identity *)
Require Import RiscvPtsto.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)


Section perm.
  Context `{!riscvFixedGS Σ, !permG Σ}.

  (* ONE in-flight request's cell.  [b = true] is PENDING (the client's
     unspent view shift), [b = false] is DONE (the receipt the completion
     produced, waiting for its enqueuer).  The receipt's identity is pinned
     by the saved proposition at [γq], of which the enqueuer keeps a
     persistent copy ([perm_receipt]) -- that is what lets it recognize its
     own [Q] among everybody else's at collection time. *)
  Definition perm_slot (gd : nat) (b : bool) (γq : gname) (w : disk_wr)
      : iProp Σ :=
    (∃ Q : iProp Σ,
       saved_prop_own γq DfracDiscarded Q ∗
       if b then disk_write_permit gd w Q else Q)%I.

  (* THE CHANNEL IS ERA-LOCAL, AND [gd] IS WHAT SAYS SO.  Every permit an
     era's clients deposit is authored by that era, so the invariant carries
     the generation ONCE rather than per entry -- which is precisely what lets
     the completion discharge the permit's [⌜n = gd + 1⌝] from the live-era
     arithmetic [wp_disk_step] already hands it ([n = gen_id + 1], and the
     disk loop holds the channel at its OWN [gen_id]).  A dead era's channel
     is never opened again -- its device loop corpse-steps -- so its permits
     die unconsumed. *)
  Definition perm_inv_body (gd : nat) (γP : gname) : iProp Σ :=
    (∃ m : gmap nat (bool * gname * disk_wr),
       ghost_map_auth γP 1 m ∗
       [∗ map] k ↦ x ∈ m, perm_slot gd x.1.1 x.1.2 x.2)%I.

  (* Disjoint from [crashN] (= [nroot .@ "crash"]) and from every
     [devN]-derived namespace, so the completion can hold all three open. *)
  Definition permN : namespace := nroot .@ "permit".

  Definition perm_inv (gd : nat) (γP : gname) : iProp Σ :=
    inv permN (perm_inv_body gd γP).

  Global Instance perm_inv_persistent gd γP : Persistent (perm_inv gd γP).
  Proof. rewrite /perm_inv. apply _. Qed.

  (* THE TIMELESS SKELETON: this is what a request slot stores.  It is a
     [ghost_map] element -- pure, discrete, timeless -- so it rides
     [disk_inv] with no [▷] cost at all, which is the whole point of the
     split.  Holding it against the invariant's auth PINS the cell's state,
     which is how the completion knows the permit is still unspent. *)
  Definition perm_tok (γP : gname) (k : nat) (b : bool) (γq : gname)
      (w : disk_wr) : iProp Σ :=
    (k ↪[γP] (b, γq, w))%I.

  Global Instance perm_tok_timeless γP k b γq w : Timeless (perm_tok γP k b γq w).
  Proof. rewrite /perm_tok. apply _. Qed.

  (* the enqueuer's persistent handle on its own receipt *)
  Definition perm_receipt (γq : gname) (Q : iProp Σ) : iProp Σ :=
    saved_prop_own γq DfracDiscarded Q.

  Global Instance perm_receipt_persistent γq Q : Persistent (perm_receipt γq Q).
  Proof. rewrite /perm_receipt. apply _. Qed.

  (* two tokens for the same key cannot both exist: the element is exclusive *)
  Lemma perm_tok_excl γP k b1 b2 γq1 γq2 w1 w2 :
    perm_tok γP k b1 γq1 w1 -∗ perm_tok γP k b2 γq2 w2 -∗ False.
  Proof.
    rewrite /perm_tok. iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne. done.
  Qed.

  (* ==================================================================== *)
  (* allocation                                                           *)
  (* ==================================================================== *)

  (* the empty channel, as the body an [inv_alloc] consumes.  Nothing is in
     flight at power-on, so the map is empty and no permit is owed. *)
  Lemma perm_ghost_alloc (gd : nat) : ⊢ |==> ∃ γP : gname, perm_inv_body gd γP.
  Proof.
    iMod (ghost_map_alloc (∅ : gmap nat (bool * gname * disk_wr)))
      as (γP) "[Hauth _]".
    iModIntro. iExists γP. rewrite /perm_inv_body.
    iExists ∅. iFrame "Hauth". by rewrite big_sepM_empty.
  Qed.

  Lemma perm_inv_alloc E gd γP : perm_inv_body gd γP ={E}=∗ perm_inv gd γP.
  Proof. iIntros "Hbody". rewrite /perm_inv. by iApply inv_alloc. Qed.

  (* ==================================================================== *)
  (* 1. DEPOSIT -- the enqueuer, in a plain fupd (no program step)         *)
  (* ==================================================================== *)

  (* The client hands in its view shift and gets back the TIMELESS token to
     park in the request's slot, plus the persistent receipt handle it will
     present at collection.  The key [k] is chosen fresh HERE (the invariant
     is the only thing that knows which keys are taken), which is why the
     caller receives it rather than supplying it -- and why nothing in this
     file has to know that the caller's requests are queue positions. *)
  Lemma perm_deposit (gd : nat) (γP : gname) (w : disk_wr) (Q : iProp Σ)
      (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗ disk_write_permit gd w Q ={E}=∗
      ∃ (k : nat) (γq : gname), perm_tok γP k true γq w ∗ perm_receipt γq Q.
  Proof.
    iIntros (HE) "#Hinv Hperm".
    iMod (saved_prop_alloc Q DfracDiscarded) as (γq) "#Hsp"; [done|].
    iInv "Hinv" as "Hbody" "Hclose".
    (* the body is under a [▷]; the AUTH is timeless, so it strips inside
       this fupd, and the entries stay under the later -- which is all we
       need, because a deposit only ever ADDS to them. *)
    iDestruct "Hbody" as (m) "Hbody".
    iDestruct "Hbody" as "[Hauth Hents]".
    iMod "Hauth".
    set (k := fresh (dom m)).
    assert (Hk : m !! k = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (ghost_map_insert k (true, γq, w) Hk with "Hauth") as "[Hauth Htok]".
    iMod ("Hclose" with "[Hauth Hents Hperm]") as "_".
    { iNext. rewrite /perm_inv_body. iExists (<[k := (true, γq, w)]> m).
      iFrame "Hauth".
      rewrite (big_sepM_insert (fun k x => perm_slot gd x.1.1 x.1.2 x.2) m k
                 (true, γq, w) Hk).
      iSplitR "Hents"; [| iExact "Hents"].
      rewrite /perm_slot /=. iExists Q. iFrame "Hsp Hperm". }
    iModIntro. iExists k, γq. iFrame "Htok Hsp".
  Qed.

  (* ==================================================================== *)
  (* 2. CONSUMPTION -- the DMA completion, over the STRIPPED body          *)
  (* ==================================================================== *)

  (* THE LINEARIZATION POINT.  Stated over [perm_inv_body] rather than
     [perm_inv] on purpose: [wp_disk_loop] opens [permN] in [wp_disk_step]'s
     first (⊤→∅) leg, so by the time it knows which request completed the
     body's [▷] is already gone (the between-legs [iNext]).  The crash
     predicate arrives and leaves UNDER its own later -- that is [crash_inv]'s
     own shape and the permit's type; nothing here strips it.

     The token in hand is what refutes the done arm: the element is
     exclusive and the auth pins its value, so [b = true] and the permit is
     provably unspent. *)
  Lemma perm_consume (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (dk : Z -> bv 8) (n : nat) :
    perm_inv_body gd γP -∗ perm_tok γP k true γq w -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_tok γP k false γq w ∗ start_auth n ∗
      disk_fixed_auth (wr_apply w dk) ∗
      ▷ riscv_crash_pred.
  Proof.
    iIntros "Hbody Htok Hsa %Hn Ha HP". rewrite {1}/perm_inv_body.
    iDestruct "Hbody" as (m) "[Hauth Hents]".
    rewrite /perm_tok.
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iDestruct (big_sepM_delete (fun k x => perm_slot gd x.1.1 x.1.2 x.2) m k
                 (true, γq, w) Hk with "Hents") as "[Hent Hents]".
    rewrite /perm_slot /=.
    iDestruct "Hent" as (Q) "[#Hsp Hpm]".
    (* THE CLIENT'S VIEW SHIFT RUNS HERE, at the image the completion is
       moving the machine FROM.  The index move is the whole content of the
       reshaped permit: [w] is this request's write identity, pinned to the
       slot by [VirtioProto.slot_pend_res]. *)
    iMod ("Hpm" $! dk n with "Hsa [//] Ha HP") as "(Ha & HP & Hsa & HQ)".
    iMod (ghost_map_update (false, γq, w) with "Hauth Htok") as "[Hauth Htok]".
    iModIntro. iFrame "Htok Hsa Ha HP". rewrite /perm_inv_body.
    iExists (<[k := (false, γq, w)]> m). iFrame "Hauth".
    rewrite (big_sepM_insert_delete (fun k x => perm_slot gd x.1.1 x.1.2 x.2)
               m k (false, γq, w)).
    iSplitR "Hents"; [| iExact "Hents"].
    rewrite /perm_slot /=. iExists Q. iFrame "Hsp HQ".
  Qed.

  (* THE SEAM SHAPE [wp_disk_loop] consumes, in the PAIR form the request
     slots store ([VirtioQueue.vs_perm]).  Permits are UNIFORM: every
     published request carries one, an OUT request the client's real one and
     an IN request the trivial identity.  That is what lets the disk thread
     stay direction-agnostic -- it opens [permN] in [wp_disk_step]'s FIRST
     leg without knowing which request will complete, learns the pair from
     [virtio_proto_step], and runs ONE lemma either way.  (The recorded
     gotcha, verbatim: the caller does not know the direction -- the
     completing slot is chosen inside the protocol lemma.) *)
  Definition perm_pend (γP : gname) (kq : nat * gname) (w : disk_wr)
      : iProp Σ := perm_tok γP kq.1 true kq.2 w.

  Definition perm_done (γP : gname) (kq : nat * gname) (w : disk_wr)
      : iProp Σ := perm_tok γP kq.1 false kq.2 w.

  Global Instance perm_pend_timeless γP kq w : Timeless (perm_pend γP kq w).
  Proof. rewrite /perm_pend. apply _. Qed.
  Global Instance perm_done_timeless γP kq w : Timeless (perm_done γP kq w).
  Proof. rewrite /perm_done. apply _. Qed.

  Lemma perm_consume_kq (gd : nat) (γP : gname) (kq : nat * gname)
      (w : disk_wr) (dk : Z -> bv 8) (n : nat) :
    perm_inv_body gd γP -∗ perm_pend γP kq w -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_done γP kq w ∗ start_auth n ∗
      disk_fixed_auth (wr_apply w dk) ∗
      ▷ riscv_crash_pred.
  Proof.
    iIntros "Hbody Hpend Hsa %Hn Ha HP". rewrite /perm_pend /perm_done.
    iMod (perm_consume with "Hbody Hpend Hsa [//] Ha HP")
      as "(Hbody & Htok & Hsa & Ha & HP)".
    iModIntro. iFrame "Hbody Htok Hsa Ha HP".
  Qed.

  (* the pair form of the deposit: what an enqueuer calls, returning exactly
     the [vs_perm] it must publish in its slot *)
  Lemma perm_deposit_kq (gd : nat) (γP : gname) (w : disk_wr) (Q : iProp Σ)
      (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗ disk_write_permit gd w Q ={E}=∗
      ∃ kq : nat * gname, perm_pend γP kq w ∗ perm_receipt kq.2 Q.
  Proof.
    iIntros (HE) "#Hinv Hperm".
    iMod (perm_deposit gd γP w Q E HE with "Hinv Hperm") as (k γq) "[Htok #Hrc]".
    iModIntro. iExists (k, γq). rewrite /perm_pend /=. iFrame "Htok Hrc".
  Qed.

  (* ==================================================================== *)
  (* 3. COLLECTION -- the enqueuer, after its wake                         *)
  (* ==================================================================== *)

  (* Over the stripped body (a caller with a program step to spare): ONE
     later, and it is the saved-prop agreement's, not the invariant's. *)
  Lemma perm_collect_body (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (Q : iProp Σ) :
    perm_inv_body gd γP -∗ perm_receipt γq Q -∗ perm_tok γP k false γq w ==∗
      perm_inv_body gd γP ∗ ▷ Q.
  Proof.
    iIntros "Hbody #Hrc Htok". rewrite {1}/perm_inv_body /perm_tok /perm_receipt.
    iDestruct "Hbody" as (m) "[Hauth Hents]".
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iDestruct (big_sepM_delete (fun k x => perm_slot gd x.1.1 x.1.2 x.2) m k
                 (false, γq, w) Hk with "Hents") as "[Hent Hents]".
    rewrite /perm_slot /=.
    iDestruct "Hent" as (Q') "[#Hsp HQ]".
    iDestruct (saved_prop_agree γq DfracDiscarded DfracDiscarded Q' Q
                 with "Hsp Hrc") as "#Heq".
    iMod (ghost_map_delete with "Hauth Htok") as "Hauth".
    iModIntro. iSplitR "HQ".
    { rewrite /perm_inv_body. iExists (delete k m). iFrame "Hauth Hents". }
    iNext. iRewrite -"Heq". iExact "HQ".
  Qed.

  (* Over the invariant, in a plain fupd (no program step): TWO laters --
     the invariant's own, and the agreement's.  A caller with a step to
     spare should use [perm_collect_body] instead. *)
  Lemma perm_collect (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (Q : iProp Σ) (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗ perm_receipt γq Q -∗ perm_tok γP k false γq w ={E}=∗
      ▷ ▷ Q.
  Proof.
    iIntros (HE) "#Hinv #Hrc Htok".
    iInv "Hinv" as "Hbody" "Hclose".
    rewrite /perm_inv_body /perm_tok /perm_receipt.
    iDestruct "Hbody" as (m) "Hbody".
    iDestruct "Hbody" as "[Hauth Hents]".
    iMod "Hauth".
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iEval (rewrite big_sepM_later) in "Hents".
    iDestruct (big_sepM_delete (fun k x => ▷ perm_slot gd x.1.1 x.1.2 x.2)%I
                 m k (false, γq, w) Hk with "Hents") as "[Hent Hents]".
    iMod (ghost_map_delete with "Hauth Htok") as "Hauth".
    iEval (rewrite -big_sepM_later) in "Hents".
    iMod ("Hclose" with "[Hauth Hents]") as "_".
    { iNext. iExists (delete k m). iFrame "Hauth Hents". }
    rewrite /perm_slot /=.
    iDestruct "Hent" as (Q') "[#Hsp HQ]".
    iAssert (▷ ▷ (Q' ≡ Q))%I as "#Heq".
    { iNext. iApply (saved_prop_agree γq DfracDiscarded DfracDiscarded Q' Q
                       with "Hsp Hrc"). }
    iModIntro. iNext. iNext. iRewrite -"Heq". iExact "HQ".
  Qed.

  (* the pair form of the collection: what a woken enqueuer calls, over the
     [vs_perm] its own claim pinned *)
  Lemma perm_collect_kq (gd : nat) (γP : gname) (kq : nat * gname)
      (w : disk_wr) (Q : iProp Σ) :
    perm_inv_body gd γP -∗ perm_receipt kq.2 Q -∗ perm_done γP kq w ==∗
      perm_inv_body gd γP ∗ ▷ Q.
  Proof.
    iIntros "Hbody #Hrc Htok". rewrite /perm_done.
    iApply (perm_collect_body with "Hbody Hrc Htok").
  Qed.

  (* ==================================================================== *)
  (* 4. THE SECTOR VECTOR (claude-notes/projects/sector-atomic-disk.md)    *)
  (*                                                                      *)
  (*    A 512-byte sector lands atomically and a 1024-byte block does not, *)
  (*    so ONE write request has one linearization point per sector and    *)
  (*    therefore one permit per sector.  Nothing about the channel        *)
  (*    changes -- [perm_deposit_kq]/[perm_consume_kq]/[perm_collect_kq]   *)
  (*    are already per key -- these are just the vector forms the driver  *)
  (*    calls once per request instead of once per sector.                 *)
  (* ==================================================================== *)

  Lemma perm_deposit_seq (gd : nat) (γP : gname) (f : nat -> disk_wr)
      (Qs : nat -> iProp Σ) (n : nat) (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗
    ([∗ list] i ∈ seq 0 n, disk_write_permit gd (f i) (Qs i)) ={E}=∗
      ∃ ks : list (nat * gname),
        ⌜length ks = n⌝ ∗
        ([∗ list] i ↦ kq ∈ ks, perm_pend γP kq (f i)) ∗
        ([∗ list] i ↦ kq ∈ ks, perm_receipt kq.2 (Qs i)).
  Proof.
    iIntros (HE) "#Hinv Hps".
    iInduction n as [|n IH] "IH".
    - iModIntro. iExists []. cbn. by iFrame.
    - rewrite seq_S Nat.add_0_l big_sepL_app big_sepL_singleton.
      iDestruct "Hps" as "[Hps Hlast]".
      iMod ("IH" with "Hps") as (ks) "(%Hlen & Hpend & Hrc)".
      iMod (perm_deposit_kq gd γP (f n) (Qs n) E HE with "Hinv Hlast")
        as (kq) "[Hpend0 Hrc0]".
      iModIntro. iExists (ks ++ [kq]).
      rewrite !big_sepL_snoc length_app Hlen.
      iSplitR; [iPureIntro; cbn [length]; lia|].
      iFrame "Hpend Hrc Hpend0 Hrc0".
  Qed.

  (* what an enqueuer calls ONCE, on the permits its caller supplied: the
     keys come back as a list in sector order, which is exactly what the
     published slot records ([VirtioQueue.vs_perms]). *)
  Lemma perm_deposit_sectors (gd : nat) (γP : gname) (w : disk_wr)
      (Qs : nat -> iProp Σ) (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗ disk_sector_permits gd w Qs ={E}=∗
      ∃ ks : list (nat * gname),
        ⌜length ks = wr_nsectors w⌝ ∗
        ([∗ list] i ↦ kq ∈ ks, perm_pend γP kq (wr_sector w i)) ∗
        ([∗ list] i ↦ kq ∈ ks, perm_receipt kq.2 (Qs i)).
  Proof.
    iIntros (HE) "#Hinv Hps". rewrite /disk_sector_permits.
    iApply (perm_deposit_seq gd γP (wr_sector w) Qs (wr_nsectors w) E HE
              with "Hinv Hps").
  Qed.

  (* ...and what the woken enqueuer calls once, on the receipts it recorded *)
  Lemma perm_collect_list (gd : nat) (γP : gname) (ks : list (nat * gname))
      (ws : nat -> disk_wr) (Qs : nat -> iProp Σ) :
    perm_inv_body gd γP -∗
    ([∗ list] i ↦ kq ∈ ks, perm_receipt kq.2 (Qs i)) -∗
    ([∗ list] i ↦ kq ∈ ks, perm_done γP kq (ws i)) ==∗
      perm_inv_body gd γP ∗ ▷ ([∗ list] i ↦ kq ∈ ks, Qs i).
  Proof.
    iIntros "Hbody Hrc Hdone".
    iInduction ks as [|k ks IH] "IH" forall (Qs ws).
    - iModIntro. iFrame "Hbody". by iNext.
    - rewrite !big_sepL_cons.
      iDestruct "Hrc" as "[Hrc0 Hrc]". iDestruct "Hdone" as "[Hd0 Hd]".
      iMod (perm_collect_kq gd γP k (ws 0%nat) (Qs 0%nat)
              with "Hbody Hrc0 Hd0") as "[Hbody HQ0]".
      iMod ("IH" $! (fun i => Qs (S i)) (fun i => ws (S i))
              with "Hbody Hrc Hd") as "[Hbody HQ]".
      iModIntro. iFrame "Hbody". iNext. iFrame "HQ0 HQ".
  Qed.

  (* the same, over the INVARIANT: two laters (the invariant's own and the
     saved-proposition agreement's), exactly like [perm_collect], one opening
     per key.  This is what the woken publisher calls on the sector receipts
     its claim pinned. *)
  Lemma perm_collect_list_inv (gd : nat) (γP : gname) (ks : list (nat * gname))
      (ws : nat -> disk_wr) (Qs : nat -> iProp Σ) (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗
    ([∗ list] i ↦ k ∈ ks, perm_receipt k.2 (Qs i)) -∗
    ([∗ list] i ↦ k ∈ ks, perm_done γP k (ws i)) ={E}=∗
      ▷ ▷ ([∗ list] i ↦ k ∈ ks, Qs i).
  Proof.
    iIntros (HE) "#Hinv Hrc Hdone".
    iInduction ks as [|k ks IH] "IH" forall (Qs ws).
    - iModIntro. by iNext.
    - rewrite !big_sepL_cons.
      iDestruct "Hrc" as "[Hrc0 Hrc]". iDestruct "Hdone" as "[Hd0 Hd]".
      iMod (perm_collect gd γP k.1 k.2 (ws 0%nat) (Qs 0%nat) E HE
              with "Hinv Hrc0 Hd0") as "HQ0".
      iMod ("IH" $! (fun i => Qs (S i)) (fun i => ws (S i))
              with "Hrc Hd") as "HQ".
      iModIntro. iNext. iNext. iFrame "HQ0 HQ".
  Qed.

End perm.
