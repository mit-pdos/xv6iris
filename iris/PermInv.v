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
(* THE FOUR MOMENTS, and the [▷] discipline each one needs.  (The middle    *)
(* one is new with the SEQUENTIAL permit, sector-atomic-disk.md §6e: a      *)
(* request's obligation unfolds one 512-byte sector at a time, so between   *)
(* the deposit and the completion the cell is spent and RE-DEPOSITED once   *)
(* per landing, at the same key, re-indexed at the sectors still to go.)    *)
(*                                                                          *)
(*  - DEPOSIT ([perm_deposit], the enqueuer).  A plain fupd, no program step *)
(*    needed: the invariant's auth is timeless (so its [▷] strips inside the *)
(*    fupd), and the permit itself is only ADDED under the later             *)
(*    ([▷B ∗ P ⊢ ▷(B ∗ P)]).  The enqueuer never has to USE a permit.        *)
(*  - SECTOR LANDING ([perm_step], the disk thread).  Exactly the           *)
(*    consumption discipline below, but the cell stays PENDING: the branch  *)
(*    the device took is spent and its receipt -- the RESIDUAL obligation   *)
(*    for the remaining sectors -- goes straight back in.  This is the      *)
(*    only moment the durable image moves.                                  *)
(*  - CONSUMPTION ([perm_consume], the disk thread, at the LEAF).  Stated over the *)
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
     unspent obligation), [b = false] is DONE (the receipt the completion
     produced, waiting for its enqueuer).  The receipt's identity is pinned
     by the saved proposition at [γq], of which the enqueuer keeps a
     persistent copy ([perm_receipt]) -- that is what lets it recognize its
     own [Q] among everybody else's at collection time.

     THE PENDING SIDE IS THE SEQUENTIAL PERMIT (sector-atomic-disk.md §6e),
     not a single view shift: a request's data reaches the disk one 512-byte
     SECTOR at a time, so the cell holds [RiscvPtsto.sperm] at the sectors
     STILL TO LAND.  Each landing spends one branch and RE-DEPOSITS the
     residual at the same key ([perm_step]); when nothing is left the cell
     holds the leaf -- the completion's identity permit -- and [perm_consume]
     spends it for [Q].  A READ is at the leaf from the start
     ([wr_nsectors None = 0]), so the read side of the driver is unchanged. *)
  Definition perm_slot (gd : nat) (b : bool) (γq : gname) (w : disk_wr)
      (todo : gset nat) : iProp Σ :=
    (∃ Q : iProp Σ,
       saved_prop_own γq DfracDiscarded Q ∗
       if b then sperm gd w todo Q else Q)%I.

  (* THE CHANNEL IS ERA-LOCAL, AND [gd] IS WHAT SAYS SO.  Every permit an
     era's clients deposit is authored by that era, so the invariant carries
     the generation ONCE rather than per entry -- which is precisely what lets
     the completion discharge the permit's [⌜n = gd + 1⌝] from the live-era
     arithmetic [wp_disk_step] already hands it ([n = gen_id + 1], and the
     disk loop holds the channel at its OWN [gen_id]).  A dead era's channel
     is never opened again -- its device loop corpse-steps -- so its permits
     die unconsumed. *)
  Definition perm_inv_body (gd : nat) (γP : gname) : iProp Σ :=
    (∃ m : gmap nat (bool * gname * (disk_wr * gset nat)),
       ghost_map_auth γP 1 m ∗
       [∗ map] k ↦ x ∈ m, perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2)%I.

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
     which is how the completion knows how far the request has got: the
     [todo] component IS the request's remaining sectors. *)
  Definition perm_tok (γP : gname) (k : nat) (b : bool) (γq : gname)
      (w : disk_wr) (todo : gset nat) : iProp Σ :=
    (k ↪[γP] (b, γq, (w, todo)))%I.

  Global Instance perm_tok_timeless γP k b γq w todo :
    Timeless (perm_tok γP k b γq w todo).
  Proof. rewrite /perm_tok. apply _. Qed.

  (* the enqueuer's persistent handle on its own receipt *)
  Definition perm_receipt (γq : gname) (Q : iProp Σ) : iProp Σ :=
    saved_prop_own γq DfracDiscarded Q.

  Global Instance perm_receipt_persistent γq Q : Persistent (perm_receipt γq Q).
  Proof. rewrite /perm_receipt. apply _. Qed.

  (* two tokens for the same key cannot both exist: the element is exclusive *)
  Lemma perm_tok_excl γP k b1 b2 γq1 γq2 w1 w2 t1 t2 :
    perm_tok γP k b1 γq1 w1 t1 -∗ perm_tok γP k b2 γq2 w2 t2 -∗ False.
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
    iMod (ghost_map_alloc (∅ : gmap nat (bool * gname * (disk_wr * gset nat))))
      as (γP) "[Hauth _]".
    iModIntro. iExists γP. rewrite /perm_inv_body.
    iExists ∅. iFrame "Hauth". by rewrite big_sepM_empty.
  Qed.

  Lemma perm_inv_alloc E gd γP : perm_inv_body gd γP ={E}=∗ perm_inv gd γP.
  Proof. iIntros "Hbody". rewrite /perm_inv. by iApply inv_alloc. Qed.

  (* ==================================================================== *)
  (* 1. DEPOSIT -- the enqueuer, in a plain fupd (no program step)         *)
  (* ==================================================================== *)

  (* The client hands in its whole SEQUENTIAL obligation and gets back the
     TIMELESS token to park in the request's slot, plus the persistent
     receipt handle it will present at collection.  The key [k] is chosen
     fresh HERE (the invariant is the only thing that knows which keys are
     taken), which is why the caller receives it rather than supplying it --
     and why nothing in this file has to know that the caller's requests are
     queue positions. *)
  Lemma perm_deposit (gd : nat) (γP : gname) (w : disk_wr) (Q : iProp Σ)
      (E : coPset) :
    ↑permN ⊆ E ->
    perm_inv gd γP -∗ disk_seq_permit gd w Q ={E}=∗
      ∃ (k : nat) (γq : gname),
        perm_tok γP k true γq w (set_seq 0 (wr_nsectors w)) ∗
        perm_receipt γq Q.
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
    iMod (ghost_map_insert k
            (true, γq, (w, set_seq (C := gset nat) 0 (wr_nsectors w))) Hk
            with "Hauth") as "[Hauth Htok]".
    iMod ("Hclose" with "[Hauth Hents Hperm]") as "_".
    { iNext. rewrite /perm_inv_body.
      iExists (<[k := (true, γq,
                       (w, set_seq (C := gset nat) 0 (wr_nsectors w)))]> m).
      iFrame "Hauth".
      rewrite (big_sepM_insert
                 (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2) m k
                 (true, γq, (w, set_seq (C := gset nat) 0 (wr_nsectors w)))
                 Hk).
      iSplitR "Hents"; [| iExact "Hents"].
      rewrite /perm_slot /=. iExists Q. iFrame "Hsp".
      rewrite /disk_seq_permit. iExact "Hperm". }
    iModIntro. iExists k, γq. iFrame "Htok Hsp".
  Qed.

  (* ==================================================================== *)
  (* 2. THE SECTOR LANDING -- consume one branch, RE-DEPOSIT the residual   *)
  (* ==================================================================== *)

  (* THE LINEARIZATION POINT OF A DISK WRITE.  Stated over [perm_inv_body]
     rather than [perm_inv] on purpose: [wp_disk_loop] opens [permN] in
     [wp_disk_step]'s first (⊤→∅) leg, so by the time it knows which sector
     landed the body's [▷] is already gone (the between-legs [iNext]).  The
     crash predicate arrives and leaves UNDER its own later -- that is
     [crash_inv]'s own shape and the permit's type; nothing here strips it.

     The cell does NOT move to the done state: it stays PENDING at the
     residual obligation, re-indexed at the sectors that are still to land.
     That is the whole content of the sequential design -- whatever a later
     sector needs (the client's mirror half, what an earlier sector learned)
     travels inside the residual, which no independent per-sector permit
     could have carried. *)
  Lemma perm_step (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (todo : gset nat) (i : nat)
      (dk : Z -> bv 8) (n : nat) :
    i ∈ todo ->
    perm_inv_body gd γP -∗ perm_tok γP k true γq w todo -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_tok γP k true γq w (todo ∖ {[ i ]}) ∗
      start_auth n ∗
      disk_fixed_auth (wr_apply (wr_sector w i) dk) ∗
      ▷ riscv_crash_pred.
  Proof.
    iIntros (Hi) "Hbody Htok Hsa %Hn Ha HP". rewrite {1}/perm_inv_body.
    iDestruct "Hbody" as (m) "[Hauth Hents]".
    rewrite /perm_tok.
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iDestruct (big_sepM_delete
                 (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2) m k
                 (true, γq, (w, todo)) Hk with "Hents") as "[Hent Hents]".
    rewrite /perm_slot /=.
    iDestruct "Hent" as (Q) "[#Hsp Hpm]".
    (* the obligation still has sectors outstanding, so it is the conjunction
       over them; the device picked branch [i]. *)
    assert (Hne : todo ≠ ∅).
    { intro Hc. rewrite Hc in Hi. by apply (elem_of_empty (C := gset nat) i). }
    rewrite (sperm_cons gd w todo Q Hne).
    iSpecialize ("Hpm" $! i with "[//]").
    (* THE CLIENT'S VIEW SHIFT RUNS HERE, at the image the landing is moving
       the machine FROM, and the index is this SECTOR's own slice. *)
    iMod ("Hpm" $! dk n with "Hsa [//] Ha HP") as "(Ha & HP & Hsa & Hres)".
    iMod (ghost_map_update (true, γq, (w, todo ∖ {[ i ]})) with "Hauth Htok")
      as "[Hauth Htok]".
    iModIntro. iFrame "Htok Hsa Ha HP". rewrite /perm_inv_body.
    iExists (<[k := (true, γq, (w, todo ∖ {[ i ]}))]> m). iFrame "Hauth".
    rewrite (big_sepM_insert_delete
               (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2)
               m k (true, γq, (w, todo ∖ {[ i ]}))).
    iSplitR "Hents"; [| iExact "Hents"].
    rewrite /perm_slot /=. iExists Q. iFrame "Hsp Hres".
  Qed.

  (* ==================================================================== *)
  (* 3. CONSUMPTION -- the DMA completion, at the LEAF                     *)
  (* ==================================================================== *)

  (* Every sector has landed, so the cell holds the leaf: the completion's
     own identity permit ([wr_apply None dk = dk] -- the completion writes
     the used ring, the status byte and the interrupt, and moves no disk
     byte).  Spending it produces the client's receipt and puts the cell in
     the done state for collection. *)
  Lemma perm_consume (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (dk : Z -> bv 8) (n : nat) :
    perm_inv_body gd γP -∗ perm_tok γP k true γq w ∅ -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_tok γP k false γq w ∅ ∗ start_auth n ∗
      disk_fixed_auth (wr_apply None dk) ∗
      ▷ riscv_crash_pred.
  Proof.
    iIntros "Hbody Htok Hsa %Hn Ha HP". rewrite {1}/perm_inv_body.
    iDestruct "Hbody" as (m) "[Hauth Hents]".
    rewrite /perm_tok.
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iDestruct (big_sepM_delete
                 (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2) m k
                 (true, γq, (w, ∅)) Hk with "Hents") as "[Hent Hents]".
    rewrite /perm_slot /=.
    iDestruct "Hent" as (Q) "[#Hsp Hpm]".
    rewrite sperm_nil.
    iMod ("Hpm" $! dk n with "Hsa [//] Ha HP") as "(Ha & HP & Hsa & HQ)".
    iMod (ghost_map_update (false, γq, (w, (∅ : gset nat)))
            with "Hauth Htok") as "[Hauth Htok]".
    iModIntro. iFrame "Htok Hsa Ha HP". rewrite /perm_inv_body.
    iExists (<[k := (false, γq, (w, (∅ : gset nat)))]> m). iFrame "Hauth".
    rewrite (big_sepM_insert_delete
               (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2)
               m k (false, γq, (w, (∅ : gset nat)))).
    iSplitR "Hents"; [| iExact "Hents"].
    rewrite /perm_slot /=. iExists Q. iFrame "Hsp HQ".
  Qed.

  (* THE SEAM SHAPE [wp_disk_loop] consumes, in the PAIR form the request
     slots store ([VirtioQueue.vs_perm]).  Permits are UNIFORM: every
     published request carries exactly one channel entry, an OUT request's
     re-indexed at each landing and an IN request's at the leaf from the
     start.  That is what lets the disk thread stay direction-agnostic -- it
     opens [permN] in [wp_disk_step]'s FIRST leg without knowing which
     request will complete, learns the pair from the protocol, and runs ONE
     lemma either way. *)
  Definition perm_pend (γP : gname) (kq : nat * gname) (w : disk_wr)
      (todo : gset nat) : iProp Σ := perm_tok γP kq.1 true kq.2 w todo.

  Definition perm_done (γP : gname) (kq : nat * gname) (w : disk_wr)
      : iProp Σ := perm_tok γP kq.1 false kq.2 w ∅.

  Global Instance perm_pend_timeless γP kq w todo :
    Timeless (perm_pend γP kq w todo).
  Proof. rewrite /perm_pend. apply _. Qed.
  Global Instance perm_done_timeless γP kq w : Timeless (perm_done γP kq w).
  Proof. rewrite /perm_done. apply _. Qed.

  Lemma perm_step_kq (gd : nat) (γP : gname) (kq : nat * gname)
      (w : disk_wr) (todo : gset nat) (i : nat) (dk : Z -> bv 8) (n : nat) :
    i ∈ todo ->
    perm_inv_body gd γP -∗ perm_pend γP kq w todo -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_pend γP kq w (todo ∖ {[ i ]}) ∗
      start_auth n ∗
      disk_fixed_auth (wr_apply (wr_sector w i) dk) ∗
      ▷ riscv_crash_pred.
  Proof.
    iIntros (Hi) "Hbody Hpend Hsa %Hn Ha HP". rewrite /perm_pend.
    iMod (perm_step gd γP kq.1 kq.2 w todo i dk n Hi
            with "Hbody Hpend Hsa [//] Ha HP")
      as "(Hbody & Htok & Hsa & Ha & HP)".
    iModIntro. iFrame "Hbody Htok Hsa Ha HP".
  Qed.

  Lemma perm_consume_kq (gd : nat) (γP : gname) (kq : nat * gname)
      (w : disk_wr) (dk : Z -> bv 8) (n : nat) :
    perm_inv_body gd γP -∗ perm_pend γP kq w ∅ -∗
    start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
    disk_fixed_auth dk -∗
    ▷ riscv_crash_pred ={∅}=∗
      perm_inv_body gd γP ∗ perm_done γP kq w ∗ start_auth n ∗
      disk_fixed_auth (wr_apply None dk) ∗
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
    perm_inv gd γP -∗ disk_seq_permit gd w Q ={E}=∗
      ∃ kq : nat * gname,
        perm_pend γP kq w (set_seq 0 (wr_nsectors w)) ∗ perm_receipt kq.2 Q.
  Proof.
    iIntros (HE) "#Hinv Hperm".
    iMod (perm_deposit gd γP w Q E HE with "Hinv Hperm") as (k γq) "[Htok #Hrc]".
    iModIntro. iExists (k, γq). rewrite /perm_pend /=. iFrame "Htok Hrc".
  Qed.

  (* ==================================================================== *)
  (* 4. COLLECTION -- the enqueuer, after its wake                         *)
  (* ==================================================================== *)

  (* Over the stripped body (a caller with a program step to spare): ONE
     later, and it is the saved-prop agreement's, not the invariant's. *)
  Lemma perm_collect_body (gd : nat) (γP : gname) (k : nat) (γq : gname)
      (w : disk_wr) (Q : iProp Σ) :
    perm_inv_body gd γP -∗ perm_receipt γq Q -∗ perm_tok γP k false γq w ∅ ==∗
      perm_inv_body gd γP ∗ ▷ Q.
  Proof.
    iIntros "Hbody #Hrc Htok". rewrite {1}/perm_inv_body /perm_tok /perm_receipt.
    iDestruct "Hbody" as (m) "[Hauth Hents]".
    iDestruct (ghost_map_lookup with "Hauth Htok") as %Hk.
    iDestruct (big_sepM_delete
                 (fun k x => perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2) m k
                 (false, γq, (w, ∅)) Hk with "Hents") as "[Hent Hents]".
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
    perm_inv gd γP -∗ perm_receipt γq Q -∗ perm_tok γP k false γq w ∅ ={E}=∗
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
    iDestruct (big_sepM_delete
                 (fun k x => ▷ perm_slot gd x.1.1 x.1.2 x.2.1 x.2.2)%I
                 m k (false, γq, (w, ∅)) Hk with "Hents") as "[Hent Hents]".
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

End perm.
