(*  AppInv.v -- THE APPLICATION'S RUNNING INVARIANT: half of the abstract
    map's authority beside the application's claim about its view, and the
    one ghost move on the map that every retag in the kernel goes through.

    Design of record: claude-notes/projects/app-instances.md sections 0-2
    and 7 (round A, "the running tie"), superseding design/applications.md
    sections 1-3 while the rounds land.

    THE TIE (section 2).  Owner's rule: nothing application-specific inside
    a kernel file-system invariant.  So the application's claim lives in an
    invariant of ITS OWN, and what ties it to the kernel's map is a SHARED
    PIECE that already exists: the map authority itself.  [ghost_map_auth]
    is fractional, any two fractions AGREE on the map
    ([ghost_map_auth_agree]), and an UPDATE needs the whole.
    [InodeRegion.ftop_body] keeps the kernel's half; [app_body] below keeps
    the other half beside [app_pred app_run (abs_view I)].
    Agreement pins the two maps to one; the mover needs the whole, so it
    opens BOTH invariants and re-establishes the claim -- "they move
    together" as a resource, enforced by ownership, not by discipline.  The
    kernel's invariant names no application anything.

    THE CLAIM IS OVER THE VIEW (section 7): [FsAbsDefs.abs_view] of the raw
    map, never the nodes -- block addresses and records are invisible to
    user code, so a retag that preserves [abs_of] needs nothing from the
    application ([app_top_update_same]).

    THREE WAYS TO PAY A MOVE (section 7), because two view-changing retags
    sit outside any AU fire and inside contracts every path calls (ilock's
    fresh-inode claim: free -> typed; the escrow deposit: orphan -> free):
      [_same]  the reading is unchanged -- no application input;
      [_step]  a step wand from the caller's contract -- the AU fires, whose
               bundles carry it (round A: paid by the generic dischargers
               out of [app_auto]; round B: by the process's payload);
      [_auto]  THE PARKED LICENSE [app_auto]: a persistent wand the
               application parks in its invariant admitting the kernel's
               own non-AU moves, [top_move].  Round A: [top_move] is
               everything, and every non-AU site takes this form; round E
               narrows it as each site moves onto an AU form whose step the
               caller pays.  Kernel-defined, so a kernel proof discharges it
               by itself.
    All three are ONE lemma, [app_top_update], at a later-shaped step: the
    application's claim is an arbitrary iProp -- neither timeless nor
    persistent -- so it stays under the invariant's later and the step is
    applied there ([▷ (P -∗ Q) ∗ ▷ P ⊢ ▷ Q]).  Only the authority comes out
    from under the later.

    THE MASK.  [appN] is the application's namespace: [app_inv] lives at it,
    the AU commits fire at [appE] = [↑appN] (so an application's discharger
    may open its own invariant at a fire point), and a process's own
    invariants that a commit opens sit under it ([OffGv.foffN]).  Nothing
    here is ever open at the same time as one of those. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import RiscvPtsto.      (* [riscvGS]: the invariant class *)
Require Import Xv6Cameras.      (* [fsTopG]: the top map's ghost class *)
Require Import FsBlocks.        (* [fs_names], [fs_top] *)
Require Import FsNode.          (* [fs_node] *)
Require Import FsAbsDefs.       (* [aview], [abs_view], [abs_view_insert_same] *)
Require Import AppCfg.          (* [appcfg]: [app_names], [app_pred], [app_run] *)
Require Import IcacheRef.       (* [icfg_nib]: the inode region's width, for
                                   the body's DOMAIN row (round C) *)

Local Open Scope Z_scope.

Definition appN : namespace := nroot .@ "app".
Definition appE : coPset := ↑appN.

(* THE KERNEL'S OWN NON-AU MOVES: the union of what the retag sites that
   sit outside an AU fire do to a node (the fresh-inode claim in ilock,
   the free in the escrow deposit, link/mkdir/create's landed paths).
   ROUND A: everything; round E narrows it as each site moves onto an
   AU form whose step the caller pays.  Kernel-defined, so a kernel
   proof discharges it by itself. *)
Definition top_move (n n' : fs_node) : Prop := True.

(* ------------------------------------------------------------------ *)
(*  1.  The raw license: at a predicate and an instance                 *)
(* ------------------------------------------------------------------ *)

Section AppAutoRaw.
  Context {Σ : gFunctors}.

  (* the application's PARKED LICENSE: it admits the kernel's non-AU moves.
     RAW -- the predicate (its fixed part already applied) and the instance
     are ARGUMENTS -- so the system theorem can state it under
     [riscvGpreS], before the fixed record exists
     ([SystemAdequacy.xv6_power_adequacy_gen]'s [Happ_auto]); [app_auto]
     below is the pinned form. *)
  Definition app_auto_raw {N : Type}
      (A : N -> aview -> iProp Σ) (r : N) : iProp Σ :=
    (□ (∀ (I : gmap Z fs_node) (i : Z) (n n' : fs_node),
          ⌜I !! i = Some n⌝ -∗ ⌜top_move n n'⌝ -∗
          A r (abs_view I) -∗ A r (abs_view (<[i := n']> I))))%I.

  Global Instance app_auto_raw_persistent {N} (A : N -> aview -> iProp Σ) r :
    Persistent (app_auto_raw A r).
  Proof. rewrite /app_auto_raw. apply _. Qed.

  (* the generic application's: a predicate that holds of every view holds
     of the moved one *)
  Lemma app_auto_raw_triv {N} (A : N -> aview -> iProp Σ) (r : N) :
    (forall r av, A r av ⊣⊢ True) -> ⊢ app_auto_raw A r.
  Proof.
    intros Htriv. rewrite /app_auto_raw. iIntros "!>" (I i n n') "_ _ _".
    iApply (bi.equiv_entails_1_2 _ _ (Htriv r (abs_view (<[i := n']> I)))).
    iPureIntro. exact Logic.I.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1b.  THE TRANSPORT (app-instances.md section 1; section 6 ruling 5) *)
  (* ------------------------------------------------------------------ *)

  (* THE ONE DURABILITY OBLIGATION: a copy of the claim about the view [av]
     can be made at FRESH instance names without spending the original.  A
     pure or persistent predicate pays it by duplication; one owning an
     exclusive token pays it by allocating a fresh one -- the existential
     is what lets it.  LATER-SHAPED (ruling 5): the commit's law, the boot
     mint and the PowerOn clone are fupds without a step, so the claim
     reaches every crossing under an invariant's later, and a basic update
     cannot run under it; a timeless claim strips, a claim holding
     invariants duplicates under the later.  RAW -- the predicate is an
     ARGUMENT -- for [app_auto_raw]'s reason. *)
  Definition app_xfer_raw {N : Type} (A : N -> aview -> iProp Σ) : iProp Σ :=
    (□ (∀ (r : N) (av : aview),
          ▷ A r av ==∗ ▷ A r av ∗ ∃ r' : N, ▷ A r' av))%I.

  Global Instance app_xfer_raw_persistent {N} (A : N -> aview -> iProp Σ) :
    Persistent (app_xfer_raw A).
  Proof. rewrite /app_xfer_raw. apply _. Qed.

  (* the generic application's: a predicate that holds of every view is its
     own copy (at the instance handed in, so no inhabitant is needed) *)
  Lemma app_xfer_raw_triv {N} (A : N -> aview -> iProp Σ) :
    (forall r av, A r av ⊣⊢ True) -> ⊢ app_xfer_raw A.
  Proof.
    intros Htriv. rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iModIntro. iSplitL "H"; [iExact "H" |]. iExists r. iNext.
    iApply (bi.equiv_entails_1_2 _ _ (Htriv r av)). iPureIntro. exact Logic.I.
  Qed.

  (* a PURE claim duplicates outright *)
  Lemma app_xfer_raw_pure {N} (P : aview -> Prop) :
    ⊢ app_xfer_raw (fun (_ : N) (av : aview) => ⌜P av⌝%I).
  Proof.
    rewrite /app_xfer_raw. iIntros "!>" (r av) "#H".
    iModIntro. iSplitR; [iExact "H" |]. iExists r. iExact "H".
  Qed.
End AppAutoRaw.

(* ------------------------------------------------------------------ *)
(*  2.  The invariant, at the ambient configuration                     *)
(* ------------------------------------------------------------------ *)

Section AppInv.
  (* [riscvGS] rather than a bare [invGS_gen hlc]: the has_lc index has to be
     pinned by the machine's own instance, or a consumer's statement that
     mentions nothing else ([app_inv] beside a plain fupd) cannot resolve
     it. *)
  Context `{!riscvGS Σ, !fsTopG Σ}.
  (* the era's application record (consumers reach it through [fileG]'s
     [file_app]; the kits and the mint pass it explicitly) *)
  Context `{APP : appcfg Σ}.
  (* ...and the inode cache's, for the region's width alone: the body's
     DOMAIN row below is stated at [icfg_nib].  Every carrier of [app_inv]
     has the record ambient already ([ireg_reg] is [InodeRegion]'s, and the
     files above [fileG] see it through [file_icfg]). *)
  Context `{ICFG : icfg}.

  Definition app_auto : iProp Σ := app_auto_raw app_pred app_run.

  Global Instance app_auto_persistent : Persistent app_auto.
  Proof. rewrite /app_auto. apply _. Qed.

  Lemma app_auto_of_triv :
    (forall r av, app_pred r av ⊣⊢ True) -> ⊢ app_auto.
  Proof. intros Htriv. rewrite /app_auto. by apply app_auto_raw_triv. Qed.

  (* THE TRANSPORT, PINNED (round C): parked in the body so the era owns
     it, and a premise of the era mint beside [app_auto]. *)
  Definition app_xfer : iProp Σ := app_xfer_raw app_pred.

  Global Instance app_xfer_persistent : Persistent app_xfer.
  Proof. rewrite /app_xfer. apply _. Qed.

  (* THE DOMAIN ROW (round C).  The abstract map names EXACTLY the region's
     inums.  [InodeRegion.ftop_body] carries no such row, so the commit's
     collection states its snapshot at the map RESTRICTED to the region
     ([FsCollectAll.col_reg_map]); the application's durable claim is tied
     to that snapshot by the half authority and must therefore be about the
     same map -- which is the running one only if the running one has no
     inum outside the region.  It never has: the mint founds the map at the
     snapshot's own node map, whose inums are the region's
     ([FsState.fs_geom]'s [fg_reg]/[fg_regdom]), and the one mover inserts
     at an existing key.  Kept HERE, in the application's invariant, because
     this is the one body the tie reads and the one the mover alone
     re-closes; nothing in the kernel's own invariants moves. *)
  Definition app_dom (I : gmap Z fs_node) : Prop :=
    forall z : Z, is_Some (I !! z) <-> 0 <= z < 16 * Z.of_nat icfg_nib.

  Lemma app_dom_insert (I : gmap Z fs_node) (i : Z) (n n' : fs_node) :
    I !! i = Some n -> app_dom I -> app_dom (<[i := n']> I).
  Proof.
    intros Hi Hd z. rewrite lookup_insert_is_Some'. rewrite -(Hd z).
    split; [| by right]. intros [-> | H]; [by eexists | exact H].
  Qed.

  (* THE BODY: the application's half of the authority, the claim about the
     map it carries (read through the view), the domain row, the parked
     license and the transport.  NOT timeless: the claim is an arbitrary
     iProp and stays under the later. *)
  Definition app_body (γfs : fs_names) : iProp Σ :=
    (∃ I : gmap Z fs_node,
       ghost_map_auth (fs_top γfs) (1/2) I ∗
       app_pred app_run (abs_view I) ∗
       ⌜app_dom I⌝ ∗
       app_auto ∗
       app_xfer)%I.

  Definition app_inv (γfs : fs_names) : iProp Σ := inv appN (app_body γfs).

  Global Instance app_inv_persistent γfs : Persistent (app_inv γfs).
  Proof. rewrite /app_inv. apply _. Qed.

  (* ALLOCATION, at the era mint: the guest half of the authority the boot
     founded, the claim at the founded map -- LATER-SHAPED, because it
     arrives from the durable instance through the transport (round C) and
     [inv_alloc] takes the later -- the domain row, the license and the
     transport. *)
  Lemma app_inv_alloc (γfs : fs_names) (I : gmap Z fs_node) (E : coPset) :
    app_dom I ->
    ghost_map_auth (fs_top γfs) (1/2) I -∗
    ▷ app_pred app_run (abs_view I) -∗
    app_auto -∗ app_xfer -∗ |={E}=> app_inv γfs.
  Proof.
    iIntros (Hd) "Hh Hp #Ha #Hx". rewrite /app_inv.
    iApply (inv_alloc appN E with "[Hh Hp]").
    iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Ha Hx".
    iPureIntro. exact Hd.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE ONE GHOST MOVE ON THE MAP                                   *)
  (* ------------------------------------------------------------------ *)

  (* The caller holds the KERNEL'S half and the element ([InodeRegion]'s
     movers have [ftopN] open; the AU fires have it open and are between
     the commit's two phases).  This opens [appN], agrees the two halves
     ([ghost_map_auth_agree]), combines them to the whole, moves the
     element, splits back, and re-closes the application's body at the
     new map with the claim re-established UNDER THE LATER by the step --
     which sees the license and the old claim there, [▷]-shaped, and owes
     the new one [▷]-shaped.  The three forms below are its readings. *)
  Lemma app_top_update (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    (⌜I !! i = Some n⌝ -∗ ▷ app_auto -∗
       ▷ app_pred app_run (abs_view I) -∗
       ▷ app_pred app_run (abs_view (<[i := n']> I))) -∗
    ghost_map_auth (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof.
    iIntros (HE) "#Hinv Hstep Hk Hf".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hd & #Ha & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hk Hh") as %<-.
    iDestruct (ghost_map_lookup with "Hk Hf") as %Hi.
    iAssert (ghost_map_auth (fs_top γfs) 1 I) with "[Hk Hh]" as "Hk".
    { iEval (rewrite -Qp.half_half). iSplitL "Hk"; [iExact "Hk" | iExact "Hh"]. }
    iMod (ghost_map_update n' with "Hk Hf") as "[Hk Hf]".
    iDestruct "Hk" as "[Hk Hh]".
    iDestruct ("Hstep" with "[//] Ha Hp") as "Hp".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists (<[i := n']> I). iFrame "Hh Hp Ha Hx".
      iPureIntro. exact (app_dom_insert I i n n' Hi Hd). }
    iModIntro. iFrame "Hk Hf".
  Qed.

  (* [_same]: the reading is unchanged, so the claim is *)
  Lemma app_top_update_same (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    abs_of n = abs_of n' ->
    app_inv γfs -∗
    ghost_map_auth (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof.
    iIntros (HE Habs) "#Hinv Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [] Hk Hf").
    iIntros (Hi) "_ Hp". rewrite (abs_view_insert_same I i n n' Hi Habs). iExact "Hp".
  Qed.

  (* [_step]: the caller pays, with a plain wand -- it lifts under the later *)
  Lemma app_top_update_step (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    (app_pred app_run (abs_view I) -∗
       app_pred app_run (abs_view (<[i := n']> I))) -∗
    ghost_map_auth (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof.
    iIntros (HE) "#Hinv Hstep Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [Hstep] Hk Hf").
    iIntros (Hi) "_ Hp". iNext. iApply ("Hstep" with "Hp").
  Qed.

  (* [_auto]: the parked license pays, for a move the kernel admits *)
  Lemma app_top_update_auto (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    top_move n n' ->
    app_inv γfs -∗
    ghost_map_auth (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof.
    iIntros (HE Hmv) "#Hinv Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [] Hk Hf").
    iIntros (Hi) "#Ha Hp". iNext.
    iEval (rewrite /app_auto /app_auto_raw) in "Ha".
    iApply ("Ha" $! I i n n' with "[//] [//] Hp").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE CALLER'S STEP, AS THE AU COMMIT SHAPES CARRY IT             *)
  (* ------------------------------------------------------------------ *)

  (* "my claim about the view of [I] survives the move of row [i] to the
     view [av']" -- what a write-kind AU commit's phase 1 hands back beside
     its phase-2 fupd (app-instances.md section 7; [FsAbsMknodFire.
     acre_commit_at] and its siblings).  Indexed by the RAW insert the mover
     performs, with the abstract delta as its READING, so the fire can hand
     it to [app_top_update] verbatim; and UNDER THE LATER, because that is
     where the mover applies it -- a plain wand lifts to this for free
     (section 6, ruling 5), and it is what lets a generic discharger pay it
     out of the parked license, which it can only read [▷]-shaped
     ([app_step_acc]). *)
  Definition app_step (i : Z) (I : gmap Z fs_node) (av' : aview) : iProp Σ :=
    (∀ n' : fs_node,
       ⌜abs_view (<[i := n']> I) = av'⌝ -∗
       ▷ app_pred app_run (abs_view I) -∗
       ▷ app_pred app_run (abs_view (<[i := n']> I)))%I.

  (* the fire's reading: at the node it chose *)
  Lemma app_step_at (i : Z) (I : gmap Z fs_node) (av' : aview) (n' : fs_node) :
    abs_view (<[i := n']> I) = av' ->
    app_step i I av' -∗
    ▷ app_pred app_run (abs_view I) -∗
    ▷ app_pred app_run (abs_view (<[i := n']> I)).
  Proof.
    intros Heq. iIntros "Hstep Hp". rewrite /app_step.
    iApply ("Hstep" $! n' with "[//] Hp").
  Qed.

  (* the license pays any step at a row the map has (round A: [top_move] is
     everything) *)
  Lemma app_step_of_auto (i : Z) (I : gmap Z fs_node) (av' : aview) :
    is_Some (I !! i) ->
    ▷ app_auto -∗ app_step i I av'.
  Proof.
    intros [n Hn]. iIntros "#Ha". rewrite /app_step.
    iIntros (n' Heq) "Hp". iNext.
    iEval (rewrite /app_auto /app_auto_raw) in "Ha".
    iApply ("Ha" $! I i n n' with "[//] [] Hp").
    iPureIntro. exact Logic.I.
  Qed.

  (* THE LICENSE, READ OFF THE INVARIANT: [▷]-shaped and persistent, so the
     body closes unchanged.  A generic discharger runs this inside the
     commit's own fupd (the commits fire at [appE], with [appN] closed). *)
  Lemma app_auto_acc (E : coPset) (γfs : fs_names) :
    ↑appN ⊆ E ->
    app_inv γfs ={E}=∗ ▷ app_auto.
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(Hh & Hp & Hd & #Ha & #Hx)".
    iMod ("Hclose" with "[Hh Hp Hd]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hd Ha Hx". }
    iModIntro. iExact "Ha".
  Qed.

  (* THE TRANSPORT, READ OFF THE INVARIANT: [▷]-shaped, like the license.
     Note what this is NOT good for: a fupd under a later cannot run
     without a step, so the commit's law does not read the transport here
     -- it takes [app_xfer] itself, carried from the mint on the fsinit kit
     ([FsCfgKits.fs_kit_fsinit_ghost]). *)
  Lemma app_xfer_acc (E : coPset) (γfs : fs_names) :
    ↑appN ⊆ E ->
    app_inv γfs ={E}=∗ ▷ app_xfer.
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(Hh & Hp & Hd & #Ha & #Hx)".
    iMod ("Hclose" with "[Hh Hp Hd]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hd Ha Hx". }
    iModIntro. iExact "Hx".
  Qed.

  Lemma app_step_acc (E : coPset) (γfs : fs_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    ↑appN ⊆ E ->
    is_Some (I !! i) ->
    app_inv γfs ={E}=∗ app_step i I av'.
  Proof.
    iIntros (HE Hi) "#Hinv".
    iMod (app_auto_acc E γfs HE with "Hinv") as "#Ha".
    iModIntro. iApply (app_step_of_auto i I av' Hi with "Ha").
  Qed.

End AppInv.
