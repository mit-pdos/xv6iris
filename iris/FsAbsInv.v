(* FsAbsInv.v -- THE APPLICATION-SIDE ABSTRACT-STATE INVARIANT: an [inv]
   that OWNS a client copy of the abstract file-system state, stated so
   that it can be swapped per application and never depends on a
   file-system-internal invariant.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-2
   (the AU forms and the [FsAbs] carriers), and the owner's 2026-09-03
   ruling: the invariant lives SIDE BY SIDE with the file system's crash
   invariant ([FsCrash.fs_crash_seam]), not inside it or any other
   fs-internal invariant, because it is the piece that changes with the
   application proven on top of xv6 -- a different program wants a
   different statement about the abstract state, and nothing in the
   kernel's own invariants should have to move for that.

   WHAT IT OWNS, AND WHY THIS CARRIER.  The kernel's own authority over
   the abstract state is [InodeRegion.ftop_body]'s [ghost_map_auth
   (fs_top γfs) 1 I], borrowed by the AU commits at their fire points
   ([FsAbsMknodFire] and its siblings open [ftopN] and lend the map to
   the caller's fupd).  A client cannot hold any share of THAT map
   across a syscall -- every element is the kernel's (the inode region
   parks it, the icache payload checks it out), which is [FsAbsEra]'s
   "the pins come back" finding.  So the client-side state is a SECOND
   instance of the same ghost class ([Xv6Cameras.fsTopG], already on the
   [xv6G] bundle -- no new class, nothing to thread), at a FRESH gname:
   [fsabs_client Γ γa] is the live [fs_view_names] with its [γtop]
   replaced by [γa], so every [FsAbs] reading -- [astate], [nview],
   [top_frag], the agreement lemmas -- applies to the client copy
   verbatim.  The body holds the client authority TOGETHER WITH every
   element ([fsabs_frags]): the elements are the FRAGS an application
   will later take out of the invariant for the nodes it owns
   exclusively (the tree layer's exclusivity story, design section 6),
   and while they are all inside, the whole map can be replaced at will
   ([fsabs_body_replace]).

   WHAT IT SAYS TODAY: NOTHING.  The body is purely existential.  Its
   one job in this increment is to be the resource the AU dischargers
   ([FsAbsInvFire]) open at every commit: they read the kernel's map off
   the lent authority and overwrite the client copy with it, so the
   client copy is "the abstract state as last observed at a fire point".
   That discipline is what a later, application-specific body will
   strengthen (a [⌜wf av⌝] conjunct, or per-node frags handed to the
   program), and the discharge is the one place that has to re-establish
   it.  Nothing here claims the copy tracks the kernel between fire
   points: paths that move [γtop] without firing a commit (an [iput]
   free, a syscall still on its landed contract) leave the copy stale,
   and an application invariant that needs the tie owns the obligation
   to close those paths first.

   THE MASK.  The AU commits used to be instantiated at the mask floor
   [∅]; a fupd at [∅] can open no invariant, so a commit could never
   touch this one.  Every commit now fires at [fsabsE] = [↑fsabsN]: the
   fire lemmas ask the caller for [↑fsabsN ⊆ E] beside [↑ftopN ⊆ E], and
   the two namespaces are disjoint by construction ([solve_ndisj]).  An
   application that wants several invariants open at a fire point puts
   them under [fsabsN] ([fsabsN .@ "..."]) and nothing here moves. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import RiscvPtsto.      (* [riscvGS]: the invariant class, the way FsAbs section 5 binds it *)
Require Import Xv6Cameras.
Require Import FsState.
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)

Definition fsabsN : namespace := nroot .@ "fsabs".
Definition fsabsE : coPset := ↑fsabsN.

Section FsAbsInv.
  (* [riscvGS] rather than a bare [invGS_gen hlc]: the has_lc index has to be
     pinned by the machine's own instance, or a consumer's statement that
     mentions nothing else ([fsabs_inv] beside a plain fupd) cannot resolve it *)
  Context `{!riscvGS Σ, !fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* the client Γ: the live one with a fresh [γtop] *)
  Definition fsabs_client Γ (γa : gname) : fs_view_names Σ :=
    MkFsView (fsΦ Γ) (γlink Γ) γa.

  Lemma fsabs_client_top Γ γa : γtop (fsabs_client Γ γa) = γa.
  Proof. reflexivity. Qed.

  (* every element of the client map, whole *)
  Definition fsabs_frags Γ (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, top_frag Γ i n)%I.

  (* the body: the client authority beside all of its frags.  Pure
     existential -- see the header. *)
  Definition fsabs_body Γ : iProp Σ :=
    (∃ I : gmap Z fs_node, ghost_map_auth (γtop Γ) 1 I ∗ fsabs_frags Γ I)%I.

  Definition fsabs_inv Γ : iProp Σ := inv fsabsN (fsabs_body Γ).

  Global Instance fsabs_frags_timeless Γ I : Timeless (fsabs_frags Γ I).
  Proof. rewrite /fsabs_frags /top_frag. apply _. Qed.
  Global Instance fsabs_body_timeless Γ : Timeless (fsabs_body Γ).
  Proof. rewrite /fsabs_body. apply _. Qed.
  Global Instance fsabs_inv_persistent Γ : Persistent (fsabs_inv Γ).
  Proof. rewrite /fsabs_inv. apply _. Qed.

  (* the body reads as an [astate] at the client Γ, and the map comes
     back through the same wand a fire point uses *)
  Lemma fsabs_body_astate Γ :
    fsabs_body Γ ⊢
      ∃ I, astate Γ (abs_view I) ∗ fsabs_frags Γ I.
  Proof.
    iIntros "H". iDestruct "H" as (I) "[Ha Hf]". iExists I. iFrame "Hf".
    iApply astate_intro. iExact "Ha".
  Qed.

  (* THE REPLACEMENT: with every frag inside, the whole map may be
     overwritten -- delete everything, then insert the new map.  This is
     the one ghost move the dischargers make. *)
  Lemma fsabs_body_replace Γ (I' : gmap Z fs_node) :
    fsabs_body Γ ==∗ ghost_map_auth (γtop Γ) 1 I' ∗ fsabs_frags Γ I'.
  Proof.
    iIntros "H". iDestruct "H" as (I) "[Ha Hf]".
    rewrite /fsabs_frags /top_frag.
    iMod (ghost_map_delete_big I with "Ha Hf") as "Ha".
    rewrite map_difference_diag.
    iMod (ghost_map_insert_big I' with "Ha") as "[Ha Hf]".
    { apply map_disjoint_empty_r. }
    rewrite map_union_empty. iModIntro. iFrame "Ha Hf".
  Qed.

  Lemma fsabs_body_set Γ (I' : gmap Z fs_node) :
    fsabs_body Γ ==∗ fsabs_body Γ.
  Proof.
    iIntros "H". iMod (fsabs_body_replace Γ I' with "H") as "[Ha Hf]".
    iModIntro. iExists I'. iFrame "Ha Hf".
  Qed.

  (* ALLOCATION: a fresh client copy, at any map (the boot site seeds it
     with the founded map; nothing below depends on the seed). *)
  Lemma fsabs_alloc Γ (I : gmap Z fs_node) (E : coPset) :
    ⊢ |={E}=> ∃ γa : gname, fsabs_inv (fsabs_client Γ γa).
  Proof.
    iMod (ghost_map_alloc I) as (γa) "[Ha Hf]".
    iExists γa. iApply (inv_alloc fsabsN E with "[Ha Hf]").
    iExists I. rewrite /fsabs_frags /top_frag /=. iFrame "Ha Hf".
  Qed.

End FsAbsInv.

(* a big-op body behind a definition: sealed, per the family convention
   (optimization.md, "a big-op body is the predictor") *)
Global Typeclasses Opaque fsabs_frags fsabs_body.
