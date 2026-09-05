(* FsAbsInv.v -- THE APPLICATION-SIDE ABSTRACT-STATE INVARIANT: an [inv]
   that OWNS a client copy of the abstract file-system state, stated so
   that it can be swapped per application and never depends on a
   file-system-internal invariant.

   Design of record: claude-notes/design/applications.md sections 1-2 (the
   conditional invariant [⌜A I⌝ ∨ tainted], the body and its two carriers)
   on top of fs-syscall-specs.md sections 0-2 (the AU forms and the
   [FsAbs] carriers), and the owner's 2026-09-03 ruling: the invariant
   lives SIDE BY SIDE with the file system's crash invariant
   ([FsCrash.fs_crash_seam]), not inside it or any other fs-internal
   invariant, because it is the piece that changes with the application
   proven on top of xv6 -- a different program wants a different statement
   about the abstract state, and nothing in the kernel's own invariants
   should have to move for that.

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

   WHAT IT SAYS: THE APPLICATION CONJUNCT (applications.md section 1).
   Beside the copy the body carries [fsabs_ok I]: EITHER the application's
   predicate on the abstract state holds of the copy -- [fsc_app I], a
   field of the era's file-system configuration ([FsCfg.fscfg]), chosen at
   the era mint -- OR the run is TAINTED, witnessed by a lower bound of 1
   on the machine's CLIENT PHASE COUNTER ([RiscvPtsto.client_lb 1]).  The
   counter is fixed-layer for the same reason the durable disk's name is:
   a taint must outlive the era it was minted in, and every era has to be
   able to name it without learning it.  Both arms are persistent, so the
   conjunct costs nothing to carry and nothing to duplicate.

   WHERE IT IS ESTABLISHED, AND WHERE IT IS RE-ESTABLISHED.  The copy is
   MINTED AT THE ERA MINT ([FsCfgSnap.fs_cfg_alloc_snap], through
   [fsabs_env_alloc]) at the founded map, and the seed's [fsabs_ok] is the
   application's BOOT obligation ([SystemAdequacy.xv6_boot_era]'s
   [Happ_boot]: at every era, the founded map satisfies the predicate or
   the run is tainted; [iLeft] for the generic application).  At every AU
   commit the dischargers ([FsAbsInvFire]) open the invariant, overwrite
   the copy with the map the kernel lent (phase 1: the pre-map; phase 2:
   the post-map) and close, so the copy is "the abstract state as last
   observed at a fire point" -- and they pay the new map's [fsabs_ok] with
   THE LICENSE, [fsabs_lic]: a persistent wand the application owns,

       fsabs_lic := □ (∀ I I', fsabs_ok I -∗ fsabs_ok I')

   "the copy may be re-synced to any map".  DELTA-FREE in this round
   (applications.md section 2, ruled 2026-09-04): at a fire the discharger
   holds the kernel's lent map, not the copy's, and nothing relates the
   two until every mover fires (lane L3), so a license indexed by the
   write deltas ([FsAbsDelta.fs_delta]) could not be applied.  The generic
   application ([fsc_app = fun _ => True]) holds the license outright
   ([fsabs_lic_raw_triv]); an application that constrains the state holds
   it only once tainted ([fsabs_lic_raw_tainted]).  Nothing here claims the
   copy tracks the kernel between fire points: paths that move [γtop]
   without firing a commit (an [iput] free, a syscall still on its landed
   contract) leave the copy stale, and an application invariant that
   needs the tie owns the obligation to close those paths first.

   THREE SPELLINGS OF THE CONJUNCT, AND WHY.  [fsabs_ok_raw]/[fsabs_lic_raw]
   take the counter's gname and the predicate as ARGUMENTS and bind only
   [mono_natG], so the system theorem can state them under [riscvGpreS],
   before the fixed record exists ([SystemAdequacy.xv6_power_adequacy_gen]'s
   [Happ_boot]/[Happ_lic]).  [fsabs_ok_at]/[fsabs_lic_at] are the same at
   the machine's own [riscv_client_name], spelled through a definition in a
   section where [riscvFixedGS]'s [mono_natG] is the ONLY one -- RiscvPtsto's
   rule for [client_lb]: a section that also binds [xv6G] sees a second
   [mono_natG] ([Xv6Cameras.disk_nc_inG]) and a raw spelling written there
   resolves to whichever instance search reaches first, and then fails to
   unify with this file's, both printing identically.  The boot chain
   ([FsCfgSnap], [BootShared], [xv6_boot_era]) states its premises at the
   pinned forms for that reason.  [fsabs_ok]/[fsabs_lic] are the pinned
   forms at the ambient [fsc_app], which is what the body and the
   dischargers use.

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
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
Require Import RiscvPtsto.      (* [riscvGS]: the invariant class, the way FsAbs section 5 binds it;
                                   [riscv_client_name] / [client_lb]: the taint *)
Require Import Xv6Cameras.
Require Import FsCfg.           (* [fscfg]: [fsc_app], the application's predicate *)
Require Import FsState.         (* [fs_view_names], [top_frag] *)

Definition fsabsN : namespace := nroot .@ "fsabs".
Definition fsabsE : coPset := ↑fsabsN.

(* ------------------------------------------------------------------ *)
(*  1.  The raw forms: at a gname and a predicate, [mono_natG] only     *)
(* ------------------------------------------------------------------ *)

Section FsAbsRaw.
  Context `{!mono_natG Σ}.

  (* the application conjunct: the predicate holds of [I], or the run is
     tainted (the client counter has passed 1) *)
  Definition fsabs_ok_raw (γcl : gname) (A : gmap Z fs_node -> Prop)
      (I : gmap Z fs_node) : iProp Σ :=
    (⌜A I⌝ ∨ mono_nat_lb_own γcl 1%nat)%I.

  (* THE LICENSE: the copy may be re-synced to any map *)
  Definition fsabs_lic_raw (γcl : gname) (A : gmap Z fs_node -> Prop) : iProp Σ :=
    (□ (∀ I I' : gmap Z fs_node, fsabs_ok_raw γcl A I -∗ fsabs_ok_raw γcl A I'))%I.

  Global Instance fsabs_ok_raw_persistent γcl A I : Persistent (fsabs_ok_raw γcl A I).
  Proof. rewrite /fsabs_ok_raw. apply _. Qed.
  Global Instance fsabs_ok_raw_timeless γcl A I : Timeless (fsabs_ok_raw γcl A I).
  Proof. rewrite /fsabs_ok_raw. apply _. Qed.
  Global Instance fsabs_lic_raw_persistent γcl A : Persistent (fsabs_lic_raw γcl A).
  Proof. rewrite /fsabs_lic_raw. apply _. Qed.

  Lemma fsabs_ok_raw_intro γcl A I : A I -> ⊢ fsabs_ok_raw γcl A I.
  Proof. intros HA. rewrite /fsabs_ok_raw. iLeft. done. Qed.

  Lemma fsabs_ok_raw_tainted γcl A I : mono_nat_lb_own γcl 1%nat -∗ fsabs_ok_raw γcl A I.
  Proof. iIntros "H". rewrite /fsabs_ok_raw. iRight. iExact "H". Qed.

  (* the generic application's license: [fun _ => True] holds of any map *)
  Lemma fsabs_lic_raw_triv γcl : ⊢ fsabs_lic_raw γcl (fun _ : gmap Z fs_node => True%type).
  Proof.
    rewrite /fsabs_lic_raw. iIntros "!>" (J J') "_".
    iApply fsabs_ok_raw_intro. exact Logic.I.
  Qed.

  (* ...and a constraining application's: only once tainted *)
  Lemma fsabs_lic_raw_tainted γcl A : mono_nat_lb_own γcl 1%nat -∗ fsabs_lic_raw γcl A.
  Proof.
    iIntros "#Ht". rewrite /fsabs_lic_raw. iIntros "!>" (J J') "_".
    by iApply fsabs_ok_raw_tainted.
  Qed.
End FsAbsRaw.

(* ------------------------------------------------------------------ *)
(*  2.  The pinned forms: at the machine's client counter               *)
(* ------------------------------------------------------------------ *)

Section FsAbsAt.
  (* [riscvFixedGS] and nothing else, so [riscvF_genGS] is the one
     [mono_natG] in scope -- exactly [client_lb]'s binding (header) *)
  Context `{!riscvFixedGS Σ}.

  Definition fsabs_ok_at (A : gmap Z fs_node -> Prop) (I : gmap Z fs_node) : iProp Σ :=
    fsabs_ok_raw riscv_client_name A I.
  Definition fsabs_lic_at (A : gmap Z fs_node -> Prop) : iProp Σ :=
    fsabs_lic_raw riscv_client_name A.

  Global Instance fsabs_ok_at_persistent A I : Persistent (fsabs_ok_at A I).
  Proof. rewrite /fsabs_ok_at. apply _. Qed.
  Global Instance fsabs_ok_at_timeless A I : Timeless (fsabs_ok_at A I).
  Proof. rewrite /fsabs_ok_at. apply _. Qed.
  Global Instance fsabs_lic_at_persistent A : Persistent (fsabs_lic_at A).
  Proof. rewrite /fsabs_lic_at. apply _. Qed.

  Lemma fsabs_ok_at_intro A I : A I -> ⊢ fsabs_ok_at A I.
  Proof. intros HA. rewrite /fsabs_ok_at. by iApply fsabs_ok_raw_intro. Qed.
  Lemma fsabs_ok_at_tainted A I : client_lb 1 -∗ fsabs_ok_at A I.
  Proof. rewrite /fsabs_ok_at /client_lb. iApply fsabs_ok_raw_tainted. Qed.
  Lemma fsabs_lic_at_triv : ⊢ fsabs_lic_at (fun _ : gmap Z fs_node => True%type).
  Proof. rewrite /fsabs_lic_at. iApply fsabs_lic_raw_triv. Qed.
  Lemma fsabs_lic_at_tainted A : client_lb 1 -∗ fsabs_lic_at A.
  Proof. rewrite /fsabs_lic_at /client_lb. iApply fsabs_lic_raw_tainted. Qed.
End FsAbsAt.

(* ------------------------------------------------------------------ *)
(*  3.  The invariant, at the ambient configuration                     *)
(* ------------------------------------------------------------------ *)

Section FsAbsInv.
  (* [riscvGS] rather than a bare [invGS_gen hlc]: the has_lc index has to be
     pinned by the machine's own instance, or a consumer's statement that
     mentions nothing else ([fsabs_inv] beside a plain fupd) cannot resolve it *)
  Context `{!riscvGS Σ, !fsLinkG Σ, !fsTopG Σ}.
  (* the era's configuration, for [fsc_app] (consumers reach it through
     [fileG]'s [file_fscfg]; the kits and the mint pass it explicitly) *)
  Context `{FSC : fscfg}.
  Implicit Types Γ : fs_view_names Σ.

  (* the client Γ: the live one with a fresh [γtop] *)
  Definition fsabs_client Γ (γa : gname) : fs_view_names Σ :=
    MkFsView (fsΦ Γ) (γlink Γ) γa.

  Lemma fsabs_client_top Γ γa : γtop (fsabs_client Γ γa) = γa.
  Proof. reflexivity. Qed.

  (* every element of the client map, whole *)
  Definition fsabs_frags Γ (I : gmap Z fs_node) : iProp Σ :=
    ([∗ map] i ↦ n ∈ I, top_frag Γ i n)%I.

  (* the application conjunct and the license at [fsc_app] *)
  Definition fsabs_ok (I : gmap Z fs_node) : iProp Σ := fsabs_ok_at fsc_app I.
  Definition fsabs_lic : iProp Σ := fsabs_lic_at fsc_app.

  Global Instance fsabs_ok_persistent I : Persistent (fsabs_ok I).
  Proof. rewrite /fsabs_ok. apply _. Qed.
  Global Instance fsabs_ok_timeless I : Timeless (fsabs_ok I).
  Proof. rewrite /fsabs_ok. apply _. Qed.
  Global Instance fsabs_lic_persistent : Persistent fsabs_lic.
  Proof. rewrite /fsabs_lic. apply _. Qed.

  Lemma fsabs_lic_apply (I I' : gmap Z fs_node) :
    fsabs_lic -∗ fsabs_ok I -∗ fsabs_ok I'.
  Proof.
    rewrite /fsabs_lic /fsabs_lic_at /fsabs_lic_raw /fsabs_ok /fsabs_ok_at.
    iIntros "#Hlic Hok". iApply ("Hlic" with "Hok").
  Qed.

  (* the body: the client authority beside all of its frags and the
     application conjunct (header) *)
  Definition fsabs_body Γ : iProp Σ :=
    (∃ I : gmap Z fs_node,
       ghost_map_auth (γtop Γ) 1 I ∗ fsabs_frags Γ I ∗ fsabs_ok I)%I.

  Definition fsabs_inv Γ : iProp Σ := inv fsabsN (fsabs_body Γ).

  Global Instance fsabs_frags_timeless Γ I : Timeless (fsabs_frags Γ I).
  Proof. rewrite /fsabs_frags /top_frag. apply _. Qed.
  Global Instance fsabs_body_timeless Γ : Timeless (fsabs_body Γ).
  Proof. rewrite /fsabs_body. apply _. Qed.
  Global Instance fsabs_inv_persistent Γ : Persistent (fsabs_inv Γ).
  Proof. rewrite /fsabs_inv. apply _. Qed.

  (* THE REPLACEMENT: with every frag inside, the whole map may be
     overwritten -- delete everything, then insert the new map.  This is
     the one ghost move the dischargers make; the old map's conjunct is
     dropped with it. *)
  Lemma fsabs_body_replace Γ (I' : gmap Z fs_node) :
    fsabs_body Γ ==∗ ghost_map_auth (γtop Γ) 1 I' ∗ fsabs_frags Γ I'.
  Proof.
    iIntros "H". iDestruct "H" as (I) "(Ha & Hf & _)".
    rewrite /fsabs_frags /top_frag.
    iMod (ghost_map_delete_big I with "Ha Hf") as "Ha".
    rewrite map_difference_diag.
    iMod (ghost_map_insert_big I' with "Ha") as "[Ha Hf]".
    { apply map_disjoint_empty_r. }
    rewrite map_union_empty. iModIntro. iFrame "Ha Hf".
  Qed.

  (* ...re-closed at a map whose conjunct the caller pays *)
  Lemma fsabs_body_set Γ (I' : gmap Z fs_node) :
    fsabs_body Γ -∗ fsabs_ok I' ==∗ fsabs_body Γ.
  Proof.
    iIntros "H #Hok". iMod (fsabs_body_replace Γ I' with "H") as "[Ha Hf]".
    iModIntro. iExists I'. iFrame "Ha Hf Hok".
  Qed.

  (* ...and paid with the license: what every discharger uses *)
  Lemma fsabs_body_lic_set Γ (I' : gmap Z fs_node) :
    fsabs_lic -∗ fsabs_body Γ ==∗ fsabs_body Γ.
  Proof.
    iIntros "#Hlic H". iDestruct "H" as (I) "(Ha & Hf & #Hok)".
    iDestruct (fsabs_lic_apply I I' with "Hlic Hok") as "#Hok'".
    iApply (fsabs_body_set Γ I' with "[Ha Hf] Hok'").
    iExists I. iFrame "Ha Hf Hok".
  Qed.

  (* ALLOCATION: a fresh client copy at a map whose conjunct the caller
     holds (the era mint seeds it with the founded map, and the seed's
     conjunct is the application's boot obligation -- header). *)
  Lemma fsabs_alloc Γ (I : gmap Z fs_node) (E : coPset) :
    fsabs_ok I -∗ |={E}=> ∃ γa : gname, fsabs_inv (fsabs_client Γ γa).
  Proof.
    iIntros "#Hok". iMod (ghost_map_alloc I) as (γa) "[Ha Hf]".
    iExists γa. iApply (inv_alloc fsabsN E with "[Ha Hf]").
    iExists I. rewrite /fsabs_frags /top_frag fsabs_client_top.
    iFrame "Ha Hf Hok".
  Qed.

  (* THE ENVIRONMENT an application reaches the invariant through
     (applications.md section 2): the copy at an existential gname beside
     the license.  Persistent; carried beside the sealed file system in
     [FirstTok.first_done] and read by the dispatcher off [syscall_env]. *)
  Definition fsabs_env Γ : iProp Σ :=
    (∃ γa : gname, fsabs_inv (fsabs_client Γ γa) ∗ fsabs_lic)%I.

  Global Instance fsabs_env_persistent Γ : Persistent (fsabs_env Γ).
  Proof. rewrite /fsabs_env. apply _. Qed.

  Lemma fsabs_env_intro Γ (γa : gname) :
    fsabs_inv (fsabs_client Γ γa) -∗ fsabs_lic -∗ fsabs_env Γ.
  Proof. iIntros "#Hinv #Hlic". iExists γa. iFrame "Hinv Hlic". Qed.

  (* the mint's one call: allocate the copy at the founded map and pack it *)
  Lemma fsabs_env_alloc Γ (I : gmap Z fs_node) (E : coPset) :
    fsabs_ok I -∗ fsabs_lic -∗ |={E}=> fsabs_env Γ.
  Proof.
    iIntros "#Hok #Hlic". iMod (fsabs_alloc Γ I E with "Hok") as (γa) "#Hinv".
    iModIntro. iApply (fsabs_env_intro Γ γa with "Hinv Hlic").
  Qed.

End FsAbsInv.

(* a big-op body behind a definition: sealed, per the family convention
   (optimization.md, "a big-op body is the predictor").  [fsabs_ok] stays
   transparent: a discharger's [iLeft]/[iRight] has to see the disjunction. *)
Global Typeclasses Opaque fsabs_frags fsabs_body.
