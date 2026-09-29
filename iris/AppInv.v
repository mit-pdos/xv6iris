(*  AppInv.v -- THE APPLICATION'S RUNNING INVARIANT: half of the abstract
    map's authority beside the application's claim about its view, and the
    one ghost move on the map that every retag in the kernel goes through.

    Design of record: claude-notes/projects/app-instances.md sections 0-2
    and 7 (round A, "the running tie"), superseding design/applications.md
    sections 1-3 while the rounds land.

    THE TIE (section 2).  Owner's rule: nothing application-specific inside
    a kernel file-system invariant.  So the application's claim lives in an
    invariant of ITS OWN, and what ties it to the kernel's map is a SHARED
    PIECE that already exists: the map authority itself.  [ghost_map_auth_frac]
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

    TWO WAYS TO PAY A MOVE (section 7):
      [_same]  the reading is unchanged -- no application input.  The two
               retags that sit outside any AU fire take this form: ilock's
               fresh-inode claim (free -> claim box) and the escrow deposit
               (orphan -> free) both move between rows the view does not
               have, and the region and the escrow carry the count that
               says so ([InodeRegion.ireg_top_park],
               [EscrowInode.escA_body]);
      [_step]  a step wand from the caller's contract -- the AU fires, whose
               bundles carry it (paid by the generic dischargers out of
               [app_sup], the credential a process that answers for nothing
               runs on; a verified program pays it from its own payload).
    THERE IS NO BLANKET FORM, AND NO PARKED LICENSE.  Every view move on a
    dispatched path is an AU fire or a [_step], the only [_same] movers are
    the ones between absent rows, and the process supplies the fires' steps
    inside its own deposit ([UexecSG.sbundle_at]); a generic slot's are paid
    from [app_sup].  The blanket promise "the claim survives ANY one-row
    move", which the dischargers used to read off the body, is gone: it was
    unpayable by any constraining application, and nothing needs it.
    Both are ONE lemma, [app_top_update], at a later-shaped step: the
    application's claim is an arbitrary iProp -- neither timeless nor
    persistent -- so it stays under the invariant's later and the step is
    applied there.  Only the authority comes out from under the later.

    THE STEP IS A BASIC UPDATE (seam I): [▷ app_pred av ==∗ ▷ app_pred av'],
    the update OUTSIDE the later, where it can run.  A claim whose survival
    of a move is a RESOURCE MOVE -- a counter bumped, a slot parked -- and
    not merely a rearrangement is then payable; a claim that only needs the
    rearrangement pays with a plain wand and lifts for free
    ([app_top_update_step], whose statement is update-free, and
    [app_step_acc] off the supply).  The seam is zero-semantic-change for
    every consumer: a proof that BUILDS a step gains an [iModIntro] and a
    proof that SPENDS one is unchanged.  What it does NOT do is create a
    resource -- it only lets a mover spend one it already holds
    ([AppTree.tree_bump_free_is_vacuous] is that lesson, in Rocq).

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
Require Import IcacheRefDefs.       (* [icfg_nib]: the inode region's width, for
                                   the body's DOMAIN row (round C) *)

Local Open Scope Z_scope.

Definition appN : namespace := nroot .@ "app".
Definition appE : coPset := ↑appN.

(* ------------------------------------------------------------------ *)
(*  1.  The raw credentials: at a predicate and an instance             *)
(* ------------------------------------------------------------------ *)

Section AppCredsRaw.
  Context {Σ : gFunctors}.

  (* ------------------------------------------------------------------ *)
  (*  1a.  THE SUPPLY: the claim holds of EVERY view                      *)
  (* ------------------------------------------------------------------ *)

  (* THE CREDENTIAL A PROCESS THAT ANSWERS FOR NOTHING RUNS ON (the ARM;
     claude-notes/projects/app-echo.md, "THE ARM, concretely").  It says
     the application's claim is TRIVIALLY TRUE -- it holds of every view at
     all -- which is what makes every view-moving commit's [app_step] free
     and is therefore what an UNVERIFIED program's syscall bundles are paid
     out of.  It is what [UexecSG.ssupply] is instantiated at
     ([UexecExecInst]).

     IT IS NOT PARKED IN [app_body] BELOW, and that is deliberate: the
     supply is a statement that the claim says nothing, which a
     CONSTRAINING application cannot make -- echo's is [taint ∨ pins],
     provable at every view only after the taint is minted.  An era mint
     that had to found it would be unfoundable for such an application.  So
     it travels as a PERSISTENT CREDENTIAL built where it is honest -- the
     GENERIC application's own discharge of the system theorem's
     [Hinit_boot] ([SystemAdequacy.init_boot_of_sup], which mints the
     generic slot on it) and the closed trap loop's generic instances --
     and it stays out of every era-owned resource and out of every kernel
     contract, so that a constraining application's own theorem simply does
     not carry it.

     RAW -- the predicate and the instance are ARGUMENTS -- so a holder can
     state it under [riscvGpreS], before the fixed record exists;
     [app_sup] below is the pinned form. *)
  Definition app_sup_raw {N : Type}
      (A : N -> aview -> iProp Σ) (r : N) : iProp Σ :=
    (□ (∀ av : aview, A r av))%I.

  Global Instance app_sup_raw_persistent {N} (A : N -> aview -> iProp Σ) r :
    Persistent (app_sup_raw A r).
  Proof using . rewrite /app_sup_raw. apply _. Qed.

  (* the generic application's: its predicate IS [True] *)
  Lemma app_sup_raw_triv {N} (A : N -> aview -> iProp Σ) (r : N) :
    (forall r av, A r av ⊣⊢ True) -> ⊢ app_sup_raw A r.
  Proof using .
    intros Htriv. rewrite /app_sup_raw. iIntros "!>" (av).
    iApply (bi.equiv_entails_1_2 _ _ (Htriv r av)). iPureIntro. exact Logic.I.
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
     ARGUMENT -- for [app_sup_raw]'s reason. *)
  Definition app_xfer_raw {N : Type} (A : N -> aview -> iProp Σ) : iProp Σ :=
    (□ (∀ (r : N) (av : aview),
          ▷ A r av ==∗ ▷ A r av ∗ ∃ r' : N, ▷ A r' av))%I.

  Global Instance app_xfer_raw_persistent {N} (A : N -> aview -> iProp Σ) :
    Persistent (app_xfer_raw A).
  Proof using . rewrite /app_xfer_raw. apply _. Qed.

  (* the generic application's: a predicate that holds of every view is its
     own copy (at the instance handed in, so no inhabitant is needed) *)
  Lemma app_xfer_raw_triv {N} (A : N -> aview -> iProp Σ) :
    (forall r av, A r av ⊣⊢ True) -> ⊢ app_xfer_raw A.
  Proof using .
    intros Htriv. rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iModIntro. iSplitL "H"; [iExact "H" |]. iExists r. iNext.
    iApply (bi.equiv_entails_1_2 _ _ (Htriv r av)). iPureIntro. exact Logic.I.
  Qed.

  (* a PURE claim duplicates outright *)
  Lemma app_xfer_raw_pure {N} (P : aview -> Prop) :
    ⊢ app_xfer_raw (fun (_ : N) (av : aview) => ⌜P av⌝%I).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "#H".
    iModIntro. iSplitR; [iExact "H" |]. iExists r. iExact "H".
  Qed.

  (* ...and the general law the pure one is an instance of: a claim that is
     PERSISTENT AT EVERY INSTANCE AND EVERY VIEW duplicates, so the copy at
     "fresh" names is the claim itself at the instance handed in.  This is
     a lemma about the TRANSPORT, not about any application: it covers a
     pure claim, a claim made of invariants, and -- what the echo
     application's [taint ∨ pins] is -- a disjunction of a persistent
     credential with a pure fact.  The later is stripped by nothing: [▷ P]
     is persistent whenever [P] is. *)
  Lemma app_xfer_raw_pers_or_pure {N} (A : N -> aview -> iProp Σ) :
    (forall (r : N) (av : aview), Persistent (A r av)) ->
    ⊢ app_xfer_raw A.
  Proof using .
    intros HP. rewrite /app_xfer_raw. iIntros "!>" (r av) "#H".
    iModIntro. iSplitR; [iExact "H" |]. iExists r. iExact "H".
  Qed.

End AppCredsRaw.

(* the merge's wand is LENT the machine's started auth (sync SY3-A1), so it
   needs the fixed record's class; nothing else in it does *)
Section AppMergeRaw.
  Context `{!riscvFixedGS Σ}.

  (* ------------------------------------------------------------------ *)
  (*  1c.  THE MERGE (sync design section 4, operation 2; SY3-K2)         *)
  (* ------------------------------------------------------------------ *)

  (* THE COMMIT'S LAW: the new durable copy is built from the running
     claim AND the old durable copy, so a durable-only resource (a share
     of a counter that travels with the durable copy) can move from the
     old copy to the new one instead of being dropped with it.

     CURRIED AT THE COLLECTION, because no one instant holds both: the
     running claim is in hand only where [appN] opens (the commit's
     collection, [FsCollectAll.fs_collect_dur]), the old copy only inside
     the header write's permit, at mask [∅]
     ([FsCrash.fs_commit_L_seq_permit]).  So the law runs on the running
     claim at the collection, gives it back, and hands out a WAND that
     turns the old copy into the new one when the permit applies it.
     Whatever the new copy needs of the running claim must be moved INTO
     the wand here -- persistent witnesses, or an exclusive share the
     running claim can spare.

     The old copy arrives as the crash slot holds it, [▷] over its
     existentials ([AppDur.app_dur_raw]), and is not stripped: a basic
     update cannot eliminate the [◇] that pulling an existential through
     a later costs.  RAW for [app_xfer_raw]'s reason.

     ...AND THE TOKEN [T] (sync K3-3, claude-notes/design/sync.md §4.3 item
     2): the application's opaque share the log invariant holds while no
     commit is in flight.  The collection hands it in with the running
     claim, and the law returns an ADDITIVE pair -- the wand that turns the
     old copy into the new one and gives the token back (the header
     write's permit applies it), or the token alone (the empty-log commit,
     which writes no header).  The token lets the law pin the running
     claim's share against the old copy's inside the wand; an application
     with nothing to pin passes it straight through
     ([app_merge_raw_of_xfer]).

     ...AND THE WAND IS LENT THE MACHINE'S STARTED AUTH (sync SY3-A1,
     design §4.5 "The merge"): [start_auth n] at [n = gd + 1], [gd] the
     era's generation, handed back untouched.  Only the WAND carries the
     loan -- it is the one arm that meets the old copy, whose era
     certificate the auth bounds; the collection that builds the wand
     runs without it.  [gd] is pinned to the era's [gen_id] by [app_merge]
     below.

     ...AND AT THE ERA'S RECORD PREDICATE [Ok] (SY3-A1 re-cut): a pure
     predicate on the application's instances that the era's running
     record satisfies and the new copy's record is born satisfying -- an
     application that cannot pin its running claim's era from ghost
     state reads it here (for the union, "this record's era field is the
     era's number").  The collection supplies [⌜Ok app_run⌝] off the pinned
     package [app_merge] below.
     ...AND AT THE DURABLE-COPY PREDICATE [Okc] (sync SY3-A3b, design
     §4.5 "The copy predicate"): what every record the crash slot holds
     satisfies ([AppDur.app_dur_raw]).  The old copy the wand consumes
     arrives with it, and the new copy's record is born satisfying it
     beside [Ok] -- so an application whose claim cannot tell a durable
     copy from a running claim by its ghost state alone (the union's role
     field) reads the difference here. *)
  Definition app_merge_raw {N : Type} (A : N -> aview -> iProp Σ)
      (Ok Okc : N -> Prop) (T : iProp Σ) (gd : nat) : iProp Σ :=
    (□ (∀ (r : N) (av : aview),
          ⌜Ok r⌝ -∗ ▷ A r av -∗ T ==∗ ▷ A r av ∗
          ∃ r' : N, ⌜Ok r'⌝ ∗ ⌜Okc r'⌝ ∗
            ((∀ n : nat, ⌜n = (gd + 1)%nat⌝ -∗ start_auth n -∗
                (▷ ∃ (r_o : N) (av_o : aview), ⌜Okc r_o⌝ ∗ A r_o av_o) ==∗
                ▷ A r' av ∗ T ∗ start_auth n)
             ∧ T)))%I.

  Global Instance app_merge_raw_persistent {N} (A : N -> aview -> iProp Σ)
      (Ok Okc : N -> Prop) (T : iProp Σ) (gd : nat) :
    Persistent (app_merge_raw A Ok Okc T gd).
  Proof using . rewrite /app_merge_raw. apply _. Qed.

  (* EVERY TRANSPORT IS A MERGE, AT ANY TOKEN AND ANY ERA: drop the old
     copy, copy the running claim, and hand the token and the loan back on
     either arm.  This is what every application with nothing to carry
     across the commit instantiates the merge with (the commit behaves as
     before).  AT A TOTAL [Ok] AND [Okc]: the transport's fresh instance
     is not known to satisfy anything, so an application whose record
     predicates say something writes its own merge. *)
  Lemma app_merge_raw_of_xfer {N} (A : N -> aview -> iProp Σ) (Ok Okc : N -> Prop)
      (T : iProp Σ) (gd : nat) :
    (forall r : N, Ok r) -> (forall r : N, Okc r) -> (⊢ app_xfer_raw A) ->
    ⊢ app_merge_raw A Ok Okc T gd.
  Proof using .
    intros HOk HOkc Hx. iPoseProof Hx as "#Hx".
    rewrite /app_xfer_raw /app_merge_raw. iIntros "!>" (r av) "_ Hp HT".
    iMod ("Hx" with "Hp") as "[Hp Hn]". iDestruct "Hn" as (r') "Hn".
    iModIntro. iFrame "Hp". iExists r'. iSplitR; [iPureIntro; apply HOk |].
    iSplitR; [iPureIntro; apply HOkc |].
    iSplit; [| iExact "HT"].
    iIntros (n _) "Hsa _". iModIntro. iFrame "Hn HT Hsa".
  Qed.

End AppMergeRaw.

(* the runner names the guest's half of the map's authority, so it needs the
   top map's ghost class; and it is a FANCY update at [∅] (an application's
   hook may strip the [◇] a timeless share under a later costs), so it
   needs the invariant class -- [riscvGS], for [AppInv]'s reason below *)
Section AppSyncRaw.
  Context `{!riscvGS Σ, !fsTopG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  1d.  THE SYNC RUNNER (sync design section 4.2-4.3; K3-3)            *)
  (* ------------------------------------------------------------------ *)

  (* THE ONE PLACE A SYNC HOOK'S MEANING IS USED.  A [sync] caller hands
     the kernel a hook [Hk Q] -- an opaque member of the application's hook
     family, which the WAL only moves -- and the GHOST COMMIT fires it
     where the new durable copy is built out of the running claim: with
     the fresh guest half, the new durable claim, the running claim and
     the token all at ONE map ([FsCollectAll.fs_collect_ghost]).  The hook
     returns every resource it is handed and yields its [Q].  A fupd at
     mask [∅]: it runs inside the collection, with the file system's
     invariants open.  The running claim's instance [r] is quantified
     here; the collection applies it at [app_run].  RAW for
     [app_xfer_raw]'s reason.  Both instances satisfy the era's record
     predicate [Ok] (SY3-A1 re-cut, [app_merge_raw]'s): the running one by
     the pinned package, the new copy's by the merge -- which also gives
     the new copy's the durable-copy predicate [Okc] (SY3-A3b), so a hook
     can tell the two instances' roles apart. *)
  Definition app_sync_run_raw {N : Type} (A : N -> aview -> iProp Σ)
      (Ok Okc : N -> Prop) (T : iProp Σ) (Hk : iProp Σ -> iProp Σ) : iProp Σ :=
    (□ (∀ (Q : iProp Σ) (gt : gname) (I : gmap Z fs_node) (r r' : N),
          ⌜Ok r⌝ -∗ ⌜Ok r'⌝ -∗ ⌜Okc r'⌝ -∗
          Hk Q -∗
          ghost_map_auth_frac gt (1/2) I -∗
          ▷ A r' (abs_view I) -∗
          ▷ A r (abs_view I) -∗
          T ={∅}=∗
            ghost_map_auth_frac gt (1/2) I ∗
            ▷ A r' (abs_view I) ∗
            ▷ A r (abs_view I) ∗
            T ∗ Q))%I.

  Global Instance app_sync_run_raw_persistent {N} (A : N -> aview -> iProp Σ)
      (Ok Okc : N -> Prop) (T : iProp Σ) (Hk : iProp Σ -> iProp Σ) :
    Persistent (app_sync_run_raw A Ok Okc T Hk).
  Proof using . rewrite /app_sync_run_raw. apply _. Qed.

  (* AN APPLICATION WITH NO SYNC LEDGER: every hook is its own [Q], and the
     runner hands it straight back. *)
  Lemma app_sync_run_raw_triv {N} (A : N -> aview -> iProp Σ) (Ok Okc : N -> Prop)
      (T : iProp Σ) (Hk : iProp Σ -> iProp Σ) :
    (forall Q : iProp Σ, Hk Q ⊣⊢ Q) -> ⊢ app_sync_run_raw A Ok Okc T Hk.
  Proof using .
    intros Hid. rewrite /app_sync_run_raw.
    iIntros "!>" (Q gt I r r') "_ _ _ HQ Hh Hn Hp HT". iModIntro.
    iFrame "Hh Hn Hp HT". iApply (bi.equiv_entails_1_1 _ _ (Hid Q)).
    iExact "HQ".
  Qed.

  (* ...FIRED ONCE PER HOOK: the collection's reading of a list of waiters'
     hooks, at any mask (the runner itself runs at [∅]).  Every resource
     comes back, and each hook's [Q] beside them. *)
  Lemma app_sync_run_list {N} (A : N -> aview -> iProp Σ) (Ok Okc : N -> Prop)
      (T : iProp Σ)
      (Hk : iProp Σ -> iProp Σ) (E : coPset) (Qs : list (iProp Σ))
      (gt : gname) (I : gmap Z fs_node) (r r' : N) :
    Ok r -> Ok r' -> Okc r' ->
    app_sync_run_raw A Ok Okc T Hk -∗
    ([∗ list] Q ∈ Qs, Hk Q) -∗
    ghost_map_auth_frac gt (1/2) I -∗
    ▷ A r' (abs_view I) -∗
    ▷ A r (abs_view I) -∗
    T ={E}=∗
      ghost_map_auth_frac gt (1/2) I ∗
      ▷ A r' (abs_view I) ∗
      ▷ A r (abs_view I) ∗
      T ∗ ([∗ list] Q ∈ Qs, Q).
  Proof using .
    intros Hr Hr' Hrc.
    induction Qs as [|Q Qs IH]; simpl.
    - iIntros "_ _ Hh Hn Hp HT". iModIntro. iFrame "Hh Hn Hp HT".
    - iIntros "#Hrun [HQ HQs] Hh Hn Hp HT".
      iMod (IH with "Hrun HQs Hh Hn Hp HT") as "(Hh & Hn & Hp & HT & HQs)".
      iMod (fupd_mask_subseteq ∅) as "Hcl"; [set_solver |].
      iMod ("Hrun" $! Q gt I r r' with "[//] [//] [//] HQ Hh Hn Hp HT")
        as "(Hh & Hn & Hp & HT & HQ)".
      iMod "Hcl" as "_". iModIntro. iFrame "Hh Hn Hp HT HQ HQs".
  Qed.
End AppSyncRaw.

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

  (* THE SUPPLY, PINNED: what the deposit class's [UexecSG.ssupply] is at
     the kernel's instance.  A CREDENTIAL, not a parked resource -- see
     [app_sup_raw] above for why it cannot live in [app_body]. *)
  Definition app_sup : iProp Σ := app_sup_raw app_pred app_run.

  Global Instance app_sup_persistent : Persistent app_sup.
  Proof using . rewrite /app_sup. apply _. Qed.

  Lemma app_sup_of_triv :
    (forall r av, app_pred r av ⊣⊢ True) -> ⊢ app_sup.
  Proof using . intros Htriv. rewrite /app_sup. by apply app_sup_raw_triv. Qed.

  (* THE READ CREDENTIAL (seccomp design §9, lane S0): what the console's
     dirty escrow ([ConsoleInv.cons_dirty_cred]) holds.  A tokenless
     console read is paid by EITHER the supply -- the generic reader, which
     pays [app_sup] ([app_rdcred_of_sup]) -- OR the era's WILD credential
     ([RiscvPtsto.riscv_rdwild], [app_rdcred_of_rdwild]) -- the READER-side
     one, split off the write licence [riscv_wild] (seccomp design 10.7):
     the dirty outcome hands this credential to whichever reader finds
     the marker moved, the shell included.  Only the ESCROWED
     proposition widens: the generic tier's supply law still pays
     [app_sup].  The era is the one the escrow is allocated in
     ([ProofMain]), and the reader's console era is [S gen_id] -- the
     index of [WpUart.cons_read_pay] at the same read. *)
  Context {GEN : RiscvLang.GenId}.

  Definition app_rdcred : iProp Σ :=
    (app_sup ∨ riscv_rdwild (S RiscvLang.gen_id))%I.

  Global Instance app_rdcred_persistent : Persistent app_rdcred.
  Proof using . rewrite /app_rdcred. apply _. Qed.

  Lemma app_rdcred_of_sup : app_sup -∗ app_rdcred.
  Proof using . rewrite /app_rdcred. iIntros "H". by iLeft. Qed.

  Lemma app_rdcred_of_rdwild : riscv_rdwild (S RiscvLang.gen_id) -∗ app_rdcred.
  Proof using . rewrite /app_rdcred. iIntros "H". by iRight. Qed.

  (* ...and its elimination at a Coq-level reading of each arm, which is
     the shape the shell tier's dirty arm spends it at *)
  Lemma app_rdcred_elim (T : iProp Σ) :
    (⊢ app_sup -∗ T) -> (⊢ riscv_rdwild (S RiscvLang.gen_id) -∗ T) ->
    ⊢ app_rdcred -∗ T.
  Proof using .
    intros Hs Hw. rewrite /app_rdcred.
    iIntros "[H | H]"; [by iApply Hs | by iApply Hw].
  Qed.

  (* THE ERA'S DURABILITY LAWS, PINNED, AS ONE PACKAGE: the merge (round
     C's transport; the merge since SY3-K2) and the sync runner (K3-3), at
     the era's sync token and hook family -- the two slots of the fixed
     record ([RiscvPtsto.riscv_sync_tok]/[riscv_sync_hook]) -- and the era's
     generation (the loan's bound, SY3-A1), both at ONE record predicate
     [Ok] that the era's running record satisfies (SY3-A1 re-cut).  ONE
     package because the two laws must agree on [Ok]; the predicate is
     EXISTENTIAL so that [appcfg] need not carry it.  The application-side
     premise of the era mint, which hands it to fsinit on the kit, where
     the commit's law and the hooked law are built out of it
     ([FsCollectAll.fs_snap_law_build]/[fs_snap_law_ghost_build]).
     AT THE DURABLE-COPY PREDICATE [Okc] (sync SY3-A3b): the crash slot's
     guest is stated at it ([AppDur.app_dur_raw]), so it is the package's
     PARAMETER, and [AppDur.app_dur_laws] closes it existentially together
     with the crash seam at the same guest. *)
  Definition app_merge (Okc : app_names -> Prop) : iProp Σ :=
    (∃ Ok : app_names -> Prop, ⌜Ok app_run⌝ ∗
       app_merge_raw app_pred Ok Okc (riscv_sync_tok RiscvLang.gen_id)
         RiscvLang.gen_id ∗
       app_sync_run_raw app_pred Ok Okc (riscv_sync_tok RiscvLang.gen_id)
         (riscv_sync_hook RiscvLang.gen_id))%I.

  Global Instance app_merge_persistent Okc : Persistent (app_merge Okc).
  Proof using . rewrite /app_merge. apply _. Qed.

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
  Proof using .
    intros Hi Hd z. rewrite lookup_insert_is_Some'. rewrite -(Hd z).
    split; [| by right]. intros [-> | H]; [by eexists | exact H].
  Qed.

  (* THE BODY: the application's half of the authority, the claim about the
     map it carries (read through the view) and the domain row.  NOT
     timeless: the claim is an arbitrary iProp and stays under the later.
     THE MERGE IS NOT PARKED HERE (sync K3-3): it is pinned at the era's
     token ([app_merge] above), so parking it would make the invariant --
     and every bundle that carries it -- depend on the era; and nothing
     read it here anyway (a fupd under the invariant's later cannot run
     without a step).  The commit takes [app_merge] off fsinit's kit. *)
  Definition app_body (γfs : fs_names) : iProp Σ :=
    (∃ I : gmap Z fs_node,
       ghost_map_auth_frac (fs_top γfs) (1/2) I ∗
       app_pred app_run (abs_view I) ∗
       ⌜app_dom I⌝)%I.

  Definition app_inv (γfs : fs_names) : iProp Σ := inv appN (app_body γfs).

  Global Instance app_inv_persistent γfs : Persistent (app_inv γfs).
  Proof using . rewrite /app_inv. apply _. Qed.

  (* ALLOCATION, at the era mint: the guest half of the authority the boot
     founded, the claim at the founded map -- LATER-SHAPED, because it
     arrives from the durable instance through the transport (round C) and
     [inv_alloc] takes the later -- and the domain row. *)
  Lemma app_inv_alloc (γfs : fs_names) (I : gmap Z fs_node) (E : coPset) :
    app_dom I ->
    ghost_map_auth_frac (fs_top γfs) (1/2) I -∗
    ▷ app_pred app_run (abs_view I) -∗ |={E}=> app_inv γfs.
  Proof using .
    iIntros (Hd) "Hh Hp". rewrite /app_inv.
    iApply (inv_alloc appN E with "[Hh Hp]").
    iNext. rewrite /app_body. iExists I. iFrame "Hh Hp".
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
     which sees the old claim there, [▷]-shaped, and owes the new one
     [▷]-shaped.  The three forms below are its readings. *)
  Lemma app_top_update (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    (⌜I !! i = Some n⌝ -∗
       ▷ app_pred app_run (abs_view I) ==∗
       ▷ app_pred app_run (abs_view (<[i := n']> I))) -∗
    ghost_map_auth_frac (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth_frac (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof using .
    iIntros (HE) "#Hinv Hstep Hk Hf".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hd)".
    iDestruct (ghost_map_auth_agree with "Hk Hh") as %<-.
    iDestruct (ghost_map_lookup with "Hk Hf") as %Hi.
    iAssert (ghost_map_auth_frac (fs_top γfs) 1 I) with "[Hk Hh]" as "Hk".
    { iEval (rewrite -Qp.half_half). iSplitL "Hk"; [iExact "Hk" | iExact "Hh"]. }
    iMod (ghost_map_update n' with "Hk Hf") as "[Hk Hf]".
    iDestruct "Hk" as "[Hk Hh]".
    iMod ("Hstep" with "[//] Hp") as "Hp".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists (<[i := n']> I). iFrame "Hh Hp".
      iPureIntro. exact (app_dom_insert I i n n' Hi Hd). }
    iModIntro. iFrame "Hk Hf".
  Qed.

  (* [_same]: the reading is unchanged, so the claim is *)
  Lemma app_top_update_same (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    abs_of n = abs_of n' ->
    app_inv γfs -∗
    ghost_map_auth_frac (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth_frac (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof using .
    iIntros (HE Habs) "#Hinv Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [] Hk Hf").
    iIntros (Hi) "Hp". iModIntro.
    rewrite (abs_view_insert_same I i n n' Hi Habs). iExact "Hp".
  Qed.

  (* [_step]: the caller pays, with a plain wand -- it lifts under the later *)
  Lemma app_top_update_step (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    (app_pred app_run (abs_view I) -∗
       app_pred app_run (abs_view (<[i := n']> I))) -∗
    ghost_map_auth_frac (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth_frac (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof using .
    iIntros (HE) "#Hinv Hstep Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [Hstep] Hk Hf").
    iIntros (Hi) "Hp". iModIntro. iNext. iApply ("Hstep" with "Hp").
  Qed.

  (* ...AND ITS [==∗] TWIN (seam I).  The step [app_top_update] takes is now
     an UPDATE under the later, so a caller may pay the move with a ghost
     move of its own -- which is the whole content of the seam: a claim
     whose survival of a move is a RESOURCE MOVE (a counter bumped, a slot
     parked) and not merely a rearrangement can now be an [app_step].  The
     update is OUTSIDE the later, where a basic update can run; a wand
     under the later is the [_step] form above and lifts into this one. *)
  Lemma app_top_update_bupd (E : coPset) (γfs : fs_names) (I : gmap Z fs_node)
      (i : Z) (n n' : fs_node) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    (▷ app_pred app_run (abs_view I) ==∗
       ▷ app_pred app_run (abs_view (<[i := n']> I))) -∗
    ghost_map_auth_frac (fs_top γfs) (1/2) I -∗ i ↪[fs_top γfs] n ={E}=∗
      ghost_map_auth_frac (fs_top γfs) (1/2) (<[i := n']> I) ∗ i ↪[fs_top γfs] n'.
  Proof using .
    iIntros (HE) "#Hinv Hstep Hk Hf".
    iApply (app_top_update E γfs I i n n' HE with "Hinv [Hstep] Hk Hf").
    iIntros (Hi) "Hp". iApply ("Hstep" with "Hp").
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
     (section 6, ruling 5).  A generic discharger pays it out of the SUPPLY
     ([app_step_acc]), whose conclusion it reads straight under the later. *)
  Definition app_step (i : Z) (I : gmap Z fs_node) (av' : aview) : iProp Σ :=
    (∀ n' : fs_node,
       ⌜abs_view (<[i := n']> I) = av'⌝ -∗
       ▷ app_pred app_run (abs_view I) ==∗
       ▷ app_pred app_run (abs_view (<[i := n']> I)))%I.

  (* the fire's reading: at the node it chose *)
  Lemma app_step_at (i : Z) (I : gmap Z fs_node) (av' : aview) (n' : fs_node) :
    abs_view (<[i := n']> I) = av' ->
    app_step i I av' -∗
    ▷ app_pred app_run (abs_view I) ==∗
    ▷ app_pred app_run (abs_view (<[i := n']> I)).
  Proof using .
    intros Heq. iIntros "Hstep Hp". rewrite /app_step.
    iApply ("Hstep" $! n' with "[//] Hp").
  Qed.

  (* THE IDENTITY STEP (E2-V2): a move that leaves the view where it is
     owes the application nothing.  It is the arm every counted commit takes
     at a row the view does not have -- the write to, the truncation of, an
     unlinked-but-open file -- and it needs nothing from the application:
     the reading is the same map. *)
  Lemma app_step_id (i : Z) (I : gmap Z fs_node) :
    ⊢ app_step i I (abs_view I).
  Proof using .
    rewrite /app_step. iIntros (n' Heq) "Hp". rewrite Heq. iModIntro.
    iExact "Hp".
  Qed.

  (* AN UPDATE OF THE CLAIM THAT DOES NOT MOVE THE MAP (lane E2 / SH-OPEN).
     [app_top_update] is for a party that HOLDS half the authority and is
     moving a row; this is for one that holds neither and only wants to
     trade a resource against the claim AT WHATEVER VIEW the invariant is
     at -- /init's failed [mknod] spending its console key for the
     persistent SEAL ([AppEcho.echo_cons_seal_step]).  The map is put back
     unchanged, so no [app_dom] obligation and no [app_step] arise.

     THE LATER IS THE CALLER'S: the body is under one and only the caller
     knows whether its own claim is timeless (echo's is), so the wand is
     handed [▷ app_pred] and owes [▷ app_pred] back. *)
  Lemma app_claim_update (E : coPset) (γfs : fs_names) (R Q : iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    □ (∀ av : aview, R -∗ ▷ app_pred app_run av ={E ∖ ↑appN}=∗
         ▷ app_pred app_run av ∗ Q) -∗
    R ={E}=∗ Q.
  Proof using .
    iIntros (HE) "#Hinv #Hstep HR".
    iMod (inv_acc E appN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(>Hh & Hp & >%Hd)".
    iMod ("Hstep" $! (abs_view I) with "HR Hp") as "[Hp HQ]".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp".
      iPureIntro. exact Hd. }
    iModIntro. iExact "HQ".
  Qed.

  (* THE STEP, OFF THE SUPPLY.  A claim that holds of every view survives
     every move of the map, so a discharger holding [app_sup] pays a
     write-kind commit's [app_step] by throwing the pre-view claim away and
     reading the post-view one straight off the credential.  There is no
     side condition left, and that is why this is ONE lemma: the retired
     license form promised only what a one-row MOVE preserves, so it needed
     the row to EXIST and a second reading beside it for the moves at a row
     the view does not have.  The supply needs neither. *)
  Lemma app_step_acc (i : Z) (I : gmap Z fs_node) (av' : aview) :
    app_sup -∗ app_step i I av'.
  Proof using .
    iIntros "#Hs". rewrite /app_step. iIntros (n' Heq) "_". iModIntro. iNext.
    rewrite /app_sup /app_sup_raw. iApply "Hs".
  Qed.

End AppInv.
