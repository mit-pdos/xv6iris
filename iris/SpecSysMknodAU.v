(* SpecSysMknodAU.v -- sys_mknod's ATOMIC-UPDATE contract, stated over the
   campaign's abstract state.  A STATEMENT FILE: definitions, trivial
   structural lemmas, and a [Module Type] seal -- no walk, no proof against
   the machine.

   ===== TOMBSTONE (fs-syscall-specs, THE DVIEW RETIREMENT, 2026-08-30) =====
   THE CONTRACT HALF OF THIS FILE IS RETIRED, and only that half: everything
   this file stated over [FsAbs.ax_hop dv_half] went with the [dview] column
   ([mknod_walk_pre], [mknod_walk_dead], the AU bundle and post arms, the
   stable arms, the machine frame and body, and [Module Type SYSMKNOD_AU]).
   The full list, with what replaced each and why the vocabulary could not
   follow it out of the build, is at the section 2b tombstone below.  What is
   sealed and consumed is [SpecSysMknodAUEra]'s [SYSMKNOD_AU_ERA] over the era
   walk.  Read the prose below as HISTORY wherever it says [dv_half],
   [nx_hop] or [wp_namei_tr].
   =========================================================================

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   (v3) and section 7's mknod row; lane W of
   claude-notes/projects/fs-syscall-specs.md.  The abstract vocabulary is
   FsAbs.v (lane A, landed): [anode]/[abs_of], [aview], [nview],
   [astate Γ av], [apath_at], and the [ftop_astate_acc]/[ftop_astate_ro]
   accessors this contract's fire points are shaped for.

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysMknod.wp_sys_mknod_sconf] (R10: the
   landed contract does not move).  Same calling convention, same ambient
   premises, same threaded resources; what is NEW is that the caller hands
   in commit steps fired at the syscall's linearization instants against
   the ONE abstract state, and the postcondition ties the returned a0 to
   which arm fired -- the doc's AU strength ("no client resources
   required; the post relates RETURN VALUES to the values OBSERVED AT THE
   INSTANT").

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY.  No durable clause of any kind appears below
   -- no [flushed], no snapshot, no batch (doc section 5: durability is
   three GLOBAL principles a consumer applies only at crash points, and
   the per-node certificates live in FsDurSyscall.v).  And nothing about
   the intermediate states create passes through: the child is minted
   (free record -> device record, unreachable orphan) STRICTLY BEFORE the
   entry insert, and that mint is an ordinary state change a concurrent
   observer may see -- exactly the honesty stance the doc takes for
   sys_write's chunks.  The spec does not pretend otherwise; see THE
   FRESHNESS SHAPE below.

   ==== THE DELTA, AND THE FRESHNESS SHAPE (deviation from doc sec. 4) ==

   [delta_create d nm i c av] is the doc's fused delta, type-parameterized
   in the child's [absnode] [c] so mkdir ([ADir] with dots, parent bump)
   and open(O_CREATE) ([AFile []]) reuse it verbatim; [acre_bump] is the
   mkdir-only parent-nlink increment, fused as the doc asks.

   The doc's sketch writes the success arm as [∃ i ∉ dom av].  That is
   NOT statable over the landed [astate]: the gtop authority carries a row
   for EVERY inum of the region (free records read as bare nodes), so
   [dom av] is the whole region and no inum is ever outside it.  The
   honest per-instant condition -- and the one the machine actually
   realizes -- is [cre_pre]'s third conjunct: at the fire instant the row
   at [i] ALREADY reads as the freshly-minted child ([MkAnode c 1], the
   orphan create built before dirlink runs).  Under that observation the
   fused delta COLLAPSES to the one-row parent insert ([delta_create_dev]
   -- [insert_id] on the child's row), which is why ONE ghost move at ONE
   instant realizes it: the fire point is dirlink's successful entry
   write, the only retag the delta needs.

   What the success arm therefore does NOT claim is "i was free at the
   start of the call".  Its freshness content is: the child's row reads
   [ADev ma mi] at nlink 1 at the instant, and the parent's entry map did
   not contain [nm].  A client that needs "i is none of MY nodes" gets it
   from agreement: its own pinned values are visible in the SAME [av]
   (the lend), so any pinned node whose value differs from the child's is
   not [i].  A stronger two-instant form (observe the mint too) needs a
   rollback-honest FAIL arm (create's fail: tail un-mints the child) and
   is deferred until a consumer needs it -- recorded as open question 1.

   ==== THE COMMIT SHAPE, AND WHERE THE MASK SITS ======================

   [acre_commit] is a TWO-PHASE HOCAP step, shaped for the accessor pair
   FsAbs section 5 provides.  The prover's sequence at the fire point:
   open [ftopN], [ftop_astate_acc] borrows [astate (fs_gamma_L γfs) av]
   out of [ftop_body]; fire phase 1 (the caller observes the pre-state --
   agreement against caller-held [nview] shares happens HERE); perform
   the one [ghost_map_update] of the parent's row (the element is
   assembled from the write-locked payload's custody); fire phase 2 (the
   caller WITNESSES the post-state authority at
   [delta_create d nm i c av]); pay the give-back wand's ROW OBLIGATION
   ([inode_local] at every entry -- the same obligation
   [InodeRegion.ireg_top_retag] charges every mover); close [ftopN].
   Both phases are inside one invariant-open critical section, so the
   pair is ONE instant to every other party.

   THE MASK IS THE FLOOR [∅].  The commit definitions take [E] for reuse,
   and the machine contract instantiates [E := ∅]: a mask-∅ fupd can be
   fired by the prover under WHATEVER invariants are open at the retag
   point ([ftopN] certainly; possibly more), and it suffices for
   everything a caller is expected to do at the instant -- ghost updates
   are basic updates, and agreement ([astate_nview]) is mask-free.  A
   client that must open its OWN invariant at the instant asks for a
   masked variant later (a new parallel form; R10).

   [dlookup_commit] is the single-phase read-only sibling, fired at
   dirlookup's found instant (under the parent's lock, off
   [ftop_astate_ro] -- the caller hands the SAME authority back and no
   row obligation arises).

   ==== THE PATH: THE TRACE, QUANTIFIED OVER THE FETCHED STRING ========
   (RETIRED 2026-08-30 with the dview column -- history, kept because the
   era contract's walk premise is this one with the lend substituted.)

   The path vocabulary is the landed ghost-trace hop, spelled
   [FsAbs.ax_hop dv_half] -- BY THE CHECKED CLAIM in FsAbs's header this
   IS [SpecNameiTr.nx_hop] on the nose, so the eventual walk fires the
   same lends [wp_namei_tr]'s does.  Two mknod-specific points:

   - THE HOP FAMILY COVERS THE PARENT PREFIX ONLY
     ([mknod_parent_elems pl = removelast (path_elems pl)]): create
     resolves with nameiparent, which fires dirlookup on every element
     but the last; the LAST element is the created NAME, tied in the
     post by [last (path_elems pl) = Some nm] (SpecNamex's bname ruling
     makes the tie provable).

   - THE CONTRACT QUANTIFIES OVER THE FETCHED PATH.  sys_mknod reads its
     path from USER memory, and the kernel contracts deliberately say
     nothing about which bytes arrive (SpecFetchstr: "they came from user
     memory; [bb_cstr] is all a kernel caller can use").  So no premise
     can pin the path, and [mknod_walk_pre] is instead a ONE-SHOT
     universal: the walk instantiates it once at the string it fetched,
     and the post EXPOSES that string existentially.  A caller that wants
     path-specific receipts keys its cursor ghosts on the [pl] it is
     handed (the ghost-var cursor of SpecNameiTr section 3 works
     verbatim).  The start fact is honest about relative paths: an
     absolute path pins the start to [FsImg.ROOTINO]; a relative one
     starts at the cwd inode, which has no exposed inum reading yet
     (SpecNameiTr's Q-c), so the caller learns only the inum the walk
     names.

   ==== THE ARMS ========================================================

   ret 0  -- the walk completed (cursor [P Lp d] returned at the parent),
             the exists-lookup MISSED, and [acre_commit] fired at [d]
             with the name [nm], the child [i], and [cre_pre] restated
             purely beside the caller's own [Φok] receipt; the unfired
             [dlookup_commit] is refunded.
   ret -1 -- the honest fold of SpecSysMknod's own blanket disjunction,
             with the caller's residue returned:
             (i)   nothing fs-visible happened (argstr failed): the whole
                   AU bundle comes back unspent;
             (ii)  the walk died at hop [k] (miss, non-directory cursor,
                   or namex's nlink guard): wp_namei_tr's refund shape --
                   [P k d] with hops from [k], or [Pmiss k d] with hops
                   from [S k] -- both commits back;
             (iii) the walk reached the parent and create failed there:
                   cursor [P Lp d] back, the success commit back, and
                   EITHER the exists-observation fired ([Φex]: the name
                   was present -- mknod's ty is T_DEVICE, so xv6's
                   open-not-fail arm never applies and exists is always a
                   failure) OR the lookup commit back (create's nlink-0
                   guard, out-of-inodes, dirlink failure, and the
                   empty-final-name path "/" -- arms with no abstract
                   observation to report; -1 deliberately does not say
                   which, matching the machine contract's "DETERMINISM:
                   none").

   ==== THE TWO STRENGTHS ==============================================

   [wp_sys_mknod_au] is the AU form.  [wp_sys_mknod_au_stable] is the
   stable corollary's STATEMENT (derivation owed by the sealer, expected
   FROM the AU form + agreement, never as a second walk): the client
   presents [apn_pins] -- [nview] shares along its expected absolute
   path's CHAIN -- and on a fetch that matches, the observed parent IS
   the client's expected one ([apath_at] names it) and the commit
   receipts land at that inum.  Three deliberate limits, each forced by
   the landed discipline:

   - THE PARENT CARRIES NO PIN.  A held [nview] share pins its row
     against every mover ([ireg_top_retag] needs the whole element), so a
     client share on the PARENT would make the success retag impossible
     and the success arm unprovable.  The chain directories are only
     READ, so chain pins are compatible with success; the guard premise
     [dpar ∉ take Lp ds] keeps cyclic tails ("/a/..", trailing dots)
     from smuggling the parent into the chain.
   - THE COLLAPSE IS CONDITIONED ON THE FETCH.  No user-memory tie
     exists at this altitude (see above), so each arm splits on whether
     the fetched string's elements matched the client's [pl0] (and was
     absolute); on a mismatch the receipts come back unlocated.
   - PINS ARE NOT RETURNED.  The landed [apn_hop] spends its pin into
     the walk; a pin-returning refinement is future work, and no
     cross-syscall pin producer exists yet anyway (the shares are
     borrow-scoped today; the tree layer at the adequacy altitude is
     where long-lived pins will come from).  SHARPER, as of lane A(iii)'s
     seam finding (FsAbsSeam, f11b41c2b13): the payload arms hold
     [top_frag] WHOLE, so an [apn_pin] against a live inum is today
     INCONSISTENT with the walk's own custody ([apn_pin_loaded_excl]) --
     the stable form below is the FUTURE-facing statement, partially
     vacuous until the payload decision (a 3/4-arm with a client quarter,
     or a second walk lending the era fragment) lands.

   ==== WHAT THE PROVER OWES ===========================================

   1. The fire points: [dlookup_commit] inside create's dirlookup(found)
      under the parent's lock via [ftop_astate_ro]; [acre_commit]'s two
      phases around the parent-row [ghost_map_update] at dirlink's
      successful entry write via [ftop_astate_acc], including the
      give-back's [inode_local] row obligation.
   2. The reading bridge at the update: [abs_view] of the updated raw map
      equals the delta -- [abs_view_insert] plus the REAL half, that the
      written parent record's [dir_entries] is [<[nm := i]> ents]
      (dir_view first-match over the appended/reused slot; the
      [dv_lookup_found]-style bridge restated over the write).
   3. The trace walk for NAMEIPARENT: no nameiparent trace contract is
      landed ([SpecNameiTr] covers namei only; its header defers the
      variant) -- the prover owes a [wp_namei_tr]-style re-walk of
      nameiparent firing this file's hop family, and the name tie
      [last (path_elems pl) = Some nm] via SpecNamex's bname ruling.
   4. The child's value: create's post gives the record
      ([SpecCreate.create_made] on the non-directory arm);
      [abs_of_create_dev] turns it into the abstract child, and the
      halfword tie [bv_unsigned major = dev_arg v1] (create's lh/sh pair
      keeps exactly the low 16 bits of the argint'd word) is bit-level
      work at the walk.
   5. The stable corollary, derived from the AU form by instantiating
      the cursor with pins + a match-tracking ghost (its binder list
      carries [ghost_varG Σ (nat * Z)] for exactly this).

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. Two-instant freshness (observe the mint): wanted, or is the
      minted-orphan observation + agreement enough for the tree layer?
      (Costs a rollback-honest FAIL arm.)
   2. The commit mask floor [∅]: fine for the anticipated consumers
      (ghost receipts, agreement); confirm no first consumer needs its
      own invariant open at the instant.
   3. The stable form returns no pins (landed [apn_hop] spends them);
      schedule a pin-returning refinement with the tree layer, or leave
      until a producer of cross-syscall pins exists?

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (the SpecCreate
   header's argument, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields.  The live Γ is
   [FsBytesGamma.fs_gamma_L fsc_fs]; its gname tie to [ftop_body]'s
   authority is definitional ([FsAbs.ftop_gamma_top], by reflexivity). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheEscrow.   (* the escrow's vocabulary (it was [dv_half]'s
                                  route here before the dview retirement) *)
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecCreate.      (* [create_slots], [T_DEVICE], [create_made] *)
Require Import SpecSysMknod.    (* K_sys_mknod; the landed contract this
                                   file states a parallel form beside *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname] *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   ([sb_ninodes] : fs_sb -> Z) would shadow
                                   the superblock CELL ADDRESSES the frame
                                   below threads *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbs.           (* the abstract state (lane A, landed) *)
Require Import FsStateDefs.    (* [fs_gamma_L]: the live Γ *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS SIDE CONDITIONS (PURE)                          *)
(* ===================================================================== *)

(* the device-number reading of a syscall argument word: argint keeps the
   low int, create's lh/sh pair keeps the low HALFWORD, and the record
   field reads back unsigned -- so the abstract child's number is the low
   sixteen bits of the trapframe word, read unsigned *)
Definition dev_arg (v : mword 64) : Z := (bv_unsigned v) mod (2 ^ 16).

Lemma dev_arg_range (v : mword 64) : 0 <= dev_arg v < 2 ^ 16.
Proof. apply Z.mod_pos_bound. lia. Qed.

(* mkdir's fused parent bump (doc section 4: "mkdir additionally:
   d.nlink+1 -- fused, one delta"); zero for every other child kind *)
Definition acre_bump (c : absnode) : nat :=
  match c with ADir _ => 1%nat | _ => 0%nat end.

(* THE DELTA (doc section 4's [δ_create], type-parameterized): the parent
   gains [nm ↦ i], the child's row becomes [c] at nlink 1, and a
   directory child bumps the parent's nlink.  Total on purpose -- applied
   where the parent is not a directory it is the identity; the side
   conditions live in [cre_pre], not in the function. *)
Definition delta_create (d : Z) (nm : fname) (i : Z) (c : absnode)
    (av : aview) : aview :=
  match av !! d with
  | Some a =>
      match an_node a with
      | ADir ents =>
          <[i := MkAnode c 1%nat]>
            (<[d := MkAnode (ADir (<[nm := i]> ents))
                            (an_nlink a + acre_bump c)%nat]> av)
      | _ => av
      end
  | None => av
  end.

(* THE SIDE CONDITIONS, as one proposition: the parent is a directory
   whose map lacks the name, and the child's row already reads as the
   freshly-minted node (see the header's FRESHNESS SHAPE) *)
Definition cre_pre (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) : Prop :=
  av !! d = Some (MkAnode (ADir ents) nl)
  /\ ents !! nm = None
  /\ av !! i = Some (MkAnode c 1%nat).

(* a non-directory child forces parent <> child: their observed rows
   differ *)
Lemma cre_pre_ne (av : aview) (d : Z) (nm : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (c : absnode) :
  cre_pre av d nm ents nl i c -> (forall e, c <> ADir e) -> d <> i.
Proof.
  intros (Hd & _ & Hi) Hc Heq. subst i. rewrite Hd in Hi.
  injection Hi as Hc' _. exact (Hc ents (eq_sym Hc')).
Qed.

(* the delta's row algebra -- the caller-facing readings unlink and write
   will restate in their own vocabulary *)
Lemma delta_create_parent (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  av !! d = Some (MkAnode (ADir ents) nl) -> d <> i ->
  delta_create d nm i c av !! d
  = Some (MkAnode (ADir (<[nm := i]> ents)) (nl + acre_bump c)%nat).
Proof.
  intros Hd Hne. rewrite /delta_create Hd /=.
  rewrite lookup_insert_ne; [| congruence].
  by rewrite lookup_insert.
Qed.

Lemma delta_create_child (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  av !! d = Some (MkAnode (ADir ents) nl) ->
  delta_create d nm i c av !! i = Some (MkAnode c 1%nat).
Proof. intros Hd. rewrite /delta_create Hd /=. by rewrite lookup_insert. Qed.

Lemma delta_create_other (av : aview) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (j : Z) :
  j <> d -> j <> i -> delta_create d nm i c av !! j = av !! j.
Proof.
  intros Hjd Hji. rewrite /delta_create.
  destruct (av !! d) as [a |]; [| done].
  destruct (an_node a) as [bs | ents0 | ma0 mi0]; [done | | done].
  rewrite lookup_insert_ne; [| congruence].
  by rewrite lookup_insert_ne; [| congruence].
Qed.

(* THE COLLAPSE (the header's freshness argument, machine-checked): under
   [cre_pre] with a device child, the fused delta IS the one-row parent
   insert -- the child's insert is the identity on its already-minted
   row.  This is what makes the AU dischargeable at ONE instant. *)
Lemma delta_create_dev (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (ma mi : Z) :
  cre_pre av d nm ents nl i (ADev ma mi) ->
  delta_create d nm i (ADev ma mi) av
  = <[d := MkAnode (ADir (<[nm := i]> ents)) nl]> av.
Proof.
  intros Hp.
  assert (Hne : d <> i).
  { eapply (cre_pre_ne av d nm ents nl i); [exact Hp |].
    intros e He. discriminate He. }
  destruct Hp as (Hd & Hnm & Hi).
  rewrite /delta_create Hd /= Nat.add_0_r.
  rewrite (insert_commute _ i d); [| congruence].
  by rewrite (insert_id av i (MkAnode (ADev ma mi) 1%nat) Hi).
Qed.

(* the reading bridge's trivial half (the prover's item 2): pushing one
   raw-map insert through [abs_view] *)
Lemma abs_view_insert (I : gmap Z fs_node) (d : Z) (n : fs_node) :
  abs_view (<[d := n]> I) = <[d := abs_of n]> (abs_view I).
Proof. apply fmap_insert. Qed.

(* the abstract child create's non-directory success arm leaves behind:
   [SpecCreate.create_made] read through [abs_of] *)
Lemma abs_of_create_dev (n : fs_node) (major minor : mword 16) :
  fn_rec n = create_made T_DEVICE major minor ->
  abs_of n
  = MkAnode (ADev (bv_unsigned major) (bv_unsigned minor)) 1%nat.
Proof.
  intros Hr.
  rewrite /abs_of /abs_node /fn_is_dir /fn_type /fn_major /fn_minor
          /fn_nlink Hr.
  reflexivity.
Qed.

(* nameiparent's hop names: every element but the last (the last is the
   created NAME, tied in the post arms) *)
Definition mknod_parent_elems (pl : list (bv 8)) : list fname :=
  removelast (path_elems pl).

(* ===================================================================== *)
(*  2.  THE COMMITS, THE WALK PACKAGE, AND THE ARMS                       *)
(* ===================================================================== *)

Section SysMknodAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The two commit steps                                          *)
  (* ------------------------------------------------------------------ *)

  (* THE SUCCESS COMMIT, two-phase (see the header: shaped for
     [ftop_astate_acc]).  Phase 1 lends the pre-state at the instant --
     agreement happens here; phase 2 lends the post-state authority, so
     the caller WITNESSES that the delta was applied.  Both at mask [E];
     the machine contract instantiates the floor [∅]. *)
  Definition acre_commit Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜cre_pre av d nm ents nl i c⌝ -∗
       astate Γ av ={E}=∗
       astate Γ av ∗
         (astate Γ (delta_create d nm i c av) ={E}=∗
          astate Γ (delta_create d nm i c av) ∗ Φ av d nm i))%I.

  (* THE FOUND OBSERVATION, single-phase and read-only: dirlookup found
     [nm ↦ i] in the locked parent at the instant; the state does not
     move ([ftop_astate_ro]'s shape).  Reusable verbatim by unlink and
     open. *)
  Definition dlookup_commit Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = Some i⌝ -∗
       astate Γ av ={E}=∗ astate Γ av ∗ Φ av d nm i)%I.

  (* sanity: both commits are satisfiable with the trivial receipt (the
     module type below cannot be vacuously blocked on the caller side) *)
  Lemma acre_commit_unit Γ E c :
    ⊢ acre_commit Γ E c (fun _ _ _ _ => True%I).
  Proof.
    rewrite /acre_commit. iIntros (av d i nm ents nl) "%Hpre Hst".
    iModIntro. iFrame "Hst". iIntros "Hst'". iModIntro. by iFrame "Hst'".
  Qed.

  Lemma dlookup_commit_unit Γ E :
    ⊢ dlookup_commit Γ E (fun _ _ _ _ => True%I).
  Proof.
    rewrite /dlookup_commit. iIntros (av d i nm ents nl) "%Hd %Hlk Hst".
    iModIntro. by iFrame "Hst".
  Qed.

  (* THE STABLE SEEDS: a caller-held [nview] share turns either commit's
     "some value" into "YOUR value" -- the doc's agreement corollary at
     the instant, discharged here once so the stable form's derivation is
     assembly rather than proof.  Note what [acre_commit_pinned] does NOT
     offer: a pin on the PARENT (the delta's own row) -- a held share
     there makes the success retag impossible (header, stable limits). *)
  Lemma dlookup_commit_pinned Γ E (q : Qp) (dpin : Z) (a : anode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    nview Γ q dpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜d = dpin -> av !! dpin = Some a⌝ -∗ nview Γ q dpin a -∗
       Φ av d nm i) -∗
    dlookup_commit Γ E Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /dlookup_commit.
    iIntros (av d i nm ents nl) "%Hd %Hlk Hst".
    destruct (decide (d = dpin)) as [-> | Hne].
    - iDestruct (astate_nview with "Hst Hn") as %Hav.
      iModIntro. iFrame "Hst".
      iApply ("HΦ" $! av dpin nm i with "[%] Hn"). auto.
    - iModIntro. iFrame "Hst".
      iApply ("HΦ" $! av d nm i with "[%] Hn"). congruence.
  Qed.

  Lemma acre_commit_pinned Γ E (c : absnode) (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    nview Γ q jpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview Γ q jpin a -∗ Φ av d nm i) -∗
    acre_commit Γ E c Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /acre_commit.
    iIntros (av d i nm ents nl) "%Hpre Hst".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    iModIntro. iFrame "Hst". iIntros "Hst'". iModIntro. iFrame "Hst'".
    iApply ("HΦ" $! av d nm i with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b-2d.  THE WALK PACKAGE, THE AU BUNDLE AND THE ARMS: RETIRED      *)
  (*          (fs-syscall-specs, THE DVIEW RETIREMENT, 2026-08-30)       *)
  (* ------------------------------------------------------------------ *)

  (*  [mknod_walk_pre] and [mknod_walk_dead] rode [FsAbs.ax_hops_from
      dv_half] -- the landed lent fragment, i.e. [SpecNameiTr.nx_hop]'s own
      resource -- and that ghost column is deleted, so the two predicates and
      everything stated over them go with it:

        - [mknod_walk_pre] / [mknod_walk_dead]           (2b);
        - [mknod_au_pre], [mknod_post_ok], [mknod_post_fail], [mknod_arms],
          [mknod_stable_arms]                            (2c, 2d);
        - [wp_sys_mknod_au_frame], [wp_sys_mknod_au_body],
          [wp_sys_mknod_au_stable_body] and [Module Type SYSMKNOD_AU]
                                                          (sections 3, 4).

      NOTHING ON THE BUILD CONSUMED THEM.  [SpecSysMknodAUEra] -- the form
      the campaign actually seals ([ProofSysMknodAU] : [SYSMKNOD_AU_ERA],
      linked by [LinkSysMknodAU]) -- carries its own frame
      ([wp_sys_mknod_au_era_frame], which the ustate sweep forced anyway,
      see its header) and its own arms over [FsAbsEraMknod]'s era walk
      predicates ([mknod_walk_pre_era] / [mknod_walk_dead_era], which are
      [ep_start] / [np_dead] at [FsAbsEra.elend]).  From this file it takes
      [dev_arg] and section 1-2a's vocabulary, all of which STAYS -- as does
      everything [SpecCreateAU], [SpecCreateAUF], [SpecSysOpenAU],
      [SpecSysUnlinkAU], [FsAbsMknodFire] and [FsAbsEraMknod] read here:
      [delta_create] and its row algebra, [cre_pre], [abs_of_create_dev],
      [mknod_parent_elems], [acre_commit] and [dlookup_commit] with their
      four lemmas.

      R10 note: this file is the CAMPAIGN's own (landed 2026-08-28, this
      lane), so the dv-consuming half is trimmed in place rather than
      taken off the build -- the vocabulary above it has twenty-five
      consumers and could not follow the ghost out.                       *)

End SysMknodAU.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor").
   The commits are match-free single wands and stay transparent.  The
   sealed row named the seven retired predicates and is gone with them. *)
