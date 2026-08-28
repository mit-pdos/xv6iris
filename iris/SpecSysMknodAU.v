(* SpecSysMknodAU.v -- sys_mknod's ATOMIC-UPDATE contract, stated over the
   campaign's abstract state.  A STATEMENT FILE: definitions, trivial
   structural lemmas, and a [Module Type] seal -- no walk, no proof against
   the machine.

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
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.   (* Require Export's DirViewG: [dv_half] *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecCreate.      (* [create_slots], [T_DEVICE], [create_made] *)
Require Import SpecSysMknod.    (* K_sys_mknod; the landed contract this
                                   file states a parallel form beside *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname] *)
Require DirView.                (* [T_DIR_z] (in FsAbs's cone) *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   ([sb_ninodes] : fs_sb -> Z) would shadow
                                   the superblock CELL ADDRESSES the frame
                                   below threads *)
Require Import FsAbs.           (* the abstract state (lane A, landed) *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
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
  (*  2b.  The walk package (the trace premise, fetched-path shaped)     *)
  (* ------------------------------------------------------------------ *)

  (* ONE SHOT, instantiated by the walk at the string argstr fetched and
     at the inum it starts from.  The hop family is [FsAbs.ax_hop] at the
     landed lent fragment [dv_half] (= [SpecNameiTr.nx_hop], checked
     claim), over the parent prefix.  The [={⊤}=∗] is fired between
     instructions where nothing is open (nx_hop culture); it lets the
     caller allocate its cursor ghosts for the path it just learned. *)
  Definition mknod_walk_pre (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜pl !! 0%nat = Some SLASH -> r = FsImg.ROOTINO⌝ ={⊤}=∗
       P 0%nat r
       ∗ ax_hops_from dv_half P Pmiss (mknod_parent_elems pl) 0%nat)%I.

  (* the walk's death receipt, [wp_namei_tr]'s refund shape verbatim:
     either hop [k] never fired (non-directory cursor, or namex's nlink
     guard) and the cursor comes back with hops from [k], or it fired and
     missed and the miss receipt comes back with hops from [S k] *)
  Definition mknod_walk_dead (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) : iProp Σ :=
    (∃ (k : nat) (d : Z),
       ⌜(k < length (mknod_parent_elems pl))%nat⌝ ∗
       ((P k d ∗ ax_hops_from dv_half P Pmiss (mknod_parent_elems pl) k)
        ∨ (Pmiss k d
           ∗ ax_hops_from dv_half P Pmiss (mknod_parent_elems pl)
               (S k))))%I.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The AU bundle and the post arms                               *)
  (* ------------------------------------------------------------------ *)

  (* everything the AU caller hands in, at the machine contract's mask
     floor [∅] *)
  Definition mknod_au_pre Γ (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_walk_pre P Pmiss
     ∗ acre_commit Γ ∅ (ADev ma mi) Φok
     ∗ dlookup_commit Γ ∅ Φex)%I.

  (* ret 0: the fetched path, the cursor at the parent, the fired success
     receipt with its instant's facts restated purely, and the unfired
     lookup commit refunded *)
  Definition mknod_post_ok Γ (ma mi : Z) (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av : aview) (d i : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
       ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       dlookup_commit Γ ∅ Φex ∗
       Φok av d nm i)%I.

  (* ret -1: the header's three-way fold, residue returned per arm *)
  Definition mknod_post_fail Γ (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (mknod_au_pre Γ ma mi P Pmiss Φok Φex
     ∨ (∃ pl : list (bv 8),
          (mknod_walk_dead P Pmiss pl
             ∗ acre_commit Γ ∅ (ADev ma mi) Φok
             ∗ dlookup_commit Γ ∅ Φex)
          ∨ (∃ d : Z,
               P (length (mknod_parent_elems pl)) d
               ∗ acre_commit Γ ∅ (ADev ma mi) Φok
               ∗ ((∃ (av : aview) (i : Z) (nm : fname)
                     (ents : gmap fname Z) (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = Some i⌝ ∗
                     Φex av d nm i)
                  ∨ dlookup_commit Γ ∅ Φex))))%I.

  (* the armed disjunction the continuation receives, keyed on a0 *)
  Definition mknod_arms Γ (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝ ∗ mknod_post_ok Γ ma mi P Φok Φex)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ mknod_post_fail Γ ma mi P Pmiss Φok Φex))%I.

  (* ------------------------------------------------------------------ *)
  (*  2d.  The stable corollary's arms (statement; header's limits)      *)
  (* ------------------------------------------------------------------ *)

  Definition mknod_stable_arms Γ (ma mi : Z) (avc : aview)
      (ds : list Z) (pl0 : list (bv 8))
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    (let ps0 := mknod_parent_elems pl0 in
     let dpar := ds !!! length ps0 in
     (⌜r = (zero_reg : mword 64)⌝ ∗ dlookup_commit Γ ∅ Φex ∗
        (∃ pl : list (bv 8),
           (⌜path_elems pl = path_elems pl0
             /\ pl !! 0%nat = Some SLASH⌝ ∗
            ∃ (av : aview) (i : Z) (nm : fname) (ents : gmap fname Z)
              (nl : nat),
              ⌜list_basics.last (path_elems pl0) = Some nm⌝ ∗
              ⌜cre_pre av dpar nm ents nl i (ADev ma mi)⌝ ∗
              ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
              ⌜apath_at avc FsImg.ROOTINO ps0 = Some dpar⌝ ∗
              Φok av dpar nm i)
           ∨ (⌜path_elems pl <> path_elems pl0
               \/ pl !! 0%nat <> Some SLASH⌝ ∗
              ∃ (av : aview) (d : Z) (nm : fname) (i : Z),
                Φok av d nm i)))
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ acre_commit Γ ∅ (ADev ma mi) Φok
        ∗ ((∃ (av : aview) (nm : fname) (i : Z),
              ⌜list_basics.last (path_elems pl0) = Some nm⌝ ∗ Φex av dpar nm i)
           ∨ (∃ (av : aview) (d : Z) (nm : fname) (i : Z),
                Φex av d nm i)
           ∨ dlookup_commit Γ ∅ Φex)))%I.

End SysMknodAU.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor").
   The commits are match-free single wands and stay transparent. *)
Global Typeclasses Opaque mknod_walk_pre mknod_walk_dead mknod_au_pre
  mknod_post_ok mknod_post_fail mknod_arms mknod_stable_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysMknod's frame + the AU              *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysMknod.wp_sys_mknod_sconf_body]'s premises and
   threaded resources VERBATIM (R10 -- the landed contract's calling
   convention, not a new one), abstracted over the AU-side extras: the
   caller's bundle [EXTRA] and the armed post [ARMS] on the returned a0
   (which REPLACES the landed ⌜sys_mknod_ret⌝ -- each arm pins a0, so the
   blanket disjunction is implied).  Both strengths below are this frame
   at their own bundle and arms. *)
Definition wp_sys_mknod_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)             (* ftable, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)                    (* syscall arguments 0 / 1 / 2 *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mknod in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mknod <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  eb = true ->
  pv_tf V !! tf_arg_idx 0 = Some v0 ->
  pv_tf V !! tf_arg_idx 1 = Some v1 ->
  pv_tf V !! tf_arg_idx 2 = Some v2 ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res fsc_disk pd pav pu) -∗
  bslots 3 -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  ireg_open -∗
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv gs -∗
  iref_slots ns -∗
  proc_priv γf pj pid V -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      (* the armed post on the returned a0 (implies [sys_mknod_ret]) *)
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE AU FORM.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs] -- the gname tie to [ftop_body]'s authority is
   definitional ([FsAbs.ftop_gamma_top]).  The device numbers are the
   syscall arguments' own low halfwords ([dev_arg]), so the caller's
   receipts speak about the numbers IT passed. *)
Definition wp_sys_mknod_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  wp_sys_mknod_au_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid V m K eb b lks
    (mknod_au_pre Γfs ma mi P Pmiss Φok Φex)
    (mknod_arms Γfs ma mi P Pmiss Φok Φex).

(* THE STABLE COROLLARY'S STATEMENT (header: THE TWO STRENGTHS; its
   derivation is the sealer's, expected from the AU form + agreement).
   The client names its expected ABSOLUTE path [pl0] and a run [ds] of
   its parent prefix through its own view [avc], and presents [apn_pins]
   for the CHAIN (never the parent -- the mover discipline forbids it;
   the [dpar ∉ take Lp ds] premise keeps cyclic tails from smuggling the
   parent in).  On a fetch that matches, the receipts land at
   [dpar = ds !!! Lp] and [apath_at] names the parent. *)
Definition wp_sys_mknod_au_stable_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !ghost_varG Σ (nat * Z)}
    `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v0 v1 v2 : mword 64)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (q : Qp) (avc : aview) (ds : list Z) (pl0 : list (bv 8))
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  let ma := dev_arg v1 in
  let mi := dev_arg v2 in
  let ps0 := mknod_parent_elems pl0 in
  pl0 !! 0%nat = Some SLASH ->
  arun avc FsImg.ROOTINO ps0 ds ->
  (ds !!! length ps0) ∉ take (length ps0) ds ->
  wp_sys_mknod_au_frame γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v0 v1 v2 pid V m K eb b lks
    (apn_pins Γfs q avc ds ps0 0%nat
     ∗ acre_commit Γfs ∅ (ADev ma mi) Φok
     ∗ dlookup_commit Γfs ∅ Φex)%I
    (mknod_stable_arms Γfs ma mi avc ds pl0 Φok Φex).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSMKNOD_AU.
  Parameter wp_sys_mknod_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_sys_mknod_au_body γf gs j gl pd pav pu ns dqb dqs dqbs dqn
        v0 v1 v2 pid V m K eb b lks P Pmiss Φok Φex.

  (* owed as a DERIVATION from [wp_sys_mknod_au] + the agreement seeds
     above, never as a second walk (doc section 2, "a COROLLARY of the AU
     form + agreement") *)
  Parameter wp_sys_mknod_au_stable :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !ghost_varG Σ (nat * Z)}
      `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v0 v1 v2 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (q : Qp) (avc : aview) (ds : list Z) (pl0 : list (bv 8))
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ),
      wp_sys_mknod_au_stable_body γf gs j gl pd pav pu ns dqb dqs dqbs dqn
        v0 v1 v2 pid V m K eb b lks q avc ds pl0 Φok Φex.
End SYSMKNOD_AU.
