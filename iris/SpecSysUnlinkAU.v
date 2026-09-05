(* SpecSysUnlinkAU.v -- sys_unlink's ATOMIC-UPDATE contract, stated over
   the campaign's abstract state.  A STATEMENT FILE: definitions, trivial
   structural lemmas, and a [Module Type] seal -- no walk, no proof against
   the machine.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 1, 4
   and 7 (v3; section 9 Q6 puts unlink SECOND in the increment order,
   "hardest in-memory arm, exercises orphans") and lane W of
   claude-notes/projects/fs-syscall-specs.md.  The abstract vocabulary is
   FsAbs.v; this file is BORN AT THE FAMILY'S ACCUMULATED FORM -- the
   mknod statement's three eras are folded in from birth:

     - the walk premise is the ERA/relative-start shape
       ([FsAbsEraMknod.mknod_walk_pre_era], consumed from
       [FsAbsStart.ep_start]: one-shot, ∀ pl r, with only the
       SLASH -> ROOTINO tie), REUSED VERBATIM -- it is nameiparent-generic
       and mentions nothing mknod's.  Rename it [npar_walk_pre_era] when
       [FsAbsEraMknod.v] is next edited (the mirror forbids touching it
       now);
     - the commits are RAW-MAP ([_at]) shaped from birth
       ([FsAbsMknodFire]'s finding: [astate]-shaped success commits cannot
       pay [ftop_body]'s give-back; no [astate] twins exist here to
       weaken to -- [dlookup_commit_at]'s one read-only weakening is that
       file's and is not repeated);
     - the continuation mirrors the LANDED [SpecSysUnlink.sys_unlink_closer]
       EXACTLY: binders [(mf, P')] and NO [M'] -- sys_unlink only READS
       user memory (argstr), so THE IMAGE DOES NOT MOVE (the closer's own
       banner).  The mknod-era frame's [M'] binder is create-side only.

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysUnlink.wp_sys_unlink_sconf] (R10: the
   landed contract does not move).  Same calling convention, same ambient
   premises, same threaded resources; what is NEW is that the caller hands
   in commit steps fired at the syscall's linearization instants against
   the ONE abstract state, and the postcondition ties the returned a0 to
   which arm fired.  Each arm pins a0, so the landed blanket
   [sys_unlink_ret] disjunction is implied.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY (doc section 5: three global principles at
   crash points; the per-syscall durable content is
   [FsDurSyscall.unlink_durable] -- the entry gone from the parent's
   snapshot row -- and [unlink_durable_freed] for the freed-inode arm.
   The composition of this contract with those certificates is the
   consumer's, through [flushed]/[dur_at]; no durable clause appears
   below).

   And NOTHING ABOUT [δ_free].  A successful unlink of a target with
   prior nlink 1 leaves the row IN the map at [an_nlink = 0] -- the
   ORPHAN state (doc section 1: "Orphans are IN the map"; section 4:
   the dir arm's child "stays in aview as an orphan dir until iput").
   Its leaving the map is [δ_free], which is IPUT's business at the last
   reference drop, not unlink's (doc section 7's close/iput row).  Two
   honest notes on that boundary:
     - when NO other process holds the target open, sys_unlink's OWN
       tail [iunlockput(ip)] is that last drop, so the free fires inside
       this very syscall, after the instants this contract receipts --
       exactly the stance the mknod header takes for create's
       mint-before-insert ("an ordinary state change a concurrent
       observer may see");
     - the orphan-dir's dots survive the delta untouched -- its [".."]
       still NAMES the (now ex-)parent, the doc's "goes grey" edge.
       [delta_unlink_orphan_file] / [delta_unlink_orphan_dir] and
       [delta_unlink_is_Some] state the rows.

   ==== THE DELTA IS TWO INSTANTS, AND THAT IS A MACHINE FACT ==========
   ==== (the one structural deviation from the mknod mold)    ==========

   Doc section 4's [δ_unlink] is fused: delete the name, target.nlink-1,
   dir arm also parent.nlink-1.  The fused delta is stated below
   ([delta_unlink], total, side conditions in [unl_pre]) -- but IT IS NOT
   REALIZABLE AT ONE COMMIT, and the landed proof is the evidence.
   [ProofSysUnlink]'s success walks fire TWO [InodeRegion.ireg_top_retag]
   steps:

     instant 1 -- THE PARENT ROW: at the zeroing ([memset]+[writei] of
        the found record; W5-FILE), or fused with the [dp->nlink--;
        iupdate(dp)] pair on the DIR arm (W5-DIR retags [dp] ONCE, after
        iupdate, covering entry-delete and count together -- legal
        because dp's lock is held across both writes).  The reading is
        [delta_unl_ent]: [dir_entries] of the flushed record is
        [delete nm] of the old one ([FsStateEra.dir_entries_unlink_eq],
        LANDED), count down [unl_dec] on the dir arm.
     instant 2 -- THE TARGET ROW: after [ip->nlink--; iupdate(ip)],
        i.e. AFTER [iunlockput(dp)] released the parent.  The reading is
        [delta_unl_tgt]: same node, count down one.

   Between the two, [ftopN] must close and reopen (real instructions run,
   other harts' movers need the invariant), so the authority PASSES
   THROUGH the intermediate state -- entry gone, target count not yet
   down -- and a concurrent observer may see it.  Neither a single
   two-row commit nor mknod's collapse trick is available: mknod's fused
   delta collapsed to ONE row because the child's row was pre-observed
   ([insert_id]); here BOTH rows genuinely move.  So the AU hands in TWO
   commits, [uent_commit_at] and [utgt_commit_at], each in
   [FsAbsMknodFire.acre_commit_at]'s two-phase mold at its own instant.

   WHAT MAKES THE PAIR READ LIKE ONE DELTA ANYWAY: [ip]'s lock is taken
   at W3, BEFORE instant 1, and held through instant 2 -- the target's
   fragment is in the walk's custody the whole way, so its row cannot
   move between the instants.  The ret-0 arm states that pin purely
   ([av1 !! t = Some a], the row [unl_pre] observed at instant 1), and
   [delta_unlink_split] is the machine-checked composition: under
   [unl_pre] the fused delta IS [delta_unl_tgt ∘ delta_unl_ent].  A
   quiescent consumer (the tree layer, holding exclusivity) reads the
   pair as one [delta_unlink]; a concurrent one gets the honest two
   steps.  This mirrors the doc's own precedent for link ("two
   linearization instants") and write (per-chunk deltas).

   ==== THE SIDE CONDITIONS, AND THE TWO KERNEL READINGS ===============

   [unl_pre] is what the kernel has established at instant 1, restated
   abstractly: the parent is a directory whose map carries [nm ↦ t]; the
   name is NEITHER dot ([FsTree.DOT]/[DOTDOT] -- the entry-map spelling
   of the two [namecmp] guards; the landed contract's own vocabulary for
   these names is [dir_bname], whose values these are); the parent's
   count is live ([1 <= nl] -- the landed walk's home-live fact, from
   [DirView.dir_orphan_clean]: a dir holding a live non-dot record
   cannot be orphaned); the target's row is [a] with [1 <= an_nlink a]
   (the kernel's [ip->nlink < 1] panic guard, walked at W3); and a
   DIRECTORY target's entry map is dots-only ([dots_only] -- THE
   ISDIREMPTY READING: the loop found every record at index >= 2 free,
   records 0 and 1 ARE the dots ([DirView.dir_dots_ix]), so first-match
   [dir_entries] holds no other name).  [unl_pre_ne] derives [d <> t]
   from these -- a dir target's dots-only map cannot carry the non-dot
   [nm] its self-row would need.

   ==== THE ARMS ========================================================

   ret 0  -- the fetched path (existential, as always: no premise can pin
             user bytes), the cursor [P Lp d] at the parent, [unl_pre]
             restated purely at instant 1 beside the caller's own
             receipts [Φent]/[Φtgt], the instant-2 target pin, the
             region bound on [t], and the two observation commits
             refunded (the found fact is subsumed by [unl_pre]; see the
             owner questions).
   ret -1 -- the honest fold of the landed contract's blanket
             disjunction, residue returned per arm:
             (i)   nothing fs-visible happened (argstr failed): the
                   whole AU bundle back unspent;
             (ii)  the walk died at hop [k]: [mknod_walk_dead_era]'s
                   refund shape, all four commits back;
             (iii) the walk delivered the parent ([P Lp d] back, both
                   delta commits back) and the transaction refused:
                   (a) THE NAME IS A DOT -- refused BY NAME, before any
                       lookup: a PURE fact about the fetched string
                       ([last (path_elems pl)] is [DOT] or [DOTDOT]),
                       both observation commits refunded (the kernel
                       looked at nothing abstract);
                   (b) GONE -- dirlookup ran and MISSED: the miss
                       observation [Φmiss] FIRED at the instant, with
                       the parent's row and the absent name stated
                       purely beside it;
                   (c) DIR NON-EMPTY -- dirlookup FOUND [t] and
                       isdirempty refuted emptiness: the found
                       observation [Φex] FIRED, at the instant where
                       BOTH locks are held, so the same [av] purely
                       carries the parent's row, the entry, the
                       target's dir row and its non-dots witness;
                   (d) no abstract observation to report -- covers
                       nameiparent's own [P Lp] hand-backs that are not
                       [walk_dead] (the k = Lp deaths: namex's type test
                       and nlink guard at the parent's own level, and
                       "unlink of /" -- FsAbsNpar's finding 3), with
                       both observation commits refunded.  As with
                       mknod: -1 deliberately does not say which arm
                       (the landed DETERMINISM: none).

   ==== WHAT THE PROVER OWES ===========================================

   1. THE FIRE POINTS, fused with the two retags the landed walk already
      performs (the mold is [FsAbsMknodFire.mkf_acre_fire]: same premise
      as [ireg_top_retag], same payout, plus the caller's two phases
      inside the one [ftopN] critical section):
        - [uent_commit_at]'s pair around the PARENT retag --
          [ProofSysUnlink] W5-FILE's retag at the zeroing, W5-DIR's
          single post-iupdate(dp) retag.  [unl_pre]'s conjuncts are all
          in hand there: the parent's row off its held fragment, the
          found entry off dirlookup (+ [dir_names_unique] for the
          first-match tie), the dot refusals off the namecmp guards, the
          home-live count off [dir_orphan_clean], the target's row off
          ITS held fragment (ip locked since W3), the nlink guard off
          the walked panic test, and dots-only off the isdirempty block
          lemma (see 3);
        - [utgt_commit_at]'s pair around the TARGET retag after
          [wp_iupdate_unlink];
        - [Φmiss] at dirlookup's miss under the parent's lock ([mkf_dlookup_fire]'s
          shape with the absent-entry premise);
        - [Φex] at the isdirempty refusal, both fragments held.
      These fire lemmas live in a new prover leaf (an unlink twin of
      [FsAbsMknodFire]; the mirror forbids appending there).
   2. THE READING BRIDGES: [FsStateEra.dir_entries_unlink_eq] is the
      delete-side half, LANDED; what is owed is its [abs_of] wrap (the
      unlink twin of [mkf_parent_row]: the zeroed record keeps type and
      count, so the row is [ADir (delete nm ents)] at the old count) and
      the count-lowered bridge at both iupdates ([su_setnl] moves
      [di_nlink] alone, so [abs_of] keeps the node and lowers [fn_nlink]
      by one -- ProofSysUnlink's [su_setnl_*] congruences, restated
      abstractly), plus the ISDIREMPTY BRIDGE both ways: loop-found-all-
      free + [dir_dots_ix] + [dir_names_unique] ==> [dots_only
      (dir_entries n)], and a live record at index >= 2 ==> a non-dot
      name in [dir_entries n] (the (iii-c) witness).
   3. THE NAME TIE: [last (path_elems pl) = Some nm] with [nm] the
      found record's [dir_bname] -- SpecNamex's bname ruling, as in the
      mknod post.
   4. THE LINK-RA (G5) THREADING -- the register moves are ALREADY the
      landed walk's, and the AU fires must interleave WITHOUT reordering
      them: [FsStateEra.ent_toks_unlink] fires caller-side at the
      zeroing and RELEASES the target's [FsStateLink.link_tok] (the
      zeroed entry gives up its token); [IregLinkNz.ireg_tok_nz] reads
      the target's type off that token (D1/G5: a non-dir target keeps
      the marker set still); [SpecIupdate.wp_iupdate_unlink] CONSUMES
      the token at the target's flush (via [ireg_dot_delta]/[link_reps]);
      on the DIR arm the child's [".."] fragment pays for [dp->nlink--]
      ([DirView.dir_dots_ix] + [ent_toks_era_borrow_at] name it;
      [link_toks_reps_S]/[link_reps_1] split it) and hands back
      [2 <= dir_nrec (di_size ip)].  The abstract commits ride BESIDE
      this: instant 1's fire sits where [ent_toks_unlink] +
      [ireg_top_retag] already sit, instant 2's where the second retag
      sits after the token is spent.  Nothing about the tokens crosses
      THIS interface -- the ledger stays below the abstraction, as the
      doc's nlink bullet (section 1) rules.
   5. THE WALK: the nameiparent era walk is LANDED ([SpecNparWrapEra]);
      the prover instantiates the reused one-shot at the fetched string
      via [FsAbsNparMknod.np_start_of_mknod]'s shape and folds the
      k = Lp deaths into arm (iii-d) ([np_dead_to_mknod]'s finding).

   ==== NO STABLE COROLLARY (family precedent) =========================

   None is stated.  The mknod stable form is partially vacuous until a
   cross-syscall pin producer exists (its header, limit 3; the worklist's
   as-landed finding: the pinned walk is refuted against a live inum
   because the walk's custody is the whole element), and unlink adds
   nothing to that story -- its parent AND target are both retagged, so
   BOTH would refuse a client pin.  The stable reading arrives with the
   tree layer's exclusivity fact, where [delta_unlink_split] makes the
   two instants one delta.

   ==== MKNOD-MOLD DEVIATIONS, COLLECTED ===============================

   (1) TWO delta commits at two instants (above) -- the fused delta
       survives as the pure [delta_unlink] + [delta_unlink_split] + the
       ret-0 target pin.
   (2) A MISS observation commit [dmiss_commit_at] (new, in
       [dlookup_commit_at]'s single-phase mold): mknod's miss was its
       success path; unlink's is a failure the kernel OBSERVED, so it
       gets a fired receipt.
   (3) [Φtgt] is binary ([aview -> Z -> iProp]): instant 2 has no name
       in hand (the name buffer is dead by then) and no parent.
   (4) ret 0 REFUNDS [Φex]/[Φmiss] rather than firing the found
       observation: [unl_pre] restates the found fact at the SAME
       instant-1 [av], so a fired [Φex] would be a second receipt at an
       earlier (dirlookup-time) instant -- owner question 2 offers it.
   (5) No stable corollary, no [_pinned] seeds (nothing to derive).

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. Is the two-instant surface acceptable as the unlink AU of record,
      with the one-delta reading deferred to the tree layer via
      [delta_unlink_split]?  (The alternative -- a one-commit spec -- is
      unrealizable against the landed retag discipline, not merely
      unproven.)
   2. Should ret 0 ALSO fire the found observation at dirlookup's own
      instant (a third fired receipt), or is [unl_pre]-at-instant-1
      enough?  Costs a commit slot in the bundle; buys an earlier
      timestamp no anticipated consumer needs.
   3. The dot refusal is PURE (arm iii-a): fine, or should it carry a
      fired parent observation (the kernel held dp's lock but read
      nothing abstract there)?
   4. Mask floor [∅] for all four commits -- inherited mknod question 2,
      unchanged.

   BINDERS: [SpecSysMknodAU]'s section list verbatim -- [fileG] is bound
   and [icacheG]/[icfg] resolve only through its fields; the FsAbs
   carriers resolve [fsTopG]/[fsLinkG] through [xv6G]'s fields.  The
   live Γ is [FsBytesGamma.fs_gamma_L fsc_fs] ([FsAbs.ftop_gamma_top]
   ties its gname to [ftop_body]'s authority by reflexivity).  [FsImg]
   is neither Required nor Imported here (the walk premise carries
   [FsImg.ROOTINO] inside the reused definition); the sb-cell addresses
   the frame threads come from the kernel-data side unshadowed. *)
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
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import SpecSysUnlink.   (* K_sys_unlink, [sys_unlink_slots]; the
                                   landed contract this file states a
                                   parallel form beside *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname], [DOT], [DOTDOT] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require Import SpecSysMknodAU.  (* [mknod_parent_elems]; the frozen mold *)
Require Import FsAbsEraMknod.   (* the era walk-premise pair, reused
                                   verbatim (nameiparent-generic) *)
Require Import FsAbsMknodFire.  (* [dlookup_commit_at]; the [_at] mold *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS SIDE CONDITIONS (PURE)                          *)
(* ===================================================================== *)

Require Export FsAbsDelta.   (* [unl_dec], [delta_unl_ent]/[delta_unl_tgt]/[delta_unlink] + their row algebra (hoisted 2026-09-04) *)

(* THE ISDIREMPTY READING: the entry map holds nothing but the dots.
   (The dots THEMSELVES stay -- doc section 1: ".", ".." are ordinary
   names of [ents], hidden only by the tree layer.) *)
Definition dots_only (es : gmap fname Z) : Prop :=
  forall nm, is_Some (es !! nm) -> nm = DOT \/ nm = DOTDOT.

(* THE SIDE CONDITIONS, as one proposition -- everything the kernel has
   walked by instant 1, restated abstractly (header: THE SIDE
   CONDITIONS).  [a] is the target's observed row. *)
Definition unl_pre (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) : Prop :=
  av !! d = Some (MkAnode (ADir ents) nl)
  /\ ents !! nm = Some t
  /\ nm <> DOT
  /\ nm <> DOTDOT
  /\ (1 <= nl)%nat
  /\ av !! t = Some a
  /\ (1 <= an_nlink a)%nat
  /\ (forall es, an_node a = ADir es -> dots_only es).

(* the parent is never the target: a dir target's dots-only map cannot
   carry the non-dot name its self-row would need *)
Lemma unl_pre_ne (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  unl_pre av d nm ents nl t a -> d <> t.
Proof.
  intros (Hd & Hnm & HnD & HnDD & _ & Ht & _ & Hdots) Heq. subst t.
  rewrite Hd in Ht. injection Ht as <-.
  destruct (Hdots ents eq_refl nm (mk_is_Some _ _ Hnm)) as [Hc | Hc];
    [exact (HnD Hc) | exact (HnDD Hc)].
Qed.

(* ---- THE COMPOSITION (header: what makes the pair one delta) --------- *)

Lemma delta_unlink_split (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (a : anode) :
  unl_pre av d nm ents nl t a ->
  delta_unlink d nm t av
  = delta_unl_tgt t (delta_unl_ent d nm (unl_dec (an_node a)) av).
Proof.
  intros Hp. pose proof (unl_pre_ne _ _ _ _ _ _ _ Hp) as Hne.
  destruct Hp as (Hd & _ & _ & _ & _ & Ht & _ & _).
  rewrite /delta_unlink /delta_unl_ent Hd Ht /=.
  rewrite /delta_unl_tgt.
  rewrite lookup_insert_ne; [| congruence].
  rewrite Ht. reflexivity.
Qed.

(* ---- THE ORPHAN FAMILY (header: nothing leaves the map) -------------- *)

(* a file target whose only link this was: the row STAYS, reading
   [an_nlink = 0] -- the unlinked-but-open state the doc's orphan bullet
   names.  (Whether it stays past the syscall is a question about who
   holds references -- see the header's δ_free note.) *)
Lemma delta_unlink_orphan_file (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (bs : list (bv 8)) :
  unl_pre av d nm ents nl t (MkAnode (AFile bs) 1%nat) ->
  delta_unlink d nm t av !! t = Some (MkAnode (AFile bs) 0%nat).
Proof.
  intros Hp. destruct Hp as (Hd & _ & _ & _ & _ & Ht & _ & _).
  by rewrite (delta_unlink_target av d nm ents nl t _ Hd Ht).
Qed.

(* the dir arm: the child stays as an ORPHAN DIR at count 0 -- its entry
   map (the dots included; [unl_pre] says it is dots-only) survives
   UNTOUCHED, so its [".."] still names [d]: the grey edge.  The parent
   pays its own count down one. *)
Lemma delta_unlink_orphan_dir (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (es : gmap fname Z) :
  unl_pre av d nm ents nl t (MkAnode (ADir es) 1%nat) ->
  delta_unlink d nm t av !! t = Some (MkAnode (ADir es) 0%nat)
  /\ delta_unlink d nm t av !! d
     = Some (MkAnode (ADir (delete nm ents)) (nl - 1)%nat).
Proof.
  intros Hp. pose proof (unl_pre_ne _ _ _ _ _ _ _ Hp) as Hne.
  destruct Hp as (Hd & _ & _ & _ & _ & Ht & _ & _).
  split.
  - by rewrite (delta_unlink_target av d nm ents nl t _ Hd Ht).
  - by rewrite (delta_unlink_parent av d nm ents nl t _ Hd Ht Hne).
Qed.

(* ===================================================================== *)
(*  2.  THE COMMITS, THE WALK PACKAGE, AND THE ARMS                       *)
(* ===================================================================== *)

Section SysUnlinkAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The four commit steps                                         *)
  (* ------------------------------------------------------------------ *)

  (* INSTANT 1 -- the parent-row commit, two-phase at the raw map
     ([acre_commit_at]'s mold: phase 1 observes the pre-state under
     [unl_pre], phase 2 witnesses the parent half applied; the prover
     fires the pair around the parent's [ireg_top_retag] inside one
     [ftopN] critical section). *)
  Definition uent_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d t : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat) (a : anode),
       ⌜unl_pre (abs_view I) d nm ents nl t a⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I'
             = delta_unl_ent d nm (unl_dec (an_node a)) (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) 1 I' ={E}=∗
            ghost_map_auth (γtop Γ) 1 I' ∗ Φ (abs_view I) d nm t))%I.

  (* INSTANT 2 -- the target-row commit, same mold.  No name, no parent:
     by this instant only the target's identity is in the machine's
     hands (header, deviation 3).  The [1 <= an_nlink a] premise is the
     walked panic guard, still true here because the target's fragment
     has been held since W3. *)
  Definition utgt_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (t : Z) (a : anode),
       ⌜abs_view I !! t = Some a⌝ -∗
       ⌜(1 <= an_nlink a)%nat⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_unl_tgt t (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) 1 I' ={E}=∗
            ghost_map_auth (γtop Γ) 1 I' ∗ Φ (abs_view I) t))%I.

  (* THE MISS OBSERVATION, single-phase and read-only --
     [dlookup_commit_at]'s twin at the ABSENT entry (header, deviation
     2): dirlookup ran under the parent's lock and found nothing. *)
  Definition dmiss_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       ⌜abs_view I !! d = Some (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = None⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗ Φ (abs_view I) d nm)%I.

  (* The FOUND observation is [FsAbsMknodFire.dlookup_commit_at],
     reused verbatim -- fired here at the isdirempty refusal (arm
     iii-c), where both locks pin both rows at one instant. *)

  (* sanity: none of the three new commits can be vacuously blocked on
     the caller's side (the family's [*_unit] discipline) *)
  Lemma uent_commit_at_unit Γ E :
    ⊢ uent_commit_at Γ E (fun _ _ _ _ => True%I).
  Proof.
    rewrite /uent_commit_at. iIntros (I d t nm ents nl a) "%Hpre Ha".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma utgt_commit_at_unit Γ E :
    ⊢ utgt_commit_at Γ E (fun _ _ => True%I).
  Proof.
    rewrite /utgt_commit_at. iIntros (I t a) "%Ht %Hnl Ha".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma dmiss_commit_at_unit Γ E :
    ⊢ dmiss_commit_at Γ E (fun _ _ _ => True%I).
  Proof.
    rewrite /dmiss_commit_at. iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  The AU bundle and the post arms                               *)
  (* ------------------------------------------------------------------ *)

  (* Everything the AU caller hands in, at the machine contract's mask
     floor [∅].  The walk premise is [FsAbsEraMknod.mknod_walk_pre_era]
     REUSED VERBATIM (header: it is nameiparent-generic -- the one-shot
     ∀ pl r with only the SLASH -> ROOTINO tie, the hop family at the
     era lend over the parent prefix [mknod_parent_elems pl]; it is what
     [FsAbsStart.ep_start] instantiates to at the fetched string). *)
  Definition unlink_au_pre Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ) : iProp Σ :=
    (mknod_walk_pre_era γfs cw P Pmiss
     ∗ uent_commit_at Γ fsabsE Φent
     ∗ utgt_commit_at Γ fsabsE Φtgt
     ∗ dlookup_commit_at Γ fsabsE Φex
     ∗ dmiss_commit_at Γ fsabsE Φmiss)%I.

  (* ret 0: the fetched path, the cursor at the parent, [unl_pre]
     restated purely at instant 1, BOTH fired receipts, the instant-2
     pin on the target's row (its lock is held across the gap), the
     region bound on the target, and the two observation commits
     refunded. *)
  Definition unlink_post_ok Γ (P : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av0 av1 : aview) (d t : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat) (a : anode),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜unl_pre av0 d nm ents nl t a⌝ ∗
       ⌜0 < t < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜av1 !! t = Some a⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       dlookup_commit_at Γ fsabsE Φex ∗
       dmiss_commit_at Γ fsabsE Φmiss ∗
       Φent av0 d nm t ∗
       Φtgt av1 t)%I.

  (* ret -1: the header's fold -- (i) bundle back, (ii) walk dead,
     (iii) refused at the parent with the observation each refusal IS *)
  Definition unlink_post_fail Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ) : iProp Σ :=
    (unlink_au_pre Γ γfs cw P Pmiss Φent Φtgt Φex Φmiss
     ∨ (∃ pl : list (bv 8),
          (mknod_walk_dead_era γfs P Pmiss pl
             ∗ uent_commit_at Γ fsabsE Φent
             ∗ utgt_commit_at Γ fsabsE Φtgt
             ∗ dlookup_commit_at Γ fsabsE Φex
             ∗ dmiss_commit_at Γ fsabsE Φmiss)
          ∨ (∃ d : Z,
               P (length (mknod_parent_elems pl)) d
               ∗ uent_commit_at Γ fsabsE Φent
               ∗ utgt_commit_at Γ fsabsE Φtgt
               ∗ ((* (iii-a) the name is a dot: refused BY NAME, before
                     any lookup -- pure, both observations refunded *)
                  (∃ nm : fname,
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜nm = DOT \/ nm = DOTDOT⌝ ∗
                     dlookup_commit_at Γ fsabsE Φex ∗
                     dmiss_commit_at Γ fsabsE Φmiss)
                  ∨ (* (iii-b) gone: the miss observation FIRED *)
                  (∃ (av : aview) (nm : fname) (ents : gmap fname Z)
                     (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = None⌝ ∗
                     Φmiss av d nm ∗
                     dlookup_commit_at Γ fsabsE Φex)
                  ∨ (* (iii-c) dir non-empty: the found observation
                       FIRED, both rows pinned at the one instant *)
                  (∃ (av : aview) (t : Z) (nm : fname)
                     (ents est : gmap fname Z) (nl nlt : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = Some t⌝ ∗
                     ⌜av !! t = Some (MkAnode (ADir est) nlt)⌝ ∗
                     ⌜~ dots_only est⌝ ∗
                     Φex av d nm t ∗
                     dmiss_commit_at Γ fsabsE Φmiss)
                  ∨ (* (iii-d) no abstract observation to report: the
                       k = Lp deaths (parent-level type/nlink guards,
                       "unlink of /") -- everything back *)
                  (dlookup_commit_at Γ fsabsE Φex ∗
                   dmiss_commit_at Γ fsabsE Φmiss)))))%I.

  (* the armed disjunction the continuation receives, keyed on a0
     (implies the landed [sys_unlink_ret]) *)
  Definition unlink_arms Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ)
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝
      ∗ unlink_post_ok Γ P Φent Φtgt Φex Φmiss)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ unlink_post_fail Γ γfs cw P Pmiss Φent Φtgt Φex Φmiss))%I.

  (* the landed return blanket, read off the arms: the one conjunct of
     [SpecSysUnlink.sys_unlink_closer] the AU form replaces, implied *)
  Lemma unlink_arms_ret Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ) (r : mword 64) :
    unlink_arms Γ γfs cw P Pmiss Φent Φtgt Φex Φmiss r ⊢ ⌜sys_unlink_ret r⌝.
  Proof.
    rewrite /unlink_arms /sys_unlink_ret.
    iIntros "[[%Hr _] | [%Hr _]]"; iPureIntro; [right | left]; exact Hr.
  Qed.

End SysUnlinkAU.

(* big-op bodies behind definitions: seal them (durable-notes;
   optimization.md, "a big-op body is the predictor").  The commits are
   match-free single wands and stay transparent, as the family's do. *)
Global Typeclasses Opaque unlink_au_pre unlink_post_ok unlink_post_fail
  unlink_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysUnlink's frame + the AU              *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysUnlink.wp_sys_unlink_sconf_body]'s premises
   and threaded resources VERBATIM (R10 -- the landed contract's calling
   convention, not a new one), abstracted over the AU-side extras: the
   caller's bundle [EXTRA] and the armed post [ARMS] on the returned a0,
   which REPLACES the landed ⌜sys_unlink_ret⌝ inside an inlined copy of
   [sys_unlink_closer] -- inlined because the closer bakes the pure
   disjunction in; every other row of it is byte-identical, INCLUDING
   the binder list [(mf, P')]: the image does not move (header). *)
Definition wp_sys_unlink_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)      (* ftable, kalloc, printk   *)
    (gs : list gname) (j : nat) (gl : gname)     (* the running process *)
    (pd pav pu : mword 64)                       (* disk fabric + lock  *)
    (dqb dqs dqbs : dfrac)
    (v0 : mword 64)                              (* syscall argument 0  *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_unlink in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_unlink <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* mkfs's [ushort] geometry, the landed contract's premise verbatim *)
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- balloc's out-of-blocks arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* nameiparent's own premise, inherited *)
  eb = true ->
  (* argstr reads syscall argument 0 out of the trapframe page *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* entered with no lock held: depth pinned at zero *)
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region the two flushes write ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* the sealed regime, riding [ireg_inv]'s channel (the landed
     contract's row and reason: this contract reaches iput's freezer) *)
  ireg_open -∗
  (* ---- the three superblock cells ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv gs -∗
  (* ---- the process, and the reference allowance the walk needs ---- *)
  iref_slots sys_unlink_slots -∗
  proc_priv γf pj pid U -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  (* the crossing is the literal [true]: sys_unlink parks in all ten
     callees (the landed contract's row) *)
  wp_next true pj (fun (CID : CpuId) =>
  (* [sys_unlink_closer]'s rows, [ARMS] in place of ⌜sys_unlink_ret⌝.
     THE IMAGE DOES NOT MOVE: only the descriptor grows (argstr), so the
     binders are [(mf, P')] and the block returns at [us_upt U P'] --
     no [M'] (the mknod-era frame's finding does not apply here). *)
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: argstr's fetchstr faults user pages
         in.  [uptd_ext_sz] is argstr's own report, relayed (the landed
         row since 745672d3c). *)
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      (* no ordering on the free pool: the zeroing's writei can ALLOCATE
         and every iunlockput can FREE (the landed header) *)
      iref_slots sys_unlink_slots -∗
      proc_priv γf pj pid (us_upt U P') -∗
      (* the armed post on the returned a0 (implies [sys_unlink_ret]) *)
      ARMS (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs] -- the gname tie to [ftop_body]'s authority is
   definitional ([FsAbs.ftop_gamma_top]). *)
Definition wp_sys_unlink_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (dqb dqs dqbs : dfrac)
    (v0 : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φent : aview -> Z -> fname -> Z -> iProp Σ)
    (Φtgt : aview -> Z -> iProp Σ)
    (Φex : aview -> Z -> fname -> Z -> iProp Σ)
    (Φmiss : aview -> Z -> fname -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_sys_unlink_au_frame γf gs j gl pd pav pu dqb dqs dqbs
    v0 pid U m K eb b lks
    (unlink_au_pre Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φent Φtgt Φex Φmiss)
    (unlink_arms Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φent Φtgt Φex Φmiss).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type SYSUNLINK_AU.
  Parameter wp_sys_unlink_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φent : aview -> Z -> fname -> Z -> iProp Σ)
      (Φtgt : aview -> Z -> iProp Σ)
      (Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φmiss : aview -> Z -> fname -> iProp Σ),
      wp_sys_unlink_au_body γf gs j gl pd pav pu dqb dqs dqbs
        v0 pid U m K eb b lks P Pmiss Φent Φtgt Φex Φmiss.
End SYSUNLINK_AU.
