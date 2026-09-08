(* SpecSysUnlinkAU.v -- the UNLINK family's STATEMENT LEAF: the fused
   delta's side conditions, its two-instant split, and the FOUR commit
   steps sys_unlink fires.  Definitions and small structural lemmas only --
   no bundle, no arms, no frame, no [Module Type].  sys_unlink's ONE
   contract is [SpecSysUnlink]'s [SYSUNLINK], which requires this file and
   states its bundle and arms over these pieces.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 1, 4
   and 7 ("ONE CONTRACT PER SYSCALL").  The abstract vocabulary is FsAbs.v;
   this file is at the family's accumulated form:

     - the walk premise is the ERA/relative-start shape
       ([FsAbsEraMknod.mknod_walk_pre_era], consumed from
       [FsAbsStart.ep_start]: one-shot, ∀ pl r, with only the
       SLASH -> ROOTINO tie), REUSED VERBATIM -- it is nameiparent-generic
       and mentions nothing mknod's.  Rename it [npar_walk_pre_era] when
       [FsAbsEraMknod.v] is next edited;
     - the commits are RAW-MAP ([_at]) shaped ([FsAbsMknodFire]'s finding:
       [astate]-shaped success commits cannot pay [ftop_body]'s give-back;
       no [astate] twins exist here to weaken to -- [dlookup_commit_at]'s
       one read-only weakening is that file's and is not repeated).

   ==== WHO ELSE TAKES THESE PIECES ====================================

   The pieces here are shared vocabulary, which is why they live below the
   contract rather than inside it:

   - [utgt_commit_at]: SpecSysLink.v, ProofSysLink.v, ProofSysLinkTails.v,
     FsAbsLinkFire.v -- sys_link's target leg is the SAME commit, at the
     failure arm where the linked target's count comes back down.
   - [uent_commit_at] / [dmiss_commit_at]: FsAbsUnlinkFire.v (the fire
     lemmas) and FsAbsInvFire.v (the trivial-family dischargers).
   - [unl_pre] and its row algebra: FsAbsUnlinkFire.v, FsAbsLinkFire.v.

   ==== THE DELTA IS TWO INSTANTS, AND THAT IS A MACHINE FACT ==========

   Doc section 4's [δ_unlink] is fused: delete the name, target.nlink-1,
   dir arm also parent.nlink-1.  The fused delta is stated below
   ([delta_unlink], total, side conditions in [unl_pre]) -- but IT IS NOT
   REALIZABLE AT ONE COMMIT, and the walk is the evidence.  Its success
   arms fire TWO [InodeRegion.ireg_top_retag_*] steps:

     instant 1 -- THE PARENT ROW: at the zeroing ([memset]+[writei] of
        the found record; W5-FILE), or fused with the [dp->nlink--;
        iupdate(dp)] pair on the DIR arm (W5-DIR retags [dp] ONCE, after
        iupdate, covering entry-delete and count together -- legal
        because dp's lock is held across both writes).  The reading is
        [delta_unl_ent]: [dir_entries] of the flushed record is
        [delete nm] of the old one ([FsStateEra.dir_entries_unlink_eq]),
        count down [unl_dec] on the dir arm.
     instant 2 -- THE TARGET ROW: after [ip->nlink--; iupdate(ip)],
        i.e. AFTER [iunlockput(dp)] released the parent.  The reading is
        [delta_unl_tgt]: same node, count down one.

   Between the two, [ftopN] must close and reopen (real instructions run,
   other harts' movers need the invariant), so the authority PASSES
   THROUGH the intermediate state -- entry gone, target count not yet
   down -- and a concurrent observer may see it.  Neither a single
   two-row commit nor mknod's collapse trick is available: mknod's fused
   delta collapsed to ONE row because the child's row was pre-observed
   ([insert_id]); here BOTH rows genuinely move.  So the bundle carries
   TWO commits, [uent_commit_at] and [utgt_commit_at], each in
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
   count is live ([1 <= nl] -- the walk's home-live fact, from
   [DirView.dir_orphan_clean]: a dir holding a live non-dot record
   cannot be orphaned); the target's row is [a] with [1 <= an_nlink a]
   (the kernel's [ip->nlink < 1] panic guard, walked at W3); and a
   DIRECTORY target's entry map is dots-only ([dots_only] -- THE
   ISDIREMPTY READING: the loop found every record at index >= 2 free,
   records 0 and 1 ARE the dots ([DirView.dir_dots_ix]), so first-match
   [dir_entries] holds no other name).  [unl_pre_ne] derives [d <> t]
   from these -- a dir target's dots-only map cannot carry the non-dot
   [nm] its self-row would need.

   ==== NOTHING ABOUT DURABILITY, AND NOTHING ABOUT [δ_free] ===========

   No durable clause appears below (doc section 5: three global principles
   at crash points; the per-syscall durable content is
   [FsDurSyscall.unlink_durable] and [unlink_durable_freed], composed by
   the consumer through [flushed]/[dur_at]).

   And nothing about [δ_free] -- THE VIEW IS THE LIVE NAMESPACE (owner
   ruling Q-d), so there is nothing left for it to do.  A successful
   unlink of a target with prior nlink 1 takes the row OUT of the view at
   instant 2 ([delta_unl_tgt] deletes at count 0): an unlinked-but-open
   file is the fd-holders' private buffer, not part of the file system a
   user can name, and [iput]'s eventual free of the record moves nothing
   the view has ([FsAbsDefs.abs_of] is [None] on both sides).  Two honest
   notes on that boundary:
     - what an fd-holder still reads of the unlinked file is the fd row's
       business (fs-syscall-specs section 4's stable corollary at the
       client's own share), not the file system's;
     - [delta_unlink_last_file] / [delta_unlink_last_dir] and
       [delta_unlink_is_Some_other] state the rows; the record's dots
       survive underneath, unnamed.

   ==== THE MISS COMMIT ================================================

   [dmiss_commit_at] is new in [dlookup_commit_at]'s single-phase mold:
   mknod's miss was its success path; unlink's is a failure the kernel
   OBSERVED, so it gets a fired receipt.  [Ftgt]'s receipt is binary
   ([aview -> Z -> iProp]) because instant 2 has no name in hand (the
   name buffer is dead by then) and no parent.

   BINDERS: [SpecSysMknodAU]'s section list verbatim -- [fileG] is bound
   and [icacheG]/[icfg] resolve only through its fields; the FsAbs
   carriers resolve [fsTopG]/[fsLinkG] through [xv6G]'s fields.  The
   live Γ is [FsBytesGamma.fs_gamma_L fsc_fs] ([FsAbs.ftop_gamma_top]
   ties its gname to [ftop_body]'s authority by reflexivity).  [FsImg]
   is neither Required nor Imported here (the walk premise carries
   [FsImg.ROOTINO] inside the reused definition). *)
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
Require Import IcacheRefDefs.
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
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname], [DOT], [DOTDOT] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require Import SpecSysMknodAU.  (* [mknod_parent_elems]                  *)
Require Import FsAbsEraMknod.   (* the era walk-premise pair, reused
                                   verbatim (nameiparent-generic) *)
Require Import FsAbsMknodFire.  (* [dlookup_commit_at]; the [_at] mold *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
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

(* ---- THE LAST-LINK FAMILY (E2-V2: the view is the live namespace) ---- *)

(* a file target whose only link this was: the row LEAVES the view.  What
   an fd-holder still sees of the file is the fd row's business
   (fs-syscall-specs section 4), not the view's. *)
Lemma delta_unlink_last_file (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (bs : list (bv 8)) :
  unl_pre av d nm ents nl t (MkAnode (AFile bs) 1%nat) ->
  delta_unlink d nm t av !! t = None.
Proof.
  intros Hp. destruct Hp as (Hd & _ & _ & _ & _ & Ht & _ & _).
  exact (delta_unlink_last av d nm ents nl t _ Hd Ht eq_refl).
Qed.

(* the dir arm: the child's row leaves too -- there is no orphan dir in
   the view, and no grey [".."] edge -- while the parent pays its own
   count down one and keeps its row. *)
Lemma delta_unlink_last_dir (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (t : Z) (es : gmap fname Z) :
  unl_pre av d nm ents nl t (MkAnode (ADir es) 1%nat) ->
  delta_unlink d nm t av !! t = None
  /\ delta_unlink d nm t av !! d
     = Some (MkAnode (ADir (delete nm ents)) (nl - 1)%nat).
Proof.
  intros Hp. pose proof (unl_pre_ne _ _ _ _ _ _ _ Hp) as Hne.
  destruct Hp as (Hd & _ & _ & _ & _ & Ht & _ & _).
  split.
  - exact (delta_unlink_last av d nm ents nl t _ Hd Ht eq_refl).
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
     fires the pair around the parent's [ireg_top_retag_*] inside one
     [ftopN] critical section). *)
  Definition uent_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d t : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat) (a : anode),
       ⌜unl_pre (abs_view I) d nm ents nl t a⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step d I (delta_unl_ent d nm (unl_dec (an_node a)) (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I'
             = delta_unl_ent d nm (unl_dec (an_node a)) (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) d nm t))%I.

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
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step t I (delta_unl_tgt t (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_unl_tgt t (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) t))%I.

  (* THE MISS OBSERVATION, single-phase and read-only --
     [dlookup_commit_at]'s twin at the ABSENT entry (header, deviation
     2): dirlookup ran under the parent's lock and found nothing. *)
  Definition dmiss_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       (* on the COUNT (E2-V2): at a miss nothing pins the parent live --
          an empty directory may have been removed between nameiparent
          and this lock, and then the view has no row for it *)
       ⌜arow_at (abs_view I) d (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = None⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ Φ (abs_view I) d nm)%I.

  (* The FOUND observation is [FsAbsMknodFire.dlookup_commit_at],
     reused verbatim -- fired here at the isdirempty refusal (arm
     iii-c), where both locks pin both rows at one instant. *)

  (* sanity: none of the three new commits can be vacuously blocked on
     the caller's side (the family's [*_unit] discipline) *)
  (* the two write-kind shapes owe the caller's step, paid here out of the
     parked license ([AppInv.app_step_acc]) at the live Γ *)
  Lemma uent_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ uent_commit_at (fs_gamma_L γfs) E (fun _ _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /uent_commit_at.
    iIntros (I d t nm ents nl a) "%Hpre Ha".
    iMod (app_step_acc E γfs d I _ HE
            (abs_view_lookup_is_Some I d _ (proj1 Hpre)) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma utgt_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ utgt_commit_at (fs_gamma_L γfs) E (fun _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /utgt_commit_at. iIntros (I t a) "%Ht %Hnl Ha".
    iMod (app_step_acc E γfs t I _ HE
            (abs_view_lookup_is_Some I t _ Ht) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma dmiss_commit_at_unit Γ E :
    ⊢ dmiss_commit_at Γ E (fun _ _ _ => True%I).
  Proof.
    rewrite /dmiss_commit_at. iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

End SysUnlinkAU.
