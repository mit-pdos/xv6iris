(* FileInvDefs.v -- the open-file table's geometry, the reference-count
   algebra, and [file_ref]/[fslot]: what every consumer that merely HOLDS or
   LOOKS UP a file reference needs (starting with [ProcInv]'s [proc_priv],
   which threads a slot index through [p->ofile]).

   The design (and the reasoning behind the algebra) is written up in
   claude-notes/design/file-table.md; the short version:

     struct file { int type; int ref; char readable; char writable;
                   struct pipe *pipe; struct inode *ip; uint off; short major; }
     struct { struct spinlock lock; struct file file[NFILE]; } ftable;

   Three different disciplines govern the fields, and the model keeps them
   apart:

   * [ref] is protected by ftable.lock -- filealloc's scan reads the [ref]
     field of EVERY entry, so all NFILE of those cells live in the lock's
     resource and none of them ever travels with a reference.
   * the other fields are immutable while [ref > 0] and are read with no lock
     at all, so a reference has to carry a real points-to FRACTION of them.
   * [off] is mutable under ip->lock, and its ownership follows that
     discipline: an FD_INODE file's cell is DEPOSITED in its inode's OFF
     LEDGER ([ioff_escrow], a per-itable-slot invariant whose ghost map
     tracks which file slots refer to that inode) and the reference carries
     a fragment of that map; any other file owns the cell directly at its
     own fraction ([foff_dead]).  See the "off ledger" note above
     [ioff_escrow] below.

   The two halves are tied together by one authoritative ghost map, keyed by
   slot index: [M !! k = Some (q,n)] says slot k has n outstanding references
   holding fraction q of the content between them, and [k ∉ dom M] says the
   slot is free.  Because [fracR] has no unit and [positiveR] no zero, a
   fragment [(q,1)] included in [(qt,n)] forces [n = 1 -> q = qt]: THE HOLDER
   OF THE ONLY REFERENCE HOLDS THE FULL FRACTION, hence write access.  That is
   what licenses sys_open's unlocked initialization of a fresh file and
   fileclose's [f->type = FD_NONE] at ref 0.

   ---- the PAYLOAD ----

   A [struct file] is a reference TO something: a pipe end (FD_PIPE) or an
   inode (FD_INODE / FD_DEVICE).  That resource rides INSIDE [file_ref], at
   the reference's own fraction, and is a FUNCTION of the file's content
   ([file_core]) -- which is what lets the exclusive holder publish a
   payload by storing to [f->type] and [f->pipe] with no lock held and no
   ghost step, exactly as pipealloc and sys_open do.  The one thing memory
   does not record is the payload's ghost identity, so that is a per-slot
   ghost FIELD ([fpay_tok]) beside the content cells, split by the same
   fractions and agreeing between holders; see the note above [fpnames] for
   why it cannot live on the authority.

   Two fraction laws are the whole of fileclose: [file_rest_absorb] (a
   departing reference's share goes back to the invariant) and
   [file_rest_join] (the last one takes the invariant's leftover, and so
   holds a WHOLE pipe end to hand to pipeclose) -- both in FileInv.v.

   ---- why this is its own file ----

   FileInv.v keeps [ftable_res]/[is_ftable] and the ~500 lines of ref-counting
   ghost-step lemmas ([file_alloc_step], [flive_*], [file_close_step], ...)
   that only filealloc/filedup/fileclose/sys_open/sys_pipe/sys_fork/kexit need
   to CHANGE a reference count.  [ProcInv] and everything downstream of it on
   the pipe-read critical path ([SchedCtx], [SpecPiperead], [ProofPiperead])
   only ever HOLD a [file_ref]/[fslot] -- they never allocate or close one --
   so splitting this slice out lets FileInv.v's heavier tail compile IN
   PARALLEL with [ProcInv]/[SchedCtx]/[SpecPiperead]/[ProofPiperead] instead
   of sitting as a serial prerequisite of all of them.  `Require Import
   FileInv` still gets everything (FileInv.v `Require Export`s this file);
   switch to `Require Import FileInvDefs` wherever only this slice is needed.
   See claude-notes/optimization.md. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own cancelable_invariants ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import ArrCursor.
Require Export FdSlots.
Require Import PipeInvDefs.
Require Import IcacheRef.
Require Import FsCfg.   (* [fscfg] -- see the note on [fileG] below *)
(* for [T_DIR_z] alone -- [inode_pay]'s witness says "not a directory", and
   the number is stated once, where [IcacheEscrow.ic_loaded]'s [dir_ok]
   states it (design fs-icache.md §17.6 (5)). *)
Require Import DirView.
(* for [MAXFILE] and [BSIZE] alone -- [off_wf], the bound the off cell carries,
   is stated over the inode layer's two constants, and the cell now lives here
   (R-open-1b).  Neither file mentions the file table, so this closes no cycle. *)
Require Import InodeInv.
Require Import BioDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import IrefSlots.  (* [iref_frac]: an ftable entry holds one unit.
     NO CYCLE -- IrefSlots reaches only ProcGeom and FdSlots, which is exactly
     why [NFILE] was moved to FdSlots (see the note below). *)
Require Import TsoCtx.
Local Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

(* struct ftable { struct spinlock lock; struct file file[NFILE]; }, so the
   lock is the first member and &ftable.lock = &ftable (SpecFileinit.v). *)
Definition ftable_addr : mword 64 := mword_of_int KernelSyms.ftable.

(* [NFILE] moved to [FdSlots.v] to break the IrefSlots -> FileInv cycle;
   it is still in scope here through this file's own [Require Import
   FdSlots], and [Require Export] keeps it visible to FileInv's importers. *)
Definition file_stride : Z := 40.               (* the loop's [addi s1,s1,40] *)
Definition file_base : Z := KernelSyms.ftable + 24.

(* the [k]th entry, &ftable.file[k].  [fnode NFILE] is one past the last entry
   -- which is where the next global (<disk>) starts, and is the literal end
   pointer filealloc's scan compares its cursor against. *)
Definition fnode (k : nat) : mword 64 := acur file_base file_stride k.

(* the field addresses, in the EXACT [add_vec base (sign_extend' 64 imm)] form
   the instructions compute, so a load/store address unifies with the cell
   without rewriting. *)
Definition foff_of (a : mword 64) (i : Z) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int i : mword 12)).

Definition a_ftype     (k : nat) : mword 64 := fnode k.
Definition a_fref      (k : nat) : mword 64 := foff_of (fnode k) 4.
Definition a_freadable (k : nat) : mword 64 := foff_of (fnode k) 8.
Definition a_fwritable (k : nat) : mword 64 := foff_of (fnode k) 9.
Definition a_fpipe     (k : nat) : mword 64 := foff_of (fnode k) 16.
Definition a_fip       (k : nat) : mword 64 := foff_of (fnode k) 24.
Definition a_foff      (k : nat) : mword 64 := foff_of (fnode k) 32.
Definition a_fmajor    (k : nat) : mword 64 := foff_of (fnode k) 36.

(* the side conditions [ArrCursor]'s cursor lemmas take, discharged once. *)
Lemma file_base_nonneg : 0 <= file_base.
Proof. unfold file_base, KernelSyms.ftable. lia. Qed.
Lemma file_stride_pos : 0 < file_stride.
Proof. unfold file_stride. lia. Qed.
Lemma file_end_fits : file_base + file_stride * Z.of_nat NFILE < 2 ^ 64.
Proof.
  unfold file_base, file_stride, NFILE, KernelSyms.ftable.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* A FILE SLOT'S ADDRESS IS NEVER NULL.  The geometry alone says so
   ([file_base] is 0x80022468), and several proofs need it: it is what kills
   pipealloc's two dead "*f0 == 0" arms, and what tells sys_pipe that
   installing a file pointer in a descriptor really does fill it. *)
Lemma fnode_nonzero (k : nat) :
  (k < NFILE)%nat -> eq_vec (fnode k : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hk. apply eq_vec_false_iff. intro Hc.
  apply (f_equal bv_unsigned) in Hc.
  rewrite (acur_unsigned file_base file_stride k NFILE
             file_base_nonneg file_stride_pos file_end_fits ltac:(lia)) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by reflexivity.
  rewrite Hz in Hc.
  unfold file_base, file_stride, KernelSyms.ftable in Hc.
  lia.
Qed.

(* the same, as a plain disequality -- what a caller reasoning about the
   VALUE stored in a descriptor wants. *)
Lemma fnode_ne_zero (k : nat) :
  (k < NFILE)%nat -> (fnode k : mword 64) <> (zero_reg : mword 64).
Proof.
  intros Hk Hc.
  pose proof (fnode_nonzero k Hk) as Hf.
  apply eq_vec_false_iff in Hf. exact (Hf Hc).
Qed.

(* the four [type] codes (file.h's anonymous enum). *)
Definition FD_NONE   : mword 32 := mword_of_int 0.
Definition FD_PIPE   : mword 32 := mword_of_int 1.
Definition FD_INODE  : mword 32 := mword_of_int 2.
Definition FD_DEVICE : mword 32 := mword_of_int 3.

(* ------------------------------------------------------------------ *)
(*  The reference-count algebra                                        *)
(* ------------------------------------------------------------------ *)

Definition frefUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

(* ------------------------------------------------------------------ *)
(*  The payload's ghost identity, and why it is a SEPARATE COMPONENT    *)
(* ------------------------------------------------------------------ *)

(* A [struct file] of type FD_PIPE owns a share of one END of a pipe
   (PipeInv.v).  [fcontent] records the pipe's ADDRESS -- that is all the
   memory says -- and a pipe's reference is indexed by its ghost names, so a
   payload share has to carry them.  Recording them under an existential
   ([PipeInv.pipe_held]) is not enough: two shares of one slot's payload would
   then not be recombinable, and recombining them is exactly what the last
   [fileclose] does when it takes [file_rest]'s leftover fraction back.

   So the names are a per-slot GHOST FIELD, fractional and agreeing, living
   beside the content cells and split by exactly the same fractions.  What
   fixes its shape is WHERE it has to be written:

   * pipealloc sets [f->type = FD_PIPE] and [f->pipe = pi] holding NO lock --
     it is the exclusive holder (ref == 1), and that is the whole licence.
     So installing the names must need no authority either, which rules out
     an [agree] component on the [frefUR] entry: a fragment of an [auth]
     cannot be updated without the authoritative element, and the authority
     is inside ftable.lock.
   * the fraction still has to agree between holders, and to come home to
     [file_rest] when a reference departs.

   A frac-times-agree gmap with NO authority does both: the exclusive holder
   ([q = 1]) can update the value by a frame-preserving update on its own
   fragment (nothing else can hold a share), and any two shares agree.  It is
   a second COMPONENT of the table's one ghost rather than a second ghost
   name, so that nothing above the file layer -- and no boot wiring -- learns
   that the payload has an identity at all.  The supply is minted with the
   authority ([ftable_ghosts_alloc]), every slot present; a free slot's entry
   is held by the invariant, exactly like its content cells.

   [fp_icv] is the FD_INODE arm's, and is a CANCELLABLE INVARIANT'S name
   rather than the inode's: see [inode_pay] for why a share of an inode
   reference cannot be the reference itself.

   [fp_iq] IS NOT A GHOST NAME, and it is the one field here that is a plain
   number: it is THE FRACTION OF THE INODE'S IDENTITY-AND-LIVENESS SLICE that
   this slot's FD_INODE / FD_DEVICE payload lends its holders, fixed when the
   file is published and unchanged for the file's life.  A holder of file
   fraction [q] carries [q * fp_iq] of it; the parked reference inside the
   cinv is SHORT by exactly [fp_iq], and the last closer's gather adds the two
   back up (see [inode_pay]).

   WHY IT HAS TO BE A CONSTANT RATHER THAN AN EXISTENTIAL.  An existential
   "some share" splits and rejoins freely, which would make
   [file_core_split] fall out for nothing -- and would make the inode
   UNFREEABLE.  [IcacheRef.inode_held_gather] re-forms the canonical reference
   only from the EXACT fraction that was carved (canonical pairing, design
   §14.6/§14.7), and [IcacheInv.iref_close_last_step] then requires the final
   closer to hold the whole outstanding slice; so every sliver handed out has
   to come back, and an existential fraction lets a holder split and drop
   half.  With a constant, [file_core_split] is distributivity,
   [(q1 + q2) * Q = q1 * Q + q2 * Q].

   It lives HERE, in the per-slot names, because that is what this record is
   for: per-slot constants agreed across every holder by [fpay_tok].

   [fp_ig] IS THE INODE SLOT'S LIVENESS GENERATION (design fs-icache.md
   §17.6 (5), ratified §17.7), and it is [fp_iq]'s exact status: a per-slot
   CONSTANT fixed when the file is published.  It is what the fd's type
   witness is keyed on -- [inode_pay] carries [IcacheRef.ity_shot fp_ig ty]
   with "[ty] is not a directory if this fd is writable" and "[ty] is not a
   device if this fd is FD_INODE", and filewrite joins it to ilock's copy
   with [IcacheRef.ity_shot_agree].  It can be a constant
   because a live reference PINS the generation: a bump needs the slot's
   whole liveness unit, which does not exist while any share is outstanding
   ([IcacheInv.live_slot_alloc] at the recycle, [IcacheInv.live_slot_regen]
   at iput's REF-1 free window -- and this fd's share refutes both).

   THERE IS NO OFF-CINV NAME HERE ANY MORE (the old [fp_ocv]).  [off] is
   not a content field -- it is mutable under ip->lock by a holder of an
   arbitrarily small fraction -- but its home is no longer a per-slot
   cancellable invariant with a per-publication name: an FD_INODE file's
   cell sits in its INODE's off ledger ([ioff_escrow] below, a permanent
   per-itable-slot invariant), and the reference carries a fractional
   fragment of that ledger's ghost map instead of a cinv token.  The
   fragment needs no recorded name -- the ledger's gnames are the ambient
   [fsc_foff] family, keyed by the itable slot the payload already pins
   through [inode_shr_held_gen]. *)
(* [fp_inum] IS THE FILE'S INODE NUMBER, and it is [fp_iq]'s exact status one
   field over: a per-slot CONSTANT fixed when the file is published and
   unchanged for the file's life.  It is here rather than in [fcontent]
   because it is not a [struct file] field -- what the C struct records is
   [f->ip], the itable ENTRY, and entries are RECYCLED, so the pointer does
   not name a file across time.  The inum does.

   IT IS TIED, not merely recorded: [file_core]'s inode arm states
   [inode_pay] at THIS inum, and [inode_pay] carries
   [IcacheRef.inode_shr_held_gen] at it -- whose [inode_ident] is a
   points-to on the entry's own [i_inum] cell.  So the field cannot drift
   from the machine, and two holders of one file agree on it for the same
   reason they agree on the rest of [pn] ([fpay_tok_agree]).

   On a PIPE or a free slot it is meaningless and unconstrained, exactly as
   [fp_pipe] is on an inode file.  It reaches a descriptor only through
   [file_ref]'s state index, which ignores it off the FD_INODE arm. *)
Record fpnames := MkFPNames
  { fp_lock : gname; fp_pipe : pipe_names; fp_icv : gname; fp_iq : Qp;
    fp_ig : gname; fp_inum : mword 32 }.

Global Instance fpnames_inhabited : Inhabited fpnames :=
  populate (MkFPNames 1%positive
              (MkPipeNames 1%positive 1%positive 1%positive 1%positive)
              1%positive 1%Qp 1%positive (mword_of_int 0)).

Definition fpayUR : ucmra :=
  gmapUR nat (prodR fracR (agreeR (leibnizO fpnames))).

(* ------------------------------------------------------------------ *)
(*  The off-borrow LIVENESS COUNTER (third component)                   *)
(* ------------------------------------------------------------------ *)

(* An FD_INODE file's [off] cell lives in its inode's off ledger
   ([ioff_escrow] below) whose checked-out disjunct parks a token.  The
   EXCLUSIVE holder of a slot ([q = 1]) has to be able to refute a STALE
   checked-out state -- fileclose reclaims the cell holding no inode lock at
   all, so it has nothing to contradict the borrower's marker with.  What
   contradicts it is a COUNT: one fungible unit per outstanding reference,
   with the authority riding beside the reference-count authority inside
   ftable.lock.  At the last reference the authority records ONE, so a second
   unit -- the parked one -- is impossible, and the cell must be resident.

   THE COUNTER'S GNAME IS THE AMBIENT [FsCfg.fsc_fol], NOT the table's [γf]
   (off-ledger ruling): the ledger invariants park a unit in their
   checked-out arms, and a γf-keyed unit would force every ledger -- and
   hence [FsReady.fs_ready] and every environment that carries the family --
   to thread γf.  The unit still composes with the SAME authority inside
   ftable.lock ([ftable_auth] owns the [fsc_fol] column beside γf's), so the
   soundness story is unchanged: only the ghost location moved.  The
   counter's camera is its own [xv6G] member ([Xv6Cameras.flivG]) rather
   than a [fileUR] component, so the era fupd can mint the authority with
   no [fileG] in sight.

   The unit is [◯ {[k := 1%positive]}], a CLOSED element: that is what makes it
   FUNGIBLE, i.e. what lets a borrower prove that the token it takes back on
   return is the token it parked.  A slice of the borrower's own fraction is
   not fungible (the invariant hands it back existentially quantified) which is
   exactly why the marker cannot be one.

   [positiveR], not [natR], for the same reason the reference count uses it: a
   unit-free count has no zero fragment, so the entry can be DELETED when the
   last reference goes.  With [natR] a stale [◯ {[k := 0]}] is a legal frame
   and blocks the deallocating local update. *)
Definition fliveUR : ucmra := authUR (gmapUR nat positiveR).

(* the table's ghost: the reference-count authority and the payload names,
   under a single [γ] -- the [γf] every consumer already threads.  The
   off-borrow liveness counter is NOT a component any more: it lives at its
   own camera ([Xv6Cameras.flivG]) under the ambient [fsc_fol], because the
   off LEDGERS park its units and they are allocated with no [γf] in sight
   (see the note above). *)
Definition fileUR : ucmra := prodUR frefUR fpayUR.

(* the liveness authority's map is the reference-count map's COUNT column: one
   unit per outstanding reference, by construction. *)
Definition Mcount (M : gmap nat (Qp * positive)) : gmap nat positive := snd <$> M.

Lemma Mcount_lookup M k : Mcount M !! k = snd <$> (M !! k).
Proof. rewrite /Mcount lookup_fmap. reflexivity. Qed.
Lemma Mcount_insert M k e : Mcount (<[k := e]> M) = <[k := e.2]> (Mcount M).
Proof. rewrite /Mcount fmap_insert. reflexivity. Qed.
Lemma Mcount_delete M k : Mcount (delete k M) = delete k (Mcount M).
Proof. rewrite /Mcount fmap_delete. reflexivity. Qed.

(* THIS CLASS CARRIES ITS OWN CAMERA AND ITS OWN CONFIG, AND NOTHING ELSE.

   It used to carry [pipeG], [icacheG] and [cinvG] as superclasses too, for
   a good reason stated badly: "so that the ~100 files that merely mention
   [proc_priv] do not have to name the pipe layer's ghosts", with the rule
   "a file that needs both must take [fileG] alone and project: two instance
   paths to [inG Σ fracR] print identically and do not unify."

   The reason was right and the remedy was local.  Bundling pure capacity so
   that consumers name ONE class is exactly right -- it is why [Xv6G.xv6G]
   exists -- but a bundle per subsystem gives you as many instance paths as
   you have bundles, and the rule it forces ("take [fileG] alone") is
   unenforceable: twenty-seven files bound [fileG] and [!icacheG] side by
   side, and [FsReady.v] deliberately declared [icacheG]/[icfg] LAST so that
   resolution would prefer them.  That is the double path the rule was
   written to prevent, in the tree, compiling.

   So the three capacity classes moved to [xv6G], which is the ONE bundle,
   and this class keeps what is genuinely its own: the file table's camera,
   and [icfg] -- which is not capacity at all but a record of NAMES, so it
   does not belong in [xv6G] either.  A file that needs the file table now
   takes [xv6G] and [fileG]: one path to each. *)
(* THE TWO CONFIGURATION RECORDS RIDE ALONG, and the second one is new.

   [file_icfg] has been here since the file table first had to name the
   inode cache: "there is exactly one inode cache per system", so threading
   its gname would have put a filesystem ghost name on [ProcInv.proc_priv]
   and hence on the thirty-odd spec files that mention it (InodeRef.v).

   [file_fscfg] is the SAME argument for the REST of the file system, and it
   is here rather than as a binder of its own for a sharper reason.
   [FsReady.fs_ready] -- the one predicate that says "the file system is
   ready to operate" -- is stated at [fscfg]'s fields, and the whole point
   of it is to be CARRIED: forkret's not-forked arm produces it, the trap
   loop's residue holds it, every syscall reads it back.  So every interface
   on that path has to be able to NAME it: [SpecSyscall]'s environment,
   [UsertrapRes]'s residue, [SpecUservec]'s and [SpecUserretClosed]'s loop.
   Reaching them by adding a binder means adding it to sixteen files' worth
   of [Module Type] parameters and [Definition] signatures -- the interface
   sweep claude-notes/completed/explicit-cpuid.md is about, whose failure
   mode is a contract that compiles while meaning something else.  Reaching
   them through the class every one of those files ALREADY binds costs one
   field.

   AND SINCE RANK 1 THE CLASS IS THE ONLY PATH.  When [file_fscfg] landed,
   an fs contract still THREADED its own copy of every name in it and tied
   the two by a pure premise; the field was there so that the predicate
   could be NAMED at the interfaces that carry it.  Ranks 1a-1d removed the
   threading itself -- [cn], [γfs], [cov], [logstart], [γi], the itable
   lock, [dev], [nib], [inodestart], the log's names, the six device and
   allocator gnames and the image's three numbers, in that order -- so the
   fs contract surface now reads all of them off this class and off
   [file_icfg], and the tie records that used to relate the two spellings
   ([FsSyscalls.fs_world], [SpecFileclose.fclose_ties]) do not exist.  That
   is why the two-instance-path trap below is not a style rule: with no
   threaded copy left there is no second spelling to fall back on.

   NEITHER RECORD IS CAPACITY, which is why they are not in [Xv6G.xv6G] --
   see that file's "what is deliberately not here".  Both are per-boot
   VALUES (gnames, gsets, block numbers), so there is no camera and no
   second instance path to get wrong: a double path in a config record can
   only disagree about a VALUE, and resolution picks one instance per use
   site.  Files that used to bind [FSC : fscfg] beside [fileG] therefore
   drop the binder rather than keep both (FsReady.v, FsSyscalls.v,
   FirstTok.v). *)
(* THE OFF LEDGER'S CAPACITY ([ghost_mapG Σ nat unit]) IS DELIBERATELY NOT
   A FIELD HERE, and not a new field ANYWHERE: the class already has a
   member on the tree -- [Xv6Cameras.logG]'s [logtx_inG], which [TxPin]
   reuses the same way.  Both wrong placements were MEASURED (2026-08-31):
   a field here lets a bare [ghost_mapG Σ nat unit] goal enter [fileG],
   whose [subG_fileΣ] wants an [fscfg], which [file_fscfg] offers through
   [fileG] again -- the search cycle [BootShared]'s header records at
   400 GB, re-run at 703 GB by [subG_fileGpreS]'s [solve_inG]; a second
   field on [Xv6G.xv6G] is two instance paths to one class and breaks
   [IcacheEscrow]'s [iFrame] on the log's own [↪[ln_tx …]] elements.  This
   file, BELOW the bundle, binds the class bare in its sections; everything
   above resolves it through [xv6G] -> [logG] -> [logtx_inG], one path. *)
Class fileG (Σ : gFunctors) := FileG {
  file_inG :: inG Σ fileUR;
  file_icfg :: icfg;
  file_fscfg :: fscfg;
}.
Definition fileΣ : gFunctors := #[GFunctor fileUR].
Global Instance subG_fileΣ {Σ} `{ICFG : icfg} `{FSC : fscfg} :
  subG fileΣ Σ -> fileG Σ.
Proof. solve_inG. Qed.

(* ---- THE CAPACITY-ONLY HALF (fs-cfg-boot.md stage 3) ------------------
   [fileG] is not obtainable before boot runs, and that is the whole
   obstruction the boot-era allocation exists to remove: its only
   constructors are [subG_fileΣ] -- which needs an AMBIENT [icfg] and
   [fscfg], i.e. two records nothing in the tree ever produced -- or a
   section binder.  So a boot fupd that wants to MINT the two records has
   nowhere to stand: the instance it is supposed to build is a premise of
   its own statement.

   [fileGpreS] is the way out, and it is [BootShared.boot_shared_alloc]'s
   own move for [fdslotG]/[irefslotG]/[pavG] applied once more: the class
   splits into the CAMERA (which the [gFunctors] fixes once, before any
   fupd) and the two per-boot VALUES (which the era fupd chooses).
   [FsCfgBoot.fs_cfg_alloc] runs at [fileGpreS], returns [icfg] and [fscfg]
   existentially, and the caller reassembles [fileG] with [fileG_of] below.

   [file_preG] is deliberately NOT declared as an instance ([::]).  If it
   were, a context holding both [fileGpreS Σ] and [fileG Σ] -- which the
   wiring site does hold, since it builds the latter from the former --
   would have TWO resolution paths to [inG Σ fileUR], the exact hazard
   this file's header records for the capacity classes that moved to
   [Xv6G.xv6G] ("two instance paths print identically and do not unify").
   Nothing needs it as an instance: the one consumer is [fileG_of].

   [subG_fileΣ] and [fileG] itself are UNTOUCHED here; retiring the former
   is stage 4's business, not this file's. *)
Class fileGpreS (Σ : gFunctors) := FileGpreS { file_preG : inG Σ fileUR }.

Global Instance subG_fileGpreS {Σ} : subG fileΣ Σ -> fileGpreS Σ.
Proof. solve_inG. Qed.

(* THE CONSTRUCTOR.  [fileG] = capacity + the two records, so the boot
   fupd's existentials plug straight in.  Applied EXPLICITLY at the wiring
   site (fs-cfg-boot.md stage 4: "this is an application, not an
   elaboration"), which is what keeps the double-path trap shut. *)
Definition fileG_of {Σ} (FGP : fileGpreS Σ) (ICFG : icfg) (FSC : fscfg)
  : fileG Σ := @FileG Σ (@file_preG Σ FGP) ICFG FSC.

(* The immutable-while-referenced content of a [struct file]: every field but
   [ref] AND [off].

   [off] is deliberately NOT here.  It is neither ftable-protected nor
   immutable-while-referenced: it is mutable under ip->lock, by a holder of an
   arbitrarily SMALL fraction of the reference (fileread does [f->off += r]
   holding whatever share its descriptor has).  A fractional content field
   cannot express that, so [off] lives in its own per-slot borrow invariant --
   [FileOff.v] -- and the only thing FileInv keeps of it is the CELL ADDRESS
   [a_foff] and the liveness counter the borrow protocol needs.  See the "off"
   note at the bottom of this file and design/file-table.md. *)
Record fcontent := MkFContent {
  fc_type     : mword 32;
  fc_readable : bv 8;
  fc_writable : bv 8;
  fc_pipe     : mword 64;
  fc_ip       : mword 64;
  fc_major    : bv 16;
}.

(* ------------------------------------------------------------------ *)
(*  ... AND THE PART OF IT A FILE DESCRIPTOR SHOWS ITS USER            *)
(* ------------------------------------------------------------------ *)

(* [FdSlots.fdstate] is the user-visible state of one descriptor; this says
   WHEN a state is the honest reading of a given file.  It is a RELATION and
   not a function of the file, for two reasons, and the second is the one
   that matters:

   - the inode NUMBER is not a [struct file] field.  What the struct records
     is [f->ip], the itable ENTRY, and entries are recycled, so [C] alone
     cannot say which file this is; the number comes from the reference
     parked in [f->ip], via [fpnames.fp_inum].

   - IT CONSTRAINS [fc_type] IN BOTH DIRECTIONS.  A function from files to
     states has to send the type codes it does not recognise somewhere, and
     the only honest target is [FdClosed] -- which would mean [FdClosed] told
     a holder nothing about [f->type].  Read as a relation each arm PINS the
     type: a descriptor in state [FdOpen (FdPipe _)] is on a file whose
     [f->type] is FD_PIPE, and one in state [FdClosed] is on an UNTYPED
     file.  That is what lets [file_ref] hide its [fcontent] entirely --
     everything a holder used to read off [C] at this altitude, it now reads
     off the state.

   [fc_readable] / [fc_writable] are deliberately not related here: this
   increment tracks only whether a descriptor is open, what KIND of file it
   names, and which one.  Adding the mode later is a field on [fdtype], not
   a change of shape.

   DEVICE FILES ARE NOT GIVEN THEIR INUM even though they hold an inode
   reference too and could be.  A device fd's identity to its user is the
   driver behind it, which is [fc_major]; the inode it was opened through is
   a mount detail.  If that turns out to be wanted it is another conjunct on
   the [FdDevice] arm, and this is the only site that would change. *)
Definition fdstate_ok (inum : mword 32) (C : fcontent) (st : fdstate) : Prop :=
  match st with
  | FdClosed => fc_type C = FD_NONE
  | FdOpen r w t =>
      fc_readable C = ((if r then mword_of_int 1 else mword_of_int 0) : mword 8)
      /\ fc_writable C = ((if w then mword_of_int 1 else mword_of_int 0) : mword 8)
      /\ match t with
         | FdPipe        => fc_type C = FD_PIPE
         | FdInode n     => fc_type C = FD_INODE /\ n = bv_unsigned inum
         | FdDevice mj   => fc_type C = FD_DEVICE /\ mj = bv_unsigned (fc_major C)
         end
  end.

(* THE FORWARD READINGS, one per type code.  A proof that has just loaded
   [f->type] and branched on it learns which state its descriptor is in --
   which is how the [st]-keyed environments in SpecFileread and friends line
   up with the arm the code took.  The mode flags come out with it, since a
   typed state cannot fail to name them.  (The converse direction is the
   definition above and needs no lemma.) *)
Lemma fdstate_ok_pipe (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st -> fc_type C = FD_PIPE ->
  ∃ r w : bool, st = FdOpen r w FdPipe.
Proof.
  destruct st as [|r w [n| |mj]]; cbn; intros Hok Ht.
  - exfalso. rewrite Ht in Hok. apply (f_equal bv_unsigned) in Hok.
    by vm_compute in Hok.
  - exfalso. destruct Hok as (_ & _ & Hc & _). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
  - by exists r, w.
  - exfalso. destruct Hok as (_ & _ & Hc & _). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
Qed.

Lemma fdstate_ok_inode (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st -> fc_type C = FD_INODE ->
  ∃ r w : bool, st = FdOpen r w (FdInode (bv_unsigned inum)).
Proof.
  destruct st as [|r w [n| |mj]]; cbn; intros Hok Ht.
  - exfalso. rewrite Ht in Hok. apply (f_equal bv_unsigned) in Hok.
    by vm_compute in Hok.
  - destruct Hok as (_ & _ & _ & ->). by exists r, w.
  - exfalso. destruct Hok as (_ & _ & Hc). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
  - exfalso. destruct Hok as (_ & _ & Hc & _). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
Qed.

Lemma fdstate_ok_device (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st -> fc_type C = FD_DEVICE ->
  ∃ r w : bool, st = FdOpen r w (FdDevice (bv_unsigned (fc_major C))).
Proof.
  destruct st as [|r w [n| |mj]]; cbn; intros Hok Ht.
  - exfalso. rewrite Ht in Hok. apply (f_equal bv_unsigned) in Hok.
    by vm_compute in Hok.
  - exfalso. destruct Hok as (_ & _ & Hc & _). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
  - exfalso. destruct Hok as (_ & _ & Hc). rewrite Ht in Hc.
    apply (f_equal bv_unsigned) in Hc. by vm_compute in Hc.
  - destruct Hok as (_ & _ & _ & ->). by exists r, w.
Qed.

Lemma fdstate_ok_none (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st -> fc_type C = FD_NONE -> st = FdClosed.
Proof.
  destruct st as [|r w [n| |mj]]; cbn; intros Hok Ht; [reflexivity | | |];
    exfalso;
    [ destruct Hok as (_ & _ & Hc & _) | destruct Hok as (_ & _ & Hc)
    | destruct Hok as (_ & _ & Hc & _) ];
    rewrite Ht in Hc; apply (f_equal bv_unsigned) in Hc; by vm_compute in Hc.
Qed.

(* THE MODE FLAGS, read off the cells.  What a proof that has just branched
   on [beqz f->readable] learns about the state it was handed. *)
Lemma fdstate_ok_rw (inum : mword 32) (C : fcontent) (r w : bool) (t : fdtype) :
  fdstate_ok inum C (FdOpen r w t) ->
  fc_readable C = ((if r then mword_of_int 1 else mword_of_int 0) : mword 8)
  /\ fc_writable C = ((if w then mword_of_int 1 else mword_of_int 0) : mword 8).
Proof. destruct t; cbn; intros (H1 & H2 & _); by split. Qed.

(* A FLAG IS DETERMINED BY ITS CELL.  One byte, two possible readings, and
   they are distinct -- so the mode a state reports cannot drift from the
   [struct file] it reports it for. *)
Lemma fdstate_bit_inj (b1 b2 : bool) (v : mword 8) :
  v = ((if b1 then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  v = ((if b2 then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  b1 = b2.
Proof.
  destruct b1, b2; intros H1 H2; try reflexivity; exfalso;
    rewrite H1 in H2; apply (f_equal bv_unsigned) in H2; by vm_compute in H2.
Qed.

(* IT IS STILL FUNCTIONAL, which is the half of "projection" worth keeping:
   a file plus its inum admits AT MOST ONE state.  So two shares of one file
   report the same thing to their users ([file_pay_st_agree]), and reading a
   descriptor's state twice cannot give two answers.  What the relation drops
   is only the other half -- the obligation to invent a state for a file
   whose [f->type] is none of the four codes. *)
Lemma fdstate_ok_inj (inum : mword 32) (C : fcontent) (st1 st2 : fdstate) :
  fdstate_ok inum C st1 -> fdstate_ok inum C st2 -> st1 = st2.
Proof.
  destruct st1 as [|r1 w1 [n1| |m1]]; cbn; intros H1 H2.
  - by rewrite (fdstate_ok_none inum C st2 H2 H1).
  - destruct H1 as (Hr & Hw & Ht & ->).
    destruct (fdstate_ok_inode inum C st2 H2 Ht) as (r2 & w2 & ->).
    destruct (fdstate_ok_rw inum C r2 w2 _ H2) as [Hr2 Hw2].
    by rewrite (fdstate_bit_inj r1 r2 _ Hr Hr2) (fdstate_bit_inj w1 w2 _ Hw Hw2).
  - destruct H1 as (Hr & Hw & Ht).
    destruct (fdstate_ok_pipe inum C st2 H2 Ht) as (r2 & w2 & ->).
    destruct (fdstate_ok_rw inum C r2 w2 _ H2) as [Hr2 Hw2].
    by rewrite (fdstate_bit_inj r1 r2 _ Hr Hr2) (fdstate_bit_inj w1 w2 _ Hw Hw2).
  - destruct H1 as (Hr & Hw & Ht & ->).
    destruct (fdstate_ok_device inum C st2 H2 Ht) as (r2 & w2 & ->).
    destruct (fdstate_ok_rw inum C r2 w2 _ H2) as [Hr2 Hw2].
    by rewrite (fdstate_bit_inj r1 r2 _ Hr Hr2) (fdstate_bit_inj w1 w2 _ Hw Hw2).
Qed.

(* the three ways a descriptor's file can be typed, as ONE fact -- what
   every producer of an [ofile_slot] file disjunct actually has to pay. *)
(* THE MODE FLAGS ARE DETERMINED BY THE FILE, which is what lets a caller
   that knows the stored bytes name the state's booleans instead of
   existentially quantifying them.  [fdstate_ok] says [fc_readable C] IS the
   0/1 encoding of [r]; the encoding is injective on booleans, so two
   readings of the same field agree. *)
Lemma fdstate_ok_flags (inum : mword 32) (C : fcontent)
    (r w : bool) (t : fdtype) (rb wb : bool) :
  fdstate_ok inum C (FdOpen r w t) ->
  fc_readable C = ((if rb then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  fc_writable C = ((if wb then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  r = rb /\ w = wb.
Proof.
  intros (Hr & Hw & _) Hrb Hwb.
  rewrite Hrb in Hr. rewrite Hwb in Hw.
  split.
  - destruct r, rb; try reflexivity; exfalso;
      (apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate Hr).
  - destruct w, wb; try reflexivity; exfalso;
      (apply (f_equal bv_unsigned) in Hw; vm_compute in Hw; discriminate Hw).
Qed.

(* ...and the SHAPE the three per-type readings share: an open descriptor is
   [FdOpen] at some mode and type.  [sys_open]'s post wants exactly this and
   nothing finer -- which mode and which type are facts about the omode
   argument and the resolved inode, not about the descriptor table. *)
Lemma fdstate_ok_opened (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st ->
  fc_type C = FD_PIPE \/ fc_type C = FD_INODE \/ fc_type C = FD_DEVICE ->
  ∃ (r w : bool) (t : fdtype), st = FdOpen r w t.
Proof.
  intros Hok [H|[H|H]].
  - destruct (fdstate_ok_pipe   inum C st Hok H) as (r & w & ->). by exists r, w, FdPipe.
  - destruct (fdstate_ok_inode  inum C st Hok H) as (r & w & ->).
    by exists r, w, (FdInode (bv_unsigned inum)).
  - destruct (fdstate_ok_device inum C st Hok H) as (r & w & ->).
    by exists r, w, (FdDevice (bv_unsigned (fc_major C))).
Qed.

Lemma fdstate_ok_open (inum : mword 32) (C : fcontent) (st : fdstate) :
  fdstate_ok inum C st ->
  fc_type C = FD_PIPE \/ fc_type C = FD_INODE \/ fc_type C = FD_DEVICE ->
  st <> FdClosed.
Proof.
  intros Hok [H|[H|H]].
  - destruct (fdstate_ok_pipe   inum C st Hok H) as (? & ? & ->). discriminate.
  - destruct (fdstate_ok_inode  inum C st Hok H) as (? & ? & ->). discriminate.
  - destruct (fdstate_ok_device inum C st Hok H) as (? & ? & ->). discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  The [ref] word: zero exactly on a free slot                         *)
(* ------------------------------------------------------------------ *)

(* filealloc's scan tests [f->ref] with a sign-extending 4-byte load and a
   [c.beqz], so what the branch consumes is the 64-bit sign extension of the
   stored word.  These two lemmas are the whole content of "the physical test
   and the ghost state agree": a slot outside the authority reads zero, a slot
   inside it reads its (positive, in-range) count and so reads nonzero. *)
Lemma fref_word_zero :
  eq_vec (sign_extend' 64 (mword_of_int 0 : mword 32)) (zero_reg : mword 64) = true.
Proof. apply eq_vec_true_iff. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fref_word_nonzero (n : positive) :
  Z.pos n < 2 ^ 31 ->
  eq_vec (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) (zero_reg : mword 64) = false.
Proof.
  intro Hn.
  (* [lia] cannot evaluate [2^k]; name the three literals first. *)
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn.
  assert (Hlt32 : (Z.pos n < 2 ^ 32)%Z) by (rewrite E32; lia).
  (* the stored word's unsigned value is [n] itself (no wrap) ... *)
  assert (Hu : bv_unsigned (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (Z.of_N 32) with 32. rewrite E32.
    rewrite Z.mod_small; [reflexivity | lia]. }
  (* ... and it is below the half modulus, so the sign extension is the
     identity on the value. *)
  assert (Hs : bv_signed (mword_of_int (Z.pos n) : mword 32) = Z.pos n).
  { unfold bv_signed. rewrite Hu. apply bv_swrap_small.
    unfold bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
    assert (Ehalf : (2 ^ 32 / 2 = 2147483648)%Z) by (vm_compute; reflexivity).
    rewrite Ehalf. lia. }
  apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz in Hc. revert Hc.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. rewrite Hs.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite E64. rewrite Z.mod_small; [lia|]. lia.
Qed.

(* the signed [f->ref < 1] test: a positive in-range count is signed-positive,
   so [bge x0,a5] falls through.  This is what makes filedup's and
   fileclose's panic arms dead for a caller that holds a reference. *)
Lemma fref_word_spos (n : positive) :
  Z.pos n < 2 ^ 31 ->
  zopz0zKzJ_s (zero_reg : mword 64)
              (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) = false.
Proof.
  intro Hn.
  unfold zopz0zKzJ_s.
  rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite sint64_moi32; lia.
Qed.

(* the count component's [⋅] IS [Pos.add]; naming it lets [lia] see the
   arithmetic in the local-update side conditions. *)
Lemma pos_op_add (a b : positive) : (a ⋅ b) = (a + b)%positive.
Proof. reflexivity. Qed.
Lemma pos_succ_1_add (b : positive) : Pos.succ (1 + b) = (2 + b)%positive.
Proof. lia. Qed.

(* ------------------------------------------------------------------ *)
(*  [off]: the namespace and the value bound                           *)
(* ------------------------------------------------------------------ *)

(* one namespace, one ledger invariant per ITABLE slot ([ioff_escrow]
   below; [offN .@ i] so two inodes' ledgers can be open at one ghost step,
   the [ic_escrow] per-slot-namespace argument) *)
Definition offN : namespace := nroot .@ "fileoff".

(* THE VALUE BOUND.  An offset never exceeds MAXFILE*BSIZE, and this is not
   decoration: readi's contract demands [off + n < 2^31] and NOTHING IN MEMORY
   bounds a freshly loaded [off], so without a bound in the invariant fileread
   cannot call readi at all.  The bound is inductive: the BSS starts zeroed,
   sys_open writes 0, and every advance is [off + r] with [r] clamped by
   readi/writei to the file's size, which is itself bounded by MAXFILE*BSIZE.
   A pipe or device file never writes the cell. *)
Definition off_wf (v : mword 32) : Prop :=
  bv_unsigned v <= Z.of_nat MAXFILE * Z.of_nat BSIZE.

Lemma off_wf_zero : off_wf (mword_of_int 0 : mword 32).
Proof.
  rewrite /off_wf.
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 32) = 0) by reflexivity.
  rewrite Hz. unfold MAXFILE, BSIZE. lia.
Qed.

(* an offset in range is BELOW int range, which is what makes the [lw] that
   loads it read the literal (and readi's [off + n < 2^31] premise
   dischargeable from a bound on [n] alone). *)
Lemma off_wf_lt31 (v : mword 32) : off_wf v -> bv_unsigned v < 2 ^ 31.
Proof.
  rewrite /off_wf. unfold MAXFILE, BSIZE. intro H.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

(* Timelessness of the word points-to the off invariant puts in its body --
   typeclass search does not unfold a [Definition] on its own, exactly as
   [RiscvPtsto.word4_pointsto_timeless]'s comment says. *)
Global Instance word_pointsto_timeless' `{!riscvGS Σ} (ktr : CurKtier) (a : Arch.pa) (dq : dfrac)
    (w : bv 64) : Timeless (word_pointsto (KTR := ktr) a dq w).
Proof. rewrite /word_pointsto. apply _. Qed.

Global Instance word_pointsto_timeless'' `{!riscvGS Σ} (ktr : ktier) (a : Arch.pa) (dq : dfrac)
    (w : bv 64) : Timeless (word_pointsto (KTR := ktr) a dq w).
Proof. exact (word_pointsto_timeless' ktr a dq w). Qed.

Section FileInv.
  Context `{XI : TsoCtx.CurCtx}.
  (* [icacheG]/[pipeG]/[cinvG] are bound HERE rather than reached through
     [fileG], since they left that class (see its note).  This file is
     BELOW [Xv6G.v] -- it is one of the files the bundle is built out of --
     so it names them individually; everything above takes [xv6G]. *)
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ,
            !icacheG Σ, !pipeG Σ, !cinvG Σ, !irefslotG Σ,
            !ghost_mapG Σ nat unit, !flivG Σ}.

  (* ---- the content cells, at an arbitrary fraction ----

     SIX fields: [off] is gone (an FD_INODE file's cell is in the off
     ledger, any other rides [file_core] as [foff_dead]), and [ref] was
     never here.

     [a_fip] IS BACK AT THE FULL NOMINAL FRACTION (off-ledger ruling).  The
     old per-slot borrow invariant held half of this cell permanently --
     that was the only way a per-FILE invariant could know WHICH INODE
     governs its offset.  The ledger is per-INODE, so it names [ientry i]
     outright and the asymmetry retires: the tie between a file and its
     ledger is the [ioff_frag] in [file_core]'s FD_INODE arm, pinned to
     [fc_ip C] by the same [∃ i, fc_ip C = ientry i] the payload's
     [inode_shr_held_gen] already carries.

     A [Qp] rather than a [dfrac]: every use is [DfracOwn] and the whole
     design turns on fractions adding back up to one. *)
  Definition file_fields (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (a_ftype k     ↦₄{DfracOwn q} fc_type C ∗
     a_freadable k ↦ₘ{DfracOwn q} fc_readable C ∗
     a_fwritable k ↦ₘ{DfracOwn q} fc_writable C ∗
     a_fpipe k     ↦₈{DfracOwn q} fc_pipe C ∗
     a_fip k       ↦₈{DfracOwn q} fc_ip C ∗
     a_fmajor k    ↦₂{DfracOwn q} fc_major C)%I.

  (* ---- ONE FREE ENTRY, AS THE IMAGE LEAVES IT ----

     40 bytes of .bss, and what the carve has to say about them splits three
     ways.  THREE WORDS COME OUT AT A LITERAL VALUE, because the table's own
     predicates read them: [type] is [FD_NONE] (that is what makes the slot
     free), [ref] is zero (filealloc's scan tests it with a [c.beqz] --
     [fref_word_zero]), and [off] is zero, which is the base case of
     [off_wf]'s inductive bound.  THE OTHER FIVE FIELDS are
     contents-existential: nothing reads them until the slot is published,
     and a free [fslot] quantifies its [fcontent] anyway.

     [BootCarveMain] carves this out of the image and [FileInv.ftable_res_boot]
     turns [NFILE] of them into the ftable lock's resource.  Nothing else in
     the tree ever mentions it: past boot a slot is only ever reached through
     [fslot]. *)
  Definition fentry_raw (k : nat) : iProp Σ :=
    (a_ftype k ↦₄ FD_NONE ∗
     a_fref k ↦₄ (mword_of_int 0 : mword 32) ∗
     (∃ r : bv 8, a_freadable k ↦ₘ r) ∗
     (∃ w : bv 8, a_fwritable k ↦ₘ w) ∗
     (∃ pp : mword 64, a_fpipe k ↦₈ pp) ∗
     (∃ ip : mword 64, a_fip k ↦₈ ip) ∗
     a_foff k ↦₄ (mword_of_int 0 : mword 32) ∗
     (∃ mj : bv 16, a_fmajor k ↦₂ mj))%I.

  (* ---- the two components of the table's ghost ----

     [fref_own] is "own this much of the reference-count component and none of
     the payload one"; every existing law about the count is stated over it,
     so the product is invisible below. *)
  Definition fref_own (γ : gname) (a : frefUR) : iProp Σ :=
    own γ ((a, ε) : fileUR).

  Lemma fref_own_op γ a b : fref_own γ (a ⋅ b) ⊣⊢ fref_own γ a ∗ fref_own γ b.
  Proof.
    rewrite /fref_own -own_op.
    assert (H : (((a, ε) : fileUR) ⋅ (b, ε)) ≡ ((a ⋅ b, ε) : fileUR)).
    { rewrite -pair_op left_id. reflexivity. }
    by rewrite H.
  Qed.

  Lemma fref_own_update γ a b : (a ~~> b) -> fref_own γ a ==∗ fref_own γ b.
  Proof.
    intros Hup. rewrite /fref_own. iApply own_update.
    apply prod_update; [exact Hup | done].
  Qed.

  Lemma fref_own_update_2' γ a b c :
    (a ⋅ b ~~> c) -> fref_own γ a -∗ fref_own γ b ==∗ fref_own γ c.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (fref_own_op γ a b with "[$Ha $Hb]") as "H".
    by iApply (fref_own_update with "H").
  Qed.

  Lemma fref_own_update_2 γ a b a' b' :
    (a ⋅ b ~~> a' ⋅ b') ->
    fref_own γ a -∗ fref_own γ b ==∗ fref_own γ a' ∗ fref_own γ b'.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (fref_own_op γ a b with "[$Ha $Hb]") as "H".
    iMod (fref_own_update _ _ (a' ⋅ b') Hup with "H") as "H".
    by iApply fref_own_op.
  Qed.

  Lemma fref_own_valid_2 γ a b :
    fref_own γ a -∗ fref_own γ b -∗ ⌜✓ (a ⋅ b)⌝.
  Proof.
    rewrite /fref_own. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %[Hv _]. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The off-borrow liveness counter                                    *)
  (* ------------------------------------------------------------------ *)

  (* "own this much of the liveness component and none of the other two" --
     the same shape as [fref_own], so the counter's laws are stated without
     the product ever showing. *)
  (* AT THE AMBIENT [fsc_fol] and ITS OWN CAMERA ([Xv6Cameras.flivG]),
     not a γ parameter and not a [fileUR] component -- see the note above
     [fliveUR]. *)
  Definition flive_own (a : fliveUR) : iProp Σ := own fsc_fol a.

  Lemma flive_own_op a b : flive_own (a ⋅ b) ⊣⊢ flive_own a ∗ flive_own b.
  Proof. rewrite /flive_own own_op //. Qed.

  Lemma flive_own_update a b : (a ~~> b) -> flive_own a ==∗ flive_own b.
  Proof. intros Hup. rewrite /flive_own. by iApply own_update. Qed.

  Lemma flive_own_update_2 a b a' b' :
    (a ⋅ b ~~> a' ⋅ b') ->
    flive_own a -∗ flive_own b ==∗ flive_own a' ∗ flive_own b'.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (flive_own_op a b with "[$Ha $Hb]") as "H".
    iMod (flive_own_update _ (a' ⋅ b') Hup with "H") as "H".
    by iApply flive_own_op.
  Qed.

  Lemma flive_own_update_2' a b c :
    (a ⋅ b ~~> c) -> flive_own a -∗ flive_own b ==∗ flive_own c.
  Proof.
    intros Hup. iIntros "Ha Hb".
    iDestruct (flive_own_op a b with "[$Ha $Hb]") as "H".
    by iApply (flive_own_update with "H").
  Qed.

  Lemma flive_own_valid_2 a b :
    flive_own a -∗ flive_own b -∗ ⌜✓ (a ⋅ b)⌝.
  Proof.
    rewrite /flive_own. iIntros "Ha Hb".
    by iDestruct (own_valid_2 with "Ha Hb") as %Hv.
  Qed.

  (* ONE unit of "there is an outstanding reference on slot k".  A closed
     element, hence fungible: what comes back out of the borrow invariant is
     provably what went in. *)
  Definition flive_tok (k : nat) : iProp Σ :=
    flive_own (◯ {[ k := 1%positive ]}).

  (* the authoritative element, held by [ftable_res] inside ftable.lock.  It is
     BOTH authorities -- the reference-count one and the off-borrow liveness
     one, whose map is the count column of the same [M].  Bundling them here
     rather than adding a conjunct to [ftable_res] keeps every ghost step's
     statement, and hence every caller, unchanged. *)
  Definition ftable_auth (γ : gname) (M : gmap nat (Qp * positive)) : iProp Σ :=
    (fref_own γ (● M) ∗ flive_own (● Mcount M))%I.

  (* ---- one reference's ghost fragment ---- *)
  Definition fref_tok (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    fref_own γ (◯ {[ k := (q, 1%positive) ]}).


  (* ------------------------------------------------------------------ *)
  (*  The payload: the thing a [struct file] is a reference TO            *)
  (* ------------------------------------------------------------------ *)

  (* ---- AN FD_INODE FILE'S PAYLOAD: A SHARE OF ONE INODE REFERENCE ----

     The predicate this file carried as [emp] until C6b.  What replaced it
     is NOT [IcacheRef.inode_held] at fraction [q], and the reason is the
     whole content of the definition:

     an icache reference is [iref_tok γ k q ∗ inode_ident k q dev inum],
     and its ghost fragment [◯ {[k := (q, 1%positive)]}] carries a COUNT of
     one.  Two of them compose to a count of TWO -- a second reference,
     which the itable would have to have handed out.  So [inode_held] does
     not split fractionally, at any fraction, and [file_core_split] --
     which is a genuine ⊣⊢, used leftwards by filedup and rightwards by
     fileclose -- cannot be satisfied by any function of [q] that mentions
     the token directly.  Recombining a resource that is not itself
     fractional out of fractional shares is exactly what a CANCELLABLE
     INVARIANT is for, and it is what [PipeInv] already does one layer down
     ([pipe_ref] carries [cinv_own (pn_cancel γp) (q/2)] beside its own
     fraction).  So: the reference goes into a [cinv], the persistent half
     rides every share, and the FRACTION is the cancel token.  The last
     closer -- and only it -- holds [cinv_own γx 1], cancels, and walks
     away with a WHOLE [inode_held] to give to iput.

     THE THIRD CONJUNCT, AND WHY THE PARKED REFERENCE IS SHORT (design §14.6's
     "share beside the cinv").  A cancel token alone says nothing ABOUT the
     inode: it cannot be read through, and it cannot discharge a contract that
     wants to know the entry is live -- which is exactly what a reader needs
     ([SpecFileread]'s [frn_s], and [SpecIlock] v3 behind it, both take an
     [IcacheRef.inode_shr]).  So a real slice travels beside the token.

     IT CANNOT BE CARVED OUT OF THE PARKED REFERENCE ON DEMAND, because the
     cinv's content is not accessible without cancelling it.  It is carved
     ONCE, when the payload is published ([inode_pay_alloc]), and what goes
     into the cinv is therefore the parent SHORT by the whole outstanding
     slice: [IcacheRef.inode_held_short v (fp_iq pn)].  That is not a breach of
     canonical pairing -- [inode_ref_short] IS the design's name for a parent
     with a share out, and the pairing is restored by the gather, which is the
     last closer's move ([inode_pay_cancel]) and happens before iput ever sees
     the reference.  Nothing can spend the parked reference in the meantime:
     the cinv is the only holder and cancelling it is what the closer does.

     The travelling slice is PROPORTIONAL, [q * fp_iq pn], so that the split
     law is distributivity and the closer at [q = 1] holds exactly the
     [fp_iq pn] the cinv is short by.  See the header above [fpnames] for why
     the constant cannot be an existential.

     [v] is the pointer, not the slot: [ientry_inj] makes them the same
     thing, and the file table has no vocabulary for a slot -- which is why
     both [inode_held_short] and [inode_shr_held] are stated at the pointer. *)
  Definition fileipN : namespace := nroot .@ "fileip".

  (* THE FOURTH CONJUNCT: THE FD'S TYPE WITNESS (design fs-icache.md §17.6
     (5), ratified §17.7).  filewrite's FD_INODE arm must rebuild
     [IcacheEscrow.ic_loaded], whose [DirView.dir_ok] constrains a
     DIRECTORY's data bytes -- and an arbitrary user write into a directory
     breaks it.  The real xv6 invariant is five frames up: sys_open refuses
     writable directory fds.  This is where it crosses.

     The travelling share is therefore GENERATION-NAMED, and the witness is
     that generation's one-shot: ilock's postcondition hands filewrite
     [ity_shot g (di_type dn)] at the caller's [g], this payload holds
     [ity_shot g ty] with [ty <> T_DIR], [IcacheRef.ity_shot_agree] joins
     them, and [DirView.dir_ok_not_dir] finishes.  A generation sees at most
     one fill (§17.6), which is what makes the agreement mean something.

     CONDITIONAL ON [wr], NOT UNCONDITIONAL: an O_RDONLY directory fd is
     legal and fileread never needs the fact.  [wr] is [fc_wbool C] at the
     call site in [file_core], and FD_DEVICE selects this payload too but
     never reaches writei.

     THE FIFTH CONJUNCT: THE FD_INODE ARM'S "NOT A DEVICE" (owner's ruling,
     2026-08-29).  sys_open writes [f->type = FD_DEVICE] EXACTLY when
     [ip->type == T_DEVICE] and FD_INODE otherwise, so an FD_INODE
     descriptor's parked inode is a regular file or a directory -- never a
     device.  The fact was true of the code and dropped at the store, which
     left the fourth conjunct as the payload's only type witness: it
     excludes a DIRECTORY on a writable fd and nothing else.  That gap cost
     [SpecSysWriteAUEra] a whole spurious third arm (a T_DEVICE inode behind
     an FD_INODE fd, on which [FsAbs.abs_node] reads [ADev] and writei moves
     no field the abstract view can see) and blocked read's
     "FdInode => AFile or ADir" custody tie.  This is where it crosses.

     IT IS KEYED ON THE DESCRIPTOR'S TYPE, WHICH IS WHY [fdty] IS A
     PARAMETER.  One payload serves both typed arms ([file_core] selects it
     on FD_INODE or FD_DEVICE), and on the FD_DEVICE arm the claim is FALSE
     -- the parked inode is precisely a device there.  So the conjunct is
     unconditional in [wr] (unlike the fourth) and conditional on the FD's
     own type word, which is [fc_type C] at the call site, exactly as [wr]
     is [fc_wbool C].  On the device arm the implication is vacuous by
     [FD_DEVICE <> FD_INODE], which is what its publisher discharges.

     THE NUMBER IS [FsImg.T_DEVICE_z], QUALIFIED AND NOT RESTATED.  FsImg is
     already in this file's cone (through [FsCfg]), so the constant is
     nameable without importing the disk-image layer for one integer --
     [ProofSysOpenAUStores] spells it the same way.  Its sibling [T_DIR_z]
     is unqualified only because [DirView] is imported here for the fourth
     conjunct's sake.

     Everything here is PERSISTENT except the cinv token and the share, so
     [inode_pay_split]'s distributivity is untouched. *)
  (* [inum] IS NAMED HERE, and that is the only change the fd-state ghost
     needed of this layer: the slice this payload carries already pinned the
     inum through [inode_ident], it was simply ∃-bound.  Naming it costs the
     consumers that do not care nothing -- an [∃ inum] in front of the
     payload is exactly what they used to have. *)
  Definition inode_pay (γx : gname) (Q : Qp) (g : gname) (inum : mword 32)
      (v : mword 64) (fdty : mword 32) (wr : bool) (q : Qp) : iProp Σ :=
    (cinv fileipN γx (inode_held_short v Q) ∗ cinv_own γx q ∗
     inode_shr_held_gen v (q * Q)%Qp g inum ∗
     ∃ ty : bv 16, ity_shot g ty ∗ ⌜wr = true -> bv_unsigned ty <> T_DIR_z⌝ ∗
                   ⌜fdty = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z⌝)%I.

  Lemma inode_pay_split γx Q g inum v fdty wr q1 q2 :
    inode_pay γx Q g inum v fdty wr (q1 + q2) ⊣⊢
    inode_pay γx Q g inum v fdty wr q1 ∗ inode_pay γx Q g inum v fdty wr q2.
  Proof.
    rewrite /inode_pay cinv_own_fractional Qp.mul_add_distr_r
            inode_shr_held_gen_split.
    iSplit.
    - iIntros "(#Hi & [H1 H2] & [S1 S2] & #Hw)". iFrame "Hi H1 H2 S1 S2 Hw".
    - iIntros "[(#Hi & H1 & S1 & #Hw) (_ & H2 & S2 & _)]".
      iFrame "Hi H1 H2 S1 S2 Hw".
  Qed.

  (* THE LAST CLOSER'S MOVE, packaged: fraction one is the whole reference.
     A fupd, and the only one the file layer performs.  The gather is what
     makes it a WHOLE one -- the cinv gives back the parent short by [Q] and
     the closer's own arm is [1 * Q], the exact complement. *)
  Lemma inode_pay_cancel (E : coPset) (γx : gname) (Q : Qp) (g : gname)
      (inum : mword 32) (v : mword 64) (fdty : mword 32) (wr : bool) :
    ↑fileipN ⊆ E -> inode_pay γx Q g inum v fdty wr 1 ={E}=∗ inode_held v.
  Proof.
    iIntros (HE) "(#Hi & Hown & Hs & _)".
    iMod (cinv_cancel with "Hi Hown") as "H"; [exact HE|].
    iMod "H". iModIntro. rewrite Qp.mul_1_l.
    iDestruct (inode_shr_held_gen_forget with "Hs") as "Hs".
    iApply (inode_held_gather with "H Hs").
  Qed.

  (* the travelling share names SOME generation -- the one every slice of
     this slot names, since [iliveUR]'s agree is per-KEY ([IcacheRef.
     live_gen_agree]).  A publisher learns it by shedding, which is why
     [inode_pay_alloc] below takes the pieces rather than the whole
     reference: the type witness sys_open must supply is keyed on a gname it
     cannot name until the shed has happened. *)
  Local Lemma inode_shr_held_gen_intro (v : mword 64) (s : Qp) :
    inode_shr_held v s -∗ ∃ (g : gname) (inum : mword 32),
      inode_shr_held_gen v s g inum.
  Proof.
    rewrite /inode_shr_held /inode_shr_held_gen.
    iIntros "(%k & %inum & %Hv & %Hk & %Hb & Hs)".
    rewrite inode_shr_gen_intro. iDestruct "Hs" as (g) "Hs".
    iExists g, inum, k. by iFrame.
  Qed.

  (* the shed hands back the INUM as well, and this is where sys_open learns
     it: the number it records in [fp_inum] -- hence the one a descriptor's
     [FdSlots.FdInode] reports to user space -- is read off the very
     reference being installed, not passed down from namei's caller.  That
     is what makes the field impossible to get wrong. *)

  (* ...and the inverse of the cancel, for whoever PUBLISHES an FD_INODE file
     (sys_open): a shed inode reference plus a TYPE WITNESS becomes a payload
     at fraction one.  The [Q] and the [g] the caller ends up recording in
     [fpnames] are the shed's outputs, which is why they are parameters here
     rather than existentials: sys_open runs [inode_held_shed_gen] first,
     reads [g] off it, discharges the witness against ilock's postcondition
     (T_FILE by construction on the O_CREATE path; O_RDONLY forced on a
     T_DIR inode on the open-existing one), and only then installs the
     names. *)
  (* THE SECOND PREMISE IS THE OWNER'S RULING, PAID HERE.  sys_open knows it
     for free: the [lh a4,68(s1); c.li a5,3; beq] at +0x76 is the test that
     decides which type word the store writes, so on the arm that writes
     FD_INODE the inode's type is not T_DEVICE and on the arm that writes
     FD_DEVICE the implication is vacuous.  [ProofSysOpenParts.so_tdev_zne]
     and [ProofSysOpenParts.so_dev_vac] state the two arms in exactly this
     shape. *)
  Lemma inode_pay_alloc (E : coPset) (v : mword 64) (Q : Qp) (g : gname)
      (inum : mword 32) (fdty : mword 32) (wr : bool) (ty : bv 16) :
    (wr = true -> bv_unsigned ty <> T_DIR_z) ->
    (fdty = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z) ->
    inode_held_short v Q -∗ inode_shr_held_gen v Q g inum -∗ ity_shot g ty
    ={E}=∗ ∃ γx : gname, inode_pay γx Q g inum v fdty wr 1.
  Proof.
    iIntros (Hwr Hdv) "Hsh Hs #Hty".
    iMod (cinv_alloc E fileipN (inode_held_short v Q) with "[Hsh]")
      as (γx) "[#Hi Hown]".
    { by iApply bi.later_intro. }
    iModIntro. iExists γx. rewrite /inode_pay Qp.mul_1_l.
    iFrame "Hi Hown Hs". iExists ty. iFrame "Hty".
    iSplit; iPureIntro; [exact Hwr | exact Hdv].
  Qed.

  (* ---- THE READING THE FD_INODE ARM'S CONSUMERS ASK FOR ----

     The fifth conjunct, surfaced against a caller's OWN copy of the
     generation's one-shot -- which is what ilock's postcondition hands
     filewrite and fileread ([IcacheRef.ity_shot_agree] joins the two, the
     generation seeing at most one fill).  So a function that has locked the
     inode behind an FD_INODE descriptor can refute the device row outright:
     [FsAbs.abs_node]'s [ADev] arm is unreachable there, which is what
     [SpecSysWriteAUEra]'s third arm and [SpecSysReadAU]'s owner question 2
     were both waiting on.

     PURE CONCLUSION, so it costs the payload nothing: the caller keeps the
     reference it read the fact off.  A holder of a [file_pay_st] reaches
     the same fact through [SpecFileread.fileread_pay_carve], which is where
     the payload's generation is named -- this layer's own statement of it,
     stated once, is here. *)
  Lemma inode_pay_not_dev (γx : gname) (Q : Qp) (g : gname) (inum : mword 32)
      (v : mword 64) (wr : bool) (q : Qp) (ty : bv 16) :
    inode_pay γx Q g inum v FD_INODE wr q -∗ ity_shot g ty -∗
    ⌜bv_unsigned ty <> FsImg.T_DEVICE_z⌝.
  Proof.
    iIntros "(_ & _ & _ & Hwt) #Hshot".
    iDestruct "Hwt" as (ty') "(#Hs & _ & %Hdv)".
    iDestruct (ity_shot_agree with "Hs Hshot") as %<-.
    iPureIntro. exact (Hdv eq_refl).
  Qed.

  (* the per-slot payload-names ghost: fractional, agreeing, and updatable
     by whoever holds the whole of it.  See the header above [fpnames]. *)
  Definition fpay_tok (γ : gname) (k : nat) (q : Qp) (pn : fpnames) : iProp Σ :=
    own γ ((ε, {[ k := (q, to_agree (pn : leibnizO fpnames)) ]}) : fileUR).

  Lemma fpay_tok_split γ k q1 q2 pn :
    fpay_tok γ k (q1 + q2) pn ⊣⊢ fpay_tok γ k q1 pn ∗ fpay_tok γ k q2 pn.
  Proof.
    rewrite /fpay_tok -own_op.
    assert (H : (((ε, {[ k := (q1, to_agree (pn : leibnizO fpnames)) ]}) : fileUR)
                 ⋅ (ε, {[ k := (q2, to_agree (pn : leibnizO fpnames)) ]}))
                ≡ ((ε, {[ k := ((q1 + q2)%Qp, to_agree (pn : leibnizO fpnames)) ]})
                   : fileUR)).
    { rewrite -pair_op left_id singleton_op -pair_op frac_op agree_idemp.
      reflexivity. }
    by rewrite H.
  Qed.

  Lemma fpay_tok_agree γ k q1 pn1 q2 pn2 :
    fpay_tok γ k q1 pn1 -∗ fpay_tok γ k q2 pn2 -∗ ⌜pn1 = pn2⌝.
  Proof.
    rewrite /fpay_tok. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[_ Hv]. iPureIntro.
    simpl in Hv. rewrite singleton_op in Hv. apply singleton_valid in Hv.
    destruct Hv as [_ Hv]; simpl in Hv.
    by apply to_agree_op_valid_L in Hv.
  Qed.

  (* THE reason the names are not on the ftable authority: the exclusive
     holder installs them with no lock in hand.  This is pipealloc's ghost
     step, and it happens at the [sd] that writes [f->pipe]. *)
  Lemma fpay_tok_update γ k pn pn' :
    fpay_tok γ k 1 pn ==∗ fpay_tok γ k 1 pn'.
  Proof.
    rewrite /fpay_tok. iIntros "H". iApply (own_update with "H").
    apply prod_update; [done|]. cbn [fst snd].
    apply singleton_update, cmra_update_exclusive. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  [off]: the per-slot CANCELLABLE borrow invariant                    *)
  (* ------------------------------------------------------------------ *)

  (* ---- full ownership of a word is EXCLUSIVE ----
     [ctx_pointsto_ne] at one address is a contradiction; that is all this
     is, and it is what refutes a stale marker / a stale resident cell. *)
  Lemma word4_pointsto_excl (a : Arch.pa) (dq : dfrac) (w1 w2 : bv 32) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !ctx_word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (ctx_pointsto_ne with "Hb1 Hb2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  Definition off_resident (k : nat) : iProp Σ :=
    (∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝)%I.

  (* the borrower's marker: the inode's [valid] flag, which ilock hands out
     at 1 and which no fs.c callee below ilock touches.  It is EXCLUSIVE, it
     is keyed by the INODE'S ADDRESS (unlike a ghost-named token, which a
     second borrower has no way to match) and it is CLOSED -- the value is
     pinned at 1 -- so what a borrower takes back on return is provably what
     it parked.  See FileOff.v's header for the full argument. *)
  Definition off_mark (ip : mword 64) : iProp Σ :=
    (i_valid ip ↦₄ (mword_of_int 1 : mword 32))%I.

  (* [tso FileInvDefs.v:1071]: the marker's accessor.  On main the marker is
     the ambient cell itself, so this is definitional. *)
  Lemma off_mark_acc (ip : mword 64) :
    off_mark ip ⊣⊢ i_valid ip ↦₄ (mword_of_int 1 : mword 32).
  Proof. reflexivity. Qed.

  (* ================================================================== *)
  (*  THE OFF LEDGER (claude-notes/projects/off-ledger.md)               *)
  (* ================================================================== *)

  (* [off] is protected by [ip->lock], and ownership now follows that
     discipline: each ITABLE slot [i] carries a permanent invariant -- its
     off LEDGER -- whose ghost map records WHICH file slots hold an
     FD_INODE reference on that inode, and which owns, per such file slot
     [k], either the resident [f->off] cell (with [off_wf], the bound
     fileread needs) or the borrower's parked credentials.

     The CHECKOUT CREDENTIAL is [off_mark (ientry i)] -- the inode's
     [valid] cell, which only the sleeplock holder has (ilock hands it out
     at 1 and nothing below ilock touches it).  It is exclusive, keyed by
     the inode's ADDRESS, and closed, so a borrower provably takes back
     what it parked; and because the ledger is per-INODE it can name
     [ientry i] outright -- no [a_fip] half, no ghost shadow.  The parked
     [flive_tok] is the LAST CLOSER's handle: fileclose reclaims the cell
     holding NO inode lock, and what refutes a stale checked-out arm there
     is the liveness COUNT read against the authority inside ftable.lock
     ([FileInv.ioff_reclaim]).

     A file that is NOT an FD_INODE file (pipe, device, free) owns its cell
     directly at its own fraction ([foff_dead] -- the cell is dead memory
     there, no bound needed; sys_open re-establishes [off_wf] by writing 0
     when it publishes).

     The ghost maps' gnames are the ambient [fsc_foff] family and the
     invariant is allocated once per era by the boot fupd
     ([ioff_escrows_alloc_at] below), so [ioff_escrows] is a FIXED
     PERSISTENT FAMILY that rides [FsReady.fs_ready] -- exactly what the
     old per-publication cancellable invariant could never be. *)

  Definition foff_dead (k : nat) (q : Qp) : iProp Σ :=
    (∃ v : mword 32, a_foff k ↦₄{DfracOwn q} v)%I.

  Lemma foff_dead_split (k : nat) (q1 q2 : Qp) :
    foff_dead k (q1 + q2) ⊣⊢ foff_dead k q1 ∗ foff_dead k q2.
  Proof.
    rewrite /foff_dead. iSplit.
    - iIntros "(%v & Hc)".
      iEval (rewrite (ctx_word4_pointsto_frac_split _ (a_foff k))) in "Hc".
      iDestruct "Hc" as "[H1 H2]".
      iSplitL "H1"; iExists v; iFrame.
    - iIntros "[(%v1 & H1) (%v2 & H2)]".
      iDestruct (ctx_word4_pointsto_agree with "H1 H2") as %<-.
      iExists v1.
      iEval (rewrite (ctx_word4_pointsto_frac_split _ (a_foff k))).
      iFrame.
  Qed.

  Global Instance foff_dead_timeless k q : Timeless (foff_dead k q).
  Proof.
    rewrite /foff_dead.
    apply bi.exist_timeless; intro v. apply _.
  Qed.

  (* one file slot's membership fragment in inode slot [i]'s ledger, at the
     reference's own fraction.  [unit] values: membership IS the content. *)
  Definition ioff_frag (i k : nat) (q : Qp) : iProp Σ :=
    (k ↪[fsc_foff i]{# q} ())%I.

  Lemma ioff_frag_split (i k : nat) (q1 q2 : Qp) :
    ioff_frag i k (q1 + q2) ⊣⊢ ioff_frag i k q1 ∗ ioff_frag i k q2.
  Proof.
    rewrite /ioff_frag. iSplit.
    - iIntros "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
      rewrite dfrac_op_own. iExact "H".
  Qed.

  Global Instance ioff_frag_timeless i k q : Timeless (ioff_frag i k q).
  Proof. rewrite /ioff_frag. apply _. Qed.

  (* THE TIE A REFERENCE CARRIES (file_core's FD_INODE arm): the fragment,
     pinned to the file's own [f->ip] value.  The [∃ i] joins across shares
     by [ientry_inj]. *)
  Definition ioff_ref (v : mword 64) (k : nat) (q : Qp) : iProp Σ :=
    (∃ i : nat, ⌜v = ientry i⌝ ∗ ⌜(i < NINODE)%nat⌝ ∗ ioff_frag i k q)%I.

  Lemma ioff_ref_split (v : mword 64) (k : nat) (q1 q2 : Qp) :
    ioff_ref v k (q1 + q2) ⊣⊢ ioff_ref v k q1 ∗ ioff_ref v k q2.
  Proof.
    rewrite /ioff_ref. iSplit.
    - iIntros "(%i & %Hv & %Hi & H)". rewrite ioff_frag_split.
      iDestruct "H" as "[H1 H2]".
      iSplitL "H1"; iExists i; by iFrame.
    - iIntros "[(%i1 & %Hv1 & %Hi1 & H1) (%i2 & %Hv2 & %Hi2 & H2)]".
      assert (i2 = i1) as ->.
      { apply (ientry_inj i2 i1); [lia | lia | congruence]. }
      iExists i1. rewrite ioff_frag_split. by iFrame.
  Qed.

  Global Instance ioff_ref_timeless v k q : Timeless (ioff_ref v k q).
  Proof.
    rewrite /ioff_ref.
    apply bi.exist_timeless; intro i.
    apply bi.sep_timeless; [apply _|].
    apply bi.sep_timeless; [apply _| apply _].
  Qed.

  (* what the ledger owns for one member file slot [k] of inode slot [i] *)
  Definition ioff_slot_res (i k : nat) : iProp Σ :=
    (off_resident k ∨ (off_mark (ientry i) ∗ flive_tok k))%I.

  Global Instance ioff_slot_res_timeless i k : Timeless (ioff_slot_res i k).
  Proof.
    rewrite /ioff_slot_res /off_resident /off_mark.
    apply bi.or_timeless.
    - apply bi.exist_timeless; intro v.
      apply bi.sep_timeless; [apply _ | apply _].
    - apply bi.sep_timeless; [apply _ | apply _].
  Qed.

  Definition ioff_body (i : nat) : iProp Σ :=
    (∃ S : gmap nat unit,
       ghost_map_auth (fsc_foff i) 1 S ∗
       [∗ set] k ∈ dom S, ioff_slot_res i k)%I.

  Global Instance ioff_body_timeless i : Timeless (ioff_body i).
  Proof.
    rewrite /ioff_body.
    apply bi.exist_timeless; intro S.
    apply bi.sep_timeless; [apply _|].
    apply big_sepS_timeless. intros k _. apply _.
  Qed.

  Definition ioff_escrow (i : nat) : iProp Σ := inv (offN .@ i) (ioff_body i).

  Global Instance ioff_escrow_persistent i : Persistent (ioff_escrow i).
  Proof. apply _. Qed.

  (* EVERY inode slot's ledger, as one persistent bundle -- what
     [FsReady.fs_ready] carries and every environment reads. *)
  Definition ioff_escrows : iProp Σ :=
    ([∗ list] i ∈ seq 0 NINODE, ioff_escrow i)%I.

  Global Instance ioff_escrows_persistent : Persistent ioff_escrows.
  Proof. apply _. Qed.

  Lemma ioff_escrows_acc (i : nat) :
    (i < NINODE)%nat -> ioff_escrows -∗ ioff_escrow i.
  Proof.
    iIntros (Hi) "H". rewrite /ioff_escrows.
    assert (Hl : seq 0 NINODE !! i = Some i) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ i i Hl with "H") as "$".
  Qed.



  (* [f->writable] as the BOOL that indexes the pipe's two ends -- the same
     bool pipeclose takes as its second argument, and the truth value of the
     byte fileclose loads with [lbu]. *)
  (* WHAT THE FILE OWNS, as a function of its CONTENT and its payload names.
     A function of [C] alone (given the names) is what lets the exclusive
     holder publish a payload by STORING to [f->type] and [f->pipe]: there is
     no ghost step to perform and no lock to hold, which is precisely the
     situation pipealloc and sys_open are in.

     The free state pins [fc_type = FD_NONE], so a free slot carries no
     payload -- which is the real xv6 invariant: fileclose writes FD_NONE
     before releasing, and the BSS starts zeroed.

     THE OFF CONJUNCT IS TYPE-INDEXED (off-ledger ruling): the FD_INODE arm
     carries the ledger fragment [ioff_ref] -- the cell itself is deposited
     in the inode's ledger, where [ip->lock] governs it -- and every other
     arm carries the dead cell itself, fractionally ([foff_dead]).
     Publishing to FD_INODE is therefore the ONE payload change with a
     ghost step ([FileOff.ioff_publish], under the inode's lock, which
     sys_open holds at its stores); every other retype is still a pure
     store. *)
  (* THE ENTRY'S IREF UNIT RIDES THE UNTYPED AND PIPE ARMS.  [IREFSLOTS]
     provisions one unit per ftable entry ([IrefSlots.v]'s header: "each
     ftable entry holding an FD_INODE / FD_DEVICE file"), and this is where
     that unit lives when the entry is NOT holding an inode reference: a free
     slot's payload holds it, so does a pipe's.  The FD_INODE / FD_DEVICE arm
     holds none, because there the unit has been SPENT -- it is what justifies
     the reference parked in [f->ip], which is exactly what [inode_pay] is.

     This is why [IrefSlots]'s counter is fractional.  The arm splits with
     [q] (filedup hands out shares of one file), so a unit that could not
     split could not live here at all -- and the alternatives all fail: at
     [q = 1] the invariant's [file_rest] is [emp] and cannot see the type, a
     descriptor's [ofile_slot] would need one unit per REFERENCE where the
     supply provisions one per FILE, and nothing can move into or out of the
     table when sys_open types the file, because filealloc has released
     ftable.lock by then.

     What it buys: sys_open's ledger CLOSES.  filealloc hands out an untyped
     slot, so its caller gets the unit for free; sys_open spends it retyping
     to FD_INODE, and its net is zero.  sys_pipe's stays inside the reference
     and rides into the descriptor.  At the last close the holder has [q = 1],
     so a WHOLE unit either way -- from here on the pipe arm, from [iput] on
     the inode arm -- which is what goes back into the freed slot.  Neither
     the type nor the lastness has to appear in fileclose's postcondition. *)
  Definition fc_wbool (C : fcontent) : bool :=
    negb (eq_vec (fc_writable C : mword 8) (mword_of_int 0 : mword 8)).

  (* THE PAYLOAD PROPER -- what a type-dispatched consumer (fileclose's
     pipeclose/iput arms, the two carves) spends.  This is the historical
     [file_core], unchanged; the off conjunct is factored out beside it so
     that no consumer of an ARM ever has to mention the cell. *)
  Definition file_core_noff (q : Qp) (pn : fpnames) (C : fcontent) : iProp Σ :=
    (if bool_decide (fc_type C = FD_PIPE)
     then is_pipe (fp_lock pn) (fp_pipe pn) (fc_pipe C) ∗
          pipe_ref (fp_pipe pn) (fc_wbool C) q ∗ iref_frac q
     else if bool_decide (fc_type C = FD_INODE) || bool_decide (fc_type C = FD_DEVICE)
     then inode_pay (fp_icv pn) (fp_iq pn) (fp_ig pn) (fp_inum pn) (fc_ip C)
            (fc_type C) (fc_wbool C) q
     else iref_frac q)%I.

  (* THE OFF CONJUNCT, TYPE-INDEXED (off-ledger ruling): the FD_INODE arm
     carries the ledger fragment (the cell itself is deposited in the
     inode's ledger), every other arm carries the dead cell at the arm's
     own fraction. *)
  Definition file_core_off (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (if bool_decide (fc_type C = FD_INODE)
     then ioff_ref (fc_ip C) k q else foff_dead k q)%I.

  Definition file_core (k : nat) (q : Qp) (pn : fpnames) (C : fcontent) : iProp Σ :=
    (file_core_noff q pn C ∗ file_core_off k q C)%I.

  (* AN UNTYPED SLOT'S PAYLOAD IS EXACTLY ITS IREF UNIT.  What filealloc
     hands out and what a retype to FD_PIPE moves into the pipe arm.

     The hypothesis is [fc_type C = FD_NONE] and a holder of a REFERENCE can
     state it even though the reference hides its [C]: [fdstate_ok]'s
     [FdClosed] arm IS this equation, so a descriptor known to be closed
     hands it over by definition. *)
  Lemma file_core_noff_none q pn C :
    fc_type C = FD_NONE -> file_core_noff q pn C ⊣⊢ iref_frac q.
  Proof.
    intro Ht. rewrite /file_core_noff Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    reflexivity.
  Qed.

  Lemma file_core_off_none k q C :
    fc_type C = FD_NONE -> file_core_off k q C ⊣⊢ foff_dead k q.
  Proof.
    intro Ht. rewrite /file_core_off Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute]. reflexivity.
  Qed.

  Lemma file_core_none k q pn C :
    fc_type C = FD_NONE -> file_core k q pn C ⊣⊢ iref_frac q ∗ foff_dead k q.
  Proof.
    intro Ht.
    by rewrite /file_core (file_core_noff_none _ _ _ Ht)
               (file_core_off_none _ _ _ Ht).
  Qed.

  Lemma file_core_noff_split q1 q2 pn C :
    file_core_noff (q1 + q2) pn C ⊣⊢
    file_core_noff q1 pn C ∗ file_core_noff q2 pn C.
  Proof.
    rewrite /file_core_noff.
    case_bool_decide as Hp; [|case_match].
    - rewrite pipe_ref_split iref_frac_op. iSplit.
      + iIntros "(#Hi & [H1 H2] & [R1 R2])".
        iSplitL "H1 R1"; (iSplitR; [iExact "Hi"|iFrame]).
      + iIntros "[(#Hi & H1 & R1) (_ & H2 & R2)]".
        iSplitR; [iExact "Hi"|]. iFrame.
    - apply inode_pay_split.
    - apply iref_frac_op.
  Qed.

  Lemma file_core_off_split k q1 q2 C :
    file_core_off k (q1 + q2) C ⊣⊢
    file_core_off k q1 C ∗ file_core_off k q2 C.
  Proof.
    rewrite /file_core_off.
    case_bool_decide; [apply ioff_ref_split | apply foff_dead_split].
  Qed.

  Lemma file_core_split k q1 q2 pn C :
    file_core k (q1 + q2) pn C ⊣⊢ file_core k q1 pn C ∗ file_core k q2 pn C.
  Proof.
    rewrite /file_core file_core_noff_split file_core_off_split.
    iSplit.
    - iIntros "[[H1 H2] [O1 O2]]". iFrame.
    - iIntros "[[H1 O1] [H2 O2]]". iFrame.
  Qed.

  (* the payload with its names quantified -- the form a reference carries,
     since nothing outside the file layer names a pipe's ghosts.  It still
     JOINS, because the names ghost makes the two shares agree.  (The old
     [file_payload] wrapper -- core plus the off-borrow cinv token -- is
     gone: the core IS the payload now, the off conjunct riding its arms.) *)
  Definition file_pay (γ : gname) (k : nat) (q : Qp) (C : fcontent) : iProp Σ :=
    (∃ pn, fpay_tok γ k q pn ∗ file_core k q pn C)%I.

  Lemma file_pay_split γ k q1 q2 C :
    file_pay γ k (q1 + q2) C ⊣⊢ file_pay γ k q1 C ∗ file_pay γ k q2 C.
  Proof.
    rewrite /file_pay. iSplit.
    - iIntros "(%pn & Hn & Hp)".
      rewrite fpay_tok_split file_core_split.
      iDestruct "Hn" as "[Hn1 Hn2]". iDestruct "Hp" as "[Hp1 Hp2]".
      iSplitL "Hn1 Hp1"; by iExists pn; iFrame.
    - iIntros "[(%pn1 & Hn1 & Hp1) (%pn2 & Hn2 & Hp2)]".
      iDestruct (fpay_tok_agree with "Hn1 Hn2") as %<-.
      iExists pn1. rewrite fpay_tok_split file_core_split. iFrame.
  Qed.

  (* ---- THE PAYLOAD, INDEXED BY THE STATE IT GIVES A DESCRIPTOR ----

     [file_pay] quantifies the names, which is right for the ftable
     invariant: it parks whatever fraction is not out and has no business
     knowing what file lives there.  A HOLDER does have that business -- see
     [file_ref] below -- so this is the same payload with the descriptor's
     view of it pulled out of the quantifier.

     WHY [st] AND NOT [fp_inum].  The inum alone would do the job, but every
     consumer would then have to relate it to a type itself, and the FD_NONE
     and FD_PIPE arms would carry a number that means nothing.  [st] is what
     the consumers actually want, and by [fdstate_ok] it is the same fact --
     in BOTH directions, which is what lets [file_ref] hide [C]. *)
  Definition file_pay_st (γ : gname) (k : nat) (q : Qp) (C : fcontent)
      (st : fdstate) : iProp Σ :=
    (∃ pn, ⌜fdstate_ok (fp_inum pn) C st⌝ ∗ fpay_tok γ k q pn ∗
           file_core k q pn C)%I.

  (* the forgetful direction only.  There is no [file_pay -∗ ∃ st,
     file_pay_st]: a payload whose [f->type] is none of the four codes has NO
     honest state, and inventing one is exactly what [fdstate_ok] refuses to
     do.  Every caller that needs the indexed form knows the type -- see
     [file_pay_st_none], which is filealloc's. *)
  Lemma file_pay_st_pay γ k q C st :
    file_pay_st γ k q C st -∗ file_pay γ k q C.
  Proof. iIntros "(%pn & _ & Hn & Hp)". iExists pn. iFrame. Qed.


  (* an UNTYPED payload gives [FdClosed] and there is nothing to choose:
     what filealloc needs to know about the file it just handed out. *)
  Lemma file_pay_st_none γ k q C :
    fc_type C = FD_NONE ->
    file_pay γ k q C -∗ file_pay_st γ k q C FdClosed.
  Proof.
    iIntros (Hty) "(%pn & Hn & Hp)". iExists pn. iFrame.
    iPureIntro. exact Hty.
  Qed.

  (* THE SPLIT, at ONE state: filedup's two shares describe one file.  It is
     the names ghost that makes this true rather than merely stated
     ([fpay_tok_agree]), same as for the content. *)
  Lemma file_pay_st_split γ k q1 q2 C st :
    file_pay_st γ k (q1 + q2) C st ⊣⊢
    file_pay_st γ k q1 C st ∗ file_pay_st γ k q2 C st.
  Proof.
    rewrite /file_pay_st. iSplit.
    - iIntros "(%pn & %Hi & Hn & Hp)".
      rewrite fpay_tok_split file_core_split.
      iDestruct "Hn" as "[Hn1 Hn2]". iDestruct "Hp" as "[Hp1 Hp2]".
      iSplitL "Hn1 Hp1"; iExists pn; by iFrame.
    - iIntros "[(%pn1 & %Hi1 & Hn1 & Hp1) (%pn2 & %Hi2 & Hn2 & Hp2)]".
      iDestruct (fpay_tok_agree with "Hn1 Hn2") as %<-.
      iExists pn1. rewrite fpay_tok_split file_core_split. by iFrame.
  Qed.

  (* THE TIE, READ WITHOUT SPENDING THE PAYLOAD.  An [∧] rather than a [∗]
     so that both sides see the whole resource: the pure fact is what a proof
     that has just branched on [f->type] needs in order to say which state
     its descriptor is in, and it must not have to give up the payload to
     learn it. *)
  Lemma file_pay_st_ok γ k q C st :
    file_pay_st γ k q C st -∗
    ⌜∃ inum : mword 32, fdstate_ok inum C st⌝ ∧ file_pay_st γ k q C st.
  Proof.
    iIntros "H". iSplit; [| iExact "H"].
    iDestruct "H" as (pn) "(%Hok & _)". iPureIntro. by exists (fp_inum pn).
  Qed.

  Lemma file_pay_st_agree γ k q1 st1 q2 st2 C :
    file_pay_st γ k q1 C st1 -∗ file_pay_st γ k q2 C st2 -∗ ⌜st1 = st2⌝.
  Proof.
    iIntros "(%pn1 & %H1 & Hn1 & _) (%pn2 & %H2 & Hn2 & _)".
    iDestruct (fpay_tok_agree with "Hn1 Hn2") as %<-.
    iPureIntro. exact (fdstate_ok_inj _ _ _ _ H1 H2).
  Qed.

  (* ---- THE predicate: holding one reference on file slot [k] ----

     The unit of ownership everywhere a [struct file *] is held: a process's
     p->ofile[fd], a syscall's local [struct file *f], pipealloc's two
     half-built files.  It is NOT persistent and NOT duplicable -- duplicating
     it is filedup, which must run under ftable.lock and bump the physical
     count.  [file_ref γ k 1 st] is the exclusive (writable) state.

     ---- WHY [st] IS AN ARGUMENT ------------------------------------------

     [st] is THE USER-VISIBLE STATE OF ANY DESCRIPTOR NAMING THIS FILE
     ([FdSlots.fdstate]), and a reference carries it because a reference is
     precisely what a descriptor holds.  [ProcInv.ofile_slot] then reads

         file_ref γf k q st ∗ fd_st_auth γd fd st

     -- the fd's ghost is the reference's own index, not a function applied
     to it -- and "this descriptor is open" is literally [st <> FdClosed].

     It is REDUNDANT of the CONTENT and that is deliberate: [st] is
     pinned by the reference's own [C] and [fp_inum].  What it
     adds is A PLACE TO PUT THE INUM.  The type and major number are [struct
     file] fields, so [C] has them; the inode NUMBER is not -- the struct
     holds [f->ip], the itable ENTRY, and entries are recycled, so the
     pointer does not name a file across time.  The number lives one layer
     down in [fp_inum], under [file_pay]'s quantifier, and indexing the
     reference is what lifts it out to where a descriptor can state it.

     ---- AND WHY [C] IS NOT AN ARGUMENT ------------------------------------

     It used to be.  Nothing outside the file layer ever projected a field of
     it: the ten files of the descriptor layer ([ProcInv], sys_close / dup /
     read / write / fstat, kexit, kfork, fdalloc) contain ZERO occurrences of
     [fc_type] and friends.  They named [C] only to pass it along, and every
     one of them already had it under a quantifier of its own -- [ofile_slot]
     and [proc_ofiles_lend] both bound it existentially, so the argument was
     doing nothing but forcing each of those sites to introduce a variable
     and thread it.

     The file layer DOES read the fields -- fileread steps through
     [lw a5, f->type] and has to know what it loaded -- but it reads them off
     [file_fields], which it gets by taking the reference apart.  Opening the
     existential is that same step.

     THE CONSEQUENCE FOR THE LOAN WINDOW.  [ProcInv.proc_ofiles_lend] hands
     a descriptor's ghost authority out WITH the reference; because both name
     [st], a syscall cannot put back a reference to a DIFFERENT file than the
     one the fd's ghost still claims.  A bare reference plus a free-floating
     authority could, and nothing would catch it. *)
  Definition file_ref (γ : gname) (k : nat) (q : Qp) (st : fdstate) : iProp Σ :=
    (∃ C : fcontent,
       fref_tok γ k q ∗ file_fields k q C ∗ file_pay_st γ k q C st ∗
       flive_tok k)%I.

  (* THE BRIDGE OUT OF THE QUANTIFIER: what a proof that has to look at the
     file's own cells opens the reference for.  Every [fc_type]-to-[st]
     step in the tree goes through this plus an [fdstate_ok_*] lemma. *)

  (* ---- the ftable lock's resource ----

     The invariant holds every slot's [ref] cell (filealloc scans them all),
     and, per slot, whatever content fraction has NOT been handed out: all of
     it when the slot is free, [1-q] when q is out, nothing at all when q = 1.
     Note what is NOT here: the content of a referenced file.  That is exactly
     why fileread can read f->type / f->ip holding no lock. *)
  Definition file_rest (γ : gname) (k : nat) (q : Qp) : iProp Σ :=
    match (1 - q)%Qp with
    | Some q' => (∃ C, file_fields k q' C ∗ file_pay γ k q' C)%I
    | None    => emp%I
    end.

  (* q = 1 -- every share is out, so the invariant keeps nothing. *)
  Lemma file_rest_full (γ : gname) (k : nat) : file_rest γ k 1 ⊣⊢ emp.
  Proof.
    rewrite /file_rest.
    assert (Hs : (1 - 1)%Qp = None) by (apply Qp.sub_None; done).
    rewrite Hs. reflexivity.
  Qed.

  (* A referenced slot holds ONE fd slot per outstanding reference: every
     holder of a reference is a file descriptor, and a descriptor that names
     a file has given its [fd_slot] away (FdSlots.v).  That is what bounds
     the count, and hence what makes [f->ref++] safe.

     The [< 2^31] conjunct is the LOCAL PROJECTION of that bound -- it is
     what a consumer walking the table actually needs, and reaching for the
     authority at every slot would infect every consumer.  It is not an
     independent assumption: every operation that changes a count re-derives
     it from [fd_slots_no_overflow]. *)
  Definition fslot (γ : gname) (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
    match M !! k with
    | None =>
        (a_fref k ↦₄ (mword_of_int 0 : mword 32) ∗
         ∃ C, ⌜fc_type C = FD_NONE⌝ ∗ file_fields k 1 C ∗
              file_pay γ k 1 C)%I
    | Some (q, n) =>
        (⌜Z.pos n < 2 ^ 31⌝ ∗
         a_fref k ↦₄ (mword_of_int (Z.pos n) : mword 32) ∗
         file_rest γ k q ∗
         fd_slots (Pos.to_nat n))%I
    end.
End FileInv.

(* ====================================================================
   THE LEDGER'S BOOT FACE (fs-cfg-boot.md's [_at] constructor discipline)

   The era fupd that allocates the ledgers runs at [fileGpreS], BEFORE the
   [fileG] instance exists, so it cannot state [ioff_escrows].  These are
   the same definitions with the two gnames explicit; once the class is
   assembled the two spellings are CONVERTIBLE ([ioff_escrows_at_eq]). *)
Section FileOffLedgerAt.
  Context `{!riscvGS Σ}.
  Context `{FLV : flivG Σ}.
  Context `{GMF : ghost_mapG Σ nat unit}.
  Context `{XI : TsoCtx.CurCtx}.

  Definition flive_tok_at (γfol : gname) (k : nat) : iProp Σ :=
    own γfol (◯ {[ k := 1%positive ]} : fliveUR).

  Definition ioff_slot_res_at (γfol : gname) (i k : nat) : iProp Σ :=
    ((∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝)
     ∨ (i_valid (ientry i) ↦₄ (mword_of_int 1 : mword 32) ∗
        flive_tok_at γfol k))%I.

  Definition ioff_body_at (γfol : gname) (γm : nat -> gname) (i : nat) : iProp Σ :=
    (∃ S : gmap nat unit,
       ghost_map_auth (γm i) 1 S ∗
       [∗ set] k ∈ dom S, ioff_slot_res_at γfol i k)%I.

  Definition ioff_escrow_at (γfol : gname) (γm : nat -> gname) (i : nat) : iProp Σ :=
    inv (offN .@ i) (ioff_body_at γfol γm i).

  Definition ioff_escrows_at (γfol : gname) (γm : nat -> gname) : iProp Σ :=
    ([∗ list] i ∈ seq 0 NINODE, ioff_escrow_at γfol γm i)%I.
  (* sealed for [ioff_escrows]'s reason (the classy family unfolds to this
     one, so an unsealed boot face would reopen the same seam) *)

  (* the off-borrow liveness AUTHORITY at the boot value -- what the era
     fupd mints beside the [fsc_fol] name it records, and what
     [FileInv.ftable_res_boot] takes as its [flive_own (● ∅)] premise (the
     two spellings are convertible once [fileG] is assembled). *)
  Definition flive_auth_at (γfol : gname) : iProp Σ :=
    own γfol (● (∅ : gmap nat positive) : fliveUR).

  Lemma flive_auth_at_alloc :
    ⊢@{iPropI Σ} |==> ∃ γfol : gname, flive_auth_at γfol.
  Proof.
    iMod (own_alloc (● (∅ : gmap nat positive) : fliveUR)) as (γfol) "H".
    { apply auth_auth_valid. intros i. rewrite lookup_empty. done. }
    iModIntro. iExists γfol. iExact "H".
  Qed.

  (* the gname family, allocated as [IcacheRef.isl_fun_alloc] allocates the
     sleeplock family: one fresh EMPTY map authority per slot. *)
  Lemma foff_fun_alloc (n j : nat) :
    ⊢@{iPropI Σ} |==> ∃ f : nat -> gname,
      [∗ list] i ∈ seq j n, ghost_map_auth (f i) 1 (∅ : gmap nat unit).
  Proof.
    iInduction n as [|n IH] forall (j).
    { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
    iMod (ghost_map_alloc_empty (K:=nat) (V:=unit)) as (γ) "Hg".
    iMod ("IH" $! (S j)) as (f) "Hf".
    iModIntro. iExists (fun z => if decide (z = j) then γ else f z).
    assert (Hcons : seq j (S n) = j :: seq (S j) n) by reflexivity.
    rewrite Hcons big_sepL_cons. iSplitL "Hg".
    { case_decide as Hd; [iExact "Hg" | congruence]. }
    iApply (big_sepL_mono with "Hf"). intros i k Hk.
    apply lookup_seq in Hk as [-> _].
    case_decide as Hd; [exfalso; lia | done].
  Qed.

  (* the NINODE ledgers, minted EMPTY: at boot no file refers to any inode
     (the image's ftable is all-FD_NONE, [fentry_raw]) *)
  Lemma ioff_escrows_alloc_at (E : coPset) (γfol : gname) (γm : nat -> gname) :
    ([∗ list] i ∈ seq 0 NINODE, ghost_map_auth (γm i) 1 (∅ : gmap nat unit))
    ={E}=∗ ioff_escrows_at γfol γm.
  Proof.
    iIntros "H". rewrite /ioff_escrows_at.
    iApply big_sepL_fupd. iApply (big_sepL_mono with "H").
    intros idx i _. iIntros "Ha".
    iApply (inv_alloc (offN .@ i) E with "[Ha]").
    iApply bi.later_intro. rewrite /ioff_body_at. iExists ∅.
    iFrame "Ha". rewrite dom_empty_L big_sepS_empty. done.
  Qed.

  Global Instance ioff_escrows_at_persistent γfol γm :
    Persistent (ioff_escrows_at γfol γm).
  Proof. rewrite /ioff_escrows_at. apply _. Qed.

End FileOffLedgerAt.

(* SEALED, AT TOP LEVEL so the setting travels (a section-local
   [Typeclasses Opaque] names the section constant and dies at discharge --
   FsReady.v's note).  A fifty-way big-op behind a [Definition] is exactly
   the seam durable-notes' [iFrame]-delta rule is about: an [iFrame] asked
   to move the family walks into the elements and fails (measured at
   [FsReady.fs_ready_establish]).  Head-symbol matching is all any consumer
   needs; a proof that wants the body says [rewrite /…]. *)
Typeclasses Opaque ioff_escrows.
Typeclasses Opaque ioff_escrows_at.

Section FileOffLedgerEq.
  Context `{XI : TsoCtx.CurCtx}.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ,
            !icacheG Σ, !pipeG Σ, !cinvG Σ, !irefslotG Σ,
            !ghost_mapG Σ nat unit, !flivG Σ}.

  (* the boot face IS the classy family, by conversion: the class-side
     definitions unfold to the [_at] ones at the two [fscfg] fields. *)
  Lemma ioff_escrows_at_eq :
    ioff_escrows_at fsc_fol fsc_foff = ioff_escrows.
  Proof. reflexivity. Qed.

  Lemma flive_auth_at_eq :
    flive_auth_at fsc_fol = flive_own (● (∅ : gmap nat positive)).
  Proof. reflexivity. Qed.
End FileOffLedgerEq.
