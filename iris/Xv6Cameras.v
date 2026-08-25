(*  Xv6Cameras.v -- THE CAMERAS THE KERNEL'S GHOST STATE IS BUILT FROM.

    Every class in this file is an [inG]/[ghost_varG]/[ghost_mapG] bundle --
    a claim about what cameras live in [Σ], and nothing else.  None of them
    carries a [gname].  That is the membership test [Xv6G.v] states, and
    this file is where the members are DEFINED.

    ---- WHY THEY LIVE HERE AND NOT IN THEIR SUBSYSTEM'S FILE ------------

    [Xv6G.xv6G] unions twelve subsystems, so it can only sit above all of
    them -- and with the classes spread across [SmodeCore] (the M-mode
    execution engine), [IcacheRef], [InodeRegion], [WpUart] and the rest,
    "above all of them" meant a cone of eighty-two files.  Every one of the
    767 files that binds the bundle therefore waited on the inode region,
    the pipe layer and the UART driver whether or not it named them, and an
    edit to any single subsystem's algebra rebuilt all 767.

    Nothing in the union justified that.  A camera is a TYPE-LEVEL claim:
    the vocabulary below is pure iris/stdpp algebra over a handful of plain
    records ([vslot], [virtio_cfg], [disk_wr], [dinode], [dclaim],
    [lock_state], [ic_dep]).  Nothing here mentions [iProp], a weakest
    precondition, an invariant, or the machine model.  So the whole file
    sits on three shallow imports and the bundle's cone becomes eleven
    files, every one of them base layer.

    ---- WHAT MOVED, AND WHAT DID NOT -----------------------------------

    THE RULE: this file holds the camera TYPES; each subsystem's own file
    keeps the constructors, projections and lemmas stated over them --
    [IcacheRef]'s [lelem*]/[lreg*]/boot maps and their validity proofs,
    [PipeInvDefs]'s [pn_end]/[pn_mark], [WpLock]'s whole lock theory.  Each
    of those files [Require Export]s this one, so every name they used to
    define is still in scope for their importers, and no downstream
    signature changes.

    NOT HERE, and each for a reason that is not about depth:

    - [icfg], [fscfg], [riscvGS]'s [riscv_eraGS], and the name records
      ([bio_names], [disk_names], [fs_names], [uart_names], [pipe_names],
      ...).  Records of NAMES and configuration, not capacity; they are
      minted per boot or per power-on and belong where they are.

    - [fileG].  It carries [icfg] beside its camera, so it fails the
      membership test as it stands; folding its [inG Σ fileUR] half in
      means retiring the class in favour of [icfg] at its 432 binder
      sites, which is its own increment.

    - [diskImgG].  Pure, but [RiscvPtsto.riscvFixedGS] CARRIES it
      ([riscvF_diskGS]), so a second path from [xv6G] would be a live
      duplicate-class trap in every scope that holds both.

    - [mono_natG].  Same reason, one level up: [riscvFixedGS] owns the
      generation counter ([riscvF_genGS]), and [LogInv]'s epoch and
      [DiskPtsto]'s counter both read it off there rather than minting a
      second instance.

    - [fdslotG], [irefslotG], [pavG].  Each is a pure [pre] class PLUS one
      [gname], minted by [BootShared.v]; the full classes do not exist
      until boot has run.

    ADDING A MEMBER TAKES THREE THINGS: the field here, a row in
    [Xv6G.xv6GΣ], and a [subG] instance for the member itself -- [solve_inG]
    has to be able to CONSTRUCT it, so a class with no [subG] breaks
    [subG_xv6GΣ] with "Cannot infer this placeholder".  *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import excl auth agree csum frac ufrac dfrac gmap
     gset numbers updates local_updates.
From iris.algebra.lib Require Import excl_auth dfrac_agree mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var ghost_map saved_prop
     mono_nat cancelable_invariants.
(* THE SAIL IMPORTS ARE EXACTLY [RiscvModelBytes]'s / [VirtioModel]'s, and
   deliberately no more.  [gmap Arch.pa (bv 8)] appears in [dclaim] and in
   [diskGhostG], and a [gmap]'s KEY INSTANCES are baked into its type -- so
   this file has to elaborate it in the same instance environment as the
   files that already form it, or the record's field type stops being the
   one [DiskPtsto]'s theory is stated over.  In particular do NOT add
   [SailStdpp.Values]: importing it leaks instances (durable-notes.md), and
   [mword] is spelled QUALIFIED below for that reason -- [RiscvPtsto]'s
   [riscvF_pstateGS] does the same. *)
Require Import SailStdpp.Operators_mwords.
Require SailStdpp.Values.     (* [mword], referenced qualified -- see above   *)
Require Import Riscv.rv64d_types.
Require Import RiscvLang.     (* [CPU]                                        *)
Require Import VirtioQueue.   (* [vslot]; brings [virtio_cfg] / [disk_wr]     *)
Require Import DinodeEnc.     (* [dinode]                                     *)
Require Import FsNode.        (* [fs_node] -- the era top map's value type    *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  SPINLOCKS AND SLEEPLOCKS  (theory: WpLock.v, SleepLock.v)         *)
(* ===================================================================== *)

(* An excl_auth over [lock_state]: the invariant keeps the authority, the
   holder keeps the fragment -- so the holder's token pins the [cpu] field,
   and the fragment cannot be forged. *)
Definition lock_state : Type := option (CPU * bool).

Definition lockUR : ucmra := excl_authUR (leibnizO lock_state).

(* The SLEEPlock's ghost state, inside [lockG] rather than a class of its
   own: a sleeplock already needs [lockG] for its inner spinlock, so a
   second field on the same class reaches all ~35 files that mention
   [is_sleeplock] for free.  Two components, under the sleeplock's OWN
   gname, so no client-visible predicate gains an index:

     excl_auth Qp        -- WHICH FRACTION THE HOLDER DEPOSITED, so a
        releaser gets back exactly the fraction it put in rather than
        "some" fraction.
     auth (option ufrac) -- THE OUTSTANDING-TOKEN COUNT.  [◯ Some q] is a
        q-share of the "somebody may hold this sleeplock" right and [● t]
        the total handed out, [None] meaning NONE -- the authoritative zero
        that refutes the lock being held at all.  UNBOUNDED fractions, so
        the total is not capped at 1.

   The full rationale is in WpLock.v, above [Section Lock]. *)
Definition slhUR : ucmra :=
  prodUR (excl_authUR (leibnizO Qp)) (authUR (optionUR ufracR)).

Class lockG (Σ : gFunctors) := LockG {
  lock_inG :: inG Σ lockUR;
  slh_inG :: inG Σ slhUR;
}.
Definition lockΣ : gFunctors := #[GFunctor lockUR; GFunctor slhUR].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ -> lockG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  2.  THE PAGE ALLOCATOR  (theory: KallocInv.v)                         *)
(* ===================================================================== *)

(* ghost state for the page-count layer: a nat-valued ghost_var (the count,
   γk.1) and a one-shot (the boot->steady seal, γk.2). *)
Definition kalloc_oneshotR := csumR (exclR unitO) (agreeR unitO).
Class kallocG (Σ : gFunctors) := KallocG {
  kalloc_count_inG :: ghost_varG Σ nat;
  kalloc_seal_inG :: inG Σ kalloc_oneshotR;
}.
Definition kallocΣ : gFunctors := #[ghost_varΣ nat; GFunctor kalloc_oneshotR].
Global Instance subG_kallocΣ {Σ} : subG kallocΣ Σ -> kallocG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  3.  THE BUFFER CACHE  (theory: BioDefs.v, BioInv.v)                   *)
(* ===================================================================== *)

(* The reference-count authority and the finite slot supply used to bound
   every buffer reference count.  These functors and names are shared with
   the log layer because [log_state] stores the unused slot fragments. *)
Definition bioUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).
Definition bioslotUR : ucmra := authUR natUR.

Class bioG (Σ : gFunctors) := BioG {
  bio_inG :: inG Σ bioUR;
}.
Definition bioΣ : gFunctors := #[GFunctor bioUR; GFunctor bioslotUR].
Global Instance subG_bioΣ {Σ} : subG bioΣ Σ -> bioG Σ.
Proof. solve_inG. Qed.

(* THE BSLOT SUPPLY'S GHOST NAME LIVES IN THE CLASS, not in [bio_names],
   exactly as [FdSlots.fdslotG] and [IrefSlots.irefslotG] do -- and for the
   reason IrefSlots.v records verbatim: there is exactly ONE such supply per
   system, and threading a [γ] for it "would drag a filesystem ghost name
   through [ProcInv.proc_dormant] and every scheduler spec".  That is not
   hypothetical here: the per-process bslot allowance has to be resident at
   EVERY proc state, so it lives in [proc_dormant] beside [fd_slots FDSPARE]
   and [iref_slots (1 + IREFSPARE)] -- and [ProcDefs] sits below the file
   system, with no [bio_names] anywhere in scope.  With the name canonical
   it needs none.
     [bio_names] keeps the per-BUFFER families ([bn_slk]/[bn_own]/[bn_mid])
   and the two bcache-wide ghosts, all of which only the bio layer names. *)
Class bioslotGpreS (Σ : gFunctors) := { bioslot_pre_inG :: inG Σ bioslotUR }.
Class bioslotG (Σ : gFunctors) := BioSlotG {
  bioslot_inG :: inG Σ bioslotUR;
  bioslot_name : gname;
}.
Global Instance bioslotG_preS `{!bioslotG Σ} : bioslotGpreS Σ :=
  {| bioslot_pre_inG := bioslot_inG |}.
Definition bioslotΣ : gFunctors := #[GFunctor bioslotUR].
Global Instance subG_bioslotΣ {Σ} : subG bioslotΣ Σ -> bioslotGpreS Σ.
Proof. solve_inG. Qed.
Global Instance subG_bioΣ_slot {Σ} : subG bioΣ Σ -> bioslotGpreS Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  4.  THE CRASH-PERMIT CHANNEL  (theory: PermInv.v)                     *)
(* ===================================================================== *)

(* The channel's typing.  Two pieces: the saved propositions that pin each
   in-flight request's receipt, and the ghost map whose ELEMENTS are the
   timeless tokens that ride the request slots.  The key is an opaque
   [nat] chosen fresh at deposit -- deliberately NOT the queue position, so
   nothing here has to know anything about the virtio protocol. *)
Class permG (Σ : gFunctors) := PermG {
  permG_saved :: savedPropG Σ;
  permG_map :: ghost_mapG Σ nat (bool * gname * (disk_wr * gset nat));
}.

Definition permΣ : gFunctors :=
  #[ savedPropΣ ; ghost_mapΣ nat (bool * gname * (disk_wr * gset nat)) ].

Global Instance subG_permΣ Σ : subG permΣ Σ -> permG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  5.  THE DISK DRIVER'S GHOSTS  (theory: DiskPtsto.v, DiskInv.v)        *)
(* ===================================================================== *)

(* THE CLAIM VALUE.  What a publish records about a request, fixed for the
   request's whole life: the [HActive] receipt carries it (that is what a
   sleeping [virtio_disk_rw] re-finds its request through), and [dn_claim]
   maps the position to it -- authority in the vdisk_lock's resource,
   fragment in the receipt -- which is how the interrupt handler, holding
   the lock, knows the SAME claim at each of its openings of the device
   invariant.  Four fields, one per downstream obligation:

     dc_buf   the [struct buf]: which cache entry the payoff belongs to;
     dc_slot  the published slot: fixes [vs_data] (a write's payload) and
              which block, i.e. the postcondition's [disk_block ...];
     dc_pin   the pinned bytes: naming the map is what lets the publisher
              split the reclaim payoff back into the windows it wrote.

   The long form is in DiskPtsto.v, above [Record disk_names]. *)
Record dclaim := DClaim {
  dc_buf  : Arch.pa;
  dc_slot : vslot;
  dc_pin  : gmap Arch.pa (bv 8);
  (* THE POSITION this chain was published at.  The receipt below carries the
     [dn_slot] fragment for it while the request is live, and the interrupt
     handler retires the slot with that fragment -- so the position has to be
     pinned in the claim rather than existentially quantified. *)
  dc_pos  : nat;
}.

(* THE PER-DESCRIPTOR RECEIPT (tools/vtest/README.md finding 5).

   xv6 indexes [disk.info[]] by the HEAD descriptor of a chain, and the
   interrupt handler learns a head -- [disk.used->ring[i].id] -- not a
   position in the available ring.  Since the device may complete out of
   turn those are different numbers, so the driver's per-request state is
   keyed by head, over the fixed eight descriptors, exactly like
   [disk.free[NUM]] and [disk.info[NUM]] in the C.

   [HInactive] is a descriptor nobody has submitted: free (its bytes are in
   the pool) or allocated and still being filled in.  It says NOTHING about
   [disk.info[i].b] -- unlike [info[i].status], which [desc[t]] points at and
   the device writes, [info[i].b] is named by no descriptor and the device
   never sees it, so while the slot is idle that cell is plain driver state
   and rides in the lock resource with the rest of the free slot.  It
   transfers into the receipt only for the in-flight window, because that is
   the one stretch where its owner (the interrupt handler, which learns the
   head from the used ring) is not the thread that allocated it.  [HActive v] is one
   whose chain is live, and the claim [v] records what was published --
   which buffer, which slot, which pinned bytes, which position.
   The FRAGMENT is what [virtio_disk_rw] carries across [sleep()]'s release
   of [vdisk_lock]: holding it is what re-authorises the poll of [b->disk]
   on every re-acquire. *)
Inductive hstate :=
  | HInactive
  (* published: the device has the chain, or it has come back *)
  | HActive (v : dclaim).

(* NB: the disk IMAGE map is deliberately NOT here -- it is
   [DiskImg.diskImgG], which [RiscvPtsto.riscvFixedGS] carries
   ([riscvF_diskGS]), because the era auth rides in [state_interp] while
   the fragments are elements of the same map.  A second path from [xv6G]
   would be exactly the duplicate-class trap this file exists to avoid.

   [mono_natG] IS NOT A FIELD HERE either.  It was, and [riscvFixedGS] owns
   one too ([riscvF_genGS], the generation counter) -- so any scope holding
   [riscvGS] and this class had TWO paths to one [inG], and
   [mono_nat_auth_own γ] built at one would not frame against the other
   while printing identically.  That is what made [RiscvAdequacy]'s
   [Section power] unprovable once it took the bundle. *)
Class diskGhostG (Σ : gFunctors) := DiskGhostG {
  (* a receipt records the slot AND the pin map deposited at publish *)
  disk_slot_inG :: ghost_mapG Σ nat (vslot * gmap Arch.pa (bv 8));
  disk_np_inG   :: ghost_varG Σ nat;
  (* THE STAGED HEAD.  xv6 publishes in two instructions -- it stores the
     descriptor head into [avail->ring[idx % NUM]], fences, and only then
     bumps [avail->idx] -- and the device invariant closes between them.
     This [ghost_var] is how the publisher carries "the cell already names
     my chain" across that gap: the invariant holds one half beside the
     protocol state and couples it to [vp_ring] at the publish position, the
     publisher the other.  [None] at rest; the ring store sets it, the index
     bump consumes it (VirtioProto's [virtio_proto_ring_acc]). *)
  disk_stage_inG :: ghost_varG Σ (option (bv 16));
  (* the publisher's private claim map: dom = the positions whose state is
     still live in disk_res (in flight or parked); the fragment is how a
     sleeping rw re-finds its own request (DiskInv.v).  See [dclaim]. *)
  disk_claim_inG :: ghost_mapG Σ nat dclaim;
  (* the per-descriptor receipt, keyed by HEAD over the fixed eight *)
  disk_head_inG :: ghost_mapG Σ nat hstate;
  (* THE COMPLETION ORDER: a request's POSITION in the available ring against
     the USED INDEX its completion was reported at.  Its elements are
     persistent identification, not ownership (DiskPtsto's [dn_ord]). *)
  disk_ord_inG :: ghost_mapG Σ nat nat;
  (* the LIVE configuration, frozen: the invariant publishes it as a
     persistent fact so a driver can tie [v_cfg v] to the pages it
     programmed at init (see [disk_cfg]) *)
  disk_cfg_inG :: inG Σ (dfrac_agreeR (leibnizO virtio_cfg));
  (* THE CRASH-PERMIT CHANNEL's typing (PermInv.v).  Nested HERE rather
     than added as a separate class to every driver signature:
     [diskGhostG] is already a premise of every statement that mentions a
     [disk_names], so nesting it means NO spec signature changes. *)
  disk_permG :: permG Σ;
}.

Definition diskGhostΣ : gFunctors :=
  #[ghost_mapΣ nat (vslot * gmap Arch.pa (bv 8));
    mono_natΣ; ghost_varΣ nat; ghost_varΣ (option (bv 16));
    ghost_mapΣ nat dclaim; ghost_mapΣ nat hstate;
    ghost_mapΣ nat nat;
    GFunctor (dfrac_agreeR (leibnizO virtio_cfg));
    permΣ].

Global Instance subG_diskGhostG Σ : subG diskGhostΣ Σ -> diskGhostG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  6.  THE UART DRIVER  (theory: WpUart.v)                               *)
(* ===================================================================== *)

(*   mono_list (bv 8)   the accepted output trace, monotone
     ghost_var  (list (bv 8))  EXCLUSIVE ownership of the transmitter
     dfrac_agree bool   DLAB -- freezable to a persistent fact              *)
Class uartGhostG (Σ : gFunctors) := UartGhostG {
  uart_ghost_listG :: inG Σ (mono_listR (leibnizO (bv 8)));
  uart_ghost_txG :: ghost_varG Σ (list (bv 8));
  uart_ghost_dlabG :: inG Σ (dfrac_agreeR (leibnizO bool));
}.

Definition uartGhostΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO (bv 8)));
     ghost_varΣ (list (bv 8));
     GFunctor (dfrac_agreeR (leibnizO bool)) ].

Global Instance subG_uartGhostG Σ : subG uartGhostΣ Σ -> uartGhostG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  7.  THE FS BLOCK LAYER  (theory: FsBlocks.v)                          *)
(* ===================================================================== *)

Class fsLogG (Σ : gFunctors) := FsLogG {
  (* the bio-side block CACHE map: what the buffer cache believes each
     covered block's bytes are.  Its halves ride in the bio payloads. *)
  fsL_inG :: ghost_mapG Σ Z (list (bv 8));
  (* THE LOGGED VIEW L, keyed by BYTE ADDRESS (durable-disk 1c), is typed
     by [DiskImg.diskImgG] -- the tree's UNIQUE source of the
     [ghost_mapG Σ Z (bv 8)] instance (RiscvPtsto.riscvF_diskGS).  A
     second field here would be a second, non-interacting Sigma slot and
     would break the disk image's own auth/fragment pairing. *)
  fsdirty_inG :: ghost_mapG Σ Z bool;
  fsown_inG :: ghost_mapG Σ Z unit;
}.
Definition fsLogΣ : gFunctors :=
  #[ghost_mapΣ Z (list (bv 8)); ghost_mapΣ Z bool; ghost_mapΣ Z unit].
Global Instance subG_fsLogΣ {Σ} : subG fsLogΣ Σ -> fsLogG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  8.  THE LOG  (theory: LogInv.v)                                       *)
(* ===================================================================== *)

(* One outstanding op's entry: its remaining BUDGET, the set of blocks it
   has ALREADY logged (so a re-log of a block already in lh.block[] costs
   nothing), and the epoch it was minted in.

   THE OBJECT SET IS GONE (durable-disk 1d).  flip-C1 appended a
   [gset fsobj] here for row (a) of [LogInv.log_state] -- "the logged view
   is the committed view except at the objects some open transaction has
   claimed".  Ruling 3 (claude-notes/design/fs-state.md) deletes row (a)
   outright: there is no abstract committed picture [A] and no per-op
   finalize obligation, so nothing reads an object set and the entry is
   back to its three fields.

   NOTE THE RE-ASSOCIATION: [(nat * gset Z * nat)] is
   [((nat * gset Z) * nat)], so the budget is [e.1.1], the already-logged
   set is [e.1.2] and the birth epoch is [e.2].  The design argument for
   the block set and the epoch is in LogInv.v, above [Definition
   op_sum]. *)
Definition op_entry : Type := (nat * gset Z * nat)%type.

(* THE EPOCH USES THE AMBIENT [mono_natG] FROM [riscvGS] (the power layer's
   [riscvF_genGS], RiscvPtsto.v) -- NOT a new field here.  A second
   [mono_natG] in the same context is the duplicate-class trap: the two
   instances make propositions that print character-for-character
   identically fail to unify.  Only the [logged_at] registry needs a new
   functor. *)
Class logG (Σ : gFunctors) := LogG {
  logops_inG :: ghost_mapG Σ nat op_entry;
  loglg_inG :: inG Σ (authR (gsetUR (nat * Z)));
  (* THE OPEN-TRANSACTION AUTHORITY (durable-disk lane A).  One element per
     transaction alive right now, at the unit value: the element carries no
     information, only EXISTENCE, so a half of it never blocks the ledger
     entry's own budget updates (which is why this cannot be the ledger map
     itself).  begin_op mints one, end_op consumes it whole, and the locked
     registry parks one while an inode's row is suspended -- so "no open
     transaction" is what makes "every inode is well-formed" readable at a
     commit ([LogInv.log_tx], [InodeRegion.ireg_locked]). *)
  logtx_inG :: ghost_mapG Σ nat unit;
}.
Definition logΣ : gFunctors :=
  #[ghost_mapΣ nat op_entry; GFunctor (authR (gsetUR (nat * Z)));
    ghost_mapΣ nat unit].
Global Instance subG_logΣ {Σ} : subG logΣ Σ -> logG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  9.  THE FS CRASH LAYER  (theory: FsCrash.v)                           *)
(* ===================================================================== *)

(* The committed history's algebra: a mono-list of durable home maps.  Only
   the ALGEBRA-level [mono_list] exists in this Iris (there is no
   [base_logic.lib.mono_list]), so the [own] wrappers are spelled out in
   FsCrash.v. *)
Notation fs_histO := (leibnizO (gmap Z (list (bv 8)))).
Notation fs_histR := (mono_listR fs_histO).

(* The TIE needs no class at all: it is the MACHINE layer's
   ([RiscvPtsto.riscv_fstie_name], over the raw disk image), and [P_fs] is a
   predicate on that image rather than an owner of a half.  The FS BOOT
   TOKEN reuses [WpLock.lock_tok_excl] rather than minting a
   [ghost_varG Σ bool] (which WOULD be ambiguous against
   [riscvF_parkGS]). *)
Class fsCrashG (Σ : gFunctors) := FsCrashG {
  fscrash_histG :: inG Σ fs_histR;
}.

Definition fsCrashΣ : gFunctors := #[ GFunctor fs_histR ].

Global Instance subG_fsCrashΣ Σ : subG fsCrashΣ Σ -> fsCrashG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  10.  THE INODE REGION  (theory: InodeRegion.v)                        *)
(* ===================================================================== *)

Class iregG (Σ : gFunctors) := IregG {
  ireg_inG :: ghost_mapG Σ Z dinode;
}.
Definition iregΣ : gFunctors := #[ghost_mapΣ Z dinode].
Global Instance subG_iregΣ {Σ} : subG iregΣ Σ -> iregG Σ.
Proof. solve_inG. Qed.

(* ---- the ERA'S TOP MAP (theory: FsState.v) -------------------------- *)

(* [fs_state.md]'s [γtop]: inum |-> the era's abstract inode.  It is a
   MEMBER because since durable-disk 2b-inode-3 a checked-out payload
   carries its fragment ([IcacheEscrow.ic_loaded] holds
   [FsState.top_frag]), so the class reaches [ProcInv.proc_priv] through
   [FirstTok.first_boot_persist] and from there essentially every proof
   file in the tree; the alternative to membership is an explicit binder in
   ~400 of them.  The one thing that had to move for it is the record
   [fs_node] itself ([FsNode.v]); the whole [FsState*] theory stays where
   it is, and this file's cone grows by one leaf over [DinodeEnc], which it
   already requires.

   THE STANDING RULE APPLIES: a file at or above [Xv6G.v] binds [xv6G] and
   NOT this class.  The [FsState*] stack, which sits below the bundle,
   binds it alone. *)
Class fsTopG (Σ : gFunctors) := FsTopG {
  fs_top_inG :: ghost_mapG Σ Z fs_node;
}.
Definition fsTopΣ : gFunctors := #[ghost_mapΣ Z fs_node].
Global Instance subG_fsTopΣ {Σ} : subG fsTopΣ Σ -> fsTopG Σ.
Proof. solve_inG. Qed.

(* ---- the LINK-COUNTING FAMILY (theory: FsStateLink.v) ---------------- *)

(* [fs_state.md] section 2's counting RA: ONE auth-of-nat per inum, all
   inums in a single element at [γlink].  [natUR]'s [op] is [+] and its
   [≼] is [≤], so the law "#tokens ≤ nlink" IS [auth_both_valid_discrete]
   plus [nat_included]; [k] separate tokens compose because
   [◯ 1 ⋅ ◯ 1 = ◯ 2].  One camera keyed by inum (rather than one gname per
   inum) is what lets a whole instance be allocated by a single
   [own_alloc].

   IT IS A MEMBER for [fsTopG]'s reason, one step further on: since
   durable-disk 2b-inode-4 a checked-out payload carries its directory's
   link TOKENS ([IcacheEscrow.ic_loaded] holds [FsStateInode.ent_toks])
   and the inode REGION parks the per-inum authority
   ([InodeRegion.ireg_slot]), so the class would otherwise be an explicit
   binder on [ireg_inv] -- hence on the thirty-odd fs contracts that thread
   it -- and on every payload site.  Nothing had to move for it: the
   camera is plain iris algebra.

   THE STANDING RULE APPLIES: a file at or above [Xv6G.v] binds [xv6G] and
   NOT this class.  The [FsState*] stack, which sits below the bundle,
   binds it alone.

   NAMED [fsLinkUR], not [linkUR]: the inode cache's own ledger camera
   (section 11 below) already owns that name in this file. *)
Definition fsLinkUR : ucmra := gmapUR Z (authR natUR).

Class fsLinkG (Σ : gFunctors) := FsLinkG {
  fs_link_inG :: inG Σ fsLinkUR;
}.
Definition fsLinkΣ : gFunctors := #[ GFunctor fsLinkUR ].
Global Instance subG_fsLinkΣ {Σ} : subG fsLinkΣ Σ -> fsLinkG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  11.  THE INODE CACHE  (theory: IcacheRef.v)                           *)
(* ===================================================================== *)

(* RustBelt's Arc algebra, exactly as [FileInvDefs.frefUR] uses it for
   [struct file]: [M !! k = Some (q, n)] means "itable slot [k] is live,
   with [n] outstanding references holding [q] of its identity fields
   between them"; [k ∉ dom M] means the slot is FREE.  The frac x count
   pairing is REF-1 EXCLUSIVITY: [fracR] has no unit and [positiveR] has no
   zero, so [Some (q,1) ≼ Some (qt,n)] forces [n = 1 -> q = qt]. *)
Definition icacheUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

(* THE LIVENESS POOL (design fs-icache.md §14.6): per slot, a fraction and
   an agreed GENERATION gname.  Two slices of one slot AGREE on the
   generation ([IcacheRef.live_gen_agree]), which is the mechanism the
   whole §17' design runs on. *)
Definition iliveUR : ucmra :=
  gmapUR nat (prodR fracR (agreeR (leibnizO gname))).

(* THE PER-GENERATION TYPE ONE-SHOT (design §17.2 piece 2).  The generation's
   [agree] carries a fresh GNAME rather than a type, and the type attaches
   later through a standard one-shot at that gname: iget mints it PENDING,
   and ilock's fill -- the only instruction that knows [di_type dn] --
   SPENDS it.  At [bv 16], [DinodeEnc.di_type]'s width. *)
Definition ityR : cmra := csumR (exclR unitO) (agreeR (leibnizO (bv 16))).

(* THE FREEZE PHASE.  The exclusive fragment [ifreeze FrzOff z] rides under
   the itable lock; [InodeRegion.ireg_freeze_au] SWAPS it for
   [ifreeze_pre], so the mint is a fragment-in-hand step and double-freeze
   is refuted by [Excl] alone. *)
Inductive frz := FrzOff | FrzPre (rg : bool) | FrzPost (rg : bool).

Global Instance frz_eq_dec : EqDecision frz.
Proof. solve_decision. Defined.
Global Instance frz_inhabited : Inhabited frz := populate FrzOff.

(* NAMED, and that is load-bearing rather than cosmetic: with the column
   written inline as [optionUR (exclR (leibnizO frz))] the f-cell's binders
   elaborate at the raw [option (excl frz)] and [apply prod_local_update']
   can no longer unify its [prodR ?A ?B] against [ucmra_cmraR linkElemUR]
   (verified both ways).  Every f binder is at [frzUR]. *)
Definition frzR  : cmra  := exclR (leibnizO frz).
Definition frzUR : ucmra := optionUR frzR.

(* THE TYPED CLAIM COLUMN (iclaim-ledger.md §5.2(a) item 7b): the c column
   carries the CLAIMED TYPE, so [ialloc]'s fill has a source for
   [di_type dnc = ty].  Spelled as a NAMED atom for [frzR]'s reason. *)
Definition ctyR  : cmra  := exclR (leibnizO (bv 16)).
Definition ctyUR : ucmra := optionUR ctyR.

(* THE LINK LEDGER's element (design §20.2).  [linkElemUR0] is spelled as a
   named atom rather than inline: at six columns written inline, the first
   [apply prod_local_update'] of every chain re-discovers the structure by
   unification and does not terminate in five minutes; with the atom the
   same chains are ~1 s. *)
Definition linkElemUR0 : ucmra :=
  prodUR (prodUR (prodUR (prodUR (prodUR natUR (prodUR natUR natUR)) natUR)
                 ctyUR) natUR)
         (optionUR (dfrac_agreeR (leibnizO Z))).

Definition linkElemUR1 : ucmra := prodUR linkElemUR0 frzUR.

(* the rc column (RULING R): the r column's SECOND flavour, counting the
   icache references minted at an iget that presented a [ClaimL] licence.
   The pin it buys is [InodeRegion.ireg_ref_ok]'s third conjunct,
   [c <> None -> r_plain = 0]. *)
Definition linkElemUR : ucmra := prodUR linkElemUR1 natUR.

Definition linkUR : ucmra := gmapUR Z (authR linkElemUR).

(* THE COUNT COUPLING (iclaim-ledger.md §2.2).  NOT an auth: there is no
   third party that ever needs to read the count without holding a half,
   and dropping the auth is what keeps the update requirement honest --
   exactly "both halves in hand". *)
Definition icntUR : ucmra := gmapUR Z (dfrac_agreeR (leibnizO nat)).

(* THE FREEZE RECEIPT (iclaim-ledger.md §3.14, as built). *)
Definition frzoUR : ucmra := gmapUR Z (exclR unitO).

(* THE FREEZE MIRROR (iclaim-ledger.md §3.16 = RULING A⁗).  Complementary to
   the receipt: the receipt is hand-vs-region exclusivity, the mirror is the
   region-vs-lock BRANCH SELECTOR the payload disjunction needed. *)
Definition frzmUR : ucmra := gmapUR Z (dfrac_agreeR (leibnizO bool)).

(* THE LOCK-WINDOW PIN (durable-disk B''-tx5), the escrow's per-SLOT twin of
   [ic_dep]'s [(t, q)] fields.  Two of [IcacheEscrow]'s arms -- the
   authority-side window [ic_held] and [ic_payload_arm]'s frozen alternative
   -- are windows iput holds across a program step at which it carries NO
   per-slot ghost of its own ([ic_held] spans [acquiresleep], where the
   slot's descriptor variable is inside the entry's sleeplock).  A share of
   the transaction's [LogDefs.ln_tx] element parked in such an arm would come
   back at an EXISTENTIAL [(t, q)] and could not be rejoined with the residue
   iput's caller must get back, so the arm has to NAME what it parked: one
   half of this cell sits in the arm beside the share, the other in iput's
   hand, and [hpn_agree] is what re-identifies the pair at the exit.

   [frzmUR]'s shape at the SLOT key and the pair value.  It is an [icfg]
   field, not a field of [ic_names]: [IcacheEscrow.ic_payload_arm] takes no
   [cn] at all (37 sites in that file alone), and an ambient name costs no
   arity anywhere. *)
Definition hpnUR : ucmra :=
  gmapUR nat (dfrac_agreeR (leibnizO (option (nat * Qp)))).

(* THE PER-DIRECTORY CONTENTS GHOST (namei-pinned-lookup.md §9 W1).  [icntUR]
   at the ABSTRACT ENTRY MAP: a per-inum agreement on what a directory's bytes
   say, tied definitionally to those bytes ([DirViewG.dv_of]) everywhere the
   bytes rest.  Carried WHOLE on the custody chain -- which is what keeps
   every mover a free own-update and keeps every landed contract's arity
   fixed; the fraction split belongs to the pinned form, not to the carrier.

   THE KEY TYPE IS SPELLED [list (bv 8)], NOT [FsTree.fname]: this file sits
   below [FsTree] (and below its [InodeDefs]/[BioDefs] cone), the two are the
   same definition, and [DirViewG] states the whole theory at [fname]. *)
Definition dviewUR : ucmra :=
  gmapUR Z (dfrac_agreeR (leibnizO (gmap (list (bv 8)) Z))).

(* THE PER-FILE CONTENTS GHOST (namei-pinned-lookup.md §13, D-52a).  [dviewUR]
   one layer down: a per-inum agreement on what a FILE's bytes say, tied
   definitionally to those bytes ([DirViewG.fv_of], i.e. [FsTree.file_bytes])
   everywhere the bytes rest.  A SECOND, INDEPENDENT ghost rather than a pair
   value inside [dviewUR]: re-typing the landed one would re-sweep every dview
   site in the tree, whereas a twin's sweep is purely additive beside it.

   The value type needs no [FsTree] name at all -- a file's contents ARE a
   [list (bv 8)] -- so this one costs not even [dviewUR]'s spelling note. *)
Definition fviewUR : ucmra :=
  gmapUR Z (dfrac_agreeR (leibnizO (list (bv 8)))).

(* THE ENTRY SLEEPLOCK'S DESCRIPTOR (design §14.8): what a checked-out
   entry's escrow arm is holding for the thread inside.  The fraction is a
   FIELD because an existentially-quantified one in the arm cannot be
   pinned by any resource. *)
Inductive ic_dep : Type :=
  | DepNone
  (* THERE IS NO BUNDLELESS LOCK DESCRIPTOR (durable-disk B''-tx3/-tx4), and
     that is what makes [IcacheEscrow.ic_slot_cover] finite: every [ilock] in
     this kernel publishes its FINAL arm at the checkout and every park
     retires it in the ghost step that parks the payload, so an arm the
     commit meets is one of the three below.  iput's window exits are the
     escrow's own ([IcacheEscrow.ic_held]) and [DepFrz]. *)
  (* [(t, qt)] ARE FIELDS, for [DepTx]'s reason verbatim (durable-disk
     B''-tx5): iput's freeze window (+0x5e..+0x70) parks a SHARE of its
     transaction's [LogDefs.ln_tx] element in [IcacheEscrow.ic_out_frz], so a
     commit refutes the arm outright, and the descriptor -- a [ghost_var]
     whose other half the freer carries -- pins the share to the one the
     freer must get back.  The escrow's OTHER two windows carry no descriptor
     and use [IcacheRef.hpn_h] instead. *)
  | DepFrz (q : Qp) (dev inum : SailStdpp.Values.mword 32) (t : nat) (qt : Qp)
  (* THE WRITE ARM (durable-fs-plan.md section 3, [ilock]; durable-disk
     B''-arm).  The caller's generation-named credential plus the transaction
     whose write lock this is:
     while an inode is checked out FOR WRITING the escrow's OUT arm parks a
     SHARE [q] of transaction [t]'s [LogDefs.ln_tx] element, so [end_op] --
     which consumes the whole element -- cannot run, and the commit's
     collection at quiescence can refute the arm outright against an EMPTY
     [ln_tx] authority ([IcacheEscrow.ic_out_no_write_arm]).

     [(t, q)] ARE FIELDS, not existentials, and that is the whole mechanism:
     [IcacheEscrow.ic_deposit] is a [ghost_var] whose other half the holder
     carries, so the descriptor PINS the arm's transaction and share to the
     holder's, and the park hands back exactly what the checkout parked.  An
     existentially-keyed share cannot re-identify --
     [IcacheTxRefute.tx_two_halves_no_whole] is the refutation. *)
  | DepTx (s : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname)
          (t : nat) (q : Qp)
  (* THE READ ARM (durable-fs-plan.md section 3, [ilock] without a
     transaction; durable-disk B''-join).  The write arm's content minus the
     parked share -- the credential does not change -- but the arm keeps THREE
     QUARTERS of the inode's bundle ([IcacheEscrow.ic_rd_arm]) instead of
     nothing, and the holder carries only the reader's quarter.  It is the
     other of the two states plan section 4's collection can close: an
     unlocked inode's bundle is inside at 1, a read-locked one's at 3/4, and
     [blk_owned_ne_34] is what makes 3/4 enough for cross-inode disjointness.

     A SEPARATE CONSTRUCTOR rather than a re-reading of the write arm,
     because what the ESCROW keeps differs and the deposit is what selects
     the arm. *)
  | DepRd (s : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname).

(* THE LOCKED REGISTRY'S ENTRY (durable-disk lane A, re-keyed by B''-arm):
   one ARM.  [(t, q, S)] -- the transaction whose row is suspended, the
   SHARE of its [LogDefs.ln_tx] element the registry has parked, and the
   inums whose well-formedness row that arm suspends.

   THE SHARE IS A FIELD, and that is the whole point of the re-key: an arm
   must hand back EXACTLY what it parked (the walk recombines it into the
   whole element [end_op] consumes), so an existential fraction inside the
   registry cannot be undone -- the same reason [ic_dep] spells its fraction
   as a field.  And the registry is keyed by an ARM id, not by the
   transaction: [InodeRegion.ireg_arm] then needs no freshness argument at
   all (a fresh [nat] key is free in a map the ghost step can see), which is
   what lets a walk arm from a RESIDUE after an [ilock] has parked a share
   of the same token ([IcacheTxArm.v] is the refutation of the whole-token
   form). *)
Definition ireg_arm_ent : Type := (nat * Qp * gset Z)%type.

(* The link ledger, the count coupling, the freeze receipt and the freeze
   mirror all ride in [icacheG] rather than in classes of their own, and
   all for one reason: each has one half in [InodeRegion.ireg_slot] and the
   other under the itable lock or in [IcacheEscrow]'s parked bundle, so
   BOTH altitudes must be able to name it -- and every file at either
   altitude already carries [icacheG]. *)
Class icacheG (Σ : gFunctors) := IcacheG {
  icache_inG :: inG Σ icacheUR;
  icache_idG :: ghost_varG Σ (bool * SailStdpp.Values.mword 32 * SailStdpp.Values.mword 32);
  icache_liveG :: inG Σ iliveUR;
  icache_depG :: ghost_varG Σ ic_dep;
  icache_ityG :: inG Σ ityR;
  icache_linkG :: inG Σ linkUR;
  (* OPTION A escrow: the redemption ticket and the per-inum name registry. *)
  icache_tickG :: inG Σ (exclR unitO);
  icache_regG :: ghost_mapG Σ Z (gname * gname)%type;
  (* THE LOCKED REGISTRY (durable-disk lane A, re-keyed by B''-arm): which
     transaction has suspended which inums' well-formedness row, and at what
     share of its token.  Keyed by ARM id -- a fresh [nat] the ghost step
     picks out of the map it can already see -- so that arming needs no
     freshness argument about the transaction and a walk that has parked a
     share elsewhere can still arm ([Xv6Cameras.ireg_arm_ent]'s header). *)
  icache_lkG :: ghost_mapG Σ nat ireg_arm_ent;
  (* THE FREE POOL'S RESIDENCY KEY (durable-disk lane B''-esc, plan section 4).
     The uncached inums whose row sits in the pool INVARIANT, as one set: the
     invariant holds one half and the itable lock's resource the other, so a
     lock holder is the only mover of the index and the commit -- which never
     takes that lock -- can still open the invariant and read every ordinary
     bundle at one ghost step. *)
  icache_poolG :: ghost_varG Σ (gset Z);
  (* THE FREE POOL'S TRANSIT LEDGER (durable-disk lane C-4, plan section 4).
     The inums a walk is CARRYING between an eviction's identity flip and its
     deposit, each with the transaction id and share the walk parked for it.
     [(t, q)] are FIELDS and not existentials for [ic_dep]'s reason verbatim
     ([IcacheTxRefute.tx_two_halves_no_whole]): the walk has to take back
     EXACTLY what it parked, and an existentially-keyed share cannot be
     re-identified.  One half of the ledger sits in the pool's invariant
     beside the parked shares, the other in [IcacheEscrow.ipool] under the
     itable lock. *)
  icache_ptrnG :: ghost_varG Σ (gmap Z (nat * Qp));
  icache_cntG :: inG Σ icntUR;
  icache_frzoG :: inG Σ frzoUR;
  icache_frzmG :: inG Σ frzmUR;
  (* THE LOCK-WINDOW PIN (durable-disk B''-tx5), ambient for [icfg_frzm]'s
     reason verbatim: one half rides in an [IcacheEscrow] arm and the other
     in the freeing walk's hand across a window that spans a program step. *)
  icache_hpnG :: inG Σ hpnUR;
  icache_dviewG :: inG Σ dviewUR;
  icache_fviewG :: inG Σ fviewUR;
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * SailStdpp.Values.mword 32 * SailStdpp.Values.mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep; GFunctor ityR; GFunctor linkUR;
    GFunctor (exclR unitO); ghost_mapΣ Z (gname * gname)%type;
    ghost_mapΣ nat ireg_arm_ent;
    ghost_varΣ (gset Z);
    ghost_varΣ (gmap Z (nat * Qp));
    GFunctor icntUR; GFunctor frzoUR; GFunctor frzmUR; GFunctor hpnUR;
    GFunctor dviewUR;
    GFunctor fviewUR].
Global Instance subG_icacheΣ {Σ} : subG icacheΣ Σ -> icacheG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  12.  PIPES  (theory: PipeInvDefs.v, PipeInv.v)                        *)
(* ===================================================================== *)

Class pipeG (Σ : gFunctors) := PipeG {
  pipe_inG :: inG Σ fracR;          (* the two end fractions *)
  pipe_mark_inG :: inG Σ dfracR }.  (* the two "still open" markers *)
Definition pipeΣ : gFunctors := #[GFunctor fracR; GFunctor dfracR].
Global Instance subG_pipeΣ {Σ} : subG pipeΣ Σ -> pipeG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  13.  THE S-MODE INTERRUPT-ENABLE GHOST  (theory: SmodeCore.v)         *)
(* ===================================================================== *)

(* One half rides in [sconf] (the ambient S-mode config), the acquire /
   release pair owns the other. *)
Class sieG (Σ : gFunctors) := SieG { sie_inG :: ghost_varG Σ (SailStdpp.Values.mword 1) }.
Definition sieΣ : gFunctors := #[ ghost_varΣ (SailStdpp.Values.mword 1) ].
Global Instance subG_sieΣ {Σ} : subG sieΣ Σ -> sieG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  14.  THE UMODE TIER'S I/O GHOSTS  (theory: UmodeIo.v)                 *)
(* ===================================================================== *)

Class uioG (Σ : gFunctors) := {
  uio_stdinG :: ghost_varG Σ (list (bv 8));
  uio_brkG   :: ghost_varG Σ Z;
}.
Definition uioΣ : gFunctors := #[ ghost_varΣ (list (bv 8)); ghost_varΣ Z ].
Global Instance subG_uioΣ {Σ} : subG uioΣ Σ -> uioG Σ.
Proof. solve_inG. Qed.
