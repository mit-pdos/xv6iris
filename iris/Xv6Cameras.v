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
From iris.algebra Require Import excl auth agree csum frac ufrac dfrac gmap gset
     gset gmultiset numbers updates local_updates.
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
Require Import VirtioModel.   (* [virtio_cfg], [disk_wr]                      *)
Require Import VSlot.         (* [vslot] -- the TYPE only; see that file       *)
Require Import DinodeEnc.
Require Import BlkmapDefs.    (* [blkmap] -- the icache box shape (§15)       *)     (* [dinode]                                     *)
Require Import FsNode.        (* [fs_node] -- the era top map's value type    *)
Require Export ChildTok.      (* [genF] / [ctokG] -- the generation's saved
                                 element and its capacity class (14c) *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  SPINLOCKS AND SLEEPLOCKS  (theory: WpLock.v, SleepLock.v)         *)
(* ===================================================================== *)

(* An excl_auth over [lock_state]: the invariant keeps the authority, the
   holder keeps the fragment -- so the holder's token pins the [cpu] field,
   and the fragment cannot be forged. *)
Definition lock_state : Type := option (CPU * bool).

(* >>> A6.119 (1'): THE LOCK'S GHOST CARRIES A SECOND, AGREED COMPONENT --
   the ACQUIRE POSITION, which the holder and the invariant must agree on so
   that the word's value-set pin can be read (§0.35'(iv) case 2).  A PRODUCT
   rather than a wider [lock_state]: the position is a fact two parties agree
   on, not a component every consumer of the state must see, and this way no
   arity moves and every existing ghost step keeps its shape.  Both halves
   hide it existentially at the [lock_auth] / [lock_frag] level; the [_at]
   forms below expose it to the two places that need it. <<< *)
Definition lockUR : ucmra :=
  prodUR (excl_authUR (leibnizO lock_state)) (excl_authUR (leibnizO nat)).

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
(* ENDGAME A6.155: the share is [option frac] -- [None] for the buffer
   cache's chain reference (no fraction), [Some q] for a fractioned one;
   the positive counts both.  See [BioInv.btok]. *)
Definition bioUR : ucmra := authUR (gmapUR nat (prodR (optionUR fracR) positiveR)).
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
  (* the RECEIVE TOKEN's half ([WpUart.uart_rx_tok]): the count of bytes ever
     removed from the receive FIFO.  The push counter beside it and the
     one-shot that says uartinit has run are [mono_nat]s and use the AMBIENT
     [riscvF_genGS] (RiscvPtsto.v) -- a second [mono_natG] here would make
     resolution ambiguous (TsoGhost.v).
     THE ANCHOR RIDES WITH THE COUNT (app-echo.md, lane CONS-CURSOR, C1):
     the value is [(k, hl)] -- [k] bytes popped, [hl] the history the LAST
     popped byte arrived at ([None] before the first pop) -- because the
     queued histories' chain has to survive an EMPTY queue, and the only
     thing that outlives an empty queue is the popper's own token. *)
  uart_ghost_rxpopG :: ghost_varG Σ (nat * option (list mobs));
  (* THE CONSUMER'S HIGH-WATER MARK ([WpUart.uart_rx_hi]): the history of
     the last byte the console ring stored.  Its two halves are the whole
     link between the ring and the popper -- one rides in the PLIC payload
     beside the receive token, the other inside [ConsoleInv.cons_res] -- and
     that link is what makes "the ring's newest byte is older than the one I
     just popped" a fact rather than a hope. *)
  uart_ghost_rxhiG :: ghost_varG Σ (option (list mobs));
  (* THE CONSOLE RING'S COMMITTED SEQUENCE ([ConsoleInv.cons_stored_auth]):
     the append-only log of (history, byte) pairs consoleread consumes, and
     the READER'S CURSOR into it ([ConsoleInv.cons_reader], a [ghost_var]
     over the number of bytes consumed).  They are console state and not
     UART state, but they are cameras of the same receive path and a class
     of their own would have to be bound in every file that names
     [WpUart.dev_inv]. *)
  cons_ghost_logG :: inG Σ (mono_listR (leibnizO (list mobs * bv 8)));
  cons_ghost_rdG :: ghost_varG Σ nat;
}.

Definition uartGhostΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO (bv 8)));
     ghost_varΣ (list (bv 8));
     GFunctor (dfrac_agreeR (leibnizO bool));
     ghost_varΣ (nat * option (list mobs));
     ghost_varΣ (option (list mobs));
     GFunctor (mono_listR (leibnizO (list mobs * bv 8)));
     ghost_varΣ nat ].

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
  (* THE BYTE VIEW'S EXCEPTION SET (durable-disk lane E-except).  A
     ONE-KEY ghost map, so that its single element carries both jobs the
     recovery window needs: the WAL's exclusive HANDLE on the pending set
     ([FsBlocks.exc_own], which [install_trans] shrinks), and -- once the
     element is persisted at [∅] -- the PERSISTENT SEAL
     ([FsBlocks.exc_sealed]) that every runtime crossing of the byte view
     reads "recovery is done" off.  A discarded element cannot be moved
     again, which is exactly why the seal is sound. *)
  fsexc_inG :: ghost_mapG Σ unit (gset Z);
}.
Definition fsLogΣ : gFunctors :=
  #[ghost_mapΣ Z (list (bv 8)); ghost_mapΣ Z bool;
    ghost_mapΣ unit (gset Z)].
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
(*  8b.  THE OFF-BORROW LIVENESS COUNTER  (theory: FileInvDefs.v)         *)
(* ===================================================================== *)

(* One unit per outstanding reference on a file slot, authority beside the
   reference-count authority inside ftable.lock ([FileInvDefs.flive_own]).
   Its gname is the ambient [FsCfg.fsc_fol]; the CAMERA is a member here
   because the off LEDGERS ([FileInvDefs.ioff_body], allocated by the era
   fupd at [xv6G] with no [fileG] in sight) park a unit in their
   checked-out arms -- so the capacity cannot ride [fileG]'s own [inG]
   (that is [fileUR]'s, keyed by the table's threaded [γf]).  [positiveR]
   for [FileInvDefs.fliveUR]'s reason: a unit-free count has no zero
   fragment, so an entry can be DELETED at the last close. *)
Class flivG (Σ : gFunctors) := FlivG {
  fliv_inG :: inG Σ (authUR (gmapUR nat positiveR));
}.
Definition flivΣ : gFunctors := #[GFunctor (authUR (gmapUR nat positiveR))].
Global Instance subG_flivΣ {Σ} : subG flivΣ Σ -> flivG Σ.
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
   (section 11 below) already owns that name in this file.

   THE COUNT AND THE TYPE ARE ONE RA -- THE TYPE REGISTER (fs-state.md
   section 6.5, lane G5).  Per inum: [authUR (gmultisetUR ity)] with
   [ity := TFile | TDir p].  The AUTHORITY is a UNIFORM multiset
   [(nlink + [type = DIR and live]) copies of ty] parked in the inode
   region beside the record and tied to it; the FRAGMENTS are singletons
   [{[ty]}], one per counted dirent, and they ride in the naming
   directory's checked-out payload ([FsStateInode.ent_toks]).

   Validity gives the two readings at once: a fragment's element IS the
   authority's [ty] (AGREEMENT -- a uniform multiset has one element), and
   #fragments <= multiplicity (the COUNT law, which is what the free path
   reads).  Retyping is legal exactly at multiplicity zero, where the
   authority is [auth-empty] and the type is not mentioned at all.

   This replaces the [prodUR (authUR natUR) fsParUR] of lanes G2/G3: there
   is no separate count column any more (the link count IS the fragment
   count) and no separate parent register (a directory's [ty] carries its
   parent, and its ["."] fragment ties that to its [".."] entry). *)
Inductive ity : Type := TFile | TDir (p : Z).

Global Instance ity_eq_dec : EqDecision ity.
Proof. solve_decision. Defined.

Global Instance ity_countable : Countable ity.
Proof.
  refine (inj_countable'
            (fun t => match t with TFile => None | TDir p => Some p end)
            (fun o => match o with None => TFile | Some p => TDir p end) _).
  by intros [].
Defined.

Global Instance ity_inhabited : Inhabited ity := populate TFile.

Definition fsLinkElemUR : ucmra := authUR (gmultisetUR ity).
Definition fsLinkUR : ucmra := gmapUR Z fsLinkElemUR.

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
(* A6.145: the generation agree carries the generation's gname AND its
   EPOCH FLOOR (the arm store's log position, the word-set pin's [pw_lo]).
   Two slices of one slot agreeing on the pair is what hands a racy
   [ip->ref] reader the CURRENT epoch's floor with no extra ghost: a
   stale (g, lo) is unownable exactly as a stale g was. *)
Definition iliveUR : ucmra :=
  gmapUR nat (prodR fracR (agreeR (leibnizO (gname * nat)))).

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
(* THE FREEZE INDEX CARRIES THE FREEZING TRANSACTION (durable-disk C-6,
   [FsCollect.v]'s residue (F)).  The window from iput's eviction to
   [EscrowDeposit.ireg_free_deposit_au] leaves the region slot on the MARKED
   sub-arm with NO record fragment, so the commit's collection finds no
   bundle at that inum.  It is unreachable at a commit because the window is
   inside iput's caller's transaction, and what PROVES that is a share of
   that transaction's [LogDefs.ln_tx] element parked in the slot's own freeze
   clause ([InodeRegion.ireg_fsh]).  A parked share has to come back to the
   freezer AT ITS OWN [(t, q)] -- two halves of one element are not the
   whole -- so the pair rides in the phase's own INDEX beside the regime
   bit, which is
   exactly where the freezer's [IcacheRef.ifreeze_pre] / [ifreeze_post]
   fragment already re-identifies it.  [rg.1] is RULING G''s regime arm as
   before; [rg.2] is the transaction and its share. *)
Definition frzidx : Type := (bool * (nat * Qp))%type.

Inductive frz := FrzOff | FrzPre (rg : frzidx) | FrzPost (rg : frzidx).

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
(* THE CLAIM'S VALUE CARRIES THE CLAIMING TRANSACTION (durable-disk C-5,
   [FsCollect.v]'s residue (E)).  A claim box -- the [fresh_shape] record
   [InodeRegion.ireg_claim_au] writes and [ireg_withdraw] retires -- is a
   NONZERO-typed record sitting on the region's IN arm, and the commit's
   collection cannot read a bundle at such an inum ([FsCollect.
   col_claim_box_untied]).  It is unreachable at a commit because ialloc
   runs inside a transaction, and what PROVES that is a share of the
   claiming transaction's [LogDefs.ln_tx] element parked in the region's
   slot ([InodeRegion.ireg_cpin]).  A parked share has to come back to the
   claimant AT ITS OWN [(t, q)] -- two halves of one element are not the
   whole -- so the pair rides in the c column's own VALUE: the column is
   keyed by
   the INUM, the claimant holds the exclusive fragment at that key, and
   [IcacheRef.link_claim_agree] is the re-identification. *)
Definition ctyval : Type := (bv 16 * (nat * Qp))%type.
Definition ctyR  : cmra  := exclR (leibnizO ctyval).
Definition ctyUR : ucmra := optionUR ctyR.

(* THE INODE-REFERENCE ELEMENT (design §20.2).  [linkElemUR0] is spelled as
   a named atom rather than inline: with the columns written inline, the
   first [apply prod_local_update'] of every chain re-discovers the
   structure by unification and does not terminate in five minutes; with the
   atom the same chains are ~1 s.
   It carries [c] (the typed claim) and [r] (the plain reference count)
   and nothing else: link counts and types are ONE SEPARATE RA
   (fs-state.md §6½, [Xv6Cameras.fsLinkUR]), not a column here. *)
Definition linkElemUR0 : ucmra := prodUR ctyUR natUR.

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

(* THE FREEZE MIRROR (iclaim-ledger.md §3.16 = RULING A⁗): the region-vs-lock
   BRANCH SELECTOR the free path's payload disjunction needs, and the only
   handle on an inum's f column a party outside the region has. *)
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

(* THE TWO CONTENTS GHOSTS ARE GONE (fs-syscall-specs, THE DVIEW RETIREMENT,
   2026-08-30).  [dviewUR] was [icntUR] at the ABSTRACT ENTRY MAP -- a
   per-inum agreement on what a directory's bytes say -- and [fviewUR] its
   per-FILE twin, both carried WHOLE on the custody chain beside the payload's
   era fragment.  The fragment's own readings ([FsStateEra.dir_entries_era_node],
   [FsTree.fn_file_bytes]) ARE what they said, so the column, its two class
   members and its two [GFunctor] rows leave the tree together.  The audited
   theorem moves the safe way: it now holds at a SMALLER functor list, and
   [SystemAdequacy.v] / [SystemAssumptions.v] are byte-identical to main. *)

(* THE ENTRY SLEEPLOCK'S DESCRIPTOR (design §14.8): what a checked-out
   entry's escrow arm is holding for the thread inside.  The fraction is a
   FIELD because an existentially-quantified one in the arm cannot be
   pinned by any resource. *)
(* A6.145: the checked-out descriptors record the generation's ARM POINT
   [lo] beside its gname -- the pair the liveness camera agrees on.  The
   escrow arm's slice then sits at [live_genlo _ _ g lo] (floor-free, so
   the plain-invariant discipline holds) and the racy guard read's
   credential ties through the deposit: the holder's floor is at >= lo. *)
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
     existentially-keyed share cannot re-identify: two halves of one
     element are not the whole. *)
  | DepTx (s : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname)
          (lo : nat) (t : nat) (q : Qp)
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
  | DepRd (s : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname)
          (lo : nat).
  (* [lo] is the credential's epoch on every credential-bearing arm
     (tso-flip A6.145), so the park hands the liveness slice back at the
     epoch the holder's floor names.  tso-flip's [DepRef] (F16, a WHOLE
     reference checked out by iput's free path) is GONE (tso-cutover
     endgame F39): under the stitch iput's free path is main's -- the
     ref == 1 GUARD (a) at count 1 and the (g) exchange to [DepFrz]; no
     whole-unit (e) exists. *)

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
   of the same token.  A walk arms BY SHARE: an arm that demanded the WHOLE
   token could never fire beside a parked one. *)
Definition ireg_arm_ent : Type := (nat * Qp * gset Z)%type.

(* THE CORPSE LEDGER's value (durable-disk C-7, plan section 4).  One row per
   inum in the pool's IN-TRANSITION index -- the pending/await entries iput's
   free path parks at +0x94 -- recording whether that inum's OFF-LOCK DEPOSIT
   ([EscrowDeposit.ireg_free_deposit_au]) has run yet.

   The two values are what the row PARKS, and each is what the commit needs
   at that state:

   - [CrpPre t q]: the deposit has NOT run, and the row parks a positive
     share [q] of the freeing transaction [t]'s [LogDefs.ln_tx] element --
     so the state is refuted outright at a commit, exactly as
     [IcacheEscrow.ipool_transit] is ([ipool_corpse_no_ops]).  [(t, q)] are
     FIELDS and not existentials for [ic_dep]'s reason verbatim (two halves
     of one element are not the whole): the deposit hands the freer back
     EXACTLY the share [ipool_put_corpse] parked.
   - [CrpDep]: the deposit HAS run, and the row parks [InodeRegion.imark] --
     which is what refutes the region slot's own MARKED arm and leaves the
     commit's collection the free bundle on the PENDING one
     ([FsCollect.col_free_slot_acc]).  It is the marker
     [EscrowInode.escA_body]'s FILLED state used to hold; the escrow keeps
     the ledger's ELEMENT in its place, which is what ties the two one-shots
     together ([IcacheEscrow.ipool_take_lend]).  *)
Inductive icorpse : Type :=
  | CrpPre (t : nat) (q : Qp)
  | CrpDep.

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
     (two halves of one element are not the whole): the walk has to take
     back EXACTLY what it parked, and an existentially-keyed share cannot be
     re-identified.  One half of the ledger sits in the pool's invariant
     beside the parked shares, the other in [IcacheEscrow.ipool] under the
     itable lock. *)
  icache_ptrnG :: ghost_varG Σ (gmap Z (nat * Qp));
  (* THE FREE POOL'S CORPSE LEDGER (durable-disk lane C-7, plan section 4).
     One row per inum in the pool's IN-TRANSITION index [X], keyed so that
     the OFF-LOCK deposit -- which cannot reach [IcacheEscrow.ipool]'s rows
     nor its [X] index, the itable lock being twenty instructions gone --
     locates its own row with the ELEMENT alone.  The AUTHORITY sits in the
     pool's invariant beside the parked rows; see [icorpse]'s header for what
     each value parks. *)
  icache_pcrpG :: ghost_mapG Σ Z icorpse;
  icache_cntG :: inG Σ icntUR;
  icache_frzmG :: inG Σ frzmUR;
  (* THE LOCK-WINDOW PIN (durable-disk B''-tx5), ambient for [icfg_frzm]'s
     reason verbatim: one half rides in an [IcacheEscrow] arm and the other
     in the freeing walk's hand across a window that spans a program step. *)
  icache_hpnG :: inG Σ hpnUR;
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * SailStdpp.Values.mword 32 * SailStdpp.Values.mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep; GFunctor ityR; GFunctor linkUR;
    GFunctor (exclR unitO); ghost_mapΣ Z (gname * gname)%type;
    ghost_mapΣ nat ireg_arm_ent;
    ghost_varΣ (gset Z);
    ghost_varΣ (gmap Z (nat * Qp));
    ghost_mapΣ Z icorpse;
    GFunctor icntUR; GFunctor frzmUR; GFunctor hpnUR].
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

(* ===================================================================== *)
(*  14b. THE PROCESS'S CHILDREN SET  (theory: UserChildren.v)            *)
(* ===================================================================== *)

(* The generations of a process's live children, as one ghost variable
   split in half: the ENGINE's half rides inside [UkRun.urun] at the very
   set the trap key carries ([UexecSlot.uvis_ch]), the PROGRAM's half is
   what a proof carries so that it can say which children it has.  The
   working directory's shape ([Xv6Cameras]'s [uioG] break ghost, used by
   [UserCwd]) one value wider.  A class of its own because [gset gname]
   has no other member on this bundle. *)
Class uchG (Σ : gFunctors) := UchG { uch_inG :: ghost_varG Σ (gset gname) }.
Definition uchΣ : gFunctors := #[ ghost_varΣ (gset gname) ].
Global Instance subG_uchΣ {Σ} : subG uchΣ Σ -> uchG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  14c. THE PROCESS SLOT'S GENERATION  (theory: ChildTok.v)             *)
(* ===================================================================== *)

(* A GENERATION IS AN INCARNATION OF A SLOT.  allocproc mints a fresh ghost
   name for every process it hands out and freeproc drops it, so the name
   identifies THIS incarnation -- which is what a wait()-side resource
   transfer is indexed by, a pid being reused and a generation not
   ([UexecSlot.uvis_gen] is the key's reading of it).

   The name is a SAVED ELEMENT and not a plain camera, because what it
   carries is a PREDICATE: the slot address, the pid, and the process's
   exit PAYLOAD [Q : Z -> iProp].  [ChildTok.genF] is that element's
   functor and [ChildTok.v] is the whole theory -- the parent's quarter
   ([child_tok]), the kernel's ([gen_kq]), the discarded half the child's
   [my_pay] and the two persistent readings come off, and the payment rule
   the escrow is redeemed by. *)
(* THE CLASS ITSELF IS [ChildTok.ctokG], one file below, and that is the one
   exception to "members are defined here": the U-tier leaves that name the
   generation's pieces bind no bundle and would otherwise have to import
   [saved_prop] to spell the raw class -- whose re-exports re-shadow
   [Forall_forall] and the numeral scopes wherever the [Require] lands.  The
   [Require Export] at the head of this file is what keeps it visible here
   and in [Xv6G]. *)

(* ===================================================================== *)
(*  14d. THE WAIT LOCK'S CHILDREN CELLS  (theory: WaitInv.v)             *)
(* ===================================================================== *)

(* The [wait_lock] sibling of the parent cells: one [gset gname] per slot,
   the generations of that slot's live children.  A ghost list and not
   memory, because [struct proc] has no such field -- the C code reads the
   same information by scanning [p->parent], and the ghost is the scan's
   contents-out form ([WaitInv.children_own_at]).

   A GHOST MAP AND NOT A LIST OF VARIABLES, keyed by the process's own
   children-ghost name ([ProcDefs.pv_chg]): the AUTHORITY is the lock's
   payload and the ROW is the process's -- it rides the trap residue beside
   [FdSlots.fd_frags] ([WaitInv.ch_frag]).  That is what makes the two
   halves findable: a lock holder that also holds a row learns the map's
   entry by [ghost_map_lookup], where two halves of a per-process
   [ghost_var] would leave it unable to say WHICH entry of the payload is
   its own.  A row is installed under the lock ([ghost_map_insert] at a
   name allocated cofinitely against the domain) and deleted there when the
   incarnation is reaped.

   THE VALUE CARRIES THE OWNER'S SLOT ADDRESS beside its set.  A row's key
   is a ghost name, and nothing in the lock's payload can say which slot
   that name belongs to -- [ProcDefs.pv_chg] lives under p->lock and
   [ChildTok.gen_slot] reads a GENERATION to a slot, not a row name.  The
   address is therefore fixed inside the AUTHORITY, where no row holder
   can move it, and the trap residue pins it to the running process's own
   slot ([UsertrapRes.ut_own] carries the row at [un_pj N]).  That is what
   makes [WaitInv.children_inv] statable. *)
(* THE NAME IS CANONICAL, and that is what makes the row spellable where
   it has to live.  A row rides the DORMANT BLOCK of the slot it belongs to
   ([ProcDefs.proc_dormant]) -- born once at boot, handed out by allocproc,
   returned by freeproc -- and [ProcDefs] sits below every party that
   threads a lock's gname, so a per-boot [γc] parameter would have to reach
   [SchedCtx.procs_inv] and its 389 spellings.  It is carried by the class
   instead, on [FdSlots.fdslot_name] / [ProcAvail.pav_name] /
   [bioslot_name]'s precedent: the capacity below may be assumed by
   adequacy, the NAME may not, so it is minted inside the boot fupd
   ([WaitInv.children_res_alloc], called from [BootShared]) and the
   instance handed out existentially. *)
(* ...AND THE ORPHANS, ON THE SAME CLASS AND FOR THE SAME REASON.  A
   process's children do not die with it: kexit hands them to <init>
   (kernel/proc.c's [reparent]), and the generations that were handed over
   that way are the second thing <wait_lock> owns ([WaitInv.orphans_own]).
   It is a plain [ghost_var] at a MAP FROM THE NEW PARENT'S ADDRESS to the
   generations reparented to it -- a second children table, keyed the way
   the row values are, and the column a lock holder may move without
   holding anybody's row.  Its name is carried here beside the map's,
   minted in the same boot fupd ([WaitInv.children_res_alloc]), so that no
   gname threads through the tree. *)
(* ...AND THE TWO GHOSTS THAT SAY WHICH INCARNATION IS THE CURRENT ONE
   ([SlotGen.v] is the theory).  They ride this class for the reason the map
   and the orphans do -- a canonical name, minted in the same boot fupd
   ([WaitInv.children_res_alloc]) -- and because the parties that hold their
   halves are the same three: the process's private block, the slot's
   dormant block, and <wait_lock>'s payload.

   [sgenUR] -- THE SLOT'S CURRENT GENERATION, keyed by the slot's ADDRESS
   ([ProcGeom.proc_addr], which is what [ProcDefs.proc_dormant] and
   [ProcInv.proc_priv] are stated at).  Fractional agreement and NO
   authority: the whole updates on its own (allocproc, at the mint), two
   halves agree, and the whole excludes any other fraction -- which is what
   makes -- this ZOMBIE block is entry k of the wait-lock invariant -- a
   resource fact rather than a pure one.

   [ghost_mapG Σ Z gname] -- THE PID REGISTER, keyed by the pid's VALUE.
   Here the AUTHORITY is real and it lives in <pid_lock>'s payload
   ([PidLock.nextpid_res_at]), because a pid is CHOSEN -- allocproc's scan
   is what proves the key fresh, and that scan runs under that lock and no
   other.  Two halves at one key agree on the generation, which is the pid
   uniqueness PidLock's header used to record as a further step.
     AT [Z] AND NOT AT [mword 32]: a ghost map's class carries its key's
   [Countable], so a client that spells the key type re-resolves that
   instance -- and an [mword] has two in this tree (stdpp's [bv_countable]
   and [SailStdpp.Instances.Countable_mword], the leak durable-notes
   records), so the class a client builds need not be the one this field
   has.  [Z] has exactly one.  Nothing is lost: two pids with one value
   ARE one pid ([bv_eq]). *)
(* THE MAP TYPE IS NAMED TOO, and it is what [SlotGen] states its own
   definitions at.  A ucmra's CARRIER is not a map type as far as
   unification is concerned (it cannot ensure that [ucmra -> Type] is a
   subtype of [Type -> Type]), so the map lemmas cannot see through
   [sgenUR]; and spelling [gmap (mword 64) _] again in another file
   resolves [Countable (mword 64)] against whatever instances THAT file
   happens to import (stdpp's [bv_countable] vs [SailStdpp.Instances.
   Countable_mword] -- the leak durable-notes records), which is a
   DIFFERENT map type.  Naming it here fixes the instances once. *)
Definition sgen_map : Type :=
  gmap (SailStdpp.Values.mword 64) (dfrac_agreeR (leibnizO gname)).
Definition sgenUR : ucmra :=
  gmapUR (SailStdpp.Values.mword 64) (dfrac_agreeR (leibnizO gname)).
(* THE ORPHAN COLUMN'S TYPE, named here for [sgen_map]'s reason: it is a
   second children table, keyed by the ADDRESS a reparent handed a
   generation to, and spelling [gmap (mword 64) _] in another file resolves
   [Countable (mword 64)] against whatever instances that file imports. *)
Definition orph_map : Type :=
  gmap (SailStdpp.Values.mword 64) (gset gname).
Class wchGpreS (Σ : gFunctors) :=
  { wch_pre_inG :: ghost_mapG Σ gname (SailStdpp.Values.mword 64 * gset gname);
    worph_pre_inG :: ghost_varG Σ orph_map;
    wsg_pre_inG :: inG Σ sgenUR;
    wpr_pre_inG :: ghost_mapG Σ Z gname }.
Class wchG (Σ : gFunctors) :=
  WchG { wch_inG :: ghost_mapG Σ gname (SailStdpp.Values.mword 64 * gset gname);
         worph_inG :: ghost_varG Σ orph_map;
         wsg_inG :: inG Σ sgenUR;
         wpr_inG :: ghost_mapG Σ Z gname;
         wch_name : gname;
         worph_name : gname;
         wsg_name : gname;
         wpr_name : gname }.
Global Instance wchG_preS `{!wchG Σ} : wchGpreS Σ :=
  {| wch_pre_inG := wch_inG; worph_pre_inG := worph_inG;
     wsg_pre_inG := wsg_inG; wpr_pre_inG := wpr_inG |}.
Definition wchΣ : gFunctors :=
  #[ ghost_mapΣ gname (SailStdpp.Values.mword 64 * gset gname);
     ghost_varΣ orph_map;
     GFunctor sgenUR;
     ghost_mapΣ Z gname ].
Global Instance subG_wchΣ {Σ} : subG wchΣ Σ -> wchGpreS Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  15.  THE BUFFER-CACHE TRANSIT BOX  (theory: BioInv.v, CtxAnchor.v)   *)
(* ===================================================================== *)

(* ENDGAME §3.2 (claude-notes/design/tso-escrow-endgame.md): the box's
   cameras.  [presR]: the presence authority -- [● None] in the IDLE arm,
   [● Some ((n_b, T_b), c)] at refs >= 1, every reference carrying
   [◯ Some (_, 1)] beside its [bref_tok].  [btagR]: the park-tag multiset,
   [● S] in the box and one claim [◯ {[+ n_P +]}] per un-decremented
   parker.  [anchorR]: the context anchor's append-only generation ledger
   ([auth] of a [gmap nat (agree nat)]; fragments are core-id, hence
   persistent).  The two pair registers ([reg_park]/[reg_drop]) are
   [ghost_var]s over [nat * nat]; the count-sync register is a
   [ghost_var nat], already a member through [kallocG].  ONE bundle so the
   ~100 files stating [bio_ctx]/[bio_init] keep [!xv6G Σ] as their only
   binder (the rule at the head of this file). *)
Definition presPair : ofe := prodO natO natO.
Definition presR : cmra :=
  authR (optionUR (prodR (agreeR presPair) positiveR)).
Class presG (Σ : gFunctors) := PresG { pres_inG :: inG Σ presR }.
Definition presΣ : gFunctors := #[GFunctor presR].
Global Instance subG_presG {Σ} : subG presΣ Σ -> presG Σ.
Proof. solve_inG. Qed.

Definition btagR : cmra := authR (gmultisetUR natO).
Class btagG (Σ : gFunctors) := BtagG { btag_inG :: inG Σ btagR }.
Definition btagΣ : gFunctors := #[GFunctor btagR].
Global Instance subG_btagG {Σ} : subG btagΣ Σ -> btagG Σ.
Proof. solve_inG. Qed.

Definition anchorR : cmra := authR (gmapUR nat (agreeR natO)).
Class anchorG (Σ : gFunctors) := AnchorG { anchor_inG :: inG Σ anchorR }.
Definition anchorΣ : gFunctors := #[GFunctor anchorR].
Global Instance subG_anchorG {Σ} : subG anchorΣ Σ -> anchorG Σ.
Proof. solve_inG. Qed.

(* BOX v2 (endgame §2/§3, F6/F7 as vetted 2026-09-01): THE GENERIC TRANSIT
   BOX is iris/CtxBox.v; its register value types, stamps camera, class and
   names record live HERE so CtxBox.v can import this file (the rule at the
   head: one bundle).  bcache instantiates it at identity dev × blockno and
   witness type = the data bytes.  The presence / tag / anchor cameras above
   are dead (kept until §6 cleanup). *)

(* ---- the registers' value types (CtxBox.v) ---- *)
Record slot_reg (id X : Type) := SlotReg {
  sr_td    : nat;      (* the stamp L1's payload floor row covers *)
  sr_win   : bool;     (* the L1 out-window is open *)
  sr_ident : id;       (* the box's current identity *)
  sr_x     : option (X * nat); (* F10/F30: the witness the open window's P_rest is at,
                                  and the box stamp the window opened at *)
}.
Arguments SlotReg {id X} _ _ _ _.
Arguments sr_td {id X} _.
Arguments sr_win {id X} _.
Arguments sr_ident {id X} _.
Arguments sr_x {id X} _.

Record l2_reg (id : Type) `{Countable id} := L2Reg {
  lr_tp   : nat;                                 (* the stamp L2's floor row covers *)
  lr_hold : option (id * gmap (id * nat) ufrac); (* the fragment parked in OUT_L2 *)
}.
Arguments L2Reg {id _ _} _ _.
Arguments lr_tp {id _ _} _.
Arguments lr_hold {id _ _} _.

(* the registers sit under the box's later: destructing their ∃ needs an
   inhabitant (bcache: dev × blockno; icache: dev × inum) *)
Global Instance slot_reg_inhabited (id X : Type) `{Inhabited id} : Inhabited (slot_reg id X) :=
  populate (SlotReg 0 false inhabitant None).
Global Instance l2_reg_inhabited (id : Type) `{Countable id} : Inhabited (l2_reg id) :=
  populate (L2Reg 0 None).

(* ---- the box's cameras, generic in the identity ---- *)
Definition stampsR (id : Type) `{Countable id} : cmra :=
  authR (gmapUR (id * nat) ufracR).
Class boxG (id : Type) `{Countable id} (X : Type) (Σ : gFunctors) := BoxG {
  box_stampsG :: inG Σ (stampsR id);
  box_cntG    :: ghost_varG Σ nat;
  box_slotdG  :: ghost_varG Σ (slot_reg id X);
  box_slotpG  :: ghost_varG Σ (l2_reg id);
}.
Record box_names := BoxNames {
  bx_stamps : gname;
  bx_cnt    : gname;
  bx_slotd  : gname;
  bx_slotp  : gname;
}.
Global Instance box_names_inhabited : Inhabited box_names :=
  populate (BoxNames inhabitant inhabitant inhabitant inhabitant).

(* ---- the bcache instance's members: stamps at dev × blockno, the two
   register ghost_vars (the count's [ghost_varG Σ nat] is a member through
   [kallocG]) ---- *)
Notation bio_id := (SailStdpp.Values.mword 32 * SailStdpp.Values.mword 32)%type.
Notation bio_x := (list (bv 8)).
(* ONE decidable-equality / countability witness for the identity, at top
   priority: files that also see Sail's instances for [mword] would
   otherwise elaborate a different (non-convertible) instance term into
   [l2_reg bio_id] / the stamps map, and the [boxG] instance would not
   match ("no type class instance found" at a register definition). *)
Global Instance bio_id_eq_dec : EqDecision bio_id | 0 := _.
Global Instance bio_id_countable : Countable bio_id | 0 := _.
Class bioboxG (Σ : gFunctors) := BioboxG {
  biobox_stampsG :: inG Σ (stampsR bio_id);
  biobox_slotdG  :: ghost_varG Σ (slot_reg bio_id bio_x);
  biobox_slotpG  :: ghost_varG Σ (l2_reg bio_id);
}.
Definition bioboxΣ : gFunctors :=
  #[ GFunctor (stampsR bio_id); ghost_varΣ (slot_reg bio_id bio_x); ghost_varΣ (l2_reg bio_id) ].
Global Instance subG_bioboxΣ {Σ} : subG bioboxΣ Σ -> bioboxG Σ.
Proof. solve_inG. Qed.
(* the generic class, assembled for bcache: the count member is kalloc's *)
Global Instance biobox_boxG {Σ} `{!bioboxG Σ} `{!kallocG Σ} : boxG bio_id bio_x Σ :=
  {| box_stampsG := biobox_stampsG; box_cntG := kalloc_count_inG;
     box_slotdG := biobox_slotdG; box_slotpG := biobox_slotpG |}.

(* ---- THE ICACHE INSTANCE (R3, endgame §4.2 M-1'/M-3): identity = Some
   (dev × inum) with None = dead (M-1'), shape with the generation (M-3).
   The per-slot box names are a field of [IcacheRefDefs.icfg] (canonical, like
   icfg_isl) so inode_ref / inode_shr keep their arity. ---- *)
Notation ic_bid := (option bio_id).
Inductive ic_x : Type :=
  | IcRaw
  | IcUnloaded (g : gname)
  | IcLoaded (g : gname) (dn : dinode) (bm : blkmap).
Global Instance ic_bid_eq_dec : EqDecision ic_bid | 0 := _.
Global Instance ic_bid_countable : Countable ic_bid | 0 := _.
Global Instance ic_bid_inhabited : Inhabited ic_bid := populate None.
Global Instance ic_x_inhabited : Inhabited ic_x := populate IcRaw.
Class icboxG (Σ : gFunctors) := IcboxG {
  icbox_stampsG :: inG Σ (stampsR ic_bid);
  icbox_slotdG  :: ghost_varG Σ (slot_reg ic_bid ic_x);
  icbox_slotpG  :: ghost_varG Σ (l2_reg ic_bid);
}.
Definition icboxΣ : gFunctors :=
  #[ GFunctor (stampsR ic_bid); ghost_varΣ (slot_reg ic_bid ic_x); ghost_varΣ (l2_reg ic_bid) ].
Global Instance subG_icboxΣ {Σ} : subG icboxΣ Σ -> icboxG Σ.
Proof. solve_inG. Qed.
Global Instance icbox_boxG {Σ} `{!icboxG Σ} `{!kallocG Σ} : boxG ic_bid ic_x Σ :=
  {| box_stampsG := icbox_stampsG; box_cntG := kalloc_count_inG;
     box_slotdG := icbox_slotdG; box_slotpG := icbox_slotpG |}.

(* ---- THE OFF BOX'S CAMERAS (R4b; tso-cutover r25 shapes, 2026-09-02) ----
   The third instance of the box (OffBox.v): X := unit, id := the file slot.
   Moved here from OffBox.v so that [xv6G] can bundle the class and no
   consumer section names it (the same reason [icboxG] lives here).  Two
   camera beyond the box's own: the per-inode-slot APPEND-ONLY SET of
   published boxes ([off_rows], an auth over a gset of box names).
   [box_names] is countable for the set.  (The slot->box tie of the first
   shapes commit is gone with the box's L1 side -- plan §9 item 24: the
   fd names its box through [fpnames.fp_obox].) *)
Global Instance box_names_eq_dec : EqDecision box_names.
Proof. solve_decision. Defined.
Global Instance box_names_countable : Countable box_names.
Proof.
  apply (inj_countable'
           (λ b, (bx_stamps b, bx_cnt b, bx_slotd b, bx_slotp b))
           (λ t, BoxNames t.1.1.1 t.1.1.2 t.1.2 t.2)).
  by intros [].
Qed.
(* [offbox_offG] is the OFFSET SHADOW's class: a [ghost_var] over [Z] whose
   value is the boxed [f->off] word ([FileOffCell.off_resident]), named per
   publish by [FdSlots.FdInode]'s [γo].  [ghost_varG Σ Z] has another
   member in the bundle ([uioG]'s [uio_brkG]), so every use PINS this one
   ([FileOffCell.off_gv]), exactly as the count's [kalloc_count_inG] is
   pinned beside the other [ghost_varG Σ nat] members. *)
Class offboxG (Σ : gFunctors) := OffboxG {
  offbox_stampsG :: inG Σ (stampsR nat);
  offbox_slotdG  :: ghost_varG Σ (slot_reg nat unit);
  offbox_slotpG  :: ghost_varG Σ (l2_reg nat);
  offbox_setG    :: inG Σ (authR (gsetUR box_names));
  offbox_offG    :: ghost_varG Σ Z;
}.
Definition offboxΣ : gFunctors :=
  #[ GFunctor (stampsR nat); ghost_varΣ (slot_reg nat unit); ghost_varΣ (l2_reg nat);
     GFunctor (authR (gsetUR box_names)); ghost_varΣ Z ].
Global Instance subG_offboxΣ {Σ} : subG offboxΣ Σ -> offboxG Σ.
Proof. solve_inG. Qed.
Global Instance offbox_boxG {Σ} `{!offboxG Σ} `{!kallocG Σ} : boxG nat unit Σ :=
  {| box_stampsG := offbox_stampsG; box_cntG := kalloc_count_inG;
     box_slotdG := offbox_slotdG; box_slotpG := offbox_slotpG |}.
