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
Require Import FsObjType.     (* [fsobj]: the ledger entry's object set        *)

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

(* THE CLAIM VALUE.  [dn_claim] is the publisher's private handle on its own
   position, and the ONLY thing a process that slept through the request
   still holds when it wakes -- so every fact the woken publisher needs
   about "its" request has to be recoverable from the claim's VALUE.  Four
   fields, one per downstream obligation:

     dc_buf   the [struct buf]: which cache entry the payoff belongs to;
     dc_slot  the published slot: fixes [vs_data] (a write's payload) and
              which block, i.e. the postcondition's [disk_block ...];
     dc_tri   the three descriptors of the chain, which is what tells the
              woken publisher its descriptors were NOT recycled while it
              slept -- hence that [free_desc] may have them back;
     dc_pin   the pinned bytes: naming the map is what lets the publisher
              split the reclaim payoff back into the windows it wrote.

   The long form is in DiskPtsto.v, above [Record disk_names]. *)
Record dclaim := DClaim {
  dc_buf  : Arch.pa;
  dc_slot : vslot;
  dc_tri  : nat * nat * nat;
  dc_pin  : gmap Arch.pa (bv 8);
}.

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
  (* the publisher's private claim map: dom = the positions whose state is
     still live in disk_res (in flight or parked); the fragment is how a
     sleeping rw re-finds its own request (DiskInv.v).  See [dclaim]. *)
  disk_claim_inG :: ghost_mapG Σ nat dclaim;
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
    mono_natΣ; ghost_varΣ nat; ghost_mapΣ nat dclaim;
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
   nothing), the epoch it was minted in, and -- since durable-disk flip-C1
   -- the set of OBJECTS it has claimed.

   WHY BOTH SETS.  The block set is the LOGBLOCKS accounting: it is what
   makes a re-log free and what [log_res] ties to lh.block[].  The object
   set is row (a)'s: an open transaction may move the logged view away
   from the committed one only at the objects it has claimed, and blocks
   are far too coarse a claim for that -- the bitmap block is shared by
   every allocating op in a group, an inode block packs 16 dinode slots
   and a dir block 64 records.  Per-block finalize responsibility fails on
   exactly those; per-OBJECT responsibility is exclusive while the op is
   open, which is the whole argument of the flip (durable-disk.md, "FLIP
   DESIGN OF RECORD").  So the two coexist and neither is derivable from
   the other.

   NOTE THE RE-ASSOCIATION: [(nat * gset Z * nat * gset fsobj)] is
   [(((nat * gset Z) * nat) * gset fsobj)], so the budget is [e.1.1.1],
   the already-logged set is [e.1.1.2], the birth epoch is [e.1.2] and the
   object set is [e.2].  The object set was appended rather than spliced
   so that the three older projections shift UNIFORMLY (each gains one
   [.1]) -- which is what made the flip's sweep mechanical.  The design
   argument for the block set and the epoch is in LogInv.v, above
   [Definition op_sum]; for the object set, above [Definition
   op_pending]. *)
Definition op_entry : Type := (nat * gset Z * nat * gset fsobj)%type.

(* THE EPOCH USES THE AMBIENT [mono_natG] FROM [riscvGS] (the power layer's
   [riscvF_genGS], RiscvPtsto.v) -- NOT a new field here.  A second
   [mono_natG] in the same context is the duplicate-class trap: the two
   instances make propositions that print character-for-character
   identically fail to unify.  Only the [logged_at] registry needs a new
   functor. *)
Class logG (Σ : gFunctors) := LogG {
  logops_inG :: ghost_mapG Σ nat op_entry;
  loglg_inG :: inG Σ (authR (gsetUR (nat * Z)));
}.
Definition logΣ : gFunctors :=
  #[ghost_mapΣ nat op_entry; GFunctor (authR (gsetUR (nat * Z)))].
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
  | DepRef (q : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname)
  | DepShr (s : Qp) (dev inum : SailStdpp.Values.mword 32) (g : gname)
  | DepFrz (q : Qp) (dev inum : SailStdpp.Values.mword 32).

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
  icache_cntG :: inG Σ icntUR;
  icache_frzoG :: inG Σ frzoUR;
  icache_frzmG :: inG Σ frzmUR;
  icache_dviewG :: inG Σ dviewUR;
  icache_fviewG :: inG Σ fviewUR;
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * SailStdpp.Values.mword 32 * SailStdpp.Values.mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep; GFunctor ityR; GFunctor linkUR;
    GFunctor (exclR unitO); ghost_mapΣ Z (gname * gname)%type;
    GFunctor icntUR; GFunctor frzoUR; GFunctor frzmUR; GFunctor dviewUR;
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
