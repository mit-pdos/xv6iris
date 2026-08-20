(*  Xv6G.v -- ONE CLASS FOR THE GHOST STATE THAT IS PURE CAPACITY.

    Every field below is an [inG]/[ghost_varG]/[ghost_mapG] -- a claim about
    what cameras live in [Σ], and nothing else.  None of them carries a
    [gname].  That is the whole criterion for membership, and it is what
    makes this class safe to hand out from adequacy before a single
    instruction of the kernel has run: there is nothing in it to allocate.

    ---- WHY ONE CLASS RATHER THAN TEN BINDERS --------------------------

    Not brevity.  A spec that spells its own [!bioG Σ, !logG Σ, …] can be
    instantiated at a DIFFERENT instance of the same class than its caller,
    and two instances of one [inG] are not equal -- so the resources they
    build are not the same resources, and the mismatch surfaces as an
    [iFrame]/[iApply] failure between two propositions that PRINT
    IDENTICALLY.  durable-notes.md's typeclass-sweep section is about that
    failure mode; it is expensive to debug precisely because nothing in the
    error names the cause.  One class means one instance path.

    So the rule that comes with this file: **a file at or above this one
    binds [xv6G] and does NOT bind any of its members.**  Binding both is
    the bug this class exists to prevent, and it compiles.

    ---- WHAT IS DELIBERATELY *NOT* HERE --------------------------------

    - [icfg].  [fileG] still carries it, and that is deliberate: it is a
      record of NAMES, not capacity, so it fails this file's membership
      test.  It is therefore still reachable both from [fileG] and from an
      explicit [ICFG : icfg] binder (eighteen files bind both today).  That
      is a pre-existing double path of the CONFIG kind, untouched here and
      worth its own increment.

    - [fdslotG], [irefslotG], [pavG].  Each is a pure [pre] class PLUS one
      [gname] ([fdslot_name], [irefslot_name], [pav_name]), minted by
      [fd_slots_alloc] / [iref_slots_alloc] / [procs_avail_alloc] in
      [BootShared.v].  Their [...GpreS] halves are pure and could be bundled
      into an [xv6Gpre]; the FULL classes cannot be, because they do not
      exist until boot has run.

    - [icfg], [fscfg], and [riscvGS]'s [riscv_eraGS].  These are records of
      NAMES and configuration, not capacity: [icfg_alloc] mints one per
      boot, [FsCfg]'s per boot, and the era record per POWER-ON
      (RiscvAdequacy.v; design/crash.md).  They are per-run values and
      belong where they are.

    - [mono_natG].  [riscvFixedGS] owns it ([riscvF_genGS], the generation
      counter), and that is the right home: [gen_cert]/[gen_started] are
      machine-model state consumed by the fetch/execute engine
      ([InstrBytes], [RiscvFetchExec], the twelve [Hart*] files) far below
      any kernel bundle.  Putting it HERE would have cost twenty-seven deep
      files a new binder to buy nothing.  What DID have to go was
      [diskGhostG]'s copy: [riscvGS] and the bundle share a scope
      constantly, so that pair was a live double path -- it is what made
      [RiscvAdequacy]'s [Section power] unprovable.  Two other owners stay,
      each because it cannot collide: [riscv_pre_genGS] allocates the
      counter BEFORE [riscvGS] exists (that is what a [pre] class is for)
      and never shares a scope with it; [CrashProto]'s [cp_monoGS] /
      [cpp_monoGS] are bound only inside [CrashProto.v], an orphan module
      with zero reverse dependencies that is independent of [RiscvPtsto] in
      both directions.

    - [diskImgG] is pure, but both its direct binders sit BELOW this file,
      where [xv6G] is invisible; [permG] already arrives through
      [diskGhostG], so naming it here would ADD a path; the [...GpreS]
      classes share their [inG] with their full counterparts.

    ADDING A MEMBER TAKES THREE THINGS, not one: the field, a row in
    [xv6GΣ], and a [subG] instance for the member itself -- [solve_inG] has
    to be able to CONSTRUCT it, so a class with no [subG] (as [uioG] had
    none) breaks [subG_xv6GΣ] with "Cannot infer this placeholder".  *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var.   (* [gFunctors], [ghost_varG] *)
Require Import SmodeCore.       (* sieG        *)
Require Import WpLock.          (* lockG       *)
Require Import KallocInv.       (* kallocG     *)
Require Import BioDefs.         (* bioG        *)
Require Import DiskPtsto.       (* diskGhostG  *)
Require Import WpUart.          (* uartGhostG  *)
Require Import FsBlocks.        (* fsLogG      *)
Require Import LogInv.          (* logG        *)
Require Import FsCrash.         (* fsCrashG    *)
Require Import InodeRegion.     (* iregG       *)
Require Import IcacheRef.       (* icacheG     *)
Require Import PipeInvDefs.     (* pipeG       *)
From iris.base_logic.lib Require Import cancelable_invariants.  (* cinvG *)

(* THE UMODE TIER'S I/O GHOSTS, hoisted here from [UmodeIo.v].  Pure
   capacity, nothing else provides it, and every consumer is above this
   file -- so it belongs in the bundle.  Defined HERE rather than imported,
   because requiring [UmodeIo] would put its 99-file cone in front of every
   file that binds [xv6G]. *)
Class uioG (Σ : gFunctors) := {
  uio_stdinG :: ghost_varG Σ (list (bv 8));
  uio_brkG   :: ghost_varG Σ Z;
}.
Definition uioΣ : gFunctors := #[ ghost_varΣ (list (bv 8)); ghost_varΣ Z ].
Global Instance subG_uioΣ {Σ} : subG uioΣ Σ -> uioG Σ.
Proof. solve_inG. Qed.

Class xv6G (Σ : gFunctors) := Xv6G {
  xv6_sie        :: sieG Σ;
  xv6_lock       :: lockG Σ;
  xv6_kalloc     :: kallocG Σ;
  xv6_bio        :: bioG Σ;
  xv6_disk       :: diskGhostG Σ;
  xv6_uart       :: uartGhostG Σ;
  xv6_fslog      :: fsLogG Σ;
  xv6_log        :: logG Σ;
  xv6_fscrash    :: fsCrashG Σ;
  xv6_ireg       :: iregG Σ;
  (* ---- the three that came OUT of [FileInvDefs.fileG] ---------------
     [fileG] carried these as superclasses so that the ~100 files merely
     mentioning [proc_priv] need not name the pipe and cache layers.  The
     motive was right and is this file's; the remedy was not, because a
     bundle per subsystem gives you one instance path per bundle.  The rule
     it forced ("a file that needs both takes [fileG] alone") was
     unenforceable and, in fact, unenforced: twenty-seven files bound
     [fileG] and [!icacheG] side by side.  One bundle, one path. *)
  xv6_icache     :: icacheG Σ;
  xv6_pipe       :: pipeG Σ;
  xv6_cinv       :: cinvG Σ;
  xv6_uio        :: uioG Σ;
}.

(* THE FUNCTOR LIST, and the [subG] instance adequacy resolves the bundle
   through.  Every member is pure capacity, so this is exactly the union of
   their own [Σ]s -- and because the fields above are [::] (instance)
   fields, Rocq cannot assemble the record on its own: without this
   instance a concrete [Σ] yields "Could not find an instance for
   [xv6G xv6Σ]" even when every constituent is present. *)
Definition xv6GΣ : gFunctors :=
  #[ sieΣ; lockΣ; kallocΣ; bioΣ; diskGhostΣ; uartGhostΣ; fsLogΣ; logΣ;
     fsCrashΣ; iregΣ; icacheΣ; pipeΣ; cinvΣ; uioΣ ].

Global Instance subG_xv6GΣ {Σ} : subG xv6GΣ Σ -> xv6G Σ.
Proof. solve_inG. Qed.
