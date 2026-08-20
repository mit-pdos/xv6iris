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

    ---- WHY THIS FILE HOLDS ONLY THE BUNDLE ----------------------------

    The members are DEFINED in [Xv6Cameras.v], which sits on ten
    base-layer files; read its header for what is in it, what is
    deliberately not, and why.  The split is not cosmetic:

    - The bundle can only sit above every member, so with the classes
      spread across their subsystems' files [xv6G]'s cone was eighty-two
      files -- the whole M-mode execution engine, the inode cache, the
      inode region, the UART driver.  All 767 files that bind the bundle
      waited on all of it, and editing ONE subsystem's algebra rebuilt all
      767.  With the definitions hoisted the cone is eleven, and an edit to
      (say) [InodeRegion.v] rebuilds 203 files instead of 768.

    - Keeping the BUNDLE out of [Xv6Cameras.v] is what enforces the rule
      above.  Every member's home file [Require Export]s [Xv6Cameras], so
      if [xv6G] lived there too it would become visible inside its own
      cone -- and a low file binding [xv6G] beside a member is exactly the
      double instance path this class exists to prevent.  It compiles, and
      nothing in the resulting error names the cause.

    THE [Require Export] BELOW IS LOAD-BEARING, not tidiness.  A member's
    FIELD instances ([uio_stdinG], [lock_inG], ...) are only active where
    [Xv6Cameras] is IMPORTED, and [Import] is not transitive -- so with a
    plain [Require Import] here, a file that reaches the bundle ONLY through
    [Xv6G] (there is one, [UmodeIo.v]) gets [xv6_uio : xv6G Σ -> uioG Σ] and
    then no way to step from [uioG Σ] to the [ghost_varG] it wraps.  The
    error names the innermost class and no cause: "Cannot infer the implicit
    parameter ghost_varG0 ... (no type class instance found)", with [xv6G]
    sitting right there in the printed environment.

    ADDING A MEMBER TAKES THREE THINGS, not one: the class (in
    [Xv6Cameras.v], with its own [subG] instance -- [solve_inG] has to be
    able to CONSTRUCT it, so a class with no [subG] breaks [subG_xv6GΣ]
    with "Cannot infer this placeholder"), the field below, and a row in
    [xv6GΣ].  *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own cancelable_invariants.
Require Export Xv6Cameras.

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
