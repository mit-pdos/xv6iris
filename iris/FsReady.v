(*  FsReady.v -- THE RUNTIME FILE SYSTEM, AS ONE PERSISTENT ASSERTION,
    AND THE SEAL THAT MAKES IT EXIST.  (SIMP-2, second half;
    claude-notes/design/ghost-simplification.md §5.2 and §5.3a;
    claude-notes/design/fs-ghost-state.md §7.)

    ---- WHAT IS HERE ----------------------------------------------------

    [fs_ready] began as [FsSyscalls.fs_world] rehomed.  Three things are
    true of it now that were not true of that assertion:

      1. IT HAS ITS OWN LEAF FILE, below the syscall layer -- and, since the
         [ic_sleeplocks] hoist, below the whole Spec layer.  Any file that
         wants the fs environment can import the predicate without
         importing the syscall bodies that used to own it.

      2. IT HAS A PRODUCER.  [fs_world] never had one: it was, in its own
         header's words, an assertion "a friendly client pays for once, at
         boot", with satisfiability unchecked (upstream's [syscall_env] is
         in the same position).  [fs_ready_seal] and [fs_ready_establish]
         below are that producer's two halves: the boot-shelter token
         [ireg_boot] that fsinit hands back DIES into the persistent sealed
         regime [ireg_open], and the remaining seventeen constituents --
         every one of which fsinit's own caller already holds -- complete
         the predicate in one [bupd].

      3. IT IS BOOT-FREE, AND THE TYPE ENFORCES IT.  Not one conjunct
         mentions boot state.  [ireg_boot] is EXCLUSIVE and is consumed by
         the seal, so the instant [fs_ready] exists, booting is over: there
         is nothing boot-shaped left to mention, and no continuation that
         carries [fs_ready] can be asked about the boot chain again.  This
         is why fsinit and ireclaim -- which run PRE-seal -- keep their
         constituent forms and must not take [fs_ready]: they hold
         [ireg_inv] without [ireg_open], and the predicate they cannot form
         is exactly the predicate whose existence says they are done.

    ---- IT TAKES NO PARAMETERS, AND THAT IS THE POINT -------------------

    [fs_ready] is meant to be CARRIED: produced by forkret's not-forked
    arm, held by a running process, handed to the trap loop, read back by
    every later syscall.  A twenty-parameter version can be carried only by
    existentially quantifying the twenty, and a bare existential is useless
    downstream -- a consumer handed [∃ γ…, fs_ready γ…] cannot feed it to
    [SpecKexec.fs_fabric] or [UsertrapRes.ut_res_bare], whose own resources
    are keyed to the CALLER's concrete names, because nothing relates the
    two.  Ambient names remove the existential instead of hiding it.

    So every name is ambient: the four the inode cache already owned
    ([icfg_log], [icfg_ist], [icfg_nib], [icfg_dev]) and the fifteen
    [FsCfg.fscfg] adds.  That is [IcacheRef.icfg]'s own argument one layer
    out -- there is exactly one file system per boot -- and [fscfg] is
    per-era exactly as [icfg] is (the disk image ghost is re-minted at
    PowerOn; design/crash.md), i.e. a Class ASSUMPTION each era's boot
    instantiates rather than a global constant.

    [procs_inv] IS NOT A CONJUNCT.  It is a PROCESS resource, it is
    persistent, every consumer holds it beside this predicate anyway
    ([SpecKexec.fs_fabric] lists it separately), and it was the only
    conjunct that reached back into the process layer -- which is what made
    the file system LOOK as though it depended on process abstractions.  A
    spec that wants it takes [procs_inv γs] as its own premise.

    [FsSyscalls.fs_world] is therefore no longer a one-line alias: it is
    this predicate AT A CALLER'S OWN NAMES -- the tie equations
    ([bn = fsc_bio], [glog = icfg_log], …) beside the ambient [fs_ready] --
    with [fs_world_all] doing the substitution once, so a body that threads
    its own names still destructs ONE row and gets the constituents spelled
    the way its callee spells them.  That is [SpecKexec]'s existing
    [g = icfg_log] idiom at full width.

    ---- WHY IT MATTERS: THE FORKRET DELTA ----

    [LinkForkretNF.v]'s header states the problem this file exists to
    solve.  forkret's not-forked arm calls fsinit and kexec, and forkret
    holds the fs environment "only INSIDE the residue closer ... If the
    arm's proof needs those resources up front, this contract grows a
    premise."  Growing it by the CONSTITUENTS is fifteen-plus rows with
    the boot/regime story unresolved at that altitude.  Growing it by
    [fs_ready] is ONE row, and a persistent one: everything the arm's
    continuation can want is recovered by the projection family below,
    which is an [iDestruct] one-liner because the family lives INSIDE this
    file's section.

    ---- THE SECTION, AND THE CLASS-USED-AS-INDEX TRAP ----

    THIS IS LOAD-BEARING.  [FsSyscalls]'s own section names [fileG] but NOT
    [icfg] or [icacheG]; [fileG] carries both as superclass FIELDS
    ([FileInvDefs.file_icfg], [FileInvDefs.file_icacheG]), so every
    icache-flavoured conjunct is elaborated at the BAKED projections rather
    than at a binder.  A foreign section with its own [ICFG : icfg]
    therefore cannot frame those conjuncts against its own re-typed copies
    -- which is what made the projection family unprobeable outside this
    file.

    So this section declares [icacheG] and [icfg] EXPLICITLY and declares
    them LAST, so that resolution prefers them over [fileG]'s fields:
    [fs_ready] is parametric in the cache's INDEX (though not in its
    names), and every projection below is stated at that same index, so a
    consumer elaborating at [file_icfg]/[file_icacheG] meets it on the
    nose.  [FSC : fscfg] is bound here too and is NOT a superclass of
    anything, so unlike [icfg] it has to be bound by hand wherever this
    predicate is named.  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
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
Require Import IcacheEscrow.
Require Import FsCfg.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecPrintk.
Require Import ProcAvail.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section FsReady.
  (* FsSyscalls' own [Section FsBundles] context, verbatim... *)
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  (* ...AND THE CACHE'S INDEX, EXPLICIT AND DECLARED LAST (the header's
     last section).  Last, because instance resolution prefers the most
     recently declared candidate: with these here, every icache conjunct
     below is at [ICFG]/[icacheG0] rather than at [fileG]'s baked fields,
     and the whole projection family is stated at the same index a
     consumer's own section would carry. *)
  Context `{!xv6G Σ} `{ICFG : icfg} `{FSC : fscfg}.

  (* ================================================================== *)
  (*  1.  THE PREDICATE                                                  *)
  (* ================================================================== *)

  (* THE RUNTIME FILE SYSTEM.  Every invariant, lock handle and certificate
     the fs cone runs on, plus the printk credential PAIR (the resource and
     its pure contract, which travel together and are wanted together by
     ialloc's out-of-inodes arm).

     NO PARAMETERS.  Every name it used to take is ambient: the four the
     inode cache already owned ([icfg_log], [icfg_ist], [icfg_nib],
     [icfg_dev]) and the fifteen [FsCfg.fscfg] adds.  That file's header
     carries the argument; the short version is that a carried predicate
     must not be an existential, because an existential cannot be fed to a
     consumer whose own resources are keyed to concrete names.

     PERSISTENT, and that is the theorem about hiding: the syscall seals
     CONSUME all eighteen and return NONE of them, and that is sound
     precisely because not one of them is spent.  A client pays for the
     file system's world once -- at the seal, below.

     [procs_inv] IS NO LONGER A CONJUNCT.  It is persistent and every
     consumer holds it beside this predicate anyway ([SpecKexec.fs_fabric]
     lists it separately; forkret's tier carries it in the park package's
     persistent world), and it was the one conjunct that reached back into
     the process layer -- which is what made [fs_ready] look as though the
     file system depended on process abstractions.  A spec that wants it
     now takes [procs_inv γs] as its own premise.

     NOT ONE CONJUNCT IS BOOT STATE.  That is the design, not an accident:
     see the header. *)
  Definition fs_ready : iProp Σ :=
    (kernel_text ∗ kernel_data ∗
     printk_env fsc_printk fsc_uart fsc_disk ∗
     ⌜printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk⌝ ∗
     bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) ∗
     log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev ∗
     fs_crash_seam fsc_cov fsc_logst ∗
     gen_cert ∗
     dev_inv fsc_uart fsc_disk ∗
     disk_geom fsc_disk fsc_desc fsc_avail fsc_used ∗
     is_lock fsc_dlock d_lock "virtio_disk"%string
             (disk_res fsc_disk fsc_desc fsc_avail fsc_used) ∗
     is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
                icfg_nib icfg_dev ∗
     itable_inv ∗
     ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗
     ic_sleeplocks fsc_ic ∗
     ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).
        Persistent, and it rides beside [ireg_inv] because that is the
        channel [SpecCreate] -> [SpecIalloc] -> [ireg_claim_au] uses.  It is
        also the ONE conjunct the boot chain cannot already have: the seal
        below is what mints it, and minting it is what ends booting. *)
     ireg_open ∗
     kalloc_env fsc_kalloc None)%I.

  Global Instance fs_ready_persistent : Persistent fs_ready.
  Proof. rewrite /fs_ready. apply _. Qed.

  (* MEASURED, AND LOAD-BEARING (SIMP-2 executor finding).  Without this,
     resolving [Persistent fs_ready_pre] below tries [fs_ready_persistent]
     as a candidate and unification delta-unfolds EIGHTEEN invariant/lock
     conjuncts against SEVENTEEN -- the file goes from 3 seconds to 18+ CPU
     minutes with no error, i.e. it looks like a hang rather than a mistake.
     Sealing the name is the standard Iris idiom and costs nothing: the two
     instances are still found by head symbol, and every proof that wants the
     body still says [rewrite /fs_ready]. *)
  Typeclasses Opaque fs_ready.

  (* ================================================================== *)
  (*  2.  THE SEAL -- the producer [fs_world] never had                  *)
  (* ================================================================== *)

  (* THE SEAL ITSELF.  fsinit's EXCLUSIVE boot-shelter token
     ([IcacheRef.ireg_boot] = [ity_pending icfg_boot], threaded from
     [icfg_alloc] through the whole boot chain and handed back by
     [SpecFsinit]'s post) is SHOT here, and what it becomes is the
     persistent sealed regime.  One [bupd], no invariant, no mask.

     THIS IS THE BOOT-FREEDOM WITNESS.  [ireg_boot] is exclusive, so after
     this step no second seal is possible and no boot-shaped resource
     survives: [ireg_open] is an existential over the one-shot's value and
     mentions nothing else.  "Booting is over the instant the predicate
     exists" is exactly this lemma. *)
  Lemma fs_ready_seal : ireg_boot ==∗ ireg_open.
  Proof.
    iIntros "Hboot". rewrite /ireg_boot /ireg_open.
    iMod (ity_shoot _ (mword_of_int (len:=16) 0) with "Hboot") as "#Hs".
    iModIntro. by iExists _.
  Qed.

  (* THE PACK, at the seventeen constituents that are NOT the regime.
     Stated as its own definition so that the establishment below reads as
     "the boot caller's pile, plus the token, is the predicate" rather than
     as a wand -- and so that a seal site can be checked against it
     constituent by constituent. *)
  Definition fs_ready_pre : iProp Σ :=
    (kernel_text ∗ kernel_data ∗
     printk_env fsc_printk fsc_uart fsc_disk ∗
     ⌜printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk⌝ ∗
     bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) ∗
     log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev ∗
     fs_crash_seam fsc_cov fsc_logst ∗
     gen_cert ∗
     dev_inv fsc_uart fsc_disk ∗
     disk_geom fsc_disk fsc_desc fsc_avail fsc_used ∗
     is_lock fsc_dlock d_lock "virtio_disk"%string
             (disk_res fsc_disk fsc_desc fsc_avail fsc_used) ∗
     is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
                icfg_nib icfg_dev ∗
     itable_inv ∗
     ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗
     ic_sleeplocks fsc_ic ∗
     ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     kalloc_env fsc_kalloc None)%I.

  Global Instance fs_ready_pre_persistent : Persistent fs_ready_pre.
  Proof. rewrite /fs_ready_pre. apply _. Qed.

  (* ...and the same seal, for the same measured reason. *)
  Typeclasses Opaque fs_ready_pre.

  (* THE ESTABLISHMENT.  This is the whole of what a seal site owes: hold
     the seventeen (every one of which is either persistent boot material
     the chain already carries, or a bundle [SpecFsinit]'s post hands
     back), hold fsinit's returned [ireg_boot], and the runtime file system
     exists.  Nothing is left over and nothing else is required. *)
  Lemma fs_ready_establish : fs_ready_pre -∗ ireg_boot ==∗ fs_ready.
  Proof.
    iIntros "Hpre Hboot".
    iMod (fs_ready_seal with "Hboot") as "#Hopen".
    iModIntro. rewrite /fs_ready /fs_ready_pre.
    iDestruct "Hpre" as "(H1 & H2 & H3 & %H4 & H5 & H6 & H7 & H8 & H9 & H10
                          & H11 & H12 & H13 & H14 & H15 & H16 & H17)".
    iFrame "H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17".
    iFrame "%". iExact "Hopen".
  Qed.

  (* ...and the converse half a seal site wants to READ BACK: the predicate
     contains its own pre.  (Trivial, but it is what lets a client that has
     been handed [fs_ready] re-enter a pre-seal-shaped callee -- ireclaim,
     say -- without unfolding by hand.) *)
  Lemma fs_ready_pre_of : fs_ready -∗ fs_ready_pre.
  Proof.
    rewrite /fs_ready /fs_ready_pre.
    iIntros "(H1 & H2 & H3 & %H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
              & H13 & H14 & H15 & H16 & _ & H17)".
    iFrame "H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17".
    iFrame "%".
  Qed.

  (* ================================================================== *)
  (*  3.  THE PROJECTION FAMILY                                          *)
  (* ================================================================== *)

  (* THE POINT OF THE REHOMING.  Each of these is one [iDestruct].  A
     consumer that holds [fs_ready] recovers exactly the rows a
     constituent-shaped contract asks for -- so a continuation carrying ONE
     persistent row can feed a callee that spells seven.

     They are grouped the way real contracts group them: the machine's two
     text/data certificates, the printk pair (and the [panic_env] every
     panic arm actually asks for), the block/log fabric, the disk fabric,
     the icache's four, the inode region's two, and the allocator. *)

  Lemma fs_ready_text : fs_ready -∗ kernel_text.
  Proof. rewrite /fs_ready. by iIntros "($ & _)". Qed.

  Lemma fs_ready_data : fs_ready -∗ kernel_data.
  Proof. rewrite /fs_ready. by iIntros "(_ & $ & _)". Qed.

  Lemma fs_ready_printk :
    fs_ready -∗ printk_env fsc_printk fsc_uart fsc_disk ∗
                ⌜printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk⌝.
  Proof. rewrite /fs_ready. by iIntros "(_ & _ & $ & $ & _)". Qed.

  (* what a panic arm actually asks for -- [printk_env] is strictly
     stronger, and this is the standing weakening. *)
  Lemma fs_ready_panic : fs_ready -∗ SpecPanic.panic_env.
  Proof.
    iIntros "H". iDestruct (fs_ready_printk with "H") as "[Hp _]".
    by iApply printk_env_panic.
  Qed.

  Lemma fs_ready_bio :
    fs_ready -∗ bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov).
  Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & $ & _)". Qed.

  Lemma fs_ready_log :
    fs_ready -∗ log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev.
  Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & $ & _)". Qed.

  Lemma fs_ready_seam : fs_ready -∗ fs_crash_seam fsc_cov fsc_logst.
  Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & _ & $ & _)". Qed.

  Lemma fs_ready_gen : fs_ready -∗ gen_cert.
  Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & _ & _ & $ & _)". Qed.

  (* the disk fabric, as the three rows every fs contract spells together *)
  Lemma fs_ready_disk :
    fs_ready -∗ dev_inv fsc_uart fsc_disk ∗
                disk_geom fsc_disk fsc_desc fsc_avail fsc_used ∗
                is_lock fsc_dlock d_lock "virtio_disk"%string
                        (disk_res fsc_disk fsc_desc fsc_avail fsc_used).
  Proof.
    rewrite /fs_ready.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & $ & $ & $ & _)".
  Qed.

  (* the icache's four, likewise *)
  Lemma fs_ready_icache :
    fs_ready -∗ is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
                           icfg_nib icfg_dev ∗ itable_inv ∗
                ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗
                ic_sleeplocks fsc_ic.
  Proof.
    rewrite /fs_ready.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & $ & $ & $ & $ & _)".
  Qed.

  (* THE INODE REGION, AND ITS REGIME.  This is the pair the whole
     second half exists for: a runtime callee wants [ireg_inv] beside the
     SEALED [ireg_open], and a client that holds [fs_ready] has both by
     construction -- there is no arm to case on and no boot token to
     thread, because the seal already happened. *)
  Lemma fs_ready_region :
    fs_ready -∗ ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗ ireg_open.
  Proof.
    rewrite /fs_ready.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & $ & $ & _)".
  Qed.

  Lemma fs_ready_kalloc : fs_ready -∗ kalloc_env fsc_kalloc None.
  Proof.
    rewrite /fs_ready.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & _ & _ & $)".
  Qed.

  (* ---- THE FORKRET ROW, spelled out -------------------------------
     This is the acceptance criterion of ghost-simplification.md §5.3, as a
     lemma: ONE persistent premise yields, in one step, the whole pile a
     runtime fs continuation can want.  What forkret's [if (first)] arm owes
     the file system is therefore exactly [fs_ready -∗] and nothing else;
     the rest is scheduler/trapframe work with no fs entanglement. *)
  Lemma fs_ready_all :
    fs_ready -∗
    kernel_text ∗ kernel_data ∗
    printk_env fsc_printk fsc_uart fsc_disk ∗
    ⌜printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk⌝ ∗
    bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) ∗
    log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev ∗
    fs_crash_seam fsc_cov fsc_logst ∗ gen_cert ∗
    dev_inv fsc_uart fsc_disk ∗
    disk_geom fsc_disk fsc_desc fsc_avail fsc_used ∗
    is_lock fsc_dlock d_lock "virtio_disk"%string
            (disk_res fsc_disk fsc_desc fsc_avail fsc_used) ∗
    is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst
               icfg_nib icfg_dev ∗ itable_inv ∗
    ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗ ic_sleeplocks fsc_ic ∗
    ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗ ireg_open ∗
    kalloc_env fsc_kalloc None.
  Proof. rewrite /fs_ready. by iIntros "$". Qed.

End FsReady.

(* AND THE SAME TWO SEALS AT TOP LEVEL.  [Typeclasses Opaque] inside a
   Section names the SECTION-LOCAL constant; after discharge the redeclared
   constant is a different one, and the setting does not travel.  Re-stating
   them here is what makes the seal hold for every IMPORTER -- without it,
   the two persistence instances above are candidates for every
   [Persistent ?P] goal downstream, and each trial unifies [?P] against a
   nineteen-conjunct chain of invariants and lock handles.  Measured:
   [FsSyscalls.v] goes from minutes to 28+ and counting.  This is the same
   trap the in-section seals fix, one scope up. *)
Typeclasses Opaque fs_ready.
Typeclasses Opaque fs_ready_pre.
