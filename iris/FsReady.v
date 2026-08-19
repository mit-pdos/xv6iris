(*  FsReady.v -- THE RUNTIME FILE SYSTEM, AS ONE PERSISTENT ASSERTION,
    AND THE SEAL THAT MAKES IT EXIST.  (SIMP-2, second half;
    claude-notes/design/ghost-simplification.md §5.2.)

    ---- WHAT IS HERE, AND WHY IT IS HERE RATHER THAN IN FsSyscalls.v ----

    [fs_ready] is [FsSyscalls.fs_world] REHOMED, conjunct for conjunct.
    Nothing about the assertion changed; what changed is three things
    around it:

      1. IT HAS ITS OWN LEAF FILE, below the syscall layer, so that any
         file that wants the fs environment can import the predicate
         without importing the syscall bodies that used to own it.
         [FsSyscalls.fs_world] is now the DERIVED form -- a one-line
         alias -- and its two friendly seals read unchanged.

      2. IT HAS A PRODUCER.  [fs_world] never had one: it was, in its own
         header's words, an assertion "a friendly client pays for once, at
         boot", with satisfiability unchecked (upstream's [syscall_env] is
         in the same position).  [fs_ready_seal] and [fs_ready_establish]
         below are that producer's two halves, and both are machine-checked
         (probe ZZSimp2.v P3, satisfiability-first per iclaim-ledger.md
         §5''''): the boot-shelter token [ireg_boot] that fsinit hands back
         DIES into the persistent sealed regime [ireg_open], and the
         remaining eighteen constituents -- every one of which fsinit's own
         caller already holds -- complete the predicate in one [bupd].

      3. IT IS BOOT-FREE, AND THE TYPE ENFORCES IT.  Not one conjunct
         mentions boot state.  [ireg_boot] is EXCLUSIVE and is consumed by
         the seal, so the instant [fs_ready] exists, booting is over: there
         is nothing boot-shaped left to mention, and no continuation that
         carries [fs_ready] can be asked about the boot chain again.  This
         is why fsinit and ireclaim -- which run PRE-seal -- keep their
         constituent forms and must not take [fs_ready]: they hold
         [ireg_inv] without [ireg_open], and the predicate they cannot form
         is exactly the predicate whose existence says they are done.

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

    THIS IS LOAD-BEARING, and it is the live finding the design pass
    recorded.  [FsSyscalls]'s own section names [fileG] but NOT [icfg] or
    [icacheG]; [fileG] carries both as superclass FIELDS
    ([FileInvDefs.file_icfg], [FileInvDefs.file_icacheG]), so every
    icache-flavoured conjunct of [fs_world] is elaborated at the BAKED
    projections rather than at a binder.  A foreign section with its own
    [ICFG : icfg] therefore cannot frame [fs_world]'s conjuncts against
    its own re-typed copies -- which is what made the projection family
    unprobeable outside this file.

    The fix, and the reason [fs_ready] is stated here at all: this section
    declares [icacheG] and [icfg] EXPLICITLY, and declares them LAST so
    that resolution prefers them over [fileG]'s fields.  [fs_ready] is
    therefore PARAMETRIC in the cache's index, every projection below is
    stated at that same parameter, and the alias in [FsSyscalls]
    instantiates it with [file_icfg]/[file_icacheG] -- recovering today's
    [fs_world] on the nose.  *)

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
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecDirlink.   (* [ic_sleeplocks] *)
Require Import ProcAvail.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Section FsReady.
  (* FsSyscalls' own [Section FsBundles] context, verbatim... *)
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId}.
  (* ...AND THE CACHE'S INDEX, EXPLICIT AND DECLARED LAST (the header's
     last section).  Last, because instance resolution prefers the most
     recently declared candidate: with these here, every icache conjunct
     below is at [ICFG]/[icacheG0] rather than at [fileG]'s baked fields,
     and the whole projection family is stated at the same index a
     consumer's own section would carry. *)
  Context `{!icacheG Σ} `{ICFG : icfg}.

  (* ================================================================== *)
  (*  1.  THE PREDICATE                                                  *)
  (* ================================================================== *)

  (* THE RUNTIME FILE SYSTEM.  Every invariant, lock handle and certificate
     the fs cone runs on, plus the printk credential PAIR (the resource and
     its pure contract, which travel together and are wanted together by
     ialloc's out-of-inodes arm).

     PERSISTENT, and that is the theorem about hiding: the syscall seals
     CONSUME all nineteen and return NONE of them, and that is sound
     precisely because not one of them is spent.  A client pays for the
     file system's world once -- at the seal, below.

     NOT ONE CONJUNCT IS BOOT STATE.  That is the design, not an accident:
     see the header. *)
  Definition fs_ready (γpr γa : gname) (γs : list gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names) (glog : log_names)
      (γfs : fs_names) (γi : gname) (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      : iProp Σ :=
    (kernel_text ∗ kernel_data ∗
     printk_env γpr γu γd ∗ ⌜printk_gen_contract (kt := KT1) γpr γu γd⌝ ∗
     bio_ctx bn (fs_view γfs γd dev cov) ∗
     log_ctx glog bn γfs cov logstart dev ∗
     fs_crash_seam cov logstart ∗
     gen_cert ∗
     dev_inv γu γd ∗
     disk_geom γd pd pav pu ∗
     is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) ∗
     is_itable2 gtl cn γfs γi cov logstart nib dev ∗
     itable_inv ∗
     ic_escrows cn γfs γi cov logstart ∗
     ic_sleeplocks cn ∗
     ireg_inv γi γfs inodestart nib ∗
     (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).
        Persistent, and it rides beside [ireg_inv] because that is the
        channel [SpecCreate] -> [SpecIalloc] -> [ireg_claim_au] uses.  It is
        also the ONE conjunct the boot chain cannot already have: the seal
        below is what mints it, and minting it is what ends booting. *)
     ireg_open ∗
     kalloc_env γa None ∗
     procs_inv γs)%I.

  Global Instance fs_ready_persistent γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    Persistent (fs_ready γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
                         cov logstart inodestart nib dev).
  Proof. rewrite /fs_ready. apply _. Qed.

  (* MEASURED, AND LOAD-BEARING (SIMP-2 executor finding).  Without this,
     resolving [Persistent (fs_ready_pre ...)] below tries [fs_ready_persistent]
     as a candidate and unification delta-unfolds NINETEEN invariant/lock
     conjuncts against EIGHTEEN -- the file goes from 3 seconds to 18+ CPU
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

  (* THE PACK, at the eighteen constituents that are NOT the regime.
     Stated as its own definition so that the establishment below reads as
     "the boot caller's pile, plus the token, is the predicate" rather than
     as a twenty-argument wand -- and so that a seal site can be checked
     against it constituent by constituent. *)
  Definition fs_ready_pre (γpr γa : gname) (γs : list gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names) (glog : log_names)
      (γfs : fs_names) (γi : gname) (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      : iProp Σ :=
    (kernel_text ∗ kernel_data ∗
     printk_env γpr γu γd ∗ ⌜printk_gen_contract (kt := KT1) γpr γu γd⌝ ∗
     bio_ctx bn (fs_view γfs γd dev cov) ∗
     log_ctx glog bn γfs cov logstart dev ∗
     fs_crash_seam cov logstart ∗
     gen_cert ∗
     dev_inv γu γd ∗
     disk_geom γd pd pav pu ∗
     is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) ∗
     is_itable2 gtl cn γfs γi cov logstart nib dev ∗
     itable_inv ∗
     ic_escrows cn γfs γi cov logstart ∗
     ic_sleeplocks cn ∗
     ireg_inv γi γfs inodestart nib ∗
     kalloc_env γa None ∗
     procs_inv γs)%I.

  Global Instance fs_ready_pre_persistent γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    Persistent (fs_ready_pre γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
                             cov logstart inodestart nib dev).
  Proof. rewrite /fs_ready_pre. apply _. Qed.

  (* ...and the same seal, for the same measured reason. *)
  Typeclasses Opaque fs_ready_pre.

  (* THE ESTABLISHMENT.  This is the whole of what a seal site owes: hold
     the eighteen (every one of which is either persistent boot material
     the chain already carries, or a bundle [SpecFsinit]'s post hands
     back), hold fsinit's returned [ireg_boot], and the runtime file system
     exists.  Nothing is left over and nothing else is required. *)
  Lemma fs_ready_establish γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    fs_ready_pre γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
                 cov logstart inodestart nib dev -∗
    ireg_boot ==∗
    fs_ready γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
             cov logstart inodestart nib dev.
  Proof.
    iIntros "Hpre Hboot".
    iMod (fs_ready_seal with "Hboot") as "#Hopen".
    iModIntro. rewrite /fs_ready /fs_ready_pre.
    iDestruct "Hpre" as "(H1 & H2 & H3 & %H4 & H5 & H6 & H7 & H8 & H9 & H10
                          & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18)".
    iFrame "H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18".
    iFrame "%". iExact "Hopen".
  Qed.

  (* ...and the converse half a seal site wants to READ BACK: the predicate
     contains its own pre.  (Trivial, but it is what lets a client that has
     been handed [fs_ready] re-enter a pre-seal-shaped callee -- ireclaim,
     say -- without unfolding by hand.) *)
  Lemma fs_ready_pre_of γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    fs_ready γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
             cov logstart inodestart nib dev -∗
    fs_ready_pre γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
                 cov logstart inodestart nib dev.
  Proof.
    rewrite /fs_ready /fs_ready_pre.
    iIntros "(H1 & H2 & H3 & %H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
              & H13 & H14 & H15 & H16 & _ & H17 & H18)".
    iFrame "H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18".
    iFrame "%".
  Qed.

  (* ================================================================== *)
  (*  3.  THE PROJECTION FAMILY                                          *)
  (* ================================================================== *)

  (* THE POINT OF THE REHOMING.  Each of these is one [iDestruct], and each
     is statable only here: outside this section the conjuncts elaborate at
     a foreign [icfg] and will not frame (the header's last section).  A
     consumer that holds [fs_ready] recovers exactly the rows a
     constituent-shaped contract asks for -- so a continuation carrying ONE
     persistent row can feed a callee that spells seven.

     They are grouped the way real contracts group them: the machine's two
     text/data certificates, the printk pair (and the [panic_env] every
     panic arm actually asks for), the block/log fabric, the disk fabric,
     the icache's four, the inode region's two, and the process/allocator
     pair. *)

  Section Projections.
    Context (γpr γa : gname) (γs : list gname)
            (γu : uart_names) (γd : disk_names) (γk : gname)
            (pd pav pu : mword 64) (bn : bio_names) (glog : log_names)
            (γfs : fs_names) (γi : gname) (cn : ic_names) (gtl : gname)
            (cov : gset Z) (logstart inodestart : Z) (nib : nat)
            (dev : mword 32).

    Notation FSR := (fs_ready γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn
                              gtl cov logstart inodestart nib dev).

    Lemma fs_ready_text : FSR -∗ kernel_text.
    Proof. rewrite /fs_ready. by iIntros "($ & _)". Qed.

    Lemma fs_ready_data : FSR -∗ kernel_data.
    Proof. rewrite /fs_ready. by iIntros "(_ & $ & _)". Qed.

    Lemma fs_ready_printk :
      FSR -∗ printk_env γpr γu γd ∗ ⌜printk_gen_contract (kt := KT1) γpr γu γd⌝.
    Proof. rewrite /fs_ready. by iIntros "(_ & _ & $ & $ & _)". Qed.

    (* what a panic arm actually asks for -- [printk_env] is strictly
       stronger, and this is the standing weakening. *)
    Lemma fs_ready_panic : FSR -∗ SpecPanic.panic_env.
    Proof.
      iIntros "H". iDestruct (fs_ready_printk with "H") as "[Hp _]".
      by iApply printk_env_panic.
    Qed.

    Lemma fs_ready_bio : FSR -∗ bio_ctx bn (fs_view γfs γd dev cov).
    Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & $ & _)". Qed.

    Lemma fs_ready_log : FSR -∗ log_ctx glog bn γfs cov logstart dev.
    Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & $ & _)". Qed.

    Lemma fs_ready_seam : FSR -∗ fs_crash_seam cov logstart.
    Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & _ & $ & _)". Qed.

    Lemma fs_ready_gen : FSR -∗ gen_cert.
    Proof. rewrite /fs_ready. by iIntros "(_ & _ & _ & _ & _ & _ & _ & $ & _)". Qed.

    (* the disk fabric, as the three rows every fs contract spells together *)
    Lemma fs_ready_disk :
      FSR -∗ dev_inv γu γd ∗ disk_geom γd pd pav pu ∗
             is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu).
    Proof.
      rewrite /fs_ready.
      by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & $ & $ & $ & _)".
    Qed.

    (* the icache's four, likewise *)
    Lemma fs_ready_icache :
      FSR -∗ is_itable2 gtl cn γfs γi cov logstart nib dev ∗ itable_inv ∗
             ic_escrows cn γfs γi cov logstart ∗ ic_sleeplocks cn.
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
      FSR -∗ ireg_inv γi γfs inodestart nib ∗ ireg_open.
    Proof.
      rewrite /fs_ready.
      by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & $ & $ & _)".
    Qed.

    Lemma fs_ready_kalloc : FSR -∗ kalloc_env γa None.
    Proof.
      rewrite /fs_ready.
      by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & _ & _ & $ & _)".
    Qed.

    Lemma fs_ready_procs : FSR -∗ procs_inv γs.
    Proof.
      rewrite /fs_ready.
      by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & _ & _ & _ & $)".
    Qed.

    (* ---- THE FORKRET ROW, spelled out -------------------------------
       This is the acceptance criterion of ghost-simplification.md §5.3,
       as a lemma: ONE persistent premise yields, in one step, the whole
       pile a runtime fs continuation can want.  What
       [wp_forkret_nf_ax]'s discharge owes the file system is therefore
       exactly [fs_ready ... -∗] and nothing else; the rest of the IOU is
       scheduler/trapframe work with no fs entanglement. *)
    Lemma fs_ready_all :
      FSR -∗
      kernel_text ∗ kernel_data ∗
      printk_env γpr γu γd ∗ ⌜printk_gen_contract (kt := KT1) γpr γu γd⌝ ∗
      bio_ctx bn (fs_view γfs γd dev cov) ∗
      log_ctx glog bn γfs cov logstart dev ∗
      fs_crash_seam cov logstart ∗ gen_cert ∗
      dev_inv γu γd ∗ disk_geom γd pd pav pu ∗
      is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) ∗
      is_itable2 gtl cn γfs γi cov logstart nib dev ∗ itable_inv ∗
      ic_escrows cn γfs γi cov logstart ∗ ic_sleeplocks cn ∗
      ireg_inv γi γfs inodestart nib ∗ ireg_open ∗
      kalloc_env γa None ∗ procs_inv γs.
    Proof. rewrite /fs_ready. by iIntros "$". Qed.

  End Projections.

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
