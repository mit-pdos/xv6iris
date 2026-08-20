(* ======================================================================= *)
(*  FsSyscalls.v -- F3: THE SYSCALL BOUNDARY, PACKAGED.                     *)
(*  design: claude-notes/design/fs-friendly.md (F3), fs-fragments.md R3/R8  *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS, AND WHAT IT IS NOT.

    F3's charter is the friendly syscall triple

      <t. fs_rep-fragment> sys_mkdir(path) <t'. post * [t' = tree_insert ...]>

    **THE TREE-DELTA HALF OF THAT CHARTER IS STOPPED, AND THE STOP IS A
    THEOREM ABOUT THE LANDED SEALS, NOT A GAP IN THIS FILE.**  Three
    independent obstructions, each verified against the landed text and
    each recorded at the point of use below:

    (S1) NO SYSCALL SEAL CARRIES A TREE DELTA, AND sys_mkdir's CANNOT BE
         GIVEN ONE CALLER-SIDE.  [SpecSysMkdir.v]:280-304 is the whole
         postcondition: a register file, [proc_priv], the four superblock
         cells, [bslots], [bitmap_res] at an UNORDERED [used'], the iref
         interval, and [sys_mkdir_ret] (0 or -1).  Nothing inode-shaped,
         nothing byte-shaped, nothing tree-shaped.  ProofSysMkdir.v:60 says
         so itself: *"Nothing inode-shaped survives the call, which is why
         this function's own post mentions none of it."*  The delta is made
         three contracts down (dirlink's record write inside create) and
         nothing on the path relays it: create's own post
         ([SpecCreate.v]:668-692) names ONLY the returned CHILD
         ([create_locked] at [k]/[inum]/[dn]/[bm]) and says nothing whatever
         about the PARENT, which create has already [iunlockput]'d -- while
         the tree delta of a mkdir IS an edge at the parent.  F2's lift
         worked because [SpecDirlookup]'s post spoke about the SAME [data]
         the caller's fragment named; there is no such shared name here.

    (S2) THERE IS NO AMBIENT TREE RESOURCE AT THE SYSCALL BOUNDARY, and R3
         forbids the only thing that would make one.  [FsRep.fnode] needs
         [InodeRegion.dinode_at], which is exclusive and lives inside
         [IcacheEscrow.ic_loaded] / [ipool_alloc] -- i.e. the ESCROW owns
         every node fragment in the system, and a thread can hold one only
         while it holds that inode's sleeplock (fs-fragments.md 1.4).  A
         syscall-level client holds no lock, so it can supply [fs_rep t]
         only at the EMPTY tree.  The HOCAP shape that would fix this is a
         whole-tree authority whose fragments clients hold -- and R3 kills
         it three times over (20.9(c)/(d)/(e)).  So the AU/HOCAP idiom is
         unavailable at this altitude for the same reason F2's is
         unavailable at a directory node, one level up: it is the lock
         placement, not the spec's shape.

    (S3) EVEN THE PURE-RESOURCE TRIPLE IS NOT COMPOSABLE FOR mkdir.  The
         iref ledger comes back as an INTERVAL ([SpecSysMkdir.v]:300,
         [ns - create_slots <= ns' <= ns]), inherited from create's own
         interval ([SpecCreate.v]:659-661).  A friendly client that wants to
         call mkdir TWICE cannot re-establish its own precondition
         ([create_slots <= ns]) from that.  sys_chdir does not have the
         problem -- its ledger closes at the literal 2 on all four arms
         ([SpecSysChdir.v]:259, :283 -- and see that file's header) -- which
         is why the chdir wrapper below is composable and the mkdir one is
         not.  NOTHING HERE AMENDS EITHER CONTRACT: the tightening, if it is
         ever wanted, is create's post, not sys_mkdir's.

    ---- SO WHAT DOES LAND -----------------------------------------------

    The OTHER half of F3's charter, item (c): what is HIDDEN.  A syscall
    seal takes 26 pure premises and 31 resources; a client that wants to
    call two syscalls in a row has to re-thread all of it.  This file gives
    the syscall boundary a CALLING CONVENTION -- three bundles and two
    wrappers derived from the landed seals, which do not move:

      [fs_geom]   the 19 pure geometry/ties premises, as ONE record.  Both
                  syscalls take the SAME one; chdir ignores five fields.
      [fs_world]  the 19 ambient resources, as ONE assertion -- **and it is
                  PERSISTENT**, which is the whole point.  A client
                  establishes the file system's world once and every syscall
                  is free of it forever after.  This is the honest content
                  of "the ambient is absorbed": not that the seals hide it,
                  but that all of it is duplicable and none of it is spent.
      [fs_res]    the 7 consumable resources that go in and come back:
                  [bslots], the four superblock cells, [bitmap_res] and the
                  iref ledger.  THIS is the part a client must account for,
                  and (S3) is exactly a statement about it.

    and, dropped outright because they are [emp] at the [eb = true] both
    seals force: [trap_csrs_ext] and [cpu_claim_ext], in the pre AND the
    post, together with the [eb] parameter itself.  That is F2's bar --
    FEWER premises than the seal, zero axioms added -- met in the one
    dimension where it can be met here.

    WHAT REMAINS IRREDUCIBLE, and is not a defect: the register file ([m],
    [mf], [callee_saved]), the stack budget [K] and the program counter.
    This is a WP over machine code; a friendly layer can bundle the file
    system's world but it cannot make the machine's own state disappear.

    ---- THE ONLY TREE-LEVEL STATEMENT AVAILABLE, AND ITS HONEST SIZE ----

    Framing.  Any assertion a client holds across one of these wrappers
    comes back untouched, [FsRep.fnode] included -- and that IS a locality
    theorem in a CSL ("this syscall cannot have touched a node you own").
    It is not stated as a lemma here because it is the frame rule, true of
    every [iProp] and provable by [iFrame], and because (S2) says a
    syscall-level client cannot in fact hold a node fragment: the escrow
    owns them all.  Recording it as an F3 result would overclaim.  The
    tree-level content of this increment is therefore exactly zero, and the
    stops above are what F3 actually learned.                              *)

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
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecDirlink.
Require Import SpecCreate.
Require Import SpecSysMkdir.
Require Import SpecSysChdir.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import FsCfg.     (* the ambient fs names [fs_ready] is stated at *)
Require Import FsReady.   (* SIMP-2: [fs_world] is now the derived form *)
Import Defs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE PURE SIDE: ONE RECORD FOR THE FILE SYSTEM'S GEOMETRY           *)
(* ====================================================================== *)

(*  The nineteen pure premises the two seals take between them, in the
    order [SpecSysMkdir.v]:201-223 states them.  It is deliberately the
    UNION and not the intersection: a friendly client establishes the file
    system's geometry ONCE (it is a fact about mkfs's image and the boot
    configuration, not about a call) and hands the same record to every
    syscall.  sys_chdir ignores [fg_bmgeom] and the four [ninodes] fields;
    that is five unused hypotheses at one call site against re-deriving
    fourteen at every other one.

    THE FOUR [icfg] TIES ARE FIELDS RATHER THAN A COERCION, and the
    instance is left implicit ON PURPOSE: at a use site it resolves from
    the ambient [fileG], which is the same [icfg] every [ic_*] resource in
    the same statement resolves through.  Binding a standalone [icfg]
    beside a [fileG] is SpecCreate.v:433-444's two-instance trap. *)
Record fs_geom `{ICFG : icfg}
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (ninodes size : Z) (dev : mword 32) (glog : log_names) : Prop := MkFsGeom {
  fg_dev      : dev = icfg_dev;
  fg_nib      : nib = icfg_nib;
  fg_log      : glog = icfg_log;
  fg_ist      : inodestart = icfg_ist;
  fg_rootdev  : dev = ROOTDEV;
  fg_nib_pos  : (0 < nib)%nat;
  fg_loggeom  : log_geom_ok cov logstart;
  fg_size     : 0 < size <= BPB;
  fg_bm_nn    : 0 <= bmapstart;
  fg_bm_cov   : bmapstart ∈ cov;
  fg_bm_out   : ~ (bmapstart ∈ log_region_set logstart);
  fg_ist_nn   : 0 <= inodestart;
  fg_covbelow : cov_below cov size;
  fg_bmgeom   : bitmap_geom_ok cov logstart bmapstart size;
  fg_iblocks  : ireg_blocks_ok inodestart nib cov logstart;
  fg_nin_lo   : 1 < ninodes;
  fg_nin_hi   : ninodes <= 16 * Z.of_nat nib;
  fg_nin_31   : ninodes < 2 ^ 31;
  fg_ushort   : 16 * Z.of_nat nib <= 2 ^ 16;
}.

(* ====================================================================== *)
(*  2.  THE TWO RESOURCE BUNDLES                                           *)
(* ====================================================================== *)

Section FsBundles.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  (* the ambient fs names [FsReady.fs_ready] is stated at.  It rides in on
     [fileG] exactly as [icfg] does (see the note on [FileInvDefs.fileG]),
     so there is no binder here and no second instance path. *)

  (* THE AMBIENT, AND IT IS PERSISTENT.  Every invariant, lock handle and
     certificate the fs cone runs on, plus the printk credential PAIR (the
     resource and its pure contract, which travel together and are wanted
     together by ialloc's out-of-inodes arm).

     [fs_world_persistent] below is this file's real theorem about hiding:
     the seals CONSUME all nineteen and return NONE of them, and that is
     sound precisely because not one of them is spent.  A friendly client
     pays for the file system's world once, at boot. *)
  (* REHOMED BY SIMP-2 (ghost-simplification.md §5.2).  The nineteen
     conjuncts are now [FsReady.fs_ready], a LEAF below this layer, and
     this is the derived form: the definition below is an alias, so the two
     friendly seals read exactly as before and every consumer of the name
     is unaffected.

     What moved with the predicate is what this file never had: a PRODUCER
     ([FsReady.fs_ready_establish] -- the boot chain's eighteen plus
     fsinit's returned [ireg_boot], in one [bupd]) and a PROJECTION FAMILY
     (each an [iDestruct], statable only inside [FsReady]'s own section --
     the class-used-as-index trap, see that file's header).  "A friendly
     client pays for the file system's world once, at boot" is, since
     SIMP-2, a lemma rather than an assumption. *)
  (* [fs_world] AT A CALLER'S OWN NAMES.  [FsReady.fs_ready] is now
     PARAMETER-FREE -- every ghost name it used to take is ambient, in
     [FsCfg.fscfg] and [IcacheRef.icfg] (see FsCfg.v's header for why a
     carried predicate must not be an existential).  The contracts below
     still THREAD their names, as every fs contract in the tree does, so
     what they want is the ambient predicate plus the equations saying the
     two agree -- [SpecKexec]'s [g = icfg_log] idiom, at the full width.
     True at boot by construction; the boot chain builds the [fscfg]
     instance out of exactly these names.

     [procs_inv] IS NO LONGER IN IT.  It is persistent, it is a PROCESS
     resource rather than a file-system one, and it was the only conjunct
     that reached back into the process layer.  The two bodies below take
     it as their own premise. *)
  (* THE THREE RING PAGES ARE A RESOURCE HERE, NOT AN EQUATION (R1).
     [fsc_desc]/[fsc_avail]/[fsc_used] left [FsCfg.fscfg] because
     [virtio_disk_init] [kalloc]s them at WP time, so there is no field left
     for [⌜pd = fsc_desc⌝] to name.  What replaces the three equations is the
     disk fabric SPELLED AT THE CALLER'S OWN [pd]/[pav]/[pu] -- which is what
     the equations bought in the first place, and it is the same trade every
     other row here makes, only one step earlier.

     IT IS A RE-SPELLING, NOT A STRENGTHENING.  [fs_ready] carries
     [∃ pd pav pu, disk_geom fsc_disk pd pav pu ∗ is_lock fsc_dlock ...], and
     [⌜γd = fsc_disk⌝] is still here, so a producer discharges the two new
     rows by unpacking that existential and instantiating this predicate's
     [pd]/[pav]/[pu] at the witness; conversely a consumer that wants the
     ambient form gets it back by [FsReady.disk_geom_agree].  The two forms
     are interderivable, [fs_world_all]'s statement is unchanged, and so is
     every contract below that takes [pd]/[pav]/[pu] as parameters. *)
  Definition fs_world (γpr γa : gname) (γs : list gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64) (bn : bio_names) (glog : log_names)
      (γfs : fs_names) (γi : gname) (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
      : iProp Σ :=
    (⌜γpr = fsc_printk⌝ ∗ ⌜γa = fsc_kalloc⌝ ∗
     ⌜γu = fsc_uart⌝ ∗ ⌜γd = fsc_disk⌝ ∗ ⌜γk = fsc_dlock⌝ ∗
     ⌜bn = fsc_bio⌝ ∗ ⌜glog = icfg_log⌝ ∗ ⌜γfs = fsc_fs⌝ ∗
     ⌜γi = fsc_ireg⌝ ∗ ⌜cn = fsc_ic⌝ ∗ ⌜gtl = fsc_itlock⌝ ∗
     ⌜cov = fsc_cov⌝ ∗ ⌜logstart = fsc_logst⌝ ∗ ⌜inodestart = icfg_ist⌝ ∗
     ⌜nib = icfg_nib⌝ ∗ ⌜dev = icfg_dev⌝ ∗
     disk_geom γd pd pav pu ∗
     is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) ∗
     FsReady.fs_ready)%I.

  Global Instance fs_world_persistent γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    Persistent (fs_world γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
                         cov logstart inodestart nib dev).
  Proof. rewrite /fs_world. apply _. Qed.

  (* THE UNPACK, at the caller's names.  This is what the [γs] parameter's
     departure and the ties buy: a body that threads its own names still
     destructs ONE row and gets the eighteen constituents spelled the way
     its callee spells them.  The substitution happens here, once, instead
     of in every consumer. *)
  Lemma fs_world_all γpr γa γs γu γd γk pd pav pu bn glog
      γfs γi cn gtl cov logstart inodestart nib dev :
    fs_world γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
             cov logstart inodestart nib dev -∗
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
    kalloc_env γa None ∗
    (* ...and the two rows SIMP-3 added to the predicate: the image's own
       arithmetic and the four superblock cells (FsReady.v §0, §0b).  They
       are at the AMBIENT names on purpose -- unlike the eighteen above,
       nothing here is re-spelled at the caller's, because [fs_geom_ok] is a
       statement about the [fscfg]/[icfg] instance itself and the cells are
       named by its fields.  A caller that threads its own names rewrites by
       the tie equations it just destructed. *)
    ⌜FsReady.fs_geom_ok⌝ ∗ FsReady.fs_sb_cells.
  Proof.
    rewrite /fs_world.
    (* SIXTEEN equations now, not nineteen, and the disk fabric arrives as
       two RESOURCES at the caller's own [pd]/[pav]/[pu] (R1).  So the two
       disk rows of the conclusion come from them rather than from
       [fs_ready], whose own disk conjunct is the existential this predicate
       replaced -- and it is dropped ([_] at slot 10). *)
    iIntros "(-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->
              & -> & -> & -> & #Hgeom & #Hdlock & Hw)".
    iDestruct (FsReady.fs_ready_all with "Hw") as
      "(H1 & H2 & H3 & %H4 & H5 & H6 & H7 & H8 & H9 & _ & H11 & H12 & H13
        & H14 & H15 & H16 & H17 & %H18 & #H19)".
    iFrame "H1 H2 H3 H5 H6 H7 H8 H9 Hgeom Hdlock H11 H12 H13 H14 H15 H16 H17
            H19".
    iFrame "%".
  Qed.

  (* the alias, as a lemma, so a reader need not take the [Definition]'s
     word for it: at the ambient names, [fs_world] IS [fs_ready] -- MODULO
     THE THREE RING PAGES, which are no longer ambient (R1).  That is the
     whole content of the change, and it is why this is now two one-way
     lemmas rather than one [⊣⊢]: the pages are universally quantified going
     down (any [pd] whose [disk_geom] you can show) and existentially coming
     back (the witness [fs_ready] already holds). *)
  Lemma fs_world_ready γs pd pav pu :
    fs_world fsc_printk fsc_kalloc γs fsc_uart fsc_disk fsc_dlock
             pd pav pu fsc_bio icfg_log fsc_fs fsc_ireg
             fsc_ic fsc_itlock fsc_cov fsc_logst icfg_ist icfg_nib icfg_dev
    ⊢ FsReady.fs_ready.
  Proof.
    rewrite /fs_world.
    by iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & _ & _ & _ & $)".
  Qed.

  Lemma fs_ready_world γs :
    FsReady.fs_ready ⊢
    ∃ pd pav pu, fs_world fsc_printk fsc_kalloc γs fsc_uart fsc_disk fsc_dlock
                   pd pav pu fsc_bio icfg_log fsc_fs fsc_ireg
                   fsc_ic fsc_itlock fsc_cov fsc_logst icfg_ist icfg_nib
                   icfg_dev.
  Proof.
    iIntros "#H".
    iDestruct (FsReady.fs_ready_disk with "H") as "[_ Hd]".
    iDestruct "Hd" as (pd pav pu) "[#Hg #Hl]".
    iExists pd, pav, pu. rewrite /fs_world.
    iFrame "Hg Hl H". by repeat iSplit.
  Qed.

  (* THE CONSUMABLES.  What actually crosses the call and comes back: the
     three block slots, the four superblock cells, the free-block ledger at
     [used], and the reference ledger at [ns].  Everything F3 has to
     ACCOUNT for is in here, which is why (S3) is a statement about this
     bundle's [ns] and nothing else. *)
  Definition fs_res (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart bmapstart inodestart ninodes size : Z)
      (used : gset Z) (ns : nat) (dqb dqs dqbs dqn : dfrac) : iProp Σ :=
    (bslots bn 3 ∗
     sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     sb_size ↦₄{dqbs} (mword_of_int size : mword 32) ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     bitmap_res γfs bmapstart cov logstart size used ∗
     iref_slots ns)%I.

End FsBundles.

(* ====================================================================== *)
(*  3.  sys_mkdir, FRIENDLY                                                *)
(* ====================================================================== *)

(*  [SpecSysMkdir.wp_sys_mkdir_sconf_body], REPACKAGED.  Five differences
    and no others:

      - the 26 pure premises become SIX: [fs_geom], the stack budget, the
        reference allowance, the two process-index facts and argstr's
        trapframe read.  (Nineteen went into the record; [eb = true] is
        discharged below, not assumed.)
      - the 19 ambient resources become ONE PERSISTENT [fs_world];
      - the 7 consumables become ONE [fs_res], in the pre and in the post;
      - [eb] is GONE as a parameter, fixed at the [true] the seal's own
        premise forces, and with it [trap_csrs_ext] / [cpu_claim_ext]
        vanish from both sides ([emp] at [true], IntrDefs.v:1068, :1737);
      - the post's four pure facts are hoisted in front of the resources,
        so a caller reads the answer before it reads the ledger.

    THE POST'S TREE CONTENT IS EMPTY, and (S1) is why.  What a friendly
    caller learns is: the call returned 0 or -1, its process block is back
    with (only) argstr's page-table growth folded in, and the ledgers moved
    by at most this much.  It learns NOTHING about the file system -- not
    that a directory was made on the 0 arm, not that none was made on the
    -1 arm.  Every syscall in sysfile.c is in the same position; see the
    file header. *)
Definition wp_sys_mkdir_friendly_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf γa γpr : gname)                                 (* ftable, kalloc, printk *)
    (γs : list gname) (j : nat) (γl : gname)             (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)     (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (glog : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                        (* the icache + itable *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (ninodes size : Z) (dev : mword 32)
    (used : gset Z) (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v : mword 64)                                       (* syscall argument 0 *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mkdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mkdir <= K)%nat ->
  fs_geom cov logstart bmapstart inodestart nib ninodes size dev glog ->
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 true pj b lks -∗
  pc_is pcE -∗
  fs_world γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
           cov logstart inodestart nib dev -∗
  (* [procs_inv] left [fs_ready] (FsCfg.v's header): a PROCESS resource,
     persistent, and every caller already holds it. *)
  procs_inv γs -∗
  fs_res bn γfs cov logstart bmapstart inodestart ninodes size used ns
         dqb dqs dqbs dqn -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z) (ns' : nat) (P' : uptd),
      ⌜sys_mkdir_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜((ns - create_slots)%nat <= ns')%nat /\ (ns' <= ns)%nat⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 true pj b lks -∗
      pc_is ret_tgt -∗
      fs_res bn γfs cov logstart bmapstart inodestart ninodes size used' ns'
             dqb dqs dqbs dqn -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE LIFTING.  A functor over the LANDED seal, F2's [FsLookupTree]
   pattern: [SpecSysMkdir] does not move, and the whole claim is that the
   packaging is available CALLER-SIDE. *)
Module FsSysMkdir (M : SYSMKDIR).

  Lemma wp_sys_mkdir_friendly
      `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf γa γpr : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (glog : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (used : gset Z) (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
      wp_sys_mkdir_friendly_body γf γa γpr γs j γl γu γd γk pd pav pu bn
                                 glog γfs γi cn gtl cov logstart bmapstart
                                 inodestart nib ninodes size dev used ns
                                 dqb dqs dqbs dqn v pid V m K b lks.
  Proof.
    unfold wp_sys_mkdir_friendly_body. cbv zeta.
    intros HK Hg Hns Hj Hgs Htf.
    destruct Hg as [Hdev Hnib Hlog Hist Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
                    Histnn Hcb Hbg Hib Hn1 Hn2 Hn3 Hus].
    iIntros "Hcg Hown Hpc Hw Hprocs Hres Hpriv Hcont".
    (* SIMP-2: the unpack is [FsReady]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       that file's two seals and the measurement behind them), so the
       nineteen conjuncts come out through the family, which is exactly what
       the family is for. *)
    (* SIMP-2: the unpack is [fs_world]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       FsReady.v's two seals and the measurement behind them), and it is now
       parameter-free, so the eighteen constituents come out through the
       family AT THIS BODY'S OWN NAMES -- which is what [fs_world_all]'s
       ties are for.  [procs_inv] is no longer among them; it arrives as its
       own premise. *)
    iDestruct (fs_world_all with "Hw") as
      "(Htext & Hdata & Hpr & %Hprg & Hbio & Hlogc &
        Hseam & Hgc & Hdev & Hdgeom & Hdlk & Hitb2 & Hitbl &
        Hesc & Hisl & Hireg & Hiopen & Hkenv & %Hgeo & #Hsbc)".
    iDestruct "Hres" as "(Hbsl & Hsbn & Hsbi & Hsbs & Hsbb & Hbm & Hir)".
    iApply (M.wp_sys_mkdir_sconf γf γa γpr γs j γl γu γd γk pd pav pu bn
              glog γfs γi cn gtl cov logstart bmapstart inodestart nib
              ninodes size dev used ns dqb dqs dqbs dqn v pid V m K true
              b lks
              HK Hdev Hnib Hlog Hist Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
              Histnn Hcb Hbg Hib Hn1 Hn2 Hn3 Hus Hprg Hns Hj Hgs
              eq_refl Htf
              with "Hcg Hown [] [] Htext Hdata Hpc Hpr Hbio Hlogc
                    Hseam Hgc Hdev Hdgeom Hdlk Hbsl Hitb2 Hitbl Hesc Hisl
                    Hireg Hiopen Hsbn Hsbi Hsbs Hsbb Hbm Hkenv Hprocs Hir
                    Hpriv").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDn) "%Hgd".
    iIntros (mf used' ns' P')
      "%Hcs %Hupt Hcg Hown _ _ Hpc Hbsl Hsbn Hsbi Hsbs Hsbb Hbm %Hns' Hir
       Hpriv %Hret".
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDn Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf used' ns' P'
              with "[%] [%] [%] [%] Hcg Hown Hpc
                    [Hbsl Hsbn Hsbi Hsbs Hsbb Hbm Hir] Hpriv").
    - exact Hret.
    - exact Hcs.
    - exact Hupt.
    - exact Hns'.
    - rewrite /fs_res. iFrame.
  Qed.

End FsSysMkdir.

(* ====================================================================== *)
(*  4.  sys_chdir, FRIENDLY -- AND COMPOSABLE                              *)
(* ====================================================================== *)

(*  The same packaging over [SpecSysChdir.wp_sys_chdir_sconf_body], and the
    contrast with mkdir is the point of building both:

    THE LEDGERS CLOSE.  [fs_res] goes in at [ns = 2] and comes back at
    [ns = 2] -- [SpecSysChdir.v]:259, :283, all four arms -- and the free
    block pool only SHRINKS ([used' ⊆ used], :280).  So a client's
    precondition is RE-ESTABLISHED by the call, up to [used'], and chdir can
    be called in a loop.  mkdir cannot (S3).  The friendly layer's first
    real distinction between two syscalls is a LEDGER fact, not a tree fact.

    THE TREE DELTA IS EMPTY -- BUT NOT FOR THE REASON THE F3 BRIEF EXPECTED.
    chdir was staged as "the NO-DELTA case: t' = t, a pure resolution plus a
    reference swap".  Two corrections, both from the landed text:

      (a) chdir's [iput(p->cwd)] can be the LAST reference to an unlinked
          inode, in which case it truncates and FREES it -- the seal's own
          [used' ⊆ used] is the visible half of that ([SpecSysChdir.v]:279
          names iput's truncate arm as the only mover).  The node store
          therefore CAN lose a node across a chdir.  What is untouched is
          the reachable tree: a freed inode has [nlink = 0] and no live
          record names it.  "t' = t" is a statement about the LIVE tree
          only, and stating it would need exactly the ambient tree (S2)
          says does not exist.
      (b) the interesting half of chdir's post -- "the new cwd is the node
          [path] resolves to" -- is UNSTATABLE, and R8 is why:
          [SpecNamex.v]:113-124 rules there is no path -> inode functional
          statement, because each dirlookup is atomic under its own lock and
          no stable global tree exists between iterations.  The seal says
          what it can: the process comes back at [upd_cwd V ipv] for an
          EXISTENTIAL [ipv] ([SpecSysChdir.v]:161-166).  That existential is
          not slack -- it is R8, at the syscall boundary.

    So chdir's friendly post is [sys_chdir_post] verbatim.  It is already
    the friendly shape: a two-armed disjunction over the process block, with
    nothing machine-level in it. *)
Definition wp_sys_chdir_friendly_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γf γa γpr : gname)
    (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (glog : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (ninodes size : Z) (dev : mword 32)
    (used : gset Z)
    (dqb dqs dqbs dqn : dfrac)
    (v : mword 64)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_chdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_chdir <= K)%nat ->
  fs_geom cov logstart bmapstart inodestart nib ninodes size dev glog ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 true pj b lks -∗
  pc_is pcE -∗
  fs_world γpr γa γs γu γd γk pd pav pu bn glog γfs γi cn gtl
           cov logstart inodestart nib dev -∗
  (* [procs_inv] left [fs_ready] (FsCfg.v's header): a PROCESS resource,
     persistent, and every caller already holds it. *)
  procs_inv γs -∗
  fs_res bn γfs cov logstart bmapstart inodestart ninodes size used 2
         dqb dqs dqbs dqn -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜used' ⊆ used⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 true pj b lks -∗
      pc_is ret_tgt -∗
      (* THE LEDGER IS RESTORED AT THE LITERAL 2 -- the composability half *)
      fs_res bn γfs cov logstart bmapstart inodestart ninodes size used' 2
             dqb dqs dqbs dqn -∗
      sys_chdir_post γf pj pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module FsSysChdir (M : SYSCHDIR).

  Lemma wp_sys_chdir_friendly
      `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf γa γpr : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (glog : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (ninodes size : Z) (dev : mword 32)
      (used : gset Z)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
      wp_sys_chdir_friendly_body γf γa γpr γs j γl γu γd γk pd pav pu bn
                                 glog γfs γi cn gtl cov logstart bmapstart
                                 inodestart nib ninodes size dev used
                                 dqb dqs dqbs dqn v pid V m K b lks.
  Proof.
    unfold wp_sys_chdir_friendly_body. cbv zeta.
    intros HK Hg Hj Hgs Htf.
    destruct Hg as [Hdev Hnib Hlog Hist Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
                    Histnn Hcb Hbg Hib Hn1 Hn2 Hn3 Hus].
    iIntros "Hcg Hown Hpc Hw Hprocs Hres Hpriv Hcont".
    (* SIMP-2: the unpack is [FsReady]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       that file's two seals and the measurement behind them), so the
       nineteen conjuncts come out through the family, which is exactly what
       the family is for. *)
    (* SIMP-2: the unpack is [fs_world]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       FsReady.v's two seals and the measurement behind them), and it is now
       parameter-free, so the eighteen constituents come out through the
       family AT THIS BODY'S OWN NAMES -- which is what [fs_world_all]'s
       ties are for.  [procs_inv] is no longer among them; it arrives as its
       own premise. *)
    iDestruct (fs_world_all with "Hw") as
      "(Htext & Hdata & Hpr & %Hprg & Hbio & Hlogc &
        Hseam & Hgc & Hdev & Hdgeom & Hdlk & Hitb2 & Hitbl &
        Hesc & Hisl & Hireg & Hiopen & Hkenv & %Hgeo & #Hsbc)".
    iDestruct "Hres" as "(Hbsl & Hsbn & Hsbi & Hsbs & Hsbb & Hbm & Hir)".
    iPoseProof (printk_env_panic with "Hpr") as "#Hpe".
    iApply (M.wp_sys_chdir_sconf γf γa γs j γl γu γd γk pd pav pu bn
              glog γfs γi cn gtl cov logstart bmapstart inodestart nib
              size dev used dqb dqs v pid V m K true b lks
              HK Hdev Hnib Hlog Hist Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
              Histnn Hcb Hib Hj Hgs eq_refl Htf
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlogc
                    Hseam Hgc Hdev Hdgeom Hdlk Hbsl Hitb2 Hitbl Hesc Hisl
                    Hireg Hiopen Hsbb Hsbi Hbm Hkenv Hprocs Hir Hpriv").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDn) "%Hgd".
    iIntros (mf used' P')
      "%Hcs %Hupt Hcg Hown _ _ Hpc Hbsl Hsbb Hsbi %Hsub Hbm Hir Hpost".
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDn Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf used' P'
              with "[%] [%] [%] Hcg Hown Hpc
                    [Hbsl Hsbn Hsbi Hsbs Hsbb Hbm Hir] Hpost").
    - exact Hcs.
    - exact Hupt.
    - exact Hsub.
    - rewrite /fs_res. iFrame.
  Qed.

End FsSysChdir.
