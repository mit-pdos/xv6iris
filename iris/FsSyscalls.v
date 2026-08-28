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
         cells, [bslots], the iref
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

    (S3) RETIRED -- THE PURE-RESOURCE TRIPLE USED NOT TO BE COMPOSABLE FOR
         mkdir.  The iref ledger came back as an INTERVAL
         ([ns - create_slots <= ns' <= ns]), inherited from create's own
         interval, and a friendly client that wanted to call mkdir TWICE
         could not re-establish its own precondition ([create_slots <= ns])
         from that.  This note said the tightening, if ever wanted, was
         create's post rather than sys_mkdir's, and that is exactly where it
         was done: [SpecCreate.v] states its figure EXACTLY now (every
         failure arm returns the ledger whole, every success arm keeps one
         out), so mkdir's and mknod's own posts say [ns' = ns] and both
         wrappers below are composable on the same footing as chdir's.

    ---- SO WHAT DOES LAND -----------------------------------------------

    The OTHER half of F3's charter, item (c): what is HIDDEN.  A syscall
    seal takes 26 pure premises and 31 resources; a client that wants to
    call two syscalls in a row has to re-thread all of it.  This file gives
    the syscall boundary a CALLING CONVENTION -- three bundles and two
    wrappers derived from the landed seals, which do not move:

      [FsReady.fs_geom_ok]  the pure geometry, as ONE PARAMETER-FREE
                  record about the ambient configuration.  Both syscalls
                  take the SAME one; chdir ignores five fields.  (This file
                  used to own a threaded copy called [fs_geom]; rank 1d
                  retired it -- there was nothing left to thread.)
      [FsReady.fs_ready]  the 19 ambient resources, as ONE assertion --
                  **and it is PERSISTENT**, which is the whole point.  A
                  client establishes the file system's world once and every
                  syscall is free of it forever after.  This is the honest
                  content of "the ambient is absorbed": not that the seals
                  hide it, but that all of it is duplicable and none of it
                  is spent.  (This file used to own a wrapper called
                  [fs_world]; rank 1d retired that too.)
      [fs_res]    the 6 consumable resources that go in and come back:
                  [bslots], the four superblock cells and the iref ledger.  THIS is the part a client must account for,
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
Require Import FsReady.   (* the file system's world, and its geometry *)
Import Defs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE PURE SIDE: THERE IS NO RECORD HERE ANY MORE                    *)
(* ====================================================================== *)

(*  [fs_geom] IS GONE (rank 1d).  It was the nineteen pure premises the two
    seals take between them, as one record parameterised by the numbers a
    syscall contract used to thread.  Every one of those numbers is a
    [FsCfg.fscfg] / [IcacheRef.icfg] field now -- [fsc_bmapstart],
    [fsc_size], [fsc_ninodes] were the last three -- so the record has no
    parameters left to take, and a parameter-free statement of the image's
    geometry already exists one layer down: [FsReady.fs_geom_ok], with
    [fgo_size] / [fgo_bm_nn] / [fgo_bm_cov] / [fgo_bm_out] as the accessors
    for [bitmap_geom_ok]'s four conjuncts.  The two friendly bodies below
    take THAT, and a client holding [FsReady.fs_ready] gets it for nothing
    ([FsReady.fs_ready_geom]).  *)

(* ====================================================================== *)
(*  2.  THE TWO RESOURCE BUNDLES                                           *)
(* ====================================================================== *)

Section FsBundles.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.
  (* the ambient fs names [FsReady.fs_ready] is stated at.  It rides in on
     [fileG] exactly as [icfg] does (see the note on [FileInvDefs.fileG]),
     so there is no binder here and no second instance path. *)

  (* THE AMBIENT IS [FsReady.fs_ready], AND THERE IS NO WRAPPER LEFT.

     [fs_world] IS GONE (rank 1d), and with it [fs_world_all],
     [fs_world_persistent], [fs_world_ready] and [fs_ready_world].  It was
     [fs_ready] plus the EQUATIONS saying a caller's own threaded names were
     the ambient ones -- nineteen of them once, eight after rank 1c (the six
     device/allocator gnames and the bitmap's two numbers).  Those eight
     names are [FsCfg.fscfg] fields now ([fsc_printk], [fsc_kalloc],
     [fsc_uart], [fsc_disk], [fsc_dlock], [fsc_bio], [fsc_bmapstart],
     [fsc_size]), so there is nothing left on either side of an equation:
     what remained of the definition was the parameter-free [fs_ready]
     itself, plus [fs_ready_disk]'s converse at a caller's three ring pages.

     A namer wants one of two things and both are one lemma away:
     [FsReady.fs_ready] as it stands, or -- if it threads its own
     [pd]/[pav]/[pu] -- [FsReady.fs_ready_disk] to unpack the witness and
     [FsReady.disk_geom_agree] to identify the two.  The three ring pages
     are the ONE thing here that is not ambient (FsCfg.v's ruling R1:
     [virtio_disk_init] [kalloc]s them at WP time), which is why they are
     the only reason the converse exists at all.

     [fs_world_all]'s twenty-one-step [iSplit] chain -- written because a
     single [iFrame] over a bundle of definition-valued rows cost 25 s of
     this file -- is [FsReady.fs_ready_all], where it always belonged. *)

  (* THE CONSUMABLES.  What actually crosses the call and comes back: the
     three block slots, the four superblock cells, and the reference ledger
     at [ns].  Everything F3 has to ACCOUNT for is in here, which is why
     (S3) is a statement about this bundle's [ns] and nothing else.  (The
     block bitmap is NOT a consumable: [BitmapInv.bitmap_inv] is a
     persistent conjunct of [fs_ready].)

     THE FOUR GEOMETRY PARAMETERS ARE GONE (rank 1d): the cells are named by
     [fsc_ninodes] / [icfg_ist] / [fsc_size] / [fsc_bmapstart], and [bn] was
     never read by this bundle at all -- it rode along because every other
     row of the calling convention took it. *)
  Definition fs_res (ns : nat) (dqb dqs dqbs dqn : dfrac) : iProp Σ :=
    (bslots 3 ∗
     sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) ∗
     sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) ∗
     iref_slots ns)%I.

End FsBundles.

(* ====================================================================== *)
(*  3.  sys_mkdir, FRIENDLY                                                *)
(* ====================================================================== *)

(*  [SpecSysMkdir.wp_sys_mkdir_sconf_body], REPACKAGED.  Five differences
    and no others:

      - the 26 pure premises become SIX: [FsReady.fs_geom_ok], the stack
        budget, the reference allowance, the two process-index facts and
        argstr's trapframe read.  (Fifteen are the image's own geometry and
        live on the ambient record; [eb = true] is discharged below, not
        assumed.)
      - the 19 ambient resources become ONE PERSISTENT [FsReady.fs_ready];
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
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)                                         (* the file table *)
    (γs : list gname) (j : nat) (γl : gname)             (* the running process *)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v : mword 64)                                       (* syscall argument 0 *)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_mkdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_mkdir <= K)%nat ->
  FsReady.fs_geom_ok ->
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 true pj b lks -∗
  pc_is pcE -∗
  (* THE FILE SYSTEM'S WORLD, AS IT IS: one persistent, parameter-free
     predicate.  [fs_world] used to sit here and it was this plus eight
     equations tying a caller's threaded device/allocator names to the
     ambient ones; the names are [FsCfg.fscfg] fields now (rank 1d).  The
     three virtio ring pages are quantified INSIDE it, which is why this
     body no longer takes [pd]/[pav]/[pu] either: the proof unpacks them
     out of [FsReady.fs_ready_disk] and hands the witness to the seal. *)
  FsReady.fs_ready -∗
  (* [procs_inv] left [fs_ready] (FsCfg.v's header): a PROCESS resource,
     persistent, and every caller already holds it. *)
  procs_inv γs -∗
  fs_res ns dqb dqs dqbs dqn -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜sys_mkdir_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      ⌜ns' = ns⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 true pj b lks -∗
      pc_is ret_tgt -∗
      fs_res ns' dqb dqs dqbs dqn -∗
      proc_priv γf pj pid (upd_upt V P') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE LIFTING.  A functor over the LANDED seal, F2's [FsLookupTree]
   pattern: [SpecSysMkdir] does not move, and the whole claim is that the
   packaging is available CALLER-SIDE. *)
Module FsSysMkdir (M : SYSMKDIR).

  Lemma wp_sys_mkdir_friendly
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
      wp_sys_mkdir_friendly_body γf γs j γl ns
                                 dqb dqs dqbs dqn v pid V m K b lks.
  Proof.
    unfold wp_sys_mkdir_friendly_body. cbv zeta.
    intros HK Hg Hns Hj Hgs Htf.
    (* [FsReady.fs_geom_ok] has ELEVEN fields where [fs_geom] had fifteen:
       [bitmap_geom_ok]'s four conjuncts are reached through [fgo_bmgeom]'s
       accessors rather than restated, so nothing here is a hedged copy of
       anything else (FsReady.v §0). *)
    pose proof (FsReady.fgo_rootdev  Hg) as Hroot.
    pose proof (FsReady.fgo_nib_pos  Hg) as Hnibp.
    pose proof (FsReady.fgo_loggeom  Hg) as Hlg.
    pose proof (FsReady.fgo_size     Hg) as Hsz.
    pose proof (FsReady.fgo_bm_nn    Hg) as Hbnn.
    pose proof (FsReady.fgo_bm_cov   Hg) as Hbcov.
    pose proof (FsReady.fgo_bm_out   Hg) as Hbout.
    pose proof (FsReady.fgo_ist_nn   Hg) as Histnn.
    pose proof (FsReady.fgo_covbelow Hg) as Hcb.
    pose proof (FsReady.fgo_bmgeom   Hg) as Hbg.
    pose proof (FsReady.fgo_iblocks  Hg) as Hib.
    pose proof (FsReady.fgo_nin_lo   Hg) as Hn1.
    pose proof (FsReady.fgo_nin_hi   Hg) as Hn2.
    pose proof (FsReady.fgo_nin_31   Hg) as Hn3.
    pose proof (FsReady.fgo_ushort   Hg) as Hus.
    iIntros "Hcg Hown Hpc #Hw Hprocs Hres Hpriv Hcont".
    (* SIMP-2: the unpack is [FsReady]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       that file's two seals and the measurement behind them), so the
       nineteen conjuncts come out through the family, which is exactly what
       the family is for.  Since rank 1d there is no [fs_world_all] in
       between: the family is applied to the predicate the caller handed in,
       at the AMBIENT names, which are the names the seal below reads too.
       The three ring pages are the one thing still quantified, so they are
       unpacked here and the seal is instantiated at the witness. *)
    iDestruct (FsReady.fs_ready_all with "Hw") as
      "(Htext & Hdata & Hpr & %Hprg & Hbio & Hlogc &
        Hseam & Hgc & Hdev & Hdisk & Hitb2 & Hitbl &
        Hesc & Hisl & Hireg & Hiopen & Hkenv & %Hgeo & #Hsbc & #Hbmi)".
    iDestruct "Hdisk" as (pd pav pu) "[#Hdgeom #Hdlk]".
    iDestruct "Hres" as "(Hbsl & Hsbn & Hsbi & Hsbs & Hsbb & Hir)".
    iApply (M.wp_sys_mkdir_sconf γf γs j γl
 pd pav pu

 ns dqb dqs dqbs dqn v pid V m K true
              b lks
              HK Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
              Histnn Hcb Hbg Hib Hn1 Hn2 Hn3 Hus Hprg Hns Hj Hgs
              eq_refl Htf
              with "Hcg Hown [] [] Htext Hdata Hpc Hpr Hbio Hlogc
                    Hseam Hgc Hdev Hdgeom Hdlk Hbsl Hitb2 Hitbl Hesc Hisl
                    Hireg Hiopen Hsbn Hsbi Hsbs Hsbb Hbmi Hkenv Hprocs Hir
                    Hpriv").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDn) "%Hgd".
    iIntros (mf ns' P')
      "%Hcs %Hupt Hcg Hown _ _ Hpc Hbsl Hsbn Hsbi Hsbs Hsbb %Hns' Hir
       Hpriv %Hret".
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDn Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf ns' P'
              with "[%] [%] [%] [%] Hcg Hown Hpc
                    [Hbsl Hsbn Hsbi Hsbs Hsbb Hir] Hpriv").
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
    [ns = 2], all four arms.  So a client's precondition is RE-ESTABLISHED
    by the call EXACTLY -- the free pool says nothing at all now that it
    lives in [bitmap_inv] -- and chdir can be called in a loop.  mkdir
    cannot (S3).  The friendly layer's first real distinction between two
    syscalls is a LEDGER fact, not a tree fact.

    THE TREE DELTA IS EMPTY -- BUT NOT FOR THE REASON THE F3 BRIEF EXPECTED.
    chdir was staged as "the NO-DELTA case: t' = t, a pure resolution plus a
    reference swap".  Two corrections, both from the landed text:

      (a) chdir's [iput(p->cwd)] can be the LAST reference to an unlinked
          inode, in which case it truncates and FREES it -- iput's truncate
          arm is the one mover, and since the free pool moved inside
          [BitmapInv.bitmap_inv] it is no longer visible in the seal at all.
          The node store therefore CAN lose a node across a chdir.  What is untouched is
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
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname)
    (γs : list gname) (j : nat) (γl : gname)
    (dqb dqs dqbs dqn : dfrac)
    (v : mword 64)
    (pid : mword 32) (V : pprivate)
    (m : regfile) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_chdir in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_chdir <= K)%nat ->
  FsReady.fs_geom_ok ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  pv_tf V !! tf_arg_idx 0 = Some v ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 true pj b lks -∗
  pc_is pcE -∗
  (* the file system's world, parameter-free -- see the mkdir body above for
     what [fs_world] used to add to it and why nothing is left of that. *)
  FsReady.fs_ready -∗
  (* [procs_inv] left [fs_ready] (FsCfg.v's header): a PROCESS resource,
     persistent, and every caller already holds it. *)
  procs_inv γs -∗
  fs_res 2 dqb dqs dqbs dqn -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 true pj b lks -∗
      pc_is ret_tgt -∗
      (* THE LEDGER IS RESTORED AT THE LITERAL 2 -- the composability half *)
      fs_res 2 dqb dqs dqbs dqn -∗
      sys_chdir_post γf pj pid (upd_upt V P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module FsSysChdir (M : SYSCHDIR).

  Lemma wp_sys_chdir_friendly
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname)
      (γs : list gname) (j : nat) (γl : gname)
      (dqb dqs dqbs dqn : dfrac)
      (v : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (b : bool) (lks : gset string) :
      wp_sys_chdir_friendly_body γf γs j γl
                                 dqb dqs dqbs dqn v pid V m K b lks.
  Proof.
    unfold wp_sys_chdir_friendly_body. cbv zeta.
    intros HK Hg Hj Hgs Htf.
    pose proof (FsReady.fgo_rootdev  Hg) as Hroot.
    pose proof (FsReady.fgo_nib_pos  Hg) as Hnibp.
    pose proof (FsReady.fgo_loggeom  Hg) as Hlg.
    pose proof (FsReady.fgo_size     Hg) as Hsz.
    pose proof (FsReady.fgo_bm_nn    Hg) as Hbnn.
    pose proof (FsReady.fgo_bm_cov   Hg) as Hbcov.
    pose proof (FsReady.fgo_bm_out   Hg) as Hbout.
    pose proof (FsReady.fgo_ist_nn   Hg) as Histnn.
    pose proof (FsReady.fgo_covbelow Hg) as Hcb.
    pose proof (FsReady.fgo_iblocks  Hg) as Hib.
    iIntros "Hcg Hown Hpc #Hw Hprocs Hres Hpriv Hcont".
    (* SIMP-2: the unpack is [FsReady]'s own projection rather than a raw
       [iDestruct].  It has to be: [fs_ready] is [Typeclasses Opaque] (see
       that file's two seals and the measurement behind them), so the
       nineteen conjuncts come out through the family, which is exactly what
       the family is for.  Since rank 1d nothing sits between the caller's
       predicate and this unpack: the names the family hands over ARE the
       names the seal below reads.  The three ring pages are the one thing
       still quantified, so they are unpacked here. *)
    iDestruct (FsReady.fs_ready_all with "Hw") as
      "(Htext & Hdata & Hpr & %Hprg & Hbio & Hlogc &
        Hseam & Hgc & Hdev & Hdisk & Hitb2 & Hitbl &
        Hesc & Hisl & Hireg & Hiopen & Hkenv & %Hgeo & #Hsbc & #Hbmi)".
    iDestruct "Hdisk" as (pd pav pu) "[#Hdgeom #Hdlk]".
    iDestruct "Hres" as "(Hbsl & Hsbn & Hsbi & Hsbs & Hsbb & Hir)".
    iPoseProof (printk_env_panic with "Hpr") as "#Hpe".
    iApply (M.wp_sys_chdir_sconf γf γs j γl
 pd pav pu

 dqb dqs v pid V m K true b lks
              HK Hroot Hnibp Hlg Hsz Hbnn Hbcov Hbout
              Histnn Hcb Hib Hj Hgs eq_refl Htf
              with "Hcg Hown [] [] Htext Hdata Hpc Hpe Hbio Hlogc
                    Hseam Hgc Hdev Hdgeom Hdlk Hbsl Hitb2 Hitbl Hesc Hisl
                    Hireg Hiopen Hsbb Hsbi Hbmi Hkenv Hprocs Hir Hpriv").
    { rewrite /trap_csrs_ext. done. }
    { rewrite /cpu_claim_ext. done. }
    iIntros (CIDn) "%Hgd".
    iIntros (mf P')
      "%Hcs %Hupt Hcg Hown _ _ Hpc Hbsl Hsbb Hsbi Hir Hpost".
    iDestruct (wp_next_at (CID0 := CID) true (proc_addr j) _ CIDn Hgd
                 with "Hcont") as "Hcont".
    iApply ("Hcont" $! mf P'
              with "[%] [%] Hcg Hown Hpc
                    [Hbsl Hsbn Hsbi Hsbs Hsbb Hir] Hpost").
    - exact Hcs.
    - exact Hupt.
    - rewrite /fs_res. iFrame.
  Qed.

End FsSysChdir.
