(* SpecFsinit.v -- the public interface of fsinit, stated independently of
   its proof, AND THE HOME OF THE FILE SYSTEM'S BOOT GEOMETRY.

     void fsinit(int dev) {
       struct buf *bp;

       bp = bread(dev, 1);                 // readsb(dev, &sb), INLINED
       memmove(&sb, bp->data, sizeof(sb));
       brelse(bp);

       if(sb.magic != FSMAGIC)
         panic("invalid file system");
       initlog(dev, &sb);
       ireclaim(dev);
     }

   112 bytes, a FOUR-slot frame ([c.addi sp,sp,-32] at +0x00, a plain
   [c.addi] -- so [stk_push_32] / [stk_pop_32] / [stk_fp_32], not the
   [c.addi16sp] family every deeper fs function uses).  [s2 = dev],
   [s1 = bp].  readsb is INLINED: there is no [jal readsb], only the
   bread / memmove / brelse triple at +0x10 / +0x26 / +0x2c.

   ==== WHY THIS FILE IS DIFFERENT FROM EVERY OTHER Spec IN THE TREE ====

   THE [memmove] AT +0x26 IS WHERE EVERY SUPERBLOCK CELL IS BORN.

   Thirteen contracts in this tree take a superblock field as a premise --
   [BitmapInv.sb_size], [BitmapInv.sb_bmapstart], [InodeInv.sb_ninodes],
   [InodeInv.sb_inodestart], and the [sb + 20] logstart cell SpecInitlog
   names inline -- always in the same shape: a plain fractional cell, read,
   never written, handed straight back.  NONE of them says where the cell
   came from or why its VALUE is any particular number.  There is
   deliberately no superblock abstraction anywhere below this file
   (BitmapInv.v and InodeInv.v both say so out loud).

   This is the function that answers both questions at once.  Before +0x26,
   [&sb] is 32 bytes of .bss -- raw, untyped, uninitialised.  After it, the
   eight words are there, and their VALUES are the mkfs image's block 1.  So
   this contract is the only place in the tree where a fact about the
   superblock can be stated as a fact about anything at all, and that is why
   the whole campaign has been parking its geometry IOUs here since N4b.

   ---- THE IOUs, NOW PAID -- OR RATHER, NOW STATED SOMEWHERE REAL ------

   Every one of these was flagged "owed to SpecFsinit" by an earlier stage
   and none of them could be stated before this file existed:

   - [1 < ninodes]                   (N5c, SpecIalloc / SpecIreclaim: kills
                                      the empty-region early return)
   - [ninodes <= 16 * Z.of_nat nib]  (N5c's NEW premise -- nothing anywhere
                                      in the tree tied sb.ninodes to the
                                      inode region's block count)
   - [ninodes < 2 ^ 31]              (makes the scan's [lw]/[bgeu] numeric)
   - [icfg_dev = ROOTDEV]            (N4b/N4d, namex's absolute arm)
   - [(0 < icfg_nib)%nat]            (N4b/N4d, iget's region bound)

   They are stated here as premises ABOUT THE IMAGE'S BLOCK 1 -- see
   [sb_image] below -- and they are THREADED, not discharged.  That is the
   honest shape and it is deliberate: they are claims about what mkfs wrote,
   so they belong to the same image-well-formedness family as
   [IcacheBoot.ipool_alloc]'s allocated-inum bundles, [InodeLock.inode_ok]
   and [DirView.dir_ok].  The boot client supplies them; no function proof
   can, and an axiom would be a lie.  What this file BUYS is that from here
   up they are premises about a named 32-byte record instead of five
   free-floating unexplained hypotheses on five different contracts.

   ---- THE FOUR-LINE DEVICE TIE, IN SpecNamex's EXACT SHAPE -----------

   N5a's ledger settled where these go and it is here, not in IcacheBoot:
   [icache_boot] is device-generic BY CONSTRUCTION (it takes [dv] and [nib]
   as parameters), and the [dv = icfg_dev] tie is [IcacheRef.icfg_alloc]'s to
   make.  So this contract carries SpecNamex's four lines verbatim --
   [dev = icfg_dev], [nib = icfg_nib], [dev = ROOTDEV], [(0 < nib)%nat] --
   and hands ireclaim the raw device-generic form it wants.

   [ROOTDEV] itself was hoisted out of [SpecNamex.v] into [InodeInv.v] (N5d,
   beside [sb_ninodes]) precisely so that this file could name it: a Spec
   file must not require another function's Spec.  SpecNamex keeps
   unqualified abbreviations, so nothing there moved.

   ---- THE MAGIC TEST IS A LIVE ARM, AND IT IS AN IMAGE PREMISE --------

   [bne a4,a5] at +0x40 compares [sb.magic] against [FSMAGIC = 0x10203040]
   ([lui a5,0x10203 / addi a5,a5,64] at +0x38/+0x3c) and jumps to
   [jal panic] at +0x6c.  Unlike balloc's and ialloc's out-of-space arms --
   which this kernel turned into [printk] and which are therefore LIVE
   BEHAVIOUR -- this one really is a panic, so a contract that promises to
   RETURN has to refute it.  [sb_magic (sb_image ...) = FSMAGIC] is what
   does, and it is an image premise of exactly the same kind as the rest:
   mkfs writes the magic.  The panic credentials still ride, because the
   callees have their own panic arms.

   ---- ONE SLOT MORE THAN initlog GIVES BACK (a real composition fact) --

   [SpecInitlog] takes [bslots bn ((LOGBLOCKS + 2) + 2)] = 34 and returns
   only TWO: the other 32 are sealed into [log_batch]'s pool inside the log
   spinlock, forever.  But [SpecIreclaim] needs THREE (iput's indirect arm,
   [iput_units]).  So fsinit cannot simply pass initlog's leftovers on, and
   it enters with [((LOGBLOCKS + 2) + 2 + 1)] = 35: one is held back across
   the [jal initlog] at +0x4e and rejoins initlog's two to make ireclaim's
   three.  fsinit's own bread at +0x10 borrows and returns one before any of
   that.  The postcondition therefore hands the caller [bslots bn 3], not
   [bslots bn 2].

   ---- WHAT COMPOSES, AND IN WHICH ORDER ------------------------------

   fsinit threads two PROVEN contracts and one of this stage's own:
   [SpecInitlog.wp_initlog_sconf] (whose whole struct-log bundle, era mirror
   and FsBlocks material ride straight through untouched) and
   [SpecIreclaim.wp_ireclaim_sconf].  Note the ORDER is load-bearing:
   initlog is what PRODUCES [log_ctx icfg_log bn γfs cov logstart dev], and
   ireclaim CONSUMES it (begin_op / end_op / iput).  So the log context does
   not cross this contract's boundary as an input at all -- it is born at
   +0x4e and handed to the caller at the end.

   ---- THE LOG'S GNAMES ARE [icfg_log]'s, NOT AN EXISTENTIAL -----------

   [initlog] is now an [_at] form (claude-notes/projects/fs-cfg-boot.md
   staging step 1): it FILLS a [log_names] it is handed instead of minting
   one, so what crosses this boundary in is [LogDefs.log_free_tok] -- the
   era fupd's receipt for the four gnames -- and what crosses out is
   [log_ctx] AT THOSE NAMES.  Here they are BAKED at [icfg_log], the
   configuration record's own field, for one reason: this contract's post is
   what the seal site turns into [FsReady.fs_ready], whose log conjunct is
   spelled [log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev].  An
   existential [∃ γ] could never be shown equal to the ambient field
   (fs-ghost-state.md §7d, and IcacheRef.v's own §G.14/§G.16 note that a tie
   carried in a body existential admits no agreement with a consumer's γ).
   [wp_initlog_sconf] itself stays general in γ; the baking happens exactly
   here, one level below the seal.  The boot kit is what delivers
   [log_free_tok icfg_log] to forkret's first arm ([FirstTok.first_tok]'s
   widened left disjunct, fs-cfg-boot.md "Transport").

   fsinit is single-threaded boot context, it SLEEPS (bread, and everything
   under initlog and ireclaim), so it threads the full running-process bundle
   and takes the parking premise.  It enters and returns at noff 0.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import BlockWords.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* fsinit's own frame is 32 bytes (4 slots) -- [c.addi sp,sp,-32] at +0x00,
   with ra/s0/s1/s2 pushed at 24/16/8/0.  Its deepest callee is ireclaim
   (68); initlog wants 56, bread 40, brelse 26, memmove 2. *)
Notation K_fsinit := (88%nat) (only parsing).
(* ===================================================================== *)
(*  THE SUPERBLOCK: ITS EIGHT CELLS, ITS 32 BYTES, AND ITS MAGIC          *)
(*                                                                        *)
(*  This is the ONLY superblock abstraction in the tree, and it exists    *)
(*  only because fsinit is the only function that touches the record as   *)
(*  a whole -- [li a2,32] at +0x16 is [sizeof(struct superblock)] and the *)
(*  [memmove] at +0x26 writes all 32 bytes at once.  Every other contract *)
(*  keeps taking its one field as a bare fractional cell; nothing below   *)
(*  this file changes.                                                    *)
(* ===================================================================== *)

(* fs.h's layout, as eight 32-bit fields.  The four that already have names
   elsewhere ARE these addresses: [BitmapInv.sb_size] is [sb + 4],
   [InodeInv.sb_ninodes] is [sb + 12], [InodeInv.sb_inodestart] is [sb + 24]
   and [BitmapInv.sb_bmapstart] is [sb + 28].  The other four are named here
   because fsinit is what brings them into existence. *)
Definition sb_base : mword 64 := mword_of_int KernelSyms.sb.
Definition sb_magic    : mword 64 := pa_add sb_base 0.
Definition sb_nblocks  : mword 64 := pa_add sb_base 8.
Definition sb_nlog     : mword 64 := pa_add sb_base 16.
Definition sb_logstart : mword 64 := pa_add sb_base 20.

Lemma sb_size_addr      : BitmapInv.sb_size      = pa_add sb_base 4.
Proof. reflexivity. Qed.
Lemma sb_ninodes_addr   : InodeInv.sb_ninodes    = pa_add sb_base 12.
Proof. reflexivity. Qed.
Lemma sb_inodestart_addr : InodeInv.sb_inodestart = pa_add sb_base 24.
Proof. reflexivity. Qed.
Lemma sb_bmapstart_addr : BitmapInv.sb_bmapstart = pa_add sb_base 28.
Proof. reflexivity. Qed.

(* [lui a5,0x10203 / addi a5,a5,64] at +0x38/+0x3c *)
Definition FSMAGIC : Z := 0x10203040.

(* THE IMAGE'S BLOCK 1, as the 32 bytes the memmove reads.  Stated with
   [BlockWords.word_bytes] rather than an inverse decode so that the premise
   below is an EQUATION ON BYTES the proof can rewrite with, not a
   proposition it has to invert. *)
Definition sb_image (magic fssize nblocks ninodes
                     nlog logstart inodestart bmapstart : mword 32)
    : list (bv 8) :=
  word_bytes magic ++ word_bytes fssize ++
  word_bytes nblocks ++ word_bytes ninodes ++
  word_bytes nlog ++ word_bytes logstart ++
  word_bytes inodestart ++ word_bytes bmapstart.

Lemma sb_image_length (magic fssize nblocks ninodes
                       nlog logstart inodestart bmapstart : mword 32) :
  length (sb_image magic fssize nblocks ninodes
                   nlog logstart inodestart bmapstart) = 32%nat.
Proof.
  rewrite /sb_image !length_app !word_bytes_length. reflexivity.
Qed.

Definition wp_fsinit_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γpr : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z)
    (ninodes : Z) (nib : nat) (size : Z)
    (used : gset Z)
    (dev : mword 32)
    (* ---- the image's block 1, field by field ---- *)
    (v_magic v_size v_nblocks v_ninodes v_nlog
     v_logstart v_inodestart v_bmapstart : mword 32)
    (bs_sb : list (bv 8))
    (sb_old : nat -> bv 8)                     (* the .bss bytes memmove kills *)
    (* ---- initlog's own bundle, threaded verbatim ---- *)
    (bs_hdr : list (bv 8))
    (L : gmap Z (list (bv 8))) (D : gmap Z bool)
    (vlock : mword 32) (vname vcpu : mword 64)
    (v_start v_dev v_nc v_n : mword 32)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fsinit in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_fsinit <= K)%nat ->
  (* ---- bread's / the log's block-number arithmetic ---- *)
  log_geom_ok cov logstart ->
  (* THE SUPERBLOCK'S OWN BLOCK: block 1, covered, and not log storage *)
  (1 : Z) ∈ cov ->
  ~ ((1 : Z) ∈ log_region_set logstart) ->
  (* ================================================================== *)
  (*  THE IMAGE PREMISES.  Everything below is a claim about what mkfs   *)
  (*  wrote into block 1, threaded from the boot client exactly as       *)
  (*  IcacheBoot's allocated-inum bundles are.  This is the family the   *)
  (*  N4b / N4d / N5a / N5c ledgers have been parking here.              *)
  (* ================================================================== *)
  (* (a) the block IS a superblock: its first 32 bytes are the eight
         fields, in fs.h's order *)
  take 32 bs_sb = sb_image v_magic v_size v_nblocks v_ninodes
                           v_nlog v_logstart v_inodestart v_bmapstart ->
  (* (b) the magic, which is what refutes the LIVE panic arm at +0x40 *)
  bv_unsigned v_magic = FSMAGIC ->
  (* (c) the three field values every fs contract downstream reads *)
  v_ninodes = (mword_of_int ninodes : mword 32) ->
  v_inodestart = (mword_of_int inodestart : mword 32) ->
  v_bmapstart = (mword_of_int bmapstart : mword 32) ->
  v_logstart = (mword_of_int logstart : mword 32) ->
  (* (d) THE THREE ninodes TIES -- SpecIalloc's and SpecIreclaim's, finally
         stated about a real record.  [ninodes <= 16 * nib] is the one that
         existed nowhere in the tree before (N5c). *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  (* (e) THE FOUR-LINE DEVICE TIE, SpecNamex's shape verbatim.  [ROOTDEV] is
         [InodeInv.ROOTDEV] since the N5d hoist. *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  (* (f) the inode region's block geometry, and itrunc's, threaded to
         ireclaim *)
  0 <= inodestart ->
  ireg_blocks_ok inodestart nib cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  cov_below cov size ->
  (* (g) initlog's STAGE-2 CLEAN-IMAGE precondition: the on-disk log header
         says n = 0, so read_head's copy loop and install_trans's recovery
         pass are both dead.  Real recovery is stage 4. *)
  hdr_n bs_hdr = 0 ->
  (* ---- ireclaim's printk, as a hypothesis and not a functor ---- *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dev *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (sign_extend' 64 dev : mword 64) ->
  (* PARKING PREMISE -- bread sleeps, and so does everything under
     initlog and ireclaim *)
  eb = true ->
  (* fsinit's cone: its own bread/brelse ("bcache", 4), initlog
     ("bcache", 4) and ireclaim ("itable", 2) -- "itable" is the lowest,
     so one premise there covers the whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  (* initlog's crash seam, era certificate and era mirror variable *)
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  log_mirror_full -∗
  (* THE LOG'S FOUR GNAMES, AT THEIR GENESIS VALUES, AND THEY ARE
     [icfg_log]'s.  Threaded straight into [initlog] at +0x4e, which fills
     them rather than minting its own.  See the header: this is the
     conjunct that makes fsinit's post assemble into [FsReady.fs_ready]. *)
  log_free_tok icfg_log -∗
  (* ================================================================== *)
  (*  THE SUPERBLOCK, BEFORE AND AFTER                                   *)
  (* ================================================================== *)
  (* IN: block 1's client half, which is what pins the bytes bread returns
     to the image; and 32 bytes of RAW .bss at [&sb], which is all the
     superblock is until +0x26 runs. *)
  fsblock γfs 1 bs_sb -∗
  ([∗ list] i ∈ seq 0 32, pa_add sb_base i ↦ₘ sb_old i) -∗
  (* ---- the icache's four persistent things, straight from
         [IcacheBoot.icache_boot] ---- *)
  ireg_inv γi γfs inodestart nib -∗
  (* THE BOOT-SHELTER TOKEN (fs-fragments.md §7.12), from [icfg_alloc] through
     the boot chain: fsinit frames it across bread/memmove/initlog and hands it
     to ireclaim, which is the only reason it is safe there (§7.1.7).  Returned
     in the post, so the boot caller can seal it to [ireg_open] after fsinit
     returns and before [kexec("/init")] -- that seal is OWED to forkret's
     first branch. *)
  ireg_boot -∗
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  ic_sleeplocks cn -∗
  (* itrunc's bitmap, through ireclaim's iput *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* ---- initlog's RAW struct log cells, threaded straight through ---- *)
  log_addr ↦₄ vlock -∗
  lock_name_field log_addr ↦₈ vname -∗
  lock_cpu log_addr ↦₈ vcpu -∗
  l_start ↦₄ v_start -∗
  l_dev ↦₄ v_dev -∗
  l_out ↦₄ (mword_of_int 0 : mword 32) -∗
  l_cmt ↦₄ (mword_of_int 0 : mword 32) -∗
  l_ncommit ↦₄ v_nc -∗
  lh_n_pa ↦₄ v_n -∗
  ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ w : mword 32, lh_block i ↦₄ w) -∗
  (* ---- initlog's FsBlocks material ---- *)
  ghost_map_auth (fs_L γfs) 1 L -∗
  ghost_map_auth (fs_dirty γfs) 1 D -∗
  ([∗ set] z ∈ cov, z ↪[fs_dirty γfs]{#(1/2)} false) -∗
  fsblock γfs (log_hdr_bno logstart) bs_hdr -∗
  ([∗ list] i ∈ seq 0 LOGBLOCKS,
     ∃ bs : list (bv 8), fsblock γfs (log_slot_bno logstart i) bs) -∗
  (* the caller's own pid cell *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle and the disk fabric *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THIRTY-FIVE slot units.  initlog seals 32 of them into [log_batch]'s
     pool and returns two; ireclaim needs three; so ONE is held back across
     the [jal initlog] at +0x4e.  See the header. *)
  bslots bn ((LOGBLOCKS + 2) + 2 + 1)%nat -∗
  (* ONE ledger unit for ireclaim's iget/iput pair; it comes back *)
  iref_slot -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* ================================================================ *)
      (*  THE EIGHT CELLS ARE BORN.  This is the whole point of the        *)
      (*  contract: the caller handed in 32 raw .bss bytes and gets back   *)
      (*  the typed fields every other fs contract in the tree takes as a  *)
      (*  premise, at the image's values.  [sb_size], [sb_ninodes],        *)
      (*  [sb_inodestart] and [sb_bmapstart] are literally the same        *)
      (*  addresses BitmapInv.v and InodeInv.v already name.               *)
      (* ================================================================ *)
      sb_magic ↦₄ v_magic -∗
      BitmapInv.sb_size ↦₄ v_size -∗
      sb_nblocks ↦₄ v_nblocks -∗
      InodeInv.sb_ninodes ↦₄ (mword_of_int ninodes : mword 32) -∗
      sb_nlog ↦₄ v_nlog -∗
      sb_logstart ↦₄ (mword_of_int logstart : mword 32) -∗
      InodeInv.sb_inodestart ↦₄ (mword_of_int inodestart : mword 32) -∗
      BitmapInv.sb_bmapstart ↦₄ (mword_of_int bmapstart : mword 32) -∗
      (* block 1's client half, untouched -- bread/brelse do not write it *)
      fsblock γfs 1 bs_sb -∗
      (* THE LOG LAYER, BUILT by initlog at +0x4e and already USED by
         ireclaim at +0x54.  It does not cross the boundary as an input.
         AT [icfg_log], not existentially: this is [FsReady.fs_ready]'s log
         conjunct, modulo the seal site's instantiation of [bn]/[γfs]/[cov]/
         [logstart] at [fsc_bio]/[fsc_fs]/[fsc_cov]/[fsc_logst] and
         [dev = icfg_dev], which premise (e) above already gives. *)
      log_ctx icfg_log bn γfs cov logstart dev -∗
      (* three, not two: see the header *)
      bslots bn 3 -∗
      iref_slot -∗
      (* the bitmap, with every orphan's blocks freed *)
      ⌜used' ⊆ used⌝ -∗
      bitmap_res γfs bmapstart cov logstart size used' -∗
      (* the boot-shelter token, handed back for the seal (fs-fragments.md
         §7.12) *)
      ireg_boot -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FSINIT.
  Parameter wp_fsinit_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ,
             ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (ninodes : Z) (nib : nat) (size : Z)
      (used : gset Z)
      (dev : mword 32)
      (v_magic v_size v_nblocks v_ninodes v_nlog
       v_logstart v_inodestart v_bmapstart : mword 32)
      (bs_sb : list (bv 8))
      (sb_old : nat -> bv 8)
      (bs_hdr : list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (vlock : mword 32) (vname vcpu : mword 64)
      (v_start v_dev v_nc v_n : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_fsinit_sconf_body γs j γl γu γd γk pd pav pu bn γfs γi cn gtl γpr
                           cov logstart bmapstart inodestart ninodes nib size
                           used dev
                           v_magic v_size v_nblocks v_ninodes v_nlog
                           v_logstart v_inodestart v_bmapstart bs_sb sb_old
                           bs_hdr L D vlock vname vcpu v_start v_dev v_nc v_n
                           pidv dq m K eb b lks.
End FSINIT.
