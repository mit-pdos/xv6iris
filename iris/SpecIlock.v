(* SpecIlock.v -- the public interface of ilock, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void ilock(struct inode *ip) {
       struct buf *bp;  struct dinode *dip;

       if (ip == 0 || ip->ref < 1) panic("ilock");
       acquiresleep(&ip->lock);
       if (ip->valid == 0) {
         bp  = bread(ip->dev, IBLOCK(ip->inum, sb));
         dip = (struct dinode * )bp->data + ip->inum % IPB;
         ip->type = dip->type;   ip->major = dip->major;
         ip->minor = dip->minor; ip->nlink = dip->nlink;
         ip->size  = dip->size;
         memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));
         brelse(bp);
         ip->valid = 1;
         if (ip->type == 0) panic("ilock: no type");
       }
     }

   174 bytes, 61 instructions.  iupdate is the FLUSH; this is the LOAD --
   same IBLOCK arithmetic, same [DinodeEnc] slot, [memmove] running the
   other way -- with a lock acquisition and a cached/uncached split on top.

   ---- THE ENTRY IS A SLOT, NOT A POINTER ------------------------------

   [ip] is [IcacheRef.ientry k] for a slot [k < NINODE], not a free pointer:
   the whole icache is indexed by slot ([ientry_inj] makes the two views
   interchangeable) and the escrow, the reference algebra and the [ref]-word
   invariant are all keyed that way.  It is also what kills the first
   panic's null test with no premise at all -- [ientry_unsigned] says the
   address is [itable + 24 + 136k], which is never zero.

   ---- WHAT IT CONSUMES, AND WHAT IT PRODUCES --------------------------

   IN: ONE SHARE, [IcacheRef.inode_shr k s dev inum] -- and it is consumed
   (v3, design §14.6/§14.8).  v2 took a whole REFERENCE; the caller that
   actually exists is fileread, whose inode reference is parked in the file
   payload for the duration of the call and can only LEND, so what crosses
   ilock's boundary is a slice of the identity cells plus the matching slice
   of the slot's liveness unit ([IcacheRef.inode_ref_carve], a pure resource
   split -- no fupd, no invariant, §14.7(2)).  A share carries NO count
   fragment ([positiveR] has no zero, §14.5), which is why the [ref < 1]
   guard below reads through the liveness pool instead.  ilock has exactly
   one caller in the tree, so there is no reference-shaped variant of this
   contract.

   The share is DEPOSITED, exactly as v2's reference was: §13.1d, a checkout
   hands its credential to the escrow's checked-out arm, where it waits for
   iunlock.  That is why this contract hands nothing back that could be
   spent, and why SpecIunlock v3 is the only way to recover the share.  What
   it DOES hand back is the other half of the entry sleeplock's descriptor
   variable ([IcacheEscrow.ic_deposit] at [DepShr s dev inum]) -- §14.8's
   repair: with the OUT arm able to hold either a share or a reference, that
   half is what lets the parker find its own arm again, and it pins the
   fraction and the identity so that iunlock's postcondition needs no
   existential.  Both identity CELLS come out at the escrow's permanent half
   (§13.1e) -- which is what lets ilock read [ip->dev] for its own bread
   after the deposit, and what lets iunlock return the share AT THIS
   DEVICE.

   The three persistent invariants replace what v1 asked a caller to own
   outright: [itable_inv] (the [ref] words -- v1's [i_ref ip ↦₄{dqr} refv]
   premise was UNSATISFIABLE, design §4), [ic_escrow] (the entry's content),
   [ireg_inv] (the inode region -- v1's [fsblock] of the whole inode block,
   plus its [diblk_wf] and its conditional-slot premise, all three of which
   §11.3 retires).  The sleeplock protects only [ic_tok cn k], the checkout
   token; the CONTENT travels through the escrow, because iget rewrites a
   recycled entry's cells holding [itable.lock] and no sleeplock at all.

   OUT: the checked-out bundle at an EXISTENTIAL [(dn, bm)] -- literally
   [IcacheEscrow.ic_loaded] plus the two identity halves and the valid cell,
   i.e. literally SpecIunlock v2's precondition and literally what
   [ic_swap_park] consumes.  The record is ∃-bound because nothing outside
   ilock knows it: v1's caller named it through the [inode_key] shadow, and
   §13.1 retires the shadow (with N reference holders only two ghost_var
   halves exist, so "the caller supplies one" is unsatisfiable for the
   second holder -- the same multi-holder trap as v1's [i_ref] premise).
   readi/writei instantiate from the existential exactly as they already do
   from [inode_locked]'s existential [data].

   PARKED-MEANS-FLUSHED (§13.1d/§13.6): the bundle's [dinode_at] is at the
   SAME [dn] as the metadata cells, not at a separate stale record.  It is
   provable on both arms -- the cached arm inherits it from the parked arm,
   the uncached arm reads the record OFF the region and so reconstructs
   exactly it -- and it is REQUIRED, because a caller that does not iupdate
   (fileread, whose middle callee is readi) could otherwise never discharge
   iunlock's flushed-record obligation.  Stale in-memory records exist only
   INSIDE a critical section, between a writei and its iupdate.

   ---- ONE PANIC IS DEAD, ONE IS LIVE ----------------------------------

   [ip == 0 || ip->ref < 1] is REFUTED: the null half by [ientry_unsigned]
   as above, the count half by [IcacheInv.iref_live_load_au] against
   [itable_inv], whose delivered [0 < v < 2^31] is exactly what
   [InodeLock.inode_ref_spos] turns into "[bge x0,a5] falls through" (v1
   took those bounds as a premise about a caller-owned cell).  v2 read
   through the reference's COUNT fragment ([iref_load_au]); a share has
   none, and reads through its LIVENESS slice instead -- a free slot's whole
   unit sits inside [IcacheInv.itable_body], so owning any slice at all
   proves the slot is live.  That lemma takes [k < NINODE] as a premise
   where its count-side twin derived it from [icM_wf]; this contract has it
   already.

   [ip->type == 0] IS LIVE -- A FIRST FOR THIS TREE.  §13.1: the shadow that
   used to carry v1's conditional agreement premise is gone, a caller
   premise "this inum is allocated" would be undischargeable today
   (allocatedness is directory-structure knowledge -- namei/ialloc, future
   work), and the pool legitimately holds free inodes ([ipool_shape]'s
   type-0 shape, §13.3).  So on the free-inode arm ilock DIVERGES through
   [SpecPanic.panic_wp_any] and this postcondition speaks only for
   successful loads.  That is sound in a partial-correctness WP and it is
   the honest statement; every other panic in this tree is refuted, and the
   proof file says at which instruction this one is taken.

   ilock SLEEPS (acquiresleep, and bread inside the uncached arm), so it
   threads the full running-process bundle.  It enters and returns at
   noff 0.  ONE [bslot]: bread's reference, which brelse gives back. *)
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
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ilock's own frame is 32 bytes (4 slots) -- [c.addi sp,sp,-32] at +0x00,
   ra/s0/s1 pushed there and s2 pushed on the uncached arm only.  Its
   deepest callee is bread (40); acquiresleep wants 26, brelse 26,
   memmove 2. *)
Definition K_ilock : nat := 44%nat.

Definition wp_ilock_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (gfs : fs_names) (gi : gname)                      (* fs blocks + region  *)
    (cn : ic_names)                                    (* the icache's names  *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
    (pidv : mword 32) (dq dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ilock in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ilock <= K)%nat ->
  (* THE ENTRY IS SLOT [k]; this is also the null test's refutation *)
  (k < NINODE)%nat ->
  (* the covered range's block-number bounds: bread's 2^31 arithmetic
     premise, and 0 is never a client block *)
  log_geom_ok cov logstart ->
  (* the superblock field is a real block number, so the [addw] that forms
     IBLOCK cannot wrap *)
  0 <= inodestart ->
  (* the inode's own block is a covered HOME block: bread's premise *)
  IBLOCK inum inodestart ∈ cov ->
  (* the inum is inside the inode region: [ireg_read]'s premise *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM -- acquiresleep and bread
     both sleep, and a parking thread hands [trap_csrs] / [cpu_claim] across
     the crossing (SpecSched.v).  At [eb = true] ilock's own [acquiresleep]
     acquire frees them out of [sie_arm true], so the complement is [emp]
     and the caller brings nothing -- which is why this used to be an
     [eb = true] premise instead.  At [eb = false] the caller brings the
     pair, holding it because the TRAP handed it over. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  (* THE THREE PERSISTENT INVARIANTS: the [ref] words, the entry's content,
     the inode region *)
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  (* THE ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* THE CALLER'S SHARE (v3) -- consumed; deposited whole at the checkout.
     GENERATION-NAMED (design 17.3, ratified 17.4): the share's liveness
     slice belongs to slot [k]'s current generation [g], and naming it is
     what lets this contract EXPOSE that generation's type witness below.
     Mechanical for every existing caller: [IcacheRef.inode_shr_gen_intro]
     is the existential its [inode_shr] already carries. *)
  inode_shr_gen k s dev inum g -∗
  (* sb.inodestart, read once *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* the caller's own pid cell (acquiresleep records it in the lock) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ONE slot unit: bread's reference, which brelse gives back *)
  bslot bn -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function PARKS (its
     acquiresleep sleeps), and a park moves the hart with interrupts off, so
     the crossing has nothing to do with SIE -- the porting guide's "a
     PARKING function's [wp_next] index is [true] UNCONDITIONALLY".  While
     the contract was pinned at [b = true] the two spellings coincided; at
     [b = false] the [b] form would claim the function returns on the hart
     that called it, which is false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (dn : dinode) (bm : blkmap),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslot bn -∗
      (* THE LOCK IS HELD ... *)
      sleeplocked gisl -∗
      sl_pid (i_lock ip) ↦₄ pidv -∗
      (* ... and the entry is CHECKED OUT and LOADED: the checkout
         descriptor's other half (§14.8 -- what the parker selects its arm
         with, and what pins [s], [dev] and [inum] there), the escrow's two
         identity halves, the valid cell, and the loaded content at a
         record the region agrees with.  Exactly [ic_swap_park]'s input,
         i.e. exactly SpecIunlock v3's precondition. *)
      ic_deposit cn k (DepShr s dev inum g) -∗
      i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
      i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
      i_valid ip ↦₄ valid_word true -∗
      ic_loaded gfs gi cov logstart k inum dn bm -∗
      (* THE FD-TYPE WITNESS (design fs-icache.md 17.6 (5), ratified 17.7).
         PERSISTENT, ADDITIVE, and ignored by every caller that does not
         write: this generation's one-shot, spent by the fill against the
         record the fill read.  It is stated at the CALLER'S [g] -- the one
         its share names -- and nothing pins it to the arm's but
         [IcacheRef.live_gen_agree], which needs no itable fact at all
         (17.1's currency requirement, discharged).

         What it is FOR: filewrite's re-park must know the inode it is
         writing is not a directory, and "not a directory" is sys_open's
         invariant, five frames up.  [FileInv.inode_pay] carries the fd's own
         [ity_shot g ty] with [fc_wbool C = true -> ty <> T_DIR];
         [IcacheRef.ity_shot_agree] joins the two, and [DirView.dir_ok] is
         vacuous.  A generation sees at most one fill (17.6), which is what
         makes that agreement sound. *)
      ity_shot g (di_type dn) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ILOCK.
  Parameter wp_ilock_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (k : nat) (s : Qp) (g : gname) (dev inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_ilock_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                          cov logstart inodestart nib k s g dev inum
                          pidv dq dqs m K eb C b.
End ILOCK.
