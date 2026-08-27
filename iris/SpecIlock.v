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
   variable ([IcacheEscrow.ic_deposit] at the checkout descriptor) -- §14.8's
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
   [ireg_inv] (the inode region -- v1's [fs_chalf] of the whole inode block,
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
   work), and the pool legitimately holds free inodes (the pool row's
   type-0 shape, §13.3).  So on the free-inode arm ilock DIVERGES through
   [SpecPanic]'s own contract and this postcondition speaks only for
   successful loads.  That is sound in a partial-correctness WP and it is
   the honest statement; every other panic in this tree is refuted, and the
   proof file says at which instruction this one is taken.

   ---- THE CLAIM-BOX INDICATOR (fs-sysfile D₀, increment 1) -------------

   The postcondition carries one more output, [filled : bool], and the
   conditional fact [filled = true -> InodeRegion.fresh_shape dn].  This is
   NOT new content: [InodeRegion.ireg_withdraw] already PROVES
   [fresh_shape] and hands it to [ProofIlock]'s third fill sub-arm --
   §16.4's CLAIM BOX, the first fill of an entry [ialloc] has just claimed
   -- and that arm then spends it building [inode_ok] / [dir_ok] and drops
   it.  The contract simply failed to expose proven content, and exposing
   it is the point of the exercise.

   IT HAS TO BE CONDITIONAL, and the boolean is the condition rather than a
   premise, because [fresh_shape dn] is FALSE on the other two arms: a
   cached entry and an ordinary fill both return a record with real size
   and real blocks.  So [filled] means EXACTLY "this call took §16.4's
   claim-box arm", the cached arm and the ordinary fill both report
   [false], and a caller that cannot show [filled = true] is exactly where
   it was before.

   WHO WANTS IT: create's [ilock(ip)] at +0x98, on the inode [ialloc] just
   claimed.  [SpecCreate]'s [made] arm needs [di_size dn = 0] and
   [di_addrs dn = replicate 13 (bv_0 32)] -- for [ProofCreateParts.
   cr_made_setf]'s [create_made] identity and for [dirlink(ip,".")]'s
   "the append fits" premise, neither of which [InodeLock.inode_ok]'s
   loose size cap can give -- and [fresh_shape] is exactly those two facts.
   That leaves [di_type dn = ty] as the half of create's fresh-record
   obligation that [ProofCreateFreshTy.v] proves off the [ClaimK] index
   below and nothing more.
   Every other caller ignores the pair.

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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
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
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* ilock's own frame is 32 bytes (4 slots) -- [c.addi sp,sp,-32] at +0x00,
   ra/s0/s1 pushed there and s2 pushed on the uncached arm only.  Its
   deepest callee is bread (40); acquiresleep wants 26, brelse 26,
   memmove 2. *)
Notation K_ilock := (62%nat) (only parsing).
Definition wp_ilock_dep_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (gfs : fs_names) (gi : gname)                      (* fs blocks + region  *)
    (cn : ic_names)                                    (* the icache's names  *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (k : nat) (s : Qp) (g : gname) (d : ic_dep) (o : ilkc) (dev inum : mword 32)
    (pidv : mword 32) (dq dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ilock in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ilock <= K)%nat ->
  (* ---- THE DESCRIPTOR THE CHECKOUT PUBLISHES (durable-fs-plan.md section
     3, [ilock]; durable-disk B''-tx3).  ONE proof of ilock's code, three
     arms, selected by [d] BEFORE the call and published at the checkout's own
     ghost step -- so no bundleless out-state stands between the contract's
     post and a later arming fupd, whatever the caller is.

       [DepTx s dev inum g t q]     THE WRITE ARM: the escrow's OUT arm parks
                                    [q] of transaction [t]'s [LogInv.log_tx]
                                    element for the whole locked window, so
                                    [end_op] cannot commit while the inode is
                                    out and the collection refutes the arm
                                    outright ([ic_out_no_write_arm]).  The
                                    share is [IcacheEscrow.ic_dep_side]'s
                                    content, below;
       [DepRd s dev inum g]         THE READ ARM: the escrow KEEPS three
                                    quarters of the bundle and what comes out
                                    is [ic_rd_held].  It needs the entry to be
                                    LOADED already, which the [ShotK] licence's
                                    one-shot gives ([ic_swap_checkout_rd]).

     [ic_dep_shr] is what the three have in common -- the caller's own
     generation-named share, unchanged in all three -- and the two
     projections below are what differs. *)
  ic_dep_shr d = Some (s, dev, inum, g) ->
  (* ...AND WHAT THE READ ARM COSTS, which is nothing its two callers do not
     already pay.  [DepRd]'s arm keeps three quarters of the bundle, so the
     checkout can only be taken where one EXISTS -- and the record proxy stays
     in the arm, so the holder cannot refute a standing [iclaim] either.  Both
     are exactly [InodeRegion.ShotK]: its licence IS this generation's type
     one-shot, which kills the unloaded payload
     ([IcacheRef.ity_pending_shot_excl]) inside the checkout's own ghost step,
     and [ilk_post (ShotK _)] already reports [filled = false].  [fileread] and
     [filestat] -- the only two [ilock] callers holding no transaction -- come
     in at [ShotK] and nowhere else does. *)
  (ic_dep_rd d = true -> exists ty : bv 16, o = ShotK ty) ->
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
  (* ilock's cone touches "sleep lock"(6) via acquiresleep and "bcache"(4)
     via bread/brelse (on the invalid-entry fill arm); bcache is the LOWER
     of the two, so one premise at its rank covers the whole cone via
     [locks_below_mono]. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM -- acquiresleep and bread
     both sleep, and a parking thread hands [trap_csrs] / [cpu_claim] across
     the crossing (SpecSched.v).  At [eb = true] ilock's own [acquiresleep]
     acquire frees them out of [sie_arm true], so the complement is [emp]
     and the caller brings nothing -- which is why this used to be an
     [eb = true] premise instead.  At [eb = false] the caller brings the
     pair, holding it because the TRAP handed it over. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  (* THE THREE PERSISTENT INVARIANTS: the [ref] words, the entry's content,
     the inode region *)
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  (* THE ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
  (* THE ENTRY'S SLEEPLOCK -- TRACKED, and at the cache's canonical gname
     for the slot: what a holder deposits in it is a share of somebody's
     REFERENCE ([SleepLock.slh_tok]), which is what lets iput -- holding the
     only reference -- prove the lock free rather than block on it
     (claude-notes/projects/iput-acquiresleep.md).  The deposit ilock leaves
     is the [slh_tok] slice of the very share it consumes below, so no
     caller pays anything new. *)
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                   (slh_tok (icfg_isl k)) -∗
  (* THE CALLER'S SHARE (v3) -- consumed; deposited whole at the checkout.
     GENERATION-NAMED (design 17.3, ratified 17.4): the share's liveness
     slice belongs to slot [k]'s current generation [g], and naming it is
     what lets this contract EXPOSE that generation's type witness below.
     Mechanical for every existing caller: [IcacheRef.inode_shr_gen_intro]
     is the existential its [inode_shr] already carries. *)
  inode_shr_gen k s dev inum g -∗
  (* WHAT THE DESCRIPTOR PARKS BESIDE THE SHARE: the transaction share at
     [DepTx], [emp] at the other two. *)
  ic_dep_side d -∗
  (* ---- THE FILL's LICENCE, INDEXED (iclaim-ledger.md §5''''', RULING C')

     §16.4's fill has a sub-arm -- the CLAIM BOX -- that no caller can be
     left stuck on, and [InodeRegion.ireg_withdraw] is the only thing that
     can discharge it.  The index says which of the three currencies this
     caller brought and therefore which discharge runs; see
     [InodeRegion.ilkc].  In one line each:

       [ClaimK ty]  create's child fill, and the only site that can present
                    ialloc's typed [iclaim].  It brings the claim TOGETHER
                    with the claim-flavoured provenance unit its own
                    reference carries, the withdraw CONVERTS the pair into
                    the plain unit, and the post below pins BOTH
                    [filled = true] and [di_type dn = ty] -- which is
                    exactly [ProofCreateFreshTy]'s span conjunct.  The
                    other two shapes the entry could be in
                    (cached, or a pool bundle) are refuted by
                    [InodeRegion.ireg_claim_no_out]: a claimed inum's record
                    is INSIDE the region, so nobody holds its [dinode_at].
       [PlainK]     the twelve in-file-unit sites.  The unit their own
                    reference carries collides with the claim pin's (R3),
                    which DERIVES [c = None] -- the box arm is refuted and
                    the unit comes straight back out.
       [ShotK ty]   the three fd sites, which can hold no whole unit across
                    this call (their inode payload is behind a cancellable
                    invariant no syscall may keep open here).  What they DO
                    hold, free and persistent, is this generation's own
                    one-shot -- and a one-shot in hand means the generation
                    has already been filled, so it refutes the UNCACHED arm
                    outright ([IcacheRef.ity_pending_shot_excl]) and the
                    post reports [filled = false].

     STATED AT THE CALLER'S [g], like [ity_shot] below and for the same
     reason. *)
  ireg_wd_lic o g (bv_unsigned inum) -∗
  (* sb.inodestart, read once *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* the caller's own pid cell (acquiresleep records it in the lock) *)
  proc_priv_bare pj pidv Vpr -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ONE slot unit: bread's reference, which brelse gives back *)
  bslot -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function PARKS (its
     acquiresleep sleeps), and a park moves the hart with interrupts off, so
     the crossing has nothing to do with SIE -- the porting guide's "a
     PARKING function's [wp_next] index is [true] UNCONDITIONALLY".  While
     the contract was pinned at [b = true] the two spellings coincided; at
     [b = false] the [b] form would claim the function returns on the hart
     that called it, which is false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (dn : dinode) (bm : blkmap) (filled : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslot -∗
      (* THE LOCK IS HELD ... *)
      sleeplocked_q gisl s (i_lock ip) pidv -∗
      (* ... and the entry is CHECKED OUT and LOADED: the checkout
         descriptor's other half (§14.8 -- what the parker selects its arm
         with, and what pins [s], [dev] and [inum] there), the escrow's two
         identity halves, the valid cell, and the loaded content at a
         record the region agrees with.  Exactly [ic_swap_park]'s input,
         i.e. exactly SpecIunlock v3's precondition. *)
      ic_deposit cn k d -∗
      i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
      i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
      i_valid ip ↦₄ valid_word true -∗
      ic_dep_held gfs gi cov logstart d k inum dn bm -∗
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
      (* ...AND THE INUM'S FREEZE TOKEN (iclaim-ledger.md §3.1 A-custody /
         §3.9 RULING A-prime).  A-custody puts the token on the PAYLOAD's
         custody path -- pool bundle <-> parked arm <-> holder -- and this is
         the holder's end of it: [IcacheEscrow.ic_payload], the predicate
         [ic_swap_checkout] takes out of the parked arm, carries
         [ifreeze_off], so a checkout hands it over exactly as it hands over
         [ic_loaded].  [SpecIunlock]'s precondition takes it back.

         WHY THE CONTRACT GREW (§3.9's ruling, and its price): the freeze
         pin's premise on [InodeRegion.ireg_write_link_reg] is FALSE at
         create's fresh child ([fresh_shape] pins the pre-count at zero) and
         unavailable at sys_link's [ip->nlink++] (no guard, no link token in
         hand); IIIc refuted every cheaper route.  The honest supply is this
         token, and a checked-out holder is exactly who has it.

         WHAT A CALLER THAT DOES NOT WRITE DOES WITH IT: nothing -- it
         threads it to its own iunlock.  iProp is affine, so a caller that
         parks through some other route may drop it. *)
      ifreeze_off (bv_unsigned inum) -∗
      (* THE CLAIM-BOX INDICATOR -- see the header.  Proven content, not a
         new obligation: [InodeRegion.ireg_withdraw] pays [fresh_shape] to
         §16.4's fill sub-arm and this clause is where it now leaves. *)
      ⌜filled = true -> fresh_shape dn⌝ -∗
      (* ...AND THE LICENCE's PAYOUT (RULING C').  [ClaimK]'s pair has
         CONVERTED into the plain unit the child reference carries from
         here on; [PlainK]'s unit is the caller's own, borrowed and
         returned; [ShotK]'s one-shot is persistent and comes back
         because it never left. *)
      ireg_wd_back o g (bv_unsigned inum) -∗
      (* ...and what the index BUYS, which is the whole of item 7: at
         [ClaimK] the fill is FORCED and the record is the record the claim
         wrote. *)
      ⌜ilk_post o filled dn⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ---- THE TRANSACTIONAL FORM (durable-fs-plan.md section 3, [ilock];
   durable-disk B''-tx) -------------------------------------------------

   ONE C FUNCTION, ONE PROOF, TWO PUBLISHED FORMS, selected by what the
   caller holds.  The body below is the generic one at [DepTx]: it CONSUMES
   [LogInv.log_tx icfg_log] and PRODUCES [IcacheEscrow.ic_tx_dep], the
   descriptor and the holder's residue bundled.  The escrow's OUT arm is a
   [DepTx] from the instant the entry leaves -- the checkout itself
   publishes it -- so a transactional walk cannot forget to arm and no
   bundleless arm is reachable for it.

   [ProofIlock] proves it by DERIVATION from the generic form
   ([wp_ilock_tx_of_dep] below); not a line of ilock's own proof is
   re-run. *)
Definition wp_ilock_tx_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (gfs : fs_names) (gi : gname)                      (* fs blocks + region  *)
    (cn : ic_names)                                    (* the icache's names  *)
    (gil gisl : gname)                                 (* ip->lock            *)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (k : nat) (s : Qp) (g : gname) (o : ilkc) (dev inum : mword 32)
    (pidv : mword 32) (dq dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
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
  (* ilock's cone touches "sleep lock"(6) via acquiresleep and "bcache"(4)
     via bread/brelse (on the invalid-entry fill arm); bcache is the LOWER
     of the two, so one premise at its rank covers the whole cone via
     [locks_below_mono]. *)
  locks_below lks "bcache" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM -- acquiresleep and bread
     both sleep, and a parking thread hands [trap_csrs] / [cpu_claim] across
     the crossing (SpecSched.v).  At [eb = true] ilock's own [acquiresleep]
     acquire frees them out of [sie_arm true], so the complement is [emp]
     and the caller brings nothing -- which is why this used to be an
     [eb = true] premise instead.  At [eb = false] the caller brings the
     pair, holding it because the TRAP handed it over. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  (* THE THREE PERSISTENT INVARIANTS: the [ref] words, the entry's content,
     the inode region *)
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  (* THE ENTRY'S SLEEPLOCK -- over the CHECKOUT TOKEN alone *)
  (* THE ENTRY'S SLEEPLOCK -- TRACKED, and at the cache's canonical gname
     for the slot: what a holder deposits in it is a share of somebody's
     REFERENCE ([SleepLock.slh_tok]), which is what lets iput -- holding the
     only reference -- prove the lock free rather than block on it
     (claude-notes/projects/iput-acquiresleep.md).  The deposit ilock leaves
     is the [slh_tok] slice of the very share it consumes below, so no
     caller pays anything new. *)
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                   (slh_tok (icfg_isl k)) -∗
  (* THE CALLER'S SHARE (v3) -- consumed; deposited whole at the checkout.
     GENERATION-NAMED (design 17.3, ratified 17.4): the share's liveness
     slice belongs to slot [k]'s current generation [g], and naming it is
     what lets this contract EXPOSE that generation's type witness below.
     Mechanical for every existing caller: [IcacheRef.inode_shr_gen_intro]
     is the existential its [inode_shr] already carries. *)
  inode_shr_gen k s dev inum g -∗
  (* ---- THE FILL's LICENCE, INDEXED (iclaim-ledger.md §5''''', RULING C')

     §16.4's fill has a sub-arm -- the CLAIM BOX -- that no caller can be
     left stuck on, and [InodeRegion.ireg_withdraw] is the only thing that
     can discharge it.  The index says which of the three currencies this
     caller brought and therefore which discharge runs; see
     [InodeRegion.ilkc].  In one line each:

       [ClaimK ty]  create's child fill, and the only site that can present
                    ialloc's typed [iclaim].  It brings the claim TOGETHER
                    with the claim-flavoured provenance unit its own
                    reference carries, the withdraw CONVERTS the pair into
                    the plain unit, and the post below pins BOTH
                    [filled = true] and [di_type dn = ty] -- which is
                    exactly [ProofCreateFreshTy]'s span conjunct.  The
                    other two shapes the entry could be in
                    (cached, or a pool bundle) are refuted by
                    [InodeRegion.ireg_claim_no_out]: a claimed inum's record
                    is INSIDE the region, so nobody holds its [dinode_at].
       [PlainK]     the twelve in-file-unit sites.  The unit their own
                    reference carries collides with the claim pin's (R3),
                    which DERIVES [c = None] -- the box arm is refuted and
                    the unit comes straight back out.
       [ShotK ty]   the three fd sites, which can hold no whole unit across
                    this call (their inode payload is behind a cancellable
                    invariant no syscall may keep open here).  What they DO
                    hold, free and persistent, is this generation's own
                    one-shot -- and a one-shot in hand means the generation
                    has already been filled, so it refutes the UNCACHED arm
                    outright ([IcacheRef.ity_pending_shot_excl]) and the
                    post reports [filled = false].

     STATED AT THE CALLER'S [g], like [ity_shot] below and for the same
     reason. *)
  ireg_wd_lic o g (bv_unsigned inum) -∗
  (* sb.inodestart, read once *)
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* the caller's own pid cell (acquiresleep records it in the lock) *)
  proc_priv_bare pj pidv Vpr -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* ONE slot unit: bread's reference, which brelse gives back *)
  bslot -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function PARKS (its
     acquiresleep sleeps), and a park moves the hart with interrupts off, so
     the crossing has nothing to do with SIE -- the porting guide's "a
     PARKING function's [wp_next] index is [true] UNCONDITIONALLY".  While
     the contract was pinned at [b = true] the two spellings coincided; at
     [b = false] the [b] form would claim the function returns on the hart
     that called it, which is false. *)
  (* ---- THE TRANSACTION'S TOKEN, HANDED IN AT THE LOCK ---------------
     (durable-fs-plan.md section 3, [ilock]; durable-disk B''-tx)

     This is the ONLY difference from the generic body on the way in, and the
     postcondition's [IcacheEscrow.ic_tx_dep] is the only one on the way
     out.  A caller that brings [LogInv.log_tx] gets the WRITE ARM: half
     its transaction's element is parked in the escrow's checked-out arm for
     the whole locked window, so [end_op] -- which consumes the whole element
     -- cannot commit while this inode is out, which is exactly what the
     collection at quiescence reads off the escrow
     ([IcacheEscrow.ic_out_no_write_arm]).  The other half rides home inside
     [ic_tx_dep], so a walk that threads the descriptor through its stages
     threads the residue with it and NO stage lemma gains a binder.

     WHAT IT COSTS THE WALK: between here and its [iunlock] it holds no
     transaction token at all, so every interior contract it calls must be
     the [log_opS]/GEN form ([SpecWritei], [SpecIupdate], [SpecItrunc],
     [SpecDirlink], [SpecBmap], [SpecBalloc], [SpecBfree],
     [SpecIunlockput]).  Every one of them already has it. *)
  log_tx icfg_log -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (dn : dinode) (bm : blkmap) (filled : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslot -∗
      (* THE LOCK IS HELD ... *)
      sleeplocked_q gisl s (i_lock ip) pidv -∗
      (* ... and the entry is CHECKED OUT and LOADED: the checkout
         descriptor's other half (§14.8 -- what the parker selects its arm
         with, and what pins [s], [dev] and [inum] there), the escrow's two
         identity halves, the valid cell, and the loaded content at a
         record the region agrees with.  Exactly [ic_swap_park]'s input,
         i.e. exactly SpecIunlock v3's precondition. *)
      ic_tx_dep cn k s dev inum g -∗
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
      (* ...AND THE INUM'S FREEZE TOKEN (iclaim-ledger.md §3.1 A-custody /
         §3.9 RULING A-prime).  A-custody puts the token on the PAYLOAD's
         custody path -- pool bundle <-> parked arm <-> holder -- and this is
         the holder's end of it: [IcacheEscrow.ic_payload], the predicate
         [ic_swap_checkout] takes out of the parked arm, carries
         [ifreeze_off], so a checkout hands it over exactly as it hands over
         [ic_loaded].  [SpecIunlock]'s precondition takes it back.

         WHY THE CONTRACT GREW (§3.9's ruling, and its price): the freeze
         pin's premise on [InodeRegion.ireg_write_link_reg] is FALSE at
         create's fresh child ([fresh_shape] pins the pre-count at zero) and
         unavailable at sys_link's [ip->nlink++] (no guard, no link token in
         hand); IIIc refuted every cheaper route.  The honest supply is this
         token, and a checked-out holder is exactly who has it.

         WHAT A CALLER THAT DOES NOT WRITE DOES WITH IT: nothing -- it
         threads it to its own iunlock.  iProp is affine, so a caller that
         parks through some other route may drop it. *)
      ifreeze_off (bv_unsigned inum) -∗
      (* THE CLAIM-BOX INDICATOR -- see the header.  Proven content, not a
         new obligation: [InodeRegion.ireg_withdraw] pays [fresh_shape] to
         §16.4's fill sub-arm and this clause is where it now leaves. *)
      ⌜filled = true -> fresh_shape dn⌝ -∗
      (* ...AND THE LICENCE's PAYOUT (RULING C').  [ClaimK]'s pair has
         CONVERTED into the plain unit the child reference carries from
         here on; [PlainK]'s unit is the caller's own, borrowed and
         returned; [ShotK]'s one-shot is persistent and comes back
         because it never left. *)
      ireg_wd_back o g (bv_unsigned inum) -∗
      (* ...and what the index BUYS, which is the whole of item 7: at
         [ClaimK] the fill is FORCED and the record is the record the claim
         wrote. *)
      ⌜ilk_post o filled dn⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE [log_tx] READING OF THE ARM, which is where the id leaves and re-enters
   [LogInv.log_tx]'s existential -- a parked share must sit at a NAMED
   [(t, q)], since two halves of one element are not the whole. *)
(* THE PUBLISHED READING, A DERIVATION OF THE ONE GENERIC BODY, which
   re-proves no line of ilock's code (durable-disk B''-tx3/-tx4).  The
   read-lockers ([fileread], [filestat]) call the generic form at [DepRd]
   directly. *)
(* (ii) THE WRITE ARM: the generic at [DepTx … t (1/2)], with the transaction
   id taken out of [LogInv.log_tx]'s existential before the call and the two
   halves rejoined into [IcacheEscrow.ic_tx_dep] at the post.  The escrow
   holds its half from the checkout on. *)
Lemma wp_ilock_tx_of_dep
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (gs : list gname) (j : nat) (gl : gname)
    (gu : uart_names) (gd : disk_names) (gk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (gfs : fs_names) (gi : gname)
    (cn : ic_names)
    (gil gisl : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (k : nat) (s : Qp) (g : gname) (o : ilkc) (dev inum : mword 32)
    (pidv : mword 32) (dq dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :
  (forall d : ic_dep,
     wp_ilock_dep_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                             cov logstart inodestart nib k s g d o dev inum
                             pidv dq dqs m K eb b lks Vpr) ->
  wp_ilock_tx_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                         cov logstart inodestart nib k s g o dev inum
                         pidv dq dqs m K eb b lks Vpr.
Proof.
  cbv beta delta [wp_ilock_tx_sconf_body wp_ilock_dep_sconf_body].
  intros Hgen pcE ip pj ret_tgt HK Hk Hgeom Hst Hcov Hinlt Hj Hgl Ha0 Hbelow.
  iIntros "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio #Hitbl #Hesc Hireg
           Hslk Hshr Hlic Hsb Hppid Hprocs Hdevi Hdgeom Hdlock Hsl Htx Hcont".
  iDestruct (log_tx_halve with "Htx") as (t) "[Ht1 Ht2]".
  iApply (Hgen (DepTx s dev inum g t (1/2))
            HK eq_refl ltac:(discriminate) Hk Hgeom Hst Hcov Hinlt Hj Hgl
            Ha0 Hbelow
            with "Hcg Hown Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hitbl Hesc
                  Hireg Hslk Hshr [Ht1] Hlic Hsb Hppid Hprocs Hdevi Hdgeom
                  Hdlock Hsl [Ht2 Hcont]").
  { rewrite /ic_dep_side. iExact "Ht1". }
  iIntros (CIDx Hqx mf dn bm filled)
    "%Hcs Hcg Hown Hextc Hextm Hpc Hppid Hsb Hsl Hslkd Hdep Hidev Hiinum
     Hivalid Hload #Hshot Hfrz %Hfl Hlicb %Hilk".
  iEval (rewrite /ic_dep_held; cbn [ic_dep_rd]) in "Hload".
  iDestruct (ic_tx_dep_intro with "Hdep Ht2") as "Hdep".
  iApply ("Hcont" $! CIDx Hqx mf dn bm filled with
            "[%] Hcg Hown Hextc Hextm Hpc Hppid Hsb Hsl Hslkd Hdep Hidev
             Hiinum Hivalid Hload Hshot Hfrz [%] Hlicb [%]");
    [exact Hcs | exact Hfl | exact Hilk].
Qed.

Module Type ILOCK.
  (* THE GENERIC FORM (durable-disk B''-tx3): ONE proof of ilock's code, the
     checkout's descriptor chosen by the caller.  [wp_ilock_tx_sconf] below
     is its [DepTx] reading ([wp_ilock_tx_of_dep]); a READ-locker
     ([fileread], [filestat]) uses it at [DepRd] directly, which is what
     retires [ic_shed_rd] at those two sites. *)
  Parameter wp_ilock_dep_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (k : nat) (s : Qp) (g : gname) (d : ic_dep) (o : ilkc) (dev inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_ilock_dep_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                              cov logstart inodestart nib k s g d o dev inum
                              pidv dq dqs m K eb b lks Vpr.
  (* THE TRANSACTIONAL FORM (durable-disk B''-tx).  Same C function, same
     proof; what selects it is whether the caller brings [LogInv.log_tx].
     [ProofIlock] defines it by [wp_ilock_tx_of_dep]. *)
  Parameter wp_ilock_tx_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (k : nat) (s : Qp) (g : gname) (o : ilkc) (dev inum : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_ilock_tx_sconf_body gs j gl gu gd gk pd pav pu bn gfs gi cn gil gisl
                             cov logstart inodestart nib k s g o dev inum
                             pidv dq dqs m K eb b lks Vpr.
End ILOCK.
