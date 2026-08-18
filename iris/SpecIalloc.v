(* SpecIalloc.v -- the public interface of ialloc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     struct inode* ialloc(uint dev, short type) {
       int inum;
       struct buf *bp;
       struct dinode *dip;

       for(inum = 1; inum < sb.ninodes; inum++){
         bp = bread(dev, IBLOCK(inum, sb));
         dip = (struct dinode * )bp->data + inum % IPB;
         if(dip->type == 0){          // a free inode
           memset(dip, 0, sizeof of a dinode);
           dip->type = type;
           log_write(bp);             // mark it allocated on the disk
           brelse(bp);
           return iget(dev, inum);
         }
         brelse(bp);
       }
       printf("ialloc: no inodes\n");
       return 0;
     }

   188 bytes, an EIGHT-slot frame.  Registers, off CodeIalloc.v:
   [s5 = dev], [s6 = type], [s2 = inum], [s4 = &sb], [s1 = bp], [s3 = dip].

   *** THE NO-INODES ARM IS LIVE, AND IT CALLS printk, NOT panic. ***  This
   kernel's ialloc was modified exactly the way its balloc was (SpecBalloc.v's
   header): the scan's fall-through at +0x66..+0x70 restores s1..s6 and lands
   on [auipc a0,0x4 / addi a0,a0,850 / jal printk] at +0x72, then [c.li a0,0].
   So this contract takes the same three things balloc's does -- [γpr], the
   two PERSISTENT credentials [kernel_data] and [printk_env], and printk's
   contract as a PURE Prop HYPOTHESIS ([SpecPrintk.printk_gen_contract])
   rather than as a functor argument.  See SpecBalloc.v's "READ THIS BEFORE
   TRUSTING THE STANDING SIX": carrying it as a hypothesis keeps
   [Print Assumptions] at the standing six, but the six are then modulo a
   THREADED printk obligation, exactly as [SpecPanic]'s credentials are.

   ---- THE CLAIM TAKES NO REGION RESOURCE AND PAYS NONE BACK (§16) -------

   This is the whole point of fs-icache.md §16, and it is what makes [create]
   statable.  ialloc's [log_write] at +0x9a retags the claimed inum's ghost
   fragment -- but ialloc holds NEITHER the itable spinlock nor any entry's
   sleeplock at that moment, so no caller could hand it the fragment and no
   caller could take it back.  What actually serialises two concurrent
   iallocs in xv6 is THE BUFFER (§16.2): [bread] returns the dinode block
   under its sleeplock and the loser's [bread] returns it with the type
   already set.

   Since N5b the model says exactly that.  A free inum's fragment lives in
   the REGION invariant ([InodeRegion.ireg_slot]'s first arm), the claim is
   [InodeRegion.ireg_claim_au] -- an atomic update with NO resource premise
   at all, plugged straight into [SpecLogWrite.wp_log_write_au]'s fupd
   premise at [Efs := ⊤ ∖ ↑iregN] and [Φfsb := True] -- and the retagged
   fragment STAYS in the region, at the [InodeRegion.fresh_shape] arm which
   IS §16.4's claim box.  The first [ilock] of the new inode withdraws it
   there ([InodeRegion.ireg_withdraw], ProofIlock's third fill case).

   So [ireg_inv] rides as the PERSISTENT premise it is, and there is no
   [dinode_at], no [imark] and no [ipool] anywhere in this contract.

   ---- WHAT THE CALLER GETS: iget's POSTCONDITION, VERBATIM --------------

   ialloc's last act is [return iget(dev, inum)] at +0xaa, so the success
   arm's payout is [SpecIget]'s: a slot [kslot < NINODE], a fraction [q],
   [a0 = ientry kslot], and ONE [IcacheRef.inode_ref kslot q dev inum].  The
   inum is existential -- the scan finds it -- and its region bound
   [bv_unsigned inum < 16 * nib] travels with it, which is what lets a
   caller rebuild [IcacheRef.inode_held] once it also knows
   [dev = icfg_dev] and [nib = icfg_nib].  Deliberately NOT a premise here:
   ialloc is device-generic exactly as iget is, and the two ties are the
   caller's to make.

   The claimed record is named too, as [ialloc_fresh ty] -- nonzero type,
   zero size, thirteen zero address words, and NOTHING ELSE, because the
   memset+[sh] pair writes nothing else.  In particular NLINK STAYS 0 until
   the caller's own [iupdate]; that is [InodeRegion.fresh_shape]'s exact
   content and it is all ilock's fill needs to build [InodeLock.inode_ok]
   out of nothing.  The fact is stated for documentation and for [create]'s
   benefit; it is not a resource, and it says nothing about the region's
   state at RETURN time -- by then another hart may already have locked the
   new inode.

   ---- THE THREE GEOMETRY PREMISES --------------------------------------

   [1 < ninodes] kills the [bgeu a5,a4] at +0x12, the EMPTY-REGION exit that
   jumps to the printk WITHOUT having pushed s1..s6 -- balloc's [0 < size]
   premise, at the same instruction offset, killing the same arm for the
   same reason (a second epilogue shape, not a second behaviour).

   [ninodes <= 16 * nib] is the SUPERBLOCK-TO-REGION tie, and it is the
   premise that did not exist before this contract: the scan's bound comes
   out of [sb.ninodes] while both [ireg_claim_au] and [iget] want
   [bv_unsigned inum < 16 * nib].  It belongs to the boot layer (SpecFsinit
   is where the superblock cells are born, N5a's ledger) and is threaded
   here, not discharged.

   [ninodes < 2 ^ 31] is what makes the [lw]-then-[bltu] comparison at
   +0x5a..+0x62 numeric: the loaded word is sign-extended into a 64-bit
   register and compared UNSIGNED against the likewise sign-extended
   [addiw a5,s2,0].

   ialloc SLEEPS (bread), so it threads the full running-process bundle
   exactly as SpecIupdate.v / SpecBalloc.v do, and takes the parking
   premise.  It enters and returns at noff 0.                             *)
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
Require Import FsBlocks LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* ialloc's own frame is 64 bytes (8 slots) -- [c.addi16sp sp,-64] at +0x00,
   with ra/s0/s1/s2/s3/s4/s5/s6 pushed at 56/48/40/32/24/16/8/0.  Its
   deepest callee is now printk on the out-of-inodes path (48, printk_stack);
   bread wants 40, brelse 26, log_write 18, iget 16 and memset 2. *)
Notation K_ialloc := (66%nat) (only parsing).
(* THE RECORD THE CLAIM WRITES.  [memset(dip, 0, 64)] at +0x90 followed by
   [sh s6,0(s3)] at +0x94 -- the type halfword and nothing else.  Stated as
   a named constructor rather than inline so that [create]'s own contract,
   and ilock's fill, can name the same term. *)
Definition ialloc_fresh (ty : mword 16) : dinode :=
  MkDinode ty (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
           (replicate 13 (bv_0 32)).

Lemma ialloc_fresh_type (ty : mword 16) : di_type (ialloc_fresh ty) = ty.
Proof. reflexivity. Qed.

Lemma ialloc_fresh_shape (ty : mword 16) :
  bv_unsigned ty <> 0 -> fresh_shape (ialloc_fresh ty).
Proof.
  intros Hty. rewrite /fresh_shape /ialloc_fresh /=.
  (* the fourth conjunct is [memset(dip,0,64)]'s own zero: [ialloc_fresh]
     builds the record with [bv_0 16] at [nlink] (design §20.18 ruling 1) *)
  split_and!; [exact Hty | reflexivity | reflexivity | reflexivity].
Qed.

Lemma ialloc_fresh_wf (ty : mword 16) : dinode_wf (ialloc_fresh ty).
Proof. rewrite /dinode_wf /ialloc_fresh /=. reflexivity. Qed.

Definition wp_ialloc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γpr : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
    (dev : mword 32) (ty : mword 16)
    (u : nat)
    (pidv : mword 32) (dq dqs dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ialloc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ialloc <= K)%nat ->
  (* bread's / log_write's block-number arithmetic, and the log's own
     storage *)
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  (* EVERY inum the region covers lives in a covered HOME block: bread's
     premise and log_write's, for the inum the scan happens to stop at.
     The scan cannot know it in advance, so the premise is the quantified
     one ([InodeInv.ireg_blocks_ok]). *)
  ireg_blocks_ok inodestart nib cov logstart ->
  (* THE THREE GEOMETRY PREMISES -- see the header *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  (* the type actually installs an ALLOCATED record; [fresh_shape] and
     therefore the whole claim need it, and every caller passes a literal *)
  bv_unsigned ty <> 0 ->
  (* THE NO-INODES ARM'S CALLEE, as a hypothesis and not a functor *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dev, a1 = type: the RV64 ABI's sign extension, and [sh s6,0(s3)]
     at +0x94 stores exactly the low sixteen bits of a1 *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (sign_extend' 64 dev : mword 64) ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- bread sleeps *)
  eb = true ->
  (* ialloc's cone: bread/brelse ("bcache", 4), log_write ("log", 3), iget
     ("itable", 2, on the tail claim), printk ("pr", 14, the no-inodes
     arm) -- "itable" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the general printk path's two PERSISTENT credentials *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the two superblock fields, read and handed straight back *)
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE INODE REGION -- persistent, and the ONLY region resource in this
     contract.  The claim is [InodeRegion.ireg_claim_au] and it takes
     nothing; see the header. *)
  ireg_inv γi γfs inodestart nib -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle and the disk fabric *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* ---- THE ICACHE, exactly as iget takes it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  (* ONE ledger unit for the tail iget; RETURNED on the no-inodes arm *)
  iref_slot -∗
  (* THIS OPERATION'S RESERVATION: the one log_write the claim runs *)
  log_op γ (S u) -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (alloc : bool) (kslot : nat) (q : Qp) (inum : mword 32)
    (dn' : dinode),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 2 -∗
      (if alloc
       then (* SUCCESS: iget's postcondition verbatim, at the claimed inum *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ientry kslot
          /\ (kslot < NINODE)%nat
          /\ 0 < bv_unsigned inum < ninodes
          /\ bv_unsigned inum < 16 * Z.of_nat nib
          (* what the claim WROTE: [ialloc_fresh ty], the weakest record a
             claim can promise and exactly what ilock's fill needs *)
          /\ dn' = ialloc_fresh ty
          /\ di_type dn' = ty
          /\ fresh_shape dn'⌝ ∗
         inode_ref kslot q dev inum ∗
         log_op γ u
       else (* NO INODES: a0 = 0, the ledger unit back, nothing spent *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗
         iref_slot ∗
         log_op γ (S u)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ---- THE CREDITED (SET-FORM) TWIN, fs-sysfile S5i, retrofit 5 of five ----

   [CreateBudget]'s arm theorems consume [ia_spend = 1] against a
   [LogInv.log_opS], and create threads ONE op-wide set across ialloc +
   iupdate x3 + dirlink x4.  [wp_ialloc_sconf] below is the set-FORGETTING
   instance of this, derived, so no existing caller moves.

   THERE IS NO ABSORPTION CREDIT HERE, and that is a fact about ialloc and
   not an omission: the block it logs is [IBLOCK inum inodestart] at the
   inum THE SCAN CHOSE, so no caller can know it in advance and no caller
   can have logged it.  fs-sysfile S5a's retrofit table says exactly this
   ("the inum is the scan's, so no credit is possible and the spend is
   unconditional"), which is why the growth is stated as the determinate
   union rather than as a [Sb ⊆ Sb'] inequality -- create needs the
   MEMBERSHIP afterwards, to credit its own [iupdate(ip)] and the iupdate
   inside every [dirlink] on [ip].                                        *)
Definition wp_ialloc_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname)                     (* the icache + itable *)
    (γpr : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
    (dev : mword 32) (ty : mword 16)
    (u : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqs dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ialloc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_ialloc <= K)%nat ->
  (* bread's / log_write's block-number arithmetic, and the log's own
     storage *)
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  (* EVERY inum the region covers lives in a covered HOME block: bread's
     premise and log_write's, for the inum the scan happens to stop at.
     The scan cannot know it in advance, so the premise is the quantified
     one ([InodeInv.ireg_blocks_ok]). *)
  ireg_blocks_ok inodestart nib cov logstart ->
  (* THE THREE GEOMETRY PREMISES -- see the header *)
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  (* the type actually installs an ALLOCATED record; [fresh_shape] and
     therefore the whole claim need it, and every caller passes a literal *)
  bv_unsigned ty <> 0 ->
  (* THE NO-INODES ARM'S CALLEE, as a hypothesis and not a functor *)
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = dev, a1 = type: the RV64 ABI's sign extension, and [sh s6,0(s3)]
     at +0x94 stores exactly the low sixteen bits of a1 *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (sign_extend' 64 dev : mword 64) ->
  m !!! Regidx (mword_of_int 11 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) -- bread sleeps *)
  eb = true ->
  (* ialloc's cone: bread/brelse ("bcache", 4), log_write ("log", 3), iget
     ("itable", 2, on the tail claim), printk ("pr", 14, the no-inodes
     arm) -- "itable" is the lowest, so one premise there covers the
     whole cone via [locks_below_mono]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the general printk path's two PERSISTENT credentials *)
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the two superblock fields, read and handed straight back *)
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE INODE REGION -- persistent, and the ONLY region resource in this
     contract.  The claim is [InodeRegion.ireg_claim_au] and it takes
     nothing; see the header. *)
  ireg_inv γi γfs inodestart nib -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle and the disk fabric *)
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* TWO slot units: bread's reference is held across log_write, which wants
     one of its own; brelse gives it back *)
  bslots bn 2 -∗
  (* ---- THE ICACHE, exactly as iget takes it ---- *)
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  (* ONE ledger unit for the tail iget; RETURNED on the no-inodes arm *)
  iref_slot -∗
  (* THIS OPERATION'S RESERVATION, IN SET FORM: the one log_write the claim
     runs.  The claimed inum is the SCAN's, so no caller can ever credit the
     block it logs -- the spend is UNCONDITIONAL, which is why this form
     carries no boolean where [wp_iupdate_cred] carries [cru]
     ([CreateBudget.ia_spend] is the literal 1). *)
  log_opS γ (S u) Sb -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (alloc : bool) (kslot : nat) (q : Qp) (inum : mword 32)
    (dn' : dinode),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 2 -∗
      (if alloc
       then (* SUCCESS: iget's postcondition verbatim, at the claimed inum *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ientry kslot
          /\ (kslot < NINODE)%nat
          /\ 0 < bv_unsigned inum < ninodes
          /\ bv_unsigned inum < 16 * Z.of_nat nib
          (* what the claim WROTE: [ialloc_fresh ty], the weakest record a
             claim can promise and exactly what ilock's fill needs *)
          /\ dn' = ialloc_fresh ty
          /\ di_type dn' = ty
          /\ fresh_shape dn'⌝ ∗
         inode_ref kslot q dev inum ∗
         (* THE SET GROWTH IS DETERMINATE, exactly as [wp_iupdate_gen]'s is:
            ialloc logs the claimed inum's HOME BLOCK and nothing else. *)
         log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})
       else (* NO INODES: a0 = 0, the ledger unit back, nothing spent *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗
         iref_slot ∗
         log_opS γ (S u) Sb) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IALLOC.
  (* the CREDITED core (fs-sysfile S5i); [wp_ialloc_sconf] is derived from
     it inside [ProofIalloc], so this is a strengthening and no consumer of
     the sconf form moves. *)
  Parameter wp_ialloc_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_ialloc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                         cov logstart inodestart ninodes nib dev ty u Sb
                         pidv dq dqs dqn m K eb b lks.

  Parameter wp_ialloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname)
      (γpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (u : nat)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_ialloc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty u
                           pidv dq dqs dqn m K eb b lks.
End IALLOC.
