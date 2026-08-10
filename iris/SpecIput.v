(* SpecIput.v -- the public interface of iput.

     void iput(struct inode *ip) {
       acquire(&itable.lock);
       if(ip->ref == 1 && ip->valid && ip->nlink == 0){
         // inode has no links and no other references: truncate and free.
         acquiresleep(&ip->lock);
         release(&itable.lock);
         itrunc(ip);
         ip->type = 0;
         iupdate(ip);
         ip->valid = 0;
         releasesleep(&ip->lock);
         acquire(&itable.lock);
       }
       ip->ref--;
       release(&itable.lock);
     }

   ONE module type, [IPUT], proven by [ProofIput.v] and instantiated with no
   axiom at all by [LinkIput.v].  (Until C6b there were two: an older
   [emp]-shaped statement written when there was no inode model, bridged to
   the callers by an [Axiom] in [LinkIputCompat.v].  Both are gone -- the
   callers now carry real references, so the frozen statement had no
   consumers left.  git history has it if it is ever wanted.)

   ==== WHAT THE CONTRACT SAYS ==========================================

   iput DESTROYS one inode reference: [IcacheRef.inode_ref k q
   dev inum] goes in and nothing comes back but one [iref_slot], the
   ledger unit that makes iget/iput a matched pair against the fixed
   IREFSLOTS supply.  On the last close of an unlinked inode it also
   TRUNCATES -- which is why the whole log/bitmap/inode-region environment
   is here, why the [bitmap_res] comes back at a SMALLER [used'] (the
   truncate arm freed blocks; the two close arms did not), and why the
   budget clause is a spend-at-most interval: [log_op] moves only through
   [LogInv.log_spend_step] against the ledger authority inside log.lock,
   and iput never takes that lock, so it cannot hand a surplus back.

   iput SLEEPS -- acquiresleep on the inode, and bread underneath itrunc /
   iupdate -- so it threads the running-process bundle exactly as
   SpecBalloc.v / SpecIupdate.v do: procs_inv / p_pid, the disk fabric,
   three buffer slots, and the parking premise [eb = true].  The bundle is
   UNCONDITIONAL: xv6's iput always MAY truncate and no caller can know in
   advance which arm runs.  It enters and returns at noff 0.

   Two below-icache blockers were found by tracing the proof forward and
   both are ruled on (design §13.12):

     (B1) iput calls acquiresleep at noff = 1 (itable.lock held), and
          SpecAcquiresleep demands [cpu_own 0 ...].  ROUTE B adopted: the
          sleeping branch is panic("sched locks"), so it DIVERGES and
          [panic_wp_any] -- which iput already carries -- closes it.
          LANDED (ef035525): the truncate arm calls
          [wp_acquiresleep_nested_sconf] at n := 0.  NOTHING in this
          statement changes because of it.

     (B2) SpecItrunc's [forall i < MAXFILE, length (data i) = BSIZE] is not
          derivable: [data] is EXISTENTIAL inside [ic_loaded], and
          [inode_ok] pinned lengths only at HOLES ([blk_holes_zero]).
          FIXED AND LANDED (a791194a): [InodeInv.inode_sized] IS
          [inode_ok]'s seventh conjunct, so iput derives the premise from
          the checked-out bundle at the call site.  NO premise appears
          below for it, and SpecItrunc is unchanged.                      *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
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
Require Import FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* iput's own frame is 48 bytes; its deepest callee is bread (40) below
   itrunc's own frame, plus acquiresleep.  Sized like balloc's, one frame
   deeper. *)
Definition K_iput : nat := 60%nat.

(* itrunc's two (bitmap block + its closing iupdate) plus iput's own
   iupdate at +0x6c.  SPEND-AT-MOST: the fast path spends nothing. *)
Definition iput_units : nat := 3%nat.

Definition wp_iput_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)          (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names)                                   (* the icache's names  *)
    (gtl : gname)                                     (* itable.lock         *)
    (gil gisl : gname)                                (* ip->lock            *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (k : nat) (q : Qp) (inum : mword 32)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iput <= K)%nat ->
  (* ENTRY BY SLOT -- a0 is the entry address, and [ientry_inj] is what
     makes the 64-bit pointer and the slot the same thing *)
  (k < NINODE)%nat ->
  (* the covered range's block-number bounds, and the log's own storage *)
  log_geom_ok cov logstart ->
  (* --- itrunc's geometry, threaded verbatim (SpecItrunc.v) --- *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the inum is one the inode REGION covers: ireg_read / ipool_acc *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* bfree's per-slot range fact, via IcacheInv.blkmap_slot_inrange *)
  cov_below cov size ->
  (* enough budget for the truncate-and-free arm *)
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* PARKING PREMISE -- UNCONDITIONAL.  iput MAY truncate, and no caller
     can know in advance which arm runs, so the bundle is not conditional.
     (Note (B1): under Route B the truncate arm's acquiresleep is the
     NESTED one, which does not park; bread under itrunc/iupdate still
     does, so this premise stays.) *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  (* ---- THE ICACHE'S PERSISTENT SET ---- *)
  (* the itable spinlock over the v2 resource; §13.11's trailing device *)
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  (* the [ref] words *)
  itable_inv -∗
  (* THIS slot's escrow -- iput knows its slot, so unlike iget it needs no
     ic_escrows family *)
  ic_escrow cn gfs gi cov logstart k -∗
  (* the inode region *)
  ireg_inv gi gfs inodestart nib -∗
  (* the entry's sleeplock, over the CHECKOUT TOKEN alone *)
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* ---- THE REFERENCE BEING DESTROYED ---- *)
  inode_ref k q dev inum -∗
  (* ---- itrunc / iupdate's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* the caller's own pid cell (acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  (* three buffer slots: itrunc's indirect arm is what forces three *)
  bslots bn 3 -∗
  (* this operation's reservation *)
  log_op g n -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (used' : gset Z),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE BITMAP IS TWO-ARMED (the C2 finding, predicted for exactly
         this contract): the truncate arm returns [used minus bm_blocks bm]
         at the ESCROW's existential [bm], the close arms return [used]
         untouched.  An unconditional record would be unprovable. *)
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      bslots bn 3 -∗
      (* at most [iput_units] gone, and none gained *)
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (* THE LEDGER: one unit back, on EVERY arm.  islot2's live arm holds
         [iref_slots (Pos.to_nat n)]; a non-last close takes n -> n-1 and
         frees one, a last close deletes the slot and frees the one the
         n = 1 arm held.  iget spends exactly one on both ITS arms, so
         iget/iput are a matched pair against the fixed IREFSLOTS supply. *)
      iref_slot -∗
      (* ...AND NOTHING ELSE.  The reference is consumed; xv6's iput
         returns void and the caller's pointer is dead. *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IPUT.
  Parameter wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                          cov logstart bmapstart inodestart nib size dev used
                          k q inum n pidv dq dqb dqs m K eb C b.
End IPUT.
