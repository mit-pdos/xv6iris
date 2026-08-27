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
   is here (the bitmap itself is the persistent [BitmapInv.bitmap_inv]:
   the truncate arm frees into it and says nothing), and why the
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

     (B1) iput calls acquiresleep at noff = 1 (itable.lock held), and the
          blocking [SpecAcquiresleep] demands [cpu_own 0 ...].  SETTLED, and
          not by the route this note first took: the truncate arm calls
          [wp_acquiresleep_nb_sconf], the NON-BLOCKING contract, which never
          reaches the sleeping branch at all -- REF-1 says no share of the
          entry's "may hold" right exists, so nobody holds the lock
          (claude-notes/projects/iput-acquiresleep.md).  The earlier plan
          leaned on the sleeping branch being panic("sched locks"); that
          contract is gone, because nothing that CAN sleep may be entered at
          noff != 0.  NOTHING in this statement changes because of it.

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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import FdSlots.
Require Import IcacheRef.
Require Import SchedCtx.
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* iput's own frame is 48 bytes; its deepest callee is bread (40) below
   itrunc's own frame, plus acquiresleep.  Sized like balloc's, one frame
   deeper.

   72 -> 74 (THE SPLICE FINDING, iclaim-ledger.md 6.2).  The REORDERED free
   path calls itrunc from the LOCKED block ([ip_free_locked], iput+0x6c) with
   iput's own six frame slots already pushed, so the cone reserve it must
   carry is [K_itrunc (68) <= K - 6], i.e. K >= 74 -- strictly stronger than
   the 72 the pre-reorder walk needed.  Every landed caller was re-checked
   against the new value; only [K_iunlockput] had to move with it (76 -> 78,
   because ProofIunlockput calls iput at [K - 4]). *)
Notation K_iput := (74%nat) (only parsing).
(* itrunc's two (bitmap block + its closing iupdate) plus iput's own
   iupdate at +0x6c.  SPEND-AT-MOST: the fast path spends nothing. *)
Definition iput_units : nat := 3%nat.

Definition wp_iput_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}

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
    (k : nat) (q : Qp) (inum : mword 32)
    (n : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
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
  (* THE FRESHNESS PREMISE, AT THE LOWEST RANK IPUT (OR ANY CALLEE) TOUCHES:
     "itable" (2) directly, then upward -- "sleep lock" (6) via the
     truncate arm's nested acquiresleep, "log"/"bcache" via itrunc/iupdate.
     One bound covers all of them ([LockRank.locks_below_mono] /
     [locks_below_union_singleton] derive each at its own call site). *)
  locks_below lks "log" ->
  (* PARKING PREMISE -- UNCONDITIONAL.  iput MAY truncate, and no caller
     can know in advance which arm runs, so the bundle is not conditional.
     (Note (B1): under Route B the truncate arm's acquiresleep is the
     NESTED one, which does not park; bread under itrunc/iupdate still
     does, so this premise stays.) *)
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement: [emp] at [eb = true], where iput's own
     acquire mints what the interior sleeps need; the real pair at
     [eb = false], where the caller holds it because the TRAP gave it
     to it.  See claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
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
  (* THE SEALED REGIME, AT THE RUNTIME ARM (iclaim-ledger.md §6′, RULING G;
     SPECIALIZED BY SIMP-1).  iput's free path FREEZES the inode
     ([InodeRegion.ireg_freeze_au] at +0x50), and §2.3's boot-shelter clause
     makes a freezer exhibit the regime it is freezing under.  A RUNTIME
     thread's regime is the sealed [IcacheRef.ireg_open] -- persistent, fired
     once by RULING B between fsinit and kexec("/init") -- so the indexed
     form's "lend a copy, get a copy back" round-trip carried no information
     at all here, and both the [(rg : bool)] binder and the return clause are
     gone: this premise IS [ireg_regime true], and being persistent the
     caller keeps its own copy across the call.  The ONE caller that freezes
     under the other regime is ireclaim, whose [ireg_boot] is exclusive and
     must come back; it reads [wp_iput_gen], which keeps the full indexed
     round-trip. *)
  ireg_open -∗
  (* the entry's sleeplock, over the CHECKOUT TOKEN alone *)
  (* TRACKED: what a holder deposits is a share of somebody's REFERENCE to
     the slot, keyed by the slot rather than by the lock -- which is what
     lets iput, at [ip->ref == 1], prove the lock free instead of blocking
     on it (claude-notes/projects/iput-acquiresleep.md). *)
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                   (slh_tok (icfg_isl k)) -∗
  (* ---- THE REFERENCE BEING DESTROYED, WITH ITS PROVENANCE UNIT ----
     ONE ROW (SIMP-2): [inode_refp] IS this pair -- the reference and the
     unit minted at the iget that created it, copied at any idup of it,
     and SPENT here.  iput's close -- last or not -- surrenders the unit
     in the same ghost step that moves the in-core count, which is what
     [InodeRegion.ireg_ref_ok]'s (R1) demands.  There is no flavour to
     bind: under RULING C' the claim flavour is CONVERTED at ilock's
     ClaimK arm, so the only unit that ever reaches an iput is the plain
     one -- which is why the package's plain form suffices and the
     restatement is a rename ([IcacheRef.inode_refp_spend], by
     [reflexivity]). *)
  inode_refp k q dev inum -∗
  (* ---- itrunc / iupdate's own resources ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  (* the caller's own pid cell (acquiresleep records it) *)
  proc_priv_bare pj pidv Vpr -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* the disk fabric *)
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string <{ disk_res gd pd pav pu }> -∗
  (* three buffer slots: itrunc's indirect arm is what forces three *)
  bslots 3 -∗
  (* this operation's reservation *)
  log_op g n -∗
  (* THE CROSSING IS THE LITERAL [true]: iput sleeps (ilock/itrunc/begin_op),
     so it can return on another hart whatever SIE was doing. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
  (* the trap-CSR complement: [emp] at [eb = true], where iput's own
     acquire mints what the interior sleeps need; the real pair at
     [eb = false], where the caller holds it because the TRAP gave it
     to it.  See claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      (* at most [iput_units] gone, and none gained *)
      ⌜((n - iput_units)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_op g n' -∗
      (* THE LEDGER: one unit back, on EVERY arm.  islot2's live arm holds
         [iref_slots (Pos.to_nat n)]; a non-last close takes n -> n-1 and
         frees one, a last close deletes the slot and frees the one the
         n = 1 arm held.  iget spends exactly one on both ITS arms, so
         iget/iput are a matched pair against the fixed IREFSLOTS supply. *)
      iref_slot -∗
      (* ...AND NOTHING ELSE.  The regime does NOT come back: the runtime
         arm's is persistent, so the caller never gave it up (SIMP-1).  The
         reference is consumed; xv6's iput returns void and the caller's
         pointer is dead. *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CREDITED SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 4b)        *)
(*                                                                        *)
(*  WHAT [freed] TURNED OUT TO BE.  GR-2a left open whether iput's post    *)
(*  must expose the [freed] boolean of [CreateBudget.ip_spend crb cru      *)
(*  freed], either existentially or by two-arming the budget clause the    *)
(*  a bitmap set used to be two-armed.  IT MUST DO NEITHER, and the reason *)
(*  is that an existential [freed] is VACUOUS: [ip_spend _ _ false = 0 <=  *)
(*  ip_spend _ _ true], so [∃ freed, n - ip_spend crb cru freed <= n']     *)
(*  is satisfied by [freed := true] whatever happened, i.e. it says        *)
(*  exactly what the unconditional worst case says and no caller can       *)
(*  extract more.  And two-arming it would be USELESS anyway, because no   *)
(*  caller can know in advance which arm runs -- the same fact that makes  *)
(*  the parking premise unconditional.                                    *)
(*                                                                        *)
(*  So the spend is stated at the WORST CASE, unconditionally, and that    *)
(*  is enough: at [crb = cru = true] the worst case is ZERO, which is      *)
(*  exactly what create's FAIL arm needs of the [iunlockput] that actually *)
(*  frees ([CreateBudget.ip_spend true true true = 0]).                    *)
(*                                                                        *)
(*  THE NEED DOES NOT MOVE.  It is still [iput_units], so                  *)
(*  [CreateBudget]'s arms -- which are all stated at [ip_need] -- are      *)
(*  unaffected.  (The credited arms could honestly ask for as little as    *)
(*  [1 + ip_spend crb cru true], but nothing needs that and keeping the    *)
(*  premise fixed keeps the ledger's theorems verbatim.)                   *)
(* ===================================================================== *)

(* what iput spends when it DOES free: itrunc's bitmap unit (unless the op
   already logged that block) plus the two flushes, of which iput's own
   always absorbs -- itrunc's post hands out [IBLOCK inum inodestart ∈ Sb']
   determinately, so iput's [ip->type = 0] iupdate runs credited for free.
   Definitionally [CreateBudget.ip_spend crb cru true].

   THE THIRD CREDIT IS THE GROUP ONE (fs-log.md §G.20 stage 2).  [cru] is
   the OWN-SET claim "this op has already logged [IBLOCK inum inodestart]",
   which a WALKER cannot make -- it never logged the block, some other
   transaction-mate did.  [crz] is the same unit bought with a GROUP
   witness instead ([InodeRegion.nlz_obs], cashed by [ireg_obs_use] into
   [LogInv.log_credit]'s right disjunct), and it buys exactly the same
   term: the unit itrunc's TAIL FLUSH would otherwise spend.  So the two
   enter the figure disjunctively and a [crz] caller's freeing iput spends
   the BITMAP unit and nothing else. *)
(* THE BITMAP UNIT, AS A REPORT (fs-log.md §G.22, G-4c).  [crb] is what the
   caller CLAIMS on the way in; [w] is what the call DID -- "the bitmap
   block was logged by this iput" -- and the post pairs it with
   [bmapstart ∈ Sb'], because spending that unit and logging that block are
   one event.  A walker needs exactly this pairing: [crb] tells level i+1
   nothing unless level i reported whether it paid.  At [crb = true] the
   report is always [false] (itrunc's paid disjunct pins the level), so a
   credited caller never sees its own credit spent back at it. *)
Definition ip_bm (w : bool) : nat := if w then 1%nat else 0%nat.

Definition ip_spend_w (w cru crz : bool) : nat :=
  (ip_bm w + (if orb cru crz then 0%nat else 1%nat))%nat.

Definition wp_iput_gen_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}

    (gs : list gname) (j : nat) (gl : gname)
    (gu : uart_names) (gd : disk_names) (gk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names)
    (gtl : gname)
    (gil gisl : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (k : nat) (q : Qp) (inum : mword 32)
    (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
    (pidv : mword 32) (dq dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) (rg : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iput in
  let ip : mword 64 := ientry k in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iput <= K)%nat ->
  (k < NINODE)%nat ->
  (* the two absorption credits, travelling to itrunc unchanged *)
  (crb = true -> bmapstart ∈ Sb) ->
  (cru = true -> IBLOCK inum inodestart ∈ Sb) ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  cov_below cov size ->
  (iput_units <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  (* THE FRESHNESS PREMISE -- see [wp_iput_sconf_body]. *)
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrow cn gfs gi cov logstart k -∗
  ireg_inv gi gfs inodestart nib -∗
  (* THE SEALED REGIME, BORROWED AND RETURNED (iclaim-ledger.md §6′, RULING G).
     iput's free path FREEZES the inode ([InodeRegion.ireg_freeze_au] at
     +0x50), and §2.3's boot-shelter clause makes a freezer exhibit the regime
     it is freezing under: the sealed [IcacheRef.ireg_open] a RUNTIME thread
     carries (persistent, fired once by RULING B between fsinit and
     kexec("/init")), or the exclusive [ireg_boot] the pre-userspace thread
     carries instead.  It is BORROWED, not consumed: the off-lock deposit at
     +0xba retires the freeze and lifts the disjunction back out of the slot's
     own clause ([EscrowDeposit.ireg_free_deposit_au]), and the two close arms
     never spend it at all -- so it comes back on EVERY arm, below.  A runtime
     caller passes [iLeft] on its persistent copy and may discard what comes
     back; ireclaim, the one boot caller, lends [ireg_boot] and needs it
     returned to run its next loop iteration. *)
  ireg_regime rg -∗
  (* TRACKED: what a holder deposits is a share of somebody's REFERENCE to
     the slot, keyed by the slot rather than by the lock -- which is what
     lets iput, at [ip->ref == 1], prove the lock free instead of blocking
     on it (claude-notes/projects/iput-acquiresleep.md). *)
  is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                   (slh_tok (icfg_isl k)) -∗
  (* the reference being destroyed, WITH its provenance unit: ONE ROW
     (SIMP-2), exactly as in the [_sconf] body above. *)
  inode_refp k q dev inum -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string <{ disk_res gd pd pav pu }> -∗
  bslots 3 -∗
  (* THE GROUP CREDIT (fs-log.md §G.18's chain, §G.21's tier).  At
     [crz = false] this is [emp] and every landed caller passes nothing.
     At [crz = true] it is the walker's persistent, inum-keyed observation
     -- "at epoch [e0], inside MY still-open op, this inum's record had a
     NONZERO nlink" -- plus the two ambient ties [InodeRegion]'s three
     mixed contracts carry ([IcacheRef]'s header: the region's [log_names]
     and its first block are AMBIENT, so a threaded [g]/[inodestart] meets
     them only through a pure equation, true at boot by [icfg_alloc]).
     iput cashes it with [InodeRegion.ireg_obs_use] at the record whose
     nlink its own +0x44 test found ZERO, and hands the resulting
     [LogInv.log_credit] to itrunc's tail flush. *)
  (if crz then nlz_obs (bv_unsigned inum) e0 ∗ ⌜g = icfg_log⌝ ∗
                ⌜inodestart = icfg_ist⌝
   else emp) -∗
  (* the reservation, EPOCH-NAMED (§G.20's asymmetry: [log_opSe] in,
     [log_opS] out -- nothing above log_write compares epochs).  [e0] is the
     op's birth epoch, the one the credit above is ordered against. *)
  log_opSe g n Sb e0 -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      proc_priv_bare pj pidv Vpr -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      bslots 3 -∗
      (* the set only GROWS, and at most the credited worst case is gone *)
      ⌜Sb ⊆ Sb'⌝ -∗
      (* THE PAID-BITMAP REPORT (G-4c): [w] is "this call spent the bitmap
         unit", and it comes with the membership that makes a walker's next
         level able to claim [crb := true]. *)
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      (* ...and a CREDITED caller is never charged its own credit back
         (fs-log.md §G.25): at [crb = true] the report is [false], which is
         what makes a walk's next level FREE and not merely bounded. *)
      ⌜crb = true -> w = false⌝ -∗
      ⌜((n - ip_spend_w w cru crz)%nat <= n')%nat /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      iref_slot -∗
      (* RULING G: the regime comes back, on every arm (see the premise). *)
      ireg_regime rg -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IPUT.
  Parameter wp_iput_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (q : Qp) (inum : mword 32)
      (n : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_iput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                          cov logstart bmapstart inodestart nib size dev
                          k q inum n pidv dq dqb dqs m K eb b lks Vpr.
  (* the credited set-form contract; [wp_iput_sconf] is this at
     [crb := cru := crz := false], derived at the [log_op] existential's own
     witness ([ip_spend_w w false false <= 2], and iput's own flush is the
     third unit [iput_units] counts) and at the birth epoch
     [LogInv.log_opS_named] opens; the paid-bitmap report is dropped. *)
  Parameter wp_iput_gen :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (k : nat) (q : Qp) (inum : mword 32)
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate) (rg : bool),
      wp_iput_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                       cov logstart bmapstart inodestart nib size dev
                       k q inum n Sb crb cru crz e0 pidv dq dqb dqs m K eb b lks Vpr rg.
End IPUT.
