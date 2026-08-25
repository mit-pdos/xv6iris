(* SpecIdup.v -- the public interface of idup(), stated over the REAL inode
   cache and no longer assumed.

     struct inode *idup(struct inode *ip) {
       acquire(&itable.lock);
       ip->ref++;
       release(&itable.lock);
       return ip;
     }

   @ KernelSyms.idup = 0x800031a6, 54 bytes (ilock begins at 0x800031dc):
   a 32-byte ra/s0/s1 frame around one acquire / [ip->ref++] / release.  No
   branch, no sleep, and no callee besides the lock pair -- idup is the
   SMALLEST function that exercises the whole icache design end to end,
   which is why it is proven before iget and iput.

   ---- WHAT CHANGED, AND WHY IT BROKE NOTHING --------------------------

   This contract used to be an [Axiom] in [LinkIdup.v], stated over
   [ProcInv.cwd_ref] -- i.e. over [FileInv.inode_ref], which is literally
   [emp].  The header then explained that nothing about [ip->ref] or
   [itable.lock] was statable against real code because no inode model
   existed.  [IcacheInv.v] is that model, so the excuse is gone.

   Restating it was free because idup HAS NO CALLERS: nothing in the tree
   applies [wp_idup_sconf] (iput, by contrast, has two).  The old
   postcondition could not survive the change in any case -- it returned
   [cwd_ref ip ∗ cwd_ref ip], i.e. fraction 1 twice, which is satisfiable
   only while the predicate is [emp].

   ---- IT TAKES A SHARE, AND HANDS THE SHARE BACK BESIDE A NEW REFERENCE ----

   [ip->ref++] does not need a reference to start from.  It needs a claim
   that the entry cannot be freed underneath it, and a count-0 SHARE
   ([IcacheRef.inode_shr]) is already that: it carries a positive slice of
   the slot's liveness unit, which blocks the last close
   ([IcacheInv.live_whole_share_absurd]), so the entry stays.

   WHAT THE INCREMENT DOES IS NOT AN UPGRADE, and this is where our algebra
   parts company with the natR version this contract was ported from.  Under
   [natR] a share IS authority mass, so "share (q,0) becomes reference (q,1)"
   conjures nothing and idup can hand back one reference at the share's own
   fraction.  Under [positiveR] the identity budget forbids it: the table's
   retained share is [1/2 - qt] against the authority's [qt] (§13.1b), so a
   new count fragment at [s] would have to be matched by [s] of identity out
   of the TABLE -- and the share's own [s] is already spoken for, as the hole
   in its parent's slice.  A share therefore cannot BECOME a reference
   (design §14.7(3), and [IcacheInv.iref_upgrade_store_au]'s header).

   So the share RIDES THROUGH UNTOUCHED and the new reference is minted from
   the table's retained share, exactly as iget's cache-hit arm mints one --
   which is why its fraction is EXISTENTIAL here (it is a slice of a [qt] no
   caller can name) where the share's is the caller's own.  The old shape
   returned two [q/2] references and cost every caller a factor of two on
   every call; this one costs the caller nothing at all -- kfork's parent
   sheds a share, gets it back, and its cwd fraction is the fraction it came
   in with.

   [(k < NINODE)] is a premise where it used to be derived.  [iref_lookup]
   read the slot's liveness off a COUNT fragment, which names its own slot in
   [dom M]; a share has no count fragment, so the share-side twin
   ([IcacheInv.iref_share_lookup_au]) takes the range as a hypothesis.  Every
   caller has it for free -- [ProcInv.cwd_ref] carries it.

   ---- THE TWO PREMISES A READER SHOULD LOOK AT TWICE -------------------

   [is_itable2] is the itable spinlock over the v2 resource (design §13.2/
   §13.3: the pure slot->inum map [ci] and the uncached POOL ride inside it
   alongside the authority half).  idup moves only the [ref] word and [M],
   so both of those ride through its critical section untouched -- the flip
   from [is_itable] is a re-framing, not a re-proof (§13.4).

   It is instantiated AT THE CALLER'S [dev], because the table is
   single-device (§13.11): the region and the pool are inum-keyed, so
   "cached" has to be decidable from inums alone, which holds exactly when
   every cached entry names one device -- [BioInv]'s [bv_dev V] for the
   inode cache.  idup neither reads nor writes an identity cell, so for IT
   the parameter is pure pass-through; it is iget's recycle that has to
   re-establish the clause, and iget's scan that would otherwise be unable
   to.  The caller supplies the same [dev] its reference already names, so
   this costs nothing at any call site.

   [itable_inv γ] is where the [ref] WORDS live -- not in [itable.lock]'s
   resource.  idup writes one while holding the lock, so it opens the
   invariant and joins the two halves of the authority; that the halves meet
   only under the lock is exactly what makes [lw; addiw; sw] atomic in the
   proof.  See [IcacheInv.v]'s header for why the words cannot live in the
   lock (ilock and iunlock read them holding nothing).

   [iref_slot] is what makes the increment SAFE, and it is not bookkeeping.
   [ip->ref++] is unconditional, so it cannot re-establish "the count is
   still an int" on its own -- the missing step is false at 2^31 - 1 and no
   axiom may assert it ([IrefSlots.v]'s header, and [SpecFiledup.v]'s before
   it).  A unit of the FIXED supply is evidence that the system has an
   actual place to keep the new reference, and it is the caller's job to
   bring one, exactly as filedup's caller brings an [fd_slot].

   The SIE/[cpu_own] bookkeeping is [SpecFiledup.v]'s, and for the same
   reason: a fully-nested acquire/release leaves [n], [eb] and the SIE
   index [b] as they came in.  Unlike filedup's, this is now DERIVED from
   the two lock contracts rather than asserted.

   ---- WHY THIS CONTRACT WIDENED IN INCREMENT IVe -----------------------

   iclaim-ledger.md §3.3 approved widening [SpecIget], [SpecIdup] and
   [SpecIput] with [ireg_inv] + the index params; IIIe executed that for the
   other two and idup's was BLOCKED on the doc's own OPEN(2.6b).  §3.19's
   RULING closes it and this increment executes the widening, so the
   paragraph that used to stand here (a full account of the block) is
   superseded.  The short version of what it said, because it is still the
   reason this contract's shape is what it is:

     [ip->ref++] is a ledger move, and RULING A (§3.1, A-AUs) gave every
     UP-count the same premise -- a borrowed [IgetLic.iname γi γfs inum l].
     idup's TWO call sites are both [idup(p->cwd)] (ProofKforkB4:365 and
     ProofNamex:5660) and NEITHER can produce a licence at ANY of the five
     constructors: [LinkedL] wants an [ipaid], [HeldL] and the region-side
     [*_alloc] lemmas want a [dinode_at] (idup reads no dinode and neither
     does its caller), [ClaimL] wants an [iclaim], [RootL] wants the inum to
     BE the root, [BufL] is boot-only -- and a cwd is not even [nlink <> 0],
     since xv6 permits unlinking a process's cwd.  The licence-free
     ARITHMETIC route ([IcacheInv.ireg_icnt_acc]) does not do it either: it
     refutes the two frozen phases from [ireg_frz_ok]'s pins ([FrzPost => n
     = 0], [FrzPre => n = 1]) and so needs [2 <= n], while a cwd held by one
     process sits at [n = 1] exactly -- the one value [FrzPre] admits.

   WHAT CLOSED IT is §2.6b's own recommendation, landed as RULING A⁗'s
   frozen park (§3.16): the freeze arm PARKS the dying reference's liveness
   slice and the escrow arm's half inside [IcacheEscrow.islot2]'s live arm,
   where a foreign idup taking the itable lock finds them.  So idup's mover
   is now [IcacheInv.iref_upgrade_mir_store_au] -- the licence-free
   up-count -- and what it presents in place of a licence is the LOCK's own
   [false] mirror half, decided by [IcacheInv.frz_park_shr_off] out of the
   caller's OWN SHARE.  [inode_shr] is enough; no licence, no REF-1, no
   count restriction.

   THE PRICE, AND IT IS EXACTLY SpecIget's (§3.19(d), the in-campaign
   precedent): the mover's up-count carries the ledger's [icnt] half, whose
   other half lives in [InodeRegion.ireg_slot], so this contract takes
   [ireg_inv γi γfs inodestart nib] and the [inodestart] binder that goes
   with it -- and, because [ireg_inv]'s own type has [Xv6Cameras.logG] as a real
   instance argument (its [ireg_ep] carries a [log_epoch_lb], §G.13/§G.17),
   the Context gains [!logG Σ].  The handle is PERSISTENT, so it costs a
   caller a frame and nothing else, and the region open is GHOST-ONLY: idup
   reads no dinode, and the only column that moves is [icnt].

   WHAT THIS CONTRACT DELIBERATELY DOES *NOT* TAKE is SpecIget's
   [bv_unsigned inum < 16 * Z.of_nat nib].  iget needs it as a premise
   because its recycle arm asks for an inum that is by construction NOT
   cached, so no table clause can speak about it.  idup's inum IS cached --
   the caller's share names a live slot -- so the bound comes out of
   [IcacheEscrow.ic_ci_wf]'s third clause inside the proof, off the very
   [ci !! k] the mint already reads.  Every caller would have had it (both
   sites hold [IcacheRef.inode_held]'s), but at [icfg_nib] rather than at
   this contract's generic [nib], and deriving it costs the proof one
   [destruct].                                                             *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import LockRank.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.

(* idup's own frame is 4 slots (addi sp,sp,-32); acquire/release want 10
   below that -- filedup's [K] budget exactly, and for the same frame. *)
Notation K_idup := (14%nat) (only parsing).
Definition wp_idup_sconf_body
    `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
    (k : nat) (dev : mword 32)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64)
    (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.idup in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (K_idup <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (k < NINODE)%nat ->
  (* a0 = ip, and a [struct inode *] IS its slot: [ientry_inj]. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ientry k ->
  (* THE PURE TIE, and it rides exactly as [FsSyscalls.sysc_fs_env]'s do:
     the package below is POINTER-keyed, so its device is the cache's own
     ([IcacheRef.icfg_dev], design §13.11's single-device pin), while the
     itable handle above is stated at whatever [dev] the caller names.
     Every caller has this equation already. *)
  dev = icfg_dev ->
  (* THE FRESHNESS PREMISE: idup acquires and releases [itable.lock]
     internally (balanced -- [lks] is unchanged across the whole call), so
     the caller must already hold only locks BELOW "itable"'s rank. *)
  locks_below lks "itable" ->
  sie_cap_gpr KT1 m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_itable2 γl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  (* THE INODE REGION, and GHOST-ONLY (header, §3.19): the [ref++] carries
     the ledger's [icnt] half and the region owns the other one, so the
     mover ([IcacheInv.iref_upgrade_mir_store_au]) opens [↑iregN] around the
     same instruction.  No dinode is read.  Persistent, so it costs a caller
     a frame and nothing else. *)
  ireg_inv γi γfs inodestart nib -∗
  (* THE precondition that makes [ip->ref++] safe -- see the header. *)
  iref_slot -∗
  (* ---- ONE ROW IN, TWO ROWS OUT (SIMP-2) ---------------------------
     STATED OVER [IcacheRef.inode_held] -- the POINTER-keyed package --
     because that is what idup's two callers already hold: kfork's parent
     block and namex's cwd both carry [inode_held] and, before SIMP-2,
     had to open it, shed a share by [inode_ref_shed], hand the share and
     the unit across, and then re-assemble TWO packages out of six
     returned rows.  All of that was bookkeeping the contract could do
     once: the carve ([IcacheRef.inode_refp_carve]) and the gather are
     equivalences, so moving them inside costs nothing and deletes the
     [s] / [dev] / [inum] binders along with four rows.

     Why the mover still only needs a share: [ip->ref++] does not need a
     reference to start from, only a claim that the entry cannot be freed
     underneath it, and a count-0 slice of the liveness unit is already
     that (see the header).  The share is carved out of THIS package, the
     count fragment stays with the short parent, and the two rejoin before
     the return -- so the caller's fraction is the fraction it came in
     with, exactly as before.

     Why the second package is a package and not a bare reference: the
     mint is SELF-PAYING (item 7a-wire, §5''.3's step 3).  The unit inside
     the argument buys the two side conditions
     [InodeRegion.ireg_ref_ok_mint] owes -- allocatedness at either
     flavour, and [c = None] at the plain one -- so idup needs no licence,
     which is what §3.11's wall said it could never have; and the COPY is
     minted at the PARENT's flavour, which is what keeps (R3) true.  Under
     RULING C' that flavour is the plain one at every rest home, so both
     packages that leave are [inode_refp]-shaped and iput-ready. *)
  inode_held (ientry k) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr
      /\ mr !!! Regidx (mword_of_int 10 : mword 5) = ientry k ⌝ -∗
    (* the caller's own package, whole and at its own fraction *)
    inode_held (ientry k) -∗
    (* ...and the new one, minted from the table's retained share at a
       fraction only the table knows -- which [inode_held] hides anyway. *)
    inode_held (ientry k) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IDUP.
  Parameter wp_idup_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (k : nat) (dev : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string),
      wp_idup_sconf_body γl cn γfs γi cov logstart inodestart nib k dev
                         m n eb p K b lks.
End IDUP.
