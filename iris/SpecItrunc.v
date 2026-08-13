(* SpecItrunc.v -- the public interface of itrunc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void itrunc(struct inode *ip) {
       int i, j;
       struct buf *bp;
       uint *a;

       for (i = 0; i < NDIRECT; i++) {
         if (ip->addrs[i]) {
           bfree(ip->dev, ip->addrs[i]);
           ip->addrs[i] = 0;
         }
       }

       if (ip->addrs[NDIRECT]) {
         bp = bread(ip->dev, ip->addrs[NDIRECT]);
         a = (uint * )bp->data;
         for (j = 0; j < NINDIRECT; j++) {
           if (a[j])
             bfree(ip->dev, a[j]);
         }
         brelse(bp);
         bfree(ip->dev, ip->addrs[NDIRECT]);
         ip->addrs[NDIRECT] = 0;
       }

       ip->size = 0;
       iupdate(ip);
     }

   148 bytes, 53 instructions.  Two loops -- twelve direct entries, then the
   256 entries of the indirect block, read through a bread/brelse pair --
   followed by the indirect block's own free, [ip->size = 0] and the flush.
   Note the compiler saves s4 CONDITIONALLY: [sd s4,0(sp)] sits at +0x50,
   inside the indirect arm, and is restored at +0x90, so the direct-only
   path never touches it.

   THE CONTRACT.  itrunc empties the inode: [inode_map] comes back at
   [InodeInv.bm_empty], every block the map named goes back to the free pool
   ([bitmap_res] loses exactly [bm_blocks bm]), the size is zeroed and the
   whole thing is flushed by the tail call to iupdate.  The postcondition is
   stated at the CLOSED value [bm_empty] rather than at "some map whose
   slots are all zero" so that iput -- the only caller -- needs no reasoning
   to see the inode names nothing.

   THE BUDGET IS THE INTERESTING PART, and it is why the log ledger had to
   change first.  itrunc calls bfree up to NDIRECT + NINDIRECT + 1 = 269
   times and then iupdate once.  Charging a unit per log_write -- the old
   always-consume accounting -- would demand 270 against a MAXOPBLOCKS of
   10, which no caller could supply.  But [FSSIZE = 2000 < BPB = 8192] means
   there is exactly ONE bitmap block, so all 269 frees hit it and the log
   ABSORBS every one after the first: the true cost is 2, one bitmap block
   and one inode block.  The credited arms of log_write and bfree
   ([LogInv.log_opS], [SpecBfree.wp_bfree_gen]) are what let that be stated.

   [bm_paid] below is the shape the loops carry.  It says "the bitmap
   block's log slot is paid for, and u units remain for everything else",
   as a disjunction over whether the payment has happened yet -- and it is
   IDEMPOTENT under bfree: the unpaid arm spends its spare unit and becomes
   paid, the paid arm presents its credit and absorbs.  So itrunc's loop
   invariant is literally [bm_paid γ bmapstart 1] -- one unit held back for
   iupdate -- unchanged across all 269 calls, with no data-dependent case
   split on which free happened to be the first.

   SPEND-AT-MOST-TWO, AT-LEAST-ONE.  The exit is [∃ u', u <= u' <= S u], the
   same shape bmap uses: iupdate always runs, so one unit is certainly
   spent; the bitmap unit is spent only if the inode named any block at all.

   itrunc SLEEPS (bread, and bfree's own bread), so it threads the full
   running-process bundle exactly as SpecBfree.v / SpecIupdate.v do.  It
   enters and returns at noff 0.

   NOT ITS BUSINESS: ip->lock.  The C comment says "Caller must hold
   ip->lock", and the caller does -- iput takes the sleeplock before
   calling.  itrunc itself performs no locking, so the contract simply takes
   the inode's resources directly, exactly as iupdate's does. *)
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
Require Import PanicStub.
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
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* itrunc's own frame is 48 bytes (6 slots) -- [addi sp,sp,-48] at +0x00,
   ra/s0/s1/s2/s3 pushed, and s4 conditionally at +0x50.  Its deepest
   callee is bfree (44); bread wants 40, brelse 26 and iupdate 44. *)
Definition K_itrunc : nat := 50%nat.

(* THE TRUNCATED RECORD: the same inode with its size zeroed and its addrs
   emptied.  [type], [major], [minor] and [nlink] are untouched -- itrunc
   frees blocks, it does not delete the inode; zeroing the type is iput's
   job, one level up.  The addrs field is set to [bm_cells bm_empty] rather
   than left alone because iupdate's premise ties it to the map, and the map
   itrunc hands back is [bm_empty]. *)
Definition di_trunc (d : dinode) : dinode :=
  MkDinode (di_type d) (di_major d) (di_minor d) (di_nlink d)
           (bv_0 32) (bm_cells bm_empty).

Lemma di_trunc_addrs (d : dinode) : di_addrs (di_trunc d) = bm_cells bm_empty.
Proof. reflexivity. Qed.

Lemma di_trunc_wf (d : dinode) : dinode_wf (di_trunc d).
Proof.
  rewrite /dinode_wf /di_trunc /bm_cells /bm_empty. cbn [di_addrs bm_dir bm_ind].
  rewrite length_app length_replicate /=. reflexivity.
Qed.

Section ItruncSpec.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* "THE BITMAP BLOCK'S LOG SLOT IS PAID FOR, and u units remain for
     everything else."

     The left disjunct is the paid state: the op holds a credit for
     [bmapstart] and [S u] units.  The right is the unpaid state: no credit,
     but one extra unit in reserve to buy one.

     IDEMPOTENT UNDER bfree, which is the whole point.  From the unpaid
     state bfree's uncredited arm spends the spare unit, records the bitmap
     block in the op's set, and lands in the paid state; from the paid state
     bfree's credited arm presents the credit, log_write absorbs, and the
     unit comes back -- paid again.  So a loop that frees an unknown number
     of blocks carries this ONE assertion and never case-splits on how many
     it has freed so far. *)
  Definition bm_paid (γ : log_names) (bmapstart : Z) (u : nat) : iProp Σ :=
    ((∃ Sb : gset Z, ⌜bmapstart ∈ Sb⌝ ∗ log_opS γ (S u) Sb)
     ∨ (∃ Sb : gset Z, log_opS γ (S (S u)) Sb))%I.

  (* entering the loops: two units and no credit yet *)
  Lemma bm_paid_intro γ bmapstart u :
    log_op γ (S (S u)) -∗ bm_paid γ bmapstart u.
  Proof.
    iIntros "H". rewrite /log_op. iDestruct "H" as (Sb) "H".
    iRight. iExists Sb. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE SET-INDEXED TWIN (fs-sysfile GR-2a's 4a design)                 *)
  (*                                                                      *)
  (*  [bm_paid] above is set-form but with the set EXISTENTIAL on both     *)
  (*  disjuncts, so the caller's [Sb] is forgotten at [bm_paid_intro] and  *)
  (*  is not recoverable at [bm_paid_elim].  That is exactly the shape     *)
  (*  GR-2a finding 1 rules out for a gen contract: [log_opS] is an        *)
  (*  exclusive ghost_map element with no auth-monotone shadow, so a set   *)
  (*  handed back at an unrelated existential relates to nothing.          *)
  (*                                                                      *)
  (*  Indexing by the ENTRY set stops the forgetting.  [Sb] is CONSTANT    *)
  (*  across both of itrunc's loops -- it is what the caller had on the    *)
  (*  way in, never the running set, which stays the existential [Sb'] --  *)
  (*  so the retrofit is one extra parameter on the two loop states,       *)
  (*  THREADED rather than proven.                                        *)
  (*                                                                      *)
  (*  THE [crb] GUARD ON THE UNPAID DISJUNCT IS LOAD-BEARING.  A caller    *)
  (*  that enters ALREADY PAID ([crb = true]) never had the spare unit at  *)
  (*  all, and the paid disjunct is absorbing -- [bm_paidS_use] returns to *)
  (*  it from both arms -- so at [crb = true] the level is pinned to       *)
  (*  [S u] all the way to the tail.  Without the guard the elim below     *)
  (*  could only offer the loose [n <= S (S u)], and create's FAIL arm,    *)
  (*  which needs [iunlockput] to spend EXACTLY ZERO while actually        *)
  (*  freeing ([CreateBudget.ip_spend crb cru true = 0] at [crb = cru =    *)
  (*  true]), would not close.                                            *)
  (*  AND THE BIRTH EPOCH IS THREADED THROUGH IT (fs-log.md §G.20).  [e0]   *)
  (*  is CONSTANT across both loops for exactly the reason [Sb] is: it is   *)
  (*  what the caller had on the way in, and nothing an open operation can  *)
  (*  do moves it.  Without it the tail flush could not present a GROUP     *)
  (*  credit at all -- a credit is a claim at a NAMED epoch, and every      *)
  (*  bfree in the loops would otherwise close the existential (§G.20's     *)
  (*  blocker).  Threaded, not proven: one more parameter on the two loop   *)
  (*  states.                                                              *)
  Definition bm_paidS (γ : log_names) (bmapstart : Z) (crb : bool)
      (u : nat) (Sb : gset Z) (e0 : nat) : iProp Σ :=
    ((∃ Sb' : gset Z, ⌜Sb ⊆ Sb'⌝ ∗ ⌜bmapstart ∈ Sb'⌝ ∗ log_opSe γ (S u) Sb' e0)
     ∨ (⌜crb = false⌝ ∗
        ∃ Sb' : gset Z, ⌜Sb ⊆ Sb'⌝ ∗ log_opSe γ (S (S u)) Sb' e0))%I.

  (* the level itrunc is HANDED, as a function of the bitmap credit: paid
     up front costs one unit less, because the bitmap block's slot is
     already bought. *)
  Definition it_entry (crb : bool) (u : nat) : nat :=
    if crb then S u else S (S u).

  (* iupdate's own spend -- definitionally [CreateBudget.iu_spend], spelled
     here so this file need not import the ledger. *)
  Definition it_iu (cru : bool) : nat := if cru then 0%nat else 1%nat.

  (* THE BITMAP UNIT, AS A REPORT (fs-log.md §G.22, G-4c).  [w] is "the
     bitmap block was logged BY THIS CALL", i.e. the unit was actually
     spent -- and spending it is the same event as putting [bmapstart] in
     the op's set, which is why the post can promise the membership beside
     the figure.  At [crb = true] no call ever spends it (the paid disjunct
     pins the level at [S u]), so the report is [false] there and the
     caller's own credit is what carries the membership. *)
  Definition it_bm (w : bool) : nat := if w then 1%nat else 0%nat.

  (* what itrunc spends AT MOST: the bitmap unit (unless already paid) plus
     the tail flush (unless already credited).  Definitionally
     [CreateBudget.ip_spend crb cru true]. *)
  Definition it_spend (crb cru : bool) : nat :=
    ((if crb then 0%nat else 1%nat) + it_iu cru)%nat.

  (* entering the loops CREDITED: the paid disjunct at the caller's own set,
     so no unit is spent on the bitmap at all.  At [crb = false] this is
     [bm_paid_intro] with the set remembered. *)
  Lemma bm_paidS_intro γ bmapstart crb u Sb e0 :
    (crb = true -> bmapstart ∈ Sb) ->
    log_opSe γ (it_entry crb u) Sb e0 -∗ bm_paidS γ bmapstart crb u Sb e0.
  Proof.
    intros Hcrb. iIntros "H". rewrite /bm_paidS /it_entry.
    destruct crb.
    - iLeft. iExists Sb. iSplitR; [iPureIntro; set_solver|].
      iSplitR; [iPureIntro; exact (Hcrb eq_refl)|]. iFrame "H".
    - iRight. iSplitR; [done|]. iExists Sb.
      iSplitR; [iPureIntro; set_solver|]. iFrame "H".
  Qed.

  (* leaving them: at least the [S u] units iupdate still needs, and never
     more than what came in.  The [crb] guard is what makes the upper bound
     tight on the credited arm.

     AND THE REPORT COMES OUT WITH THE LEVEL (G-4c).  The paid disjunct
     already holds [bmapstart ∈ Sb']; discarding it here was what made the
     walkers' [walk_spend w <= 1] unstatable, because a caller that may
     have paid could then learn neither "it paid" nor "it did not".  [w] is
     [negb crb && paid]: at [crb = true] the entry level IS [S u], nothing
     was spent, and the caller carries the membership itself. *)
  Lemma bm_paidS_elim γ bmapstart crb u Sb e0 :
    bm_paidS γ bmapstart crb u Sb e0 -∗
      ∃ (w : bool) (n : nat) (Sb' : gset Z),
        ⌜Sb ⊆ Sb'⌝ ∗ ⌜w = true -> bmapstart ∈ Sb'⌝ ∗
        ⌜(it_entry crb u - it_bm w <= n <= it_entry crb u)%nat
         /\ (S u <= n)%nat⌝ ∗
        log_opSe γ n Sb' e0.
  Proof.
    rewrite /bm_paidS /it_entry /it_bm. iIntros "[H|[%Hc H]]".
    - iDestruct "H" as (Sb') "(%Hsub & %Hin & H)".
      iExists (negb crb), (S u), Sb'. iSplitR; [iPureIntro; exact Hsub|].
      iSplitR; [iPureIntro; intros _; exact Hin|].
      iSplitR; [iPureIntro; destruct crb; simpl; lia|]. iFrame "H".
    - subst crb. iDestruct "H" as (Sb') "(%Hsub & H)".
      iExists false, (S (S u)), Sb'. iSplitR; [iPureIntro; exact Hsub|].
      iSplitR; [iPureIntro; discriminate|].
      iSplitR; [iPureIntro; simpl; lia|]. iFrame "H".
  Qed.

  (* leaving them: at least the [S u] units iupdate still needs *)
  Lemma bm_paid_elim γ bmapstart u :
    bm_paid γ bmapstart u -∗ ∃ n : nat, ⌜(S u <= n <= S (S u))%nat⌝ ∗ log_op γ n.
  Proof.
    iIntros "[H|H]".
    - iDestruct "H" as (Sb) "(_ & H)". iExists (S u).
      iSplitR; [iPureIntro; lia|]. iApply (log_opS_op with "H").
    - iDestruct "H" as (Sb) "H". iExists (S (S u)).
      iSplitR; [iPureIntro; lia|]. iApply (log_opS_op with "H").
  Qed.

End ItruncSpec.

Definition wp_itrunc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
    (data : nat -> list (bv 8))
    (u : nat)
    (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.itrunc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_itrunc <= K)%nat ->
  log_geom_ok cov logstart ->
  (* ONE BITMAP BLOCK -- the fact that makes the budget work at all *)
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  (* the inode's own block, for the closing iupdate *)
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  (* the inum is one the inode REGION covers -- iupdate's premise, which
     replaced the block-half premise and its [diblk_wf ds] (design §11.3) *)
  bv_unsigned inum < 16 * Z.of_nat nib ->
  (* THE INODE IS ALLOCATED (fs-icache §16.4).  itrunc's closing iupdate
     flushes [di_trunc dn], which keeps [dn]'s type, and the region's arm
     only lets an allocated record's fragment stay OUT of the invariant --
     a type-0 flush is iput's free path instead.  iput, the only caller,
     has it from the locked inode's [InodeLock.inode_ok]. *)
  bv_unsigned (di_type dn) <> 0 ->
  (* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d): itrunc's
     flush is [di_trunc dn], which keeps the type, and
     [InodeRegion.ireg_write_au] now forbids a RETYPE of the region's
     record -- so itrunc owes the agreement between the stale [dn0] and
     [dn].  iput, its only caller, passes the two as the same record. *)
  di_type_stable dn dn0 ->
  (* NLINK STABILITY (fs-icache.md §20.6, fs-sysfile S5f): the link
     ledger's twin of the premise above, travelling for the same reason --
     the record the REGION holds at the iupdate below is the stale [dn0].
     [InodeRegion.di_nlink_stable_refl] discharges it at any caller that
     holds the two as ONE record with a nonzero type. *)
  di_nlink_stable dn dn0 ->
  (* the map is well-formed: this is what says every block it names is a
     covered home block, and -- via injectivity -- that the 269 frees are
     269 DISTINCT blocks, so the free pool really does grow by
     [bm_blocks bm] *)
  blkmap_wf cov logstart bm ->
  (* EVERY BLOCK THE INODE NAMES IS IN RANGE FOR THE BITMAP.  bfree needs
     [0 <= b < size] of every block it frees.  That used to be taken slot
     by slot, as an owed hypothesis the model could not supply; it is not
     owed any more.  [blkmap_wf] ALREADY says every block the inode names
     is in [cov], so all that is missing is ONE PURE GEOMETRY FACT relating
     [cov] to the file system's size -- of exactly the same character as
     [log_geom_ok], and supplied from the same place.  The per-slot fact is
     then [IcacheInv.blkmap_slot_inrange], a two-line corollary, and no
     invariant moves (claude-notes/design/fs-icache.md §6(i);
     [IcacheInv.cov_below_of_image] discharges it from the boot image).

     Note there is deliberately NO [bm_blocks bm ⊆ used] premise: itrunc
     holds [blk_own] for every block it frees (via [inode_blocks] and
     [ind_res]), and bfree derives the bit-is-set fact from that token
     itself ([BitmapInv.free_pool_own_used]).  Demanding it here would have
     made the contract uncallable by iput, which has no source for it. *)
  cov_below cov size ->
  (* EVERY DATA BLOCK IS A BLOCK'S WORTH OF BYTES.  bfree demands it of the
     block it frees, and [inode_blocks] does not carry it: the bundle names
     contents but says nothing about their length.  Like the range premise
     above this is a genuine FS fact the model does not yet hold anywhere,
     and it is recorded as owed in fs-inode.md alongside it. *)
  (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
  (* the record's addrs field names the cells the map owns -- iupdate's tie,
     restated here because itrunc rewrites both together *)
  di_addrs dn = bm_cells bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a0 = ip *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  (* THE TRAP-CSR COMPLEMENT, NOT THE BARE PAIR.  itrunc itself never
     acquires or releases anything -- it is a pure PASS-THROUGH to its
     sleeping callees (bfree, bread, iupdate), each of whose OWN acquire
     mints [arm_pay 0 eb _] and whose OWN release spends it again before
     returning.  So the complement itrunc receives at entry is a PURE
     PASS-THROUGH: at [eb = true] it is [emp], so no existing caller gains
     an obligation; at [eb = false] it is the honest pair, held by the
     caller because the TRAP handed it over, and itrunc threads it straight
     through to each callee and back, unused, all the way to its own exit.
     See claude-notes/completed/sched-hart-generic.md and
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* ip->dev and ip->inum: read, never written *)
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  (* the five scalars (ip->size is written), the thirteen addrs cells and
     the indirect block's own resource *)
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  (* THE DATA BLOCKS, which is what actually gets freed *)
  inode_blocks γfs bm data -∗
  (* the two superblock fields, read and handed straight back *)
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* the bitmap, with its free pool *)
  bitmap_res γfs bmapstart cov logstart size used -∗
  (* THE INODE REGION, and this inum's (stale) on-disk record: iupdate's
     resources, threaded through (design §11.3/§12) *)
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  (* the caller's own pid cell *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THREE slot units, not two.  The indirect arm's bread holds ONE across
     the whole 256-entry loop -- the buffer stays checked out while the
     entries are freed -- and each nested bfree still wants the two its own
     bread/log_write pair needs.  brelse gives the held one back at +0x7c.
     The direct loop never has a bread outstanding, so two would do there;
     the arm is what forces three. *)
  bslots bn 3 -∗
  (* THE RESERVATION: two units.  One buys the bitmap block's log slot --
     ONCE, however many blocks are freed -- and one is iupdate's. *)
  log_op γ (S (S u)) -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      (* THE INODE IS EMPTY: no block, size zero *)
      inode_meta ip (di_trunc dn) -∗
      inode_map γfs ip bm_empty -∗
      inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
      (* ...and every block it named is back in the pool *)
      bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
      (* the flush landed: this inum's on-disk record is the truncated
         inode *)
      dinode_at γi inum (di_trunc dn) -∗
      bslots bn 3 -∗
      (* SPEND AT MOST TWO, AT LEAST ONE: iupdate always runs; the bitmap
         unit is spent only if the inode named a block at all *)
      (∃ u' : nat, ⌜(u <= u' <= S u)%nat⌝ ∗ log_op γ u') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE CREDITED SET-FORM CONTRACT (fs-sysfile GR-2b, retrofit 4a)        *)
(*                                                                        *)
(*  Verbatim [wp_itrunc_sconf_body] except for the ledger.  Three things   *)
(*  move, and every one of them is forced by [CreateBudget.ip_spend]:      *)
(*                                                                        *)
(*  (1) [crb] -- "this op has already logged the bitmap block".  It enters *)
(*      [bm_paidS] at the PAID disjunct with [Sb' := Sb], so the bitmap    *)
(*      unit is never spent and the entry level is [S u] rather than       *)
(*      [S (S u)].                                                        *)
(*  (2) [cru] -- "this op has already logged THIS inode's block".  It goes *)
(*      straight to the tail flush, which is [SpecIupdate]'s landed        *)
(*      credited walk.                                                    *)
(*  (3) the post EXPOSES [IBLOCK inum inodestart ∈ Sb'], DETERMINATELY --  *)
(*      itrunc's tail iupdate logs it unconditionally.  That membership is *)
(*      what lets iput's OWN [ip->type = 0] flush, which runs immediately  *)
(*      after itrunc returns, absorb for free; it is the second [iu_spend] *)
(*      term of [ip_spend], and without it 4b cannot hit [iput_units].     *)
(*      Stated as a membership rather than as a [⊆], following             *)
(*      [SpecIalloc.wp_ialloc_gen]'s determinate-union growth.             *)
(*                                                                        *)
(*  At [crb := false, cru := false] this is the counted contract:          *)
(*  [it_entry false u = S (S u)] is its precondition's level, and the      *)
(*  bounds collapse to [u <= u' <= S u] -- which is what makes             *)
(*  [wp_itrunc_sconf] a witness-derivation (GR-2a finding 1) and leaves    *)
(*  every counted caller unmoved.                                         *)
(* ===================================================================== *)
Definition wp_itrunc_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (ip : mword 64) (inum : mword 32)
    (dn dn0 : dinode) (bm : blkmap)
    (data : nat -> list (bv 8))
    (u : nat) (Sb : gset Z) (crb cru : bool) (e0 : nat)
    (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.itrunc in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_itrunc <= K)%nat ->
  (* THE BITMAP CREDIT'S HONESTY PREMISE.  Same device
     [SpecBmap]/[SpecLogWrite]/[SpecIupdate] all carry: the claim is only
     usable when the block really is in the op's set.  It stays PURE
     because the bitmap block is one this op logs itself -- the credit is
     handed straight to [bm_paidS_intro]'s paid disjunct, never to a group
     claimant. *)
  (crb = true -> bmapstart ∈ Sb) ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  IBLOCK inum inodestart ∈ cov ->
  ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
  bv_unsigned inum < 16 * Z.of_nat nib ->
  bv_unsigned (di_type dn) <> 0 ->
  di_type_stable dn dn0 ->
  di_nlink_stable dn dn0 ->
  blkmap_wf cov logstart bm ->
  cov_below cov size ->
  (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
  di_addrs dn = bm_cells bm ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj C b -∗
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  i_dev ip ↦₄{dqd} dev -∗
  i_inum ip ↦₄{dqn} inum -∗
  inode_meta ip dn -∗
  inode_map γfs ip bm -∗
  inode_blocks γfs bm data -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res γfs bmapstart cov logstart size used -∗
  ireg_inv γi γfs inodestart nib -∗
  dinode_at γi inum dn0 -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  bslots bn 3 -∗
  (* THE TAIL FLUSH'S CREDIT, AS A RESOURCE AT A NAMED EPOCH (fs-log.md
     §G.20).  [cru] says "this inode's block is already in lh.block[]", and
     the claim goes straight through both loops to the closing iupdate.  It
     is a [log_credit] rather than the pure [IBLOCK … ∈ Sb] because THIS is
     the unit a [crz] caller has to buy with a GROUP witness: outside the log
     spinlock a group claim cannot be turned into a set membership (§G.19),
     so a pure premise here is a premise no [crz] caller could ever satisfy.
     [LogInv.log_credit_own] converts for every caller that does hold the
     own-set fact, so the counted and create paths are unchanged. *)
  log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
  (* THE RESERVATION, SET FORM AND EPOCH-NAMED: [it_entry crb u] units at the
     caller's own set, at the birth epoch the credit above is ordered
     against.  Credited, that is ONE unit less than the counted contract asks
     for -- which is the whole point.  The POST closes the epoch again
     ([log_opS]): nothing downstream of the flush compares epochs, and the
     asymmetry is deliberate (§G.20). *)
  log_opSe γ (it_entry crb u) Sb e0 -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      i_dev ip ↦₄{dqd} dev -∗
      i_inum ip ↦₄{dqn} inum -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      inode_meta ip (di_trunc dn) -∗
      inode_map γfs ip bm_empty -∗
      inode_blocks γfs bm_empty (fun _ => replicate BSIZE (bv_0 8)) -∗
      bitmap_res γfs bmapstart cov logstart size (used ∖ bm_blocks bm) -∗
      dinode_at γi inum (di_trunc dn) -∗
      bslots bn 3 -∗
      (* THE LEDGER, SET FORM.  The set only GROWS, it provably contains
         this inode's block, and the counter is bracketed by the two
         [CreateBudget] figures: at most [it_bm w + it_iu cru] is gone, and
         the tail flush's own [it_iu cru] is gone for certain.
         [it_bm w + it_iu cru <= it_spend crb cru] always, so this is the
         landed bound and a REPORT: [w] says whether the bitmap unit was
         spent, and spending it is the same event as logging [bmapstart].
         That coupling is what a WALKER's per-level [iput] needs -- without
         it a walk of L levels can only bound its spend by L (fs-log.md
         §G.22). *)
      (∃ (w : bool) (u' : nat) (Sb' : gset Z),
         ⌜Sb ⊆ Sb'⌝ ∗
         ⌜IBLOCK inum inodestart ∈ Sb'⌝ ∗
         ⌜w = true -> bmapstart ∈ Sb'⌝ ∗
         ⌜(it_entry crb u - (it_bm w + it_iu cru) <= u')%nat
          /\ (u' + it_iu cru <= it_entry crb u)%nat⌝ ∗
         log_opS γ u' Sb') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ITRUNC.
  Parameter wp_itrunc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (data : nat -> list (bv 8))
      (u : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_itrunc_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                           cov logstart bmapstart inodestart nib size dev used
                           ip inum dn dn0 bm data u
                           pidv dq dqd dqn dqb dqs m K eb C b.
  (* the credited set-form contract; [wp_itrunc_sconf] is this at
     [crb := cru := false], derived at the [log_op] existential's own
     witness. *)
  Parameter wp_itrunc_gen :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !iregG Σ, !icacheG Σ, ICFG : icfg}
      `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (ip : mword 64) (inum : mword 32)
      (dn dn0 : dinode) (bm : blkmap)
      (data : nat -> list (bv 8))
      (u : nat) (Sb : gset Z) (crb cru : bool) (e0 : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_itrunc_gen_body γs j γl γu γd γk pd pav pu bn γ γfs γi
                         cov logstart bmapstart inodestart nib size dev used
                         ip inum dn dn0 bm data u Sb crb cru e0
                         pidv dq dqd dqn dqb dqs m K eb C b.
End ITRUNC.
