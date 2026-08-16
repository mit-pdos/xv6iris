(* SpecCreateFreshTy.v -- D₀'s ONE assumed fact, and the span at which it is
   the only consistent way to state it.

   ==== WHAT IS ASSUMED, IN ONE LINE =====================================

   At create's `ilock(ip)` (+0xb0), on the inode its own `ialloc` (+0xa8)
   has just claimed, the record the fill returns is the record the claim
   wrote: [di_type dn = ty].  Nothing else.

   ==== THE EQUIVALENCE -- WHAT IS *ACTUALLY* LEFT ======================

   The statement above is a span over two calls, and that is a matter of
   consistency (see "WHY THE SPAN IS THE TWO CALLS" below), not a measure
   of what is unproved.  What is unproved is one sentence, and the three
   flanks that bound it are MACHINE-CHECKED, in [IregBox.v]:

     [create_fresh_ty]  <->  NO FOREIGN [ireg_free_au] AT THE CLAIMED INUM
     BETWEEN [ialloc]'s [brelse] AND [ialloc]'s [iget].

   Read left to right: the only way create's [ilock] can read a type other
   than [ty] is for the claimed record to be REWRITTEN, and the only mover
   that writes a type-0 record over a claim box is [ireg_free_au] (a
   foreign [ireg_withdraw] alone changes no byte -- it hands the fragment
   out at the record the claim wrote, so a stranger who merely fills reads
   [ty] too).  A free must therefore be followed by a re-claim at another
   type; both are inside the same interval.  Read right to left: a free
   in that interval is exactly the trace fs-icache.md §17.6.1 certifies as
   machine-legal on `f60ff58` -- an [iput] past its regeneration at +0x54
   with the entry lock released at +0x5c -- and it makes the conclusion
   false.  So the axiom is not merely IMPLIED by the sentence; it IS the
   sentence.

   THE THREE FLANKS, all proved, none of them assumed:

     (i) PRE-BRELSE -- THE BUFFER HALF.  [IregBox.fsL_block_exclusive]:
     [fsblock] is a HALF of the logged view's [ghost_map] element, two
     halves are the whole element, and a third fraction of any size is
     invalid.  Every region mover hands its caller the REGION's half and
     demands it back at new bytes, so firing one requires holding the
     other half.  While [ialloc] is inside its own bread/brelse window
     ([ialloc]+0x3c .. +0xa0, and the claim itself is the [log_write] AU
     at +0x9a) NO foreign claim, write, link, unlink or free can fire at
     ANY of that dinode block's sixteen inums.

     (ii) POST-IGET -- REF-1.  [IregBox.iref_two_not_ref1]: [iput]'s free
     path is gated on [ip->ref == 1], which the model reads through
     [IcacheInv.iref_lookup]'s REF-1 conjunct ("at count one your [q] is
     the whole outstanding share"); two reference fragments at one slot
     force the count to two.  So from the instant [ialloc]'s [iget] mints
     create's reference until create drops it -- which is well past
     create's [ilock] -- no other thread can be at REF-1 on that entry,
     hence none can enter the free.  This is GENUINE ABSENCE, not a
     counter bound, which is why §20.15's objection (ii) does not apply
     to it (fs-fragments.md §7.2.2 item 2, §7.6.4).

     (iii) NO FREE WITHOUT A FILL.  At the C level: [iput]'s free path
     tests [ip->valid], and [ip->valid] is written 1 in exactly one place,
     [ilock]'s fill.  THE MODEL DOES NOT NEED THE BIT, and this is the one
     place the honest model-level form differs from the code-shape one --
     it is SHARPER, not weaker.  [ireg_free_au] takes one caller-side
     resource, [dinode_at γi inum dn], a full-fraction region fragment.
     At a claim box that fragment is INSIDE the region, so nothing else in
     the system holds it: [IregBox.ireg_claim_box_freeze] refutes any
     client copy and [IregBox.ireg_box_no_payload] refutes the two
     payloads it could have been parked in ([ipool_alloc], [ic_loaded]).
     The only producer of it at a boxed inum is [ireg_withdraw], whose
     sole gate is the marker.  So "every free passes through a fill" is a
     CUSTODY theorem about the fragment, not a control-flow claim about a
     word: the bit is per-ENTRY and dies at eviction, the fragment is
     per-INUM and is conserved (fs-fragments.md §7.7's conservation law).
     [IregBox.ireg_box_excl] is the same content stated over the slot, as
     the dichotomy a nonzero-type record satisfies: either it is CHECKED
     OUT (the region holds the marker) or it is a BOX -- and at a box
     [fresh_shape] holds, no [ilink] of any flavour names the inum, and no
     client holds the record.

   THE WINDOW, MEASURED.  [brelse] returns to [ialloc]+0xa4 and the [jal
   iget] is at +0xaa, so in [ialloc]'s own text the gap is THREE
   instructions -- +0xa4 [addiw a1,s2,0], +0xa8 [c.mv a0,s5], +0xaa [jal
   ra,iget] -- plus [iget]'s prologue up to the reference mint under
   [itable.lock].  (The FOUR instructions this file otherwise talks about
   are a different measurement: create's own span, +0xa4 .. +0xb0.  The
   two counts are unrelated and have been confused before.)  And the gap
   is not a bound on TIME: the claimant can be preempted inside it for
   arbitrarily long, which is why "it is only three instructions" is an
   argument about reachability and never about the logic.

   ==== WHY IT IS NOT DERIVABLE (fs-icache.md §20.17.6, twice) ===========

   (A) LICENCE (d) HAS NO SOURCE.  [InodeRegion.ireg_claim_au] pays out
   [True] -- "nothing crosses to ialloc's caller, so no interleaving can
   strand a concurrent ilock's fill" is its own design justification -- so
   ialloc's postcondition carries no receipt naming the claimed type, and
   §20.16.4 struck the claim token that would have carried one.

   (B) THE [ireg_withdraw] WALL.  Even given (A), the guarded clause
   [g = 0 -> claim_ok d c inreg] owes [c = None] at the withdraw, whose
   only caller is [ProofIlock]'s fill arm, and [SpecIlock] takes no
   licence -- §20.16.5(e) explains why it cannot be given one, and the
   9da28f5 guards (which prune the trace that made the proposition FALSE)
   change not one word of that.  A kernel guard prunes traces; it cannot
   hand a contract a resource.

   So the fact is TRUE of the fixed binary and UNDISCHARGED, which is
   exactly [SpecForkretPark]'s situation and exactly why this file has the
   same shape.

   ==== (C) THE MARKER ROUTE, KILLED IN ONE SENTENCE =====================

   The shortest known statement of the whole problem is that if
   [ireg_claim_au] could pay out [imark gi inum], this axiom would fall in
   two lines -- [imark] in hand means nobody can fill and nobody can free
   the inum ([ireg_withdraw]'s sole gate is the marker, [ireg_free_au]
   needs [dinode_at], and [imark_excl] settles it), with no (L5), no
   ledger clause and no free-side obligation.  ITS DEATH CERTIFICATE IS
   ONE SENTENCE: at a free inum the marker is OUTSIDE the region -- in
   [IcacheEscrow]'s [ipool], behind the itable spinlock that [ialloc] does
   not hold, and it cannot be minted either, because [IcacheBoot] allocates
   the record map and the marker map in ONE [ghost_map_alloc] and no marker
   entry is ever created afterwards, only moved.  Three separate probes
   re-derived this; it is written here so a fourth does not.

   ==== (D) STATION EXHAUSTION -- WHY NO GHOST-SIDE ROUTE CAN EXIST ======

   Seven report-only probes have attacked this axiom (all seven are
   transcribed as claude-notes/design/fs-fragments.md section 7, with the
   five named walls indexed at section 7.0).  The seventh closes the
   question with an exhaustion argument rather than a seventh dead
   candidate, and THIS IS THE PARAGRAPH THAT SHOULD STOP AN EIGHTH PROBE:

     A claim-to-fill protocol has exactly three stations -- the MINT
     ([ireg_claim_au]), the HAND-OFF ([ireg_withdraw]) and the RESET
     ([ireg_free_au]) -- plus the PAYOUT at create's [ilock].  Every
     possible carrier of the "this box is MY episode's" pin kills exactly
     one station, and the assignment space is EXHAUSTED: pin it on the
     BYTES (option (k)'s [c = Excl ty -> di_type = ty]) and the RESET
     cannot clear it; pin it on the ARM ((L6)'s [c <> None -> inreg]) and
     the HAND-OFF cannot clear it (that is R5's standing ban, and (B)
     above); pin it on a CLIENT TOKEN and the MINT is blocked, or the
     token is stale, or it is unreissuable -- and since the token is
     affine, even the good case LEAKS (a create that drops it pins
     [c = Some] forever and wedges the free on plain "create; unlink");
     pin it NOWHERE, in an authority-side protocol phase, and every
     station closes at the price of an EXISTENTIALLY-TYPED payout,
     because the mint must stay universally firable and frame-preserving,
     so every episode reset is invisible to every client frame.  That
     last payout is [exists ty', di_type dn = ty' /\ fresh_shape dn] --
     byte-for-byte the weakening this tree ALREADY HAS via [SpecIlock]'s
     [filled] indicator and [ireg_withdraw]'s [fresh_shape].

   The dichotomy is LAW, not cost: frame preservation is a property of the
   logic (a frame-preserving update is valid against ALL frames, so no
   client resource can obstruct it); each station's mover must stay
   provable because it fires on machine-reachable instantiations
   elsewhere; and the mint's emptiness of hand is the machine's own
   instruction order -- [ialloc] does [brelse] BEFORE [iget], so between
   them the claimant holds nothing revocable at all.

   CONSEQUENCE.  Do not open another ghost-side route: protocol ghosts,
   Owicki-Gries registries, birth certificates, escorts, epochs, marker
   batons and ownership-transferring claims are all instances of the four
   assignments above, and all are dead BY LAW.  The two remaining imports
   are a KERNEL change (move [ialloc]'s [brelse] after its [iget], which
   is the unique change that puts currency -- the buffer's [fs_L] half --
   into the empty window; rejected by the user, so this axiom is the
   price of that policy) or WEAKENING what depends on this file
   ([SpecCreate]'s made-arm conjunct, which breaks ARM C-OK-DIR's
   [dirlink(ip, ".")]).

   ==== (E) THE REDUCTION HISTORY, IN ONE PARAGRAPH =====================

   TEN formulations have been designed against this fact and all ten are
   death-certified in fs-fragments.md §7, which is the map worth keeping;
   they are listed here so an eleventh is recognised as a re-run rather
   than as an idea.  (1) The C' LICENCE ENUMERATION at [SpecIget] (§7.1):
   buildable, and the gate does not open when it lands -- its row (d) has
   no supplier but [ProofIalloc]'s own [iget].  (2) The ADEQUACY COUPLING
   (§7.2.2): needs "every reference is justified" AND "I hold them all";
   the second half is now available (REF-1 + [ic_ci_wf]'s ci-injectivity)
   and the first is not.  (3) The ENTRY-KEYED PAYLOAD CERTIFICATE
   (§7.2.3): the withdraw would owe it on EVERY firing, i.e. (L6) wearing
   a payload's clothes.  (4) The ESCORT (§7.2.4): decomposes exactly as
   designed, and phases 1 and 3 are flanks (i) and (ii) above -- it is
   phase 2, this file's window, that no resource reaches.  (5) The
   SPAN-STABILITY CLAUSE (§7.3): dies twice before it reaches the
   withdraw.  (6) HARMLESSNESS / an entry-keyed certificate R (§7.4):
   THE CLAIM BOX IS BORN BEFORE THE ENTRY, so no g-, k- or deposit-keyed
   proposition can be an invariant of it, and a fixed per-inum keying
   cannot be re-shot at a second type.  (7) RECORD-BACKED GREYS AND TREE
   LEVERAGE (§7.5): TRACE G -- a live directory record naming a claim box
   is reachable on the pinned binary.  (8) The REFERENCE/OCCUPANCY
   CERTIFICATE (§7.6): its temporal half is sound and new, and it dies on
   the mint side at THE CLAIM'S HORIZON -- [ireg_claim_au] fires holding
   the region invariant and the dinode block's bytes and nothing else, so
   it cannot verify the absence of a receipt that lives in the cache.
   (9) OWNERSHIP TRANSFER, the claim paying out [dinode_at] (§7.7): the
   cheapest design of the ten and the one with the highest wall -- THE
   CONSERVATION LAW, one [ghost_map_alloc] at boot and no marker ever
   minted afterwards, so the third arm it needs cannot be refuted at the
   free.  (10) The PROTOCOL GHOST / Owicki-Gries phase (§7.10): the first
   design in the series whose invariant is fully maintainable and
   §19.7-clean at every mover, and it dies at the PAYOUT -- which is (D)
   above, and is why (D) is an exhaustion argument rather than an
   eleventh certificate.  The through-line: every one of the ten either
   asks the MINT to see outside its horizon, or asks the HAND-OFF to
   clear a pin it holds no premise for, or asks the RESET to clear one an
   affine client may simply have dropped.

   ==== (F) THE THREE OPEN ROUTES, AND THEIR STATUS =====================

   (F1) K-F2 -- MOVE [ialloc]'s [brelse] AFTER ITS [iget].  Recorded,
   priced (three kernel lines plus [ProofIalloc]'s re-walk), and REJECTED
   BY POLICY (R13(iii)).  It is the unique change that deletes the window
   outright, because it is the unique change that puts a revocable
   resource -- the buffer's [fs_L] half, i.e. flank (i) -- into the gap.
   With it, flank (i) and flank (ii) meet and there is no residue at all.
   This axiom is the price of the no-kernel-change policy, and that is
   the whole of it.

   (F2) CLOSED-WORLD ADEQUACY.  Not a resource route: quantify over the
   whole system's threads at the adequacy theorem and discharge the
   sentence as a property of the closed program rather than as an Iris
   proposition.  §7.2.2's death certificate is against the RESOURCE form
   of the coupling; the closed-world form is UNAUDITED, and its obvious
   cost is that it abandons thread-modularity for the one fact -- every
   [WP] in the fs tree would be stated against a whole-system side
   condition.  Recorded, not designed.

   (F3) PROPHECY / LATE LINEARIZATION.  NOT PREVIOUSLY RECORDED, and it
   is written here because it is the one mechanism (D)'s station
   exhaustion does not literally name: a prophecy variable is not a pin
   on an EPISODE, it is a pin on a FUTURE OBSERVATION, so the four
   carrier assignments do not obviously cover it.  The claim would
   prophesy the type its own fill will read and resolve at the fill.
   CAUTION, and the reason it is filed as a route rather than as a plan:
   (D)'s clause (i) appears to cover it anyway -- prophecy resolution is
   itself a frame-preserving update and the mint must stay universally
   firable -- so the expected outcome is that the resolved value is
   existentially typed exactly as H1's payout is.  Nobody has run it.  If
   an eleventh probe is opened, THIS is the only one worth opening.

   ==== WHY THE SPAN IS THE TWO CALLS, AND NOT A NARROW FACT ============

   §19.9.2 and §20.17.9 both anticipated a one-line gate -- a pure fact, or
   an entailment over the resources create holds after ilock, concluding
   [di_type dn = ty].  **THAT STATEMENT IS INCONSISTENT AND MUST NOT BE
   WRITTEN.**  In any such form [ty] and [dn] are both free and nothing
   relates them, so instantiating at [ty₁ <> ty₂] on one [dn] derives
   [False]; an assumed contract that proves [False] defeats every
   [Print Assumptions] audit in the tree, including this one's.

   The provenance has to come from somewhere, and the tree has no resource
   that carries it (that IS licence (d), refuted above).  What remains is
   the PROGRAM POINT: [ty] is pinned by the machine word in [s4], so a
   statement that CONTAINS the [jal ialloc] has, at two different [ty],
   contradictory premises -- and is therefore consistent.  That is the
   whole reason this file states a span rather than a fact.

   THE SPAN IS FOUR INSTRUCTIONS, +0xa4 .. +0xb0:

     +0xa4  c.mv  a1,s4          a1 := type
     +0xa6  lw    a0,0(s1)       a0 := dp->dev            (the parent's cell)
     +0xa8  jal   ialloc         <- [wp_ialloc_gen] is a HYPOTHESIS
     +0xac  c.mv  s3,a0          s3 := ip
     +0xae  c.beqz a0 -> +0xec   [ARM A-FAIL]
     +0xb0  jal   ilock          <- [wp_ilock_sconf] is a HYPOTHESIS

   and it delivers control at +0xb4 (allocated) or +0xec (A-FAIL), which
   are the CFG's own two successors.  Four instructions is the price of
   consistency and it is stated here so nobody has to measure it: create
   proves the other 158.

   ==== WHY IT HIDES NOTHING ============================================

   The two callee contracts are HYPOTHESES of the parameter, supplied by
   [ProofCreate] out of its own [IA]/[IL] functor arguments.  So
   [ProofIalloc] and [ProofIlock] stay load-bearing: a wrong ialloc or a
   wrong ilock is not covered by this axiom, which is the difference
   between it and an assumed [wp_ilock_fresh].

   And [fresh_shape dn] is NOT assumed -- it arrives from ilock's own
   postcondition, whose [filled] indicator this file pins at [true].
   [InodeRegion.ireg_withdraw] proves [fresh_shape]; D₀ increment 1 made
   [SpecIlock] expose it.  The only thing below that ilock does not already
   say is [di_type dn = ty], and the only thing beyond ilock's own post
   that the conclusion adds is [filled := true] -- i.e. "the fill took
   §16.4's claim-box arm", which is the same claim as the type identity
   and is what makes the type identity meaningful.

   ==== WHAT RETIRES IT =================================================

   A carrier for "no free-and-reclaim since my claim" (fs-icache.md §20.7).
   §20.17.7 said there were TWO doors -- the kernel's F2, or a refutation
   of §20.17.6(B) at the withdraw.  THAT COUNT IS CORRECTED TO ONE:
   fs-fragments.md §7.4.6 kills the second independently, at
   [ireg_claim_au]'s re-mint rather than at the withdraw's premise, so the
   payout direction fails even with no premise at all.  The surviving
   doors are (F1)/(F2)/(F3) above, of which only (F1) is designed.  When
   one opens, this file and its [Axiom] are what get deleted, and
   [ProofCreate] loses one hypothesis and gains four instructions. *)
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
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecIalloc.
Require Import SpecIlock.
Require Import SpecDirlink.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

Local Open Scope Z_scope.

(* THE SEAM'S REGISTER CONTRACT.  [callee_saved] is FALSE across the span --
   the [c.mv s3,a0] at +0xac is the point of it -- so what the span promises
   is [callee_saved] EVERYWHERE BUT s3, with s3's own value reported per
   arm.  Both callees restore sp and s0, so the exception list is exactly
   the one register the span writes, and the predicate is stated
   POSITIVELY-BY-ONE-EXCEPTION rather than over a set the reader has to go
   and look up (durable-notes' rule; here the set IS the singleton). *)
Definition cr_cs_but_s3 (m mf : regfile) : Prop :=
  forall c : mword 5,
    is_cs_idx c = true -> c <> (mword_of_int 19 : mword 5) ->
    mf !!! Regidx c = (m !!! Regidx c : mword 64).

Definition create_fresh_ty_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ,
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname) (γpr : gname)
    (cov : gset Z) (logstart inodestart : Z) (ninodes : Z) (nib : nat)
    (dev : mword 32) (ty : mword 16)
    (kd : nat) (dqp : dfrac)                     (* the LOCKED PARENT's slot *)
    (u : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqs dqn : dfrac)
    (Ma : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) : Prop :=
  let pj := proc_addr j in
  (* ---- ialloc's and ilock's own geometry, verbatim ---- *)
  (K_ialloc <= K)%nat ->
  (K_ilock <= K)%nat ->
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  InodeInv.ireg_blocks_ok inodestart nib cov logstart ->
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  bv_unsigned ty <> 0 ->
  printk_gen_contract γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  dev = ROOTDEV ->
  (* ---- THE PINNING PREMISE.  [ty] is the halfword in s4, which is what
     makes this statement consistent: at two different [ty] these two
     equations cannot both hold.  See the header. ---- *)
  Ma !!! Regidx (mword_of_int 20 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  (* s1 = dp, whose [dev] word the [lw] at +0xa6 reads *)
  Ma !!! Regidx (mword_of_int 9 : mword 5) = ientry kd ->
  (kd < NINODE)%nat ->
  (* PARKING PREMISE *)
  eb = true ->
  (* the span's cone is ialloc ("log", 1) and ilock ("bcache", 2, and the
     inode sleeplock above it); "log" is the lower, so one premise there
     covers both via [locks_below_mono]. *)
  locks_below lks "log" ->
  (* ---- THE TWO REAL CONTRACTS, AS HYPOTHESES.  This is what keeps
     [ProofIalloc] and [ProofIlock] load-bearing: the axiom below assumes
     nothing about either function, only about the record identity across
     the two calls. ---- *)
  (forall `{CIDa : CpuId}
     (γs' : list gname) (j' : nat) (γl' : gname)
     (γu' : uart_names) (γd' : disk_names) (γk' : gname)
     (pd' pav' pu' : mword 64) (bn' : bio_names)
     (γ' : log_names) (γfs' : fs_names) (γi' : gname)
     (cn' : ic_names) (gtl' : gname) (γpr' : gname)
     (cov' : gset Z) (logstart' inodestart' ninodes' : Z) (nib' : nat)
     (dev' : mword 32) (ty' : mword 16) (u' : nat) (Sb' : gset Z)
     (pidv' : mword 32) (dq' dqs' dqn' : dfrac)
     (m' : regfile) (K' : nat) (eb' : bool) (b' : bool)
     (lks' : gset string),
     wp_ialloc_gen_body (CID := CIDa) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                        γ' γfs' γi' cn' gtl' γpr' cov' logstart' inodestart'
                        ninodes' nib' dev' ty' u' Sb' pidv' dq' dqs' dqn'
                        m' K' eb' b' lks') ->
  (forall `{CIDl : CpuId}
     (γs' : list gname) (j' : nat) (γl' : gname)
     (γu' : uart_names) (γd' : disk_names) (γk' : gname)
     (pd' pav' pu' : mword 64) (bn' : bio_names)
     (γfs' : fs_names) (γi' : gname) (cn' : ic_names) (gil' gisl' : gname)
     (cov' : gset Z) (logstart' inodestart' : Z) (nib' : nat)
     (k' : nat) (s' : Qp) (g' : gname) (dev' inum' : mword 32)
     (pidv' : mword 32) (dq' dqs' : dfrac)
     (m' : regfile) (K' : nat) (eb' : bool) (b' : bool)
     (lks' : gset string),
     wp_ilock_sconf_body (CID := CIDl) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                         γfs' γi' cn' gil' gisl' cov' logstart' inodestart'
                         nib' k' s' g' dev' inum' pidv' dq' dqs'
                         m' K' eb' b' lks') ->
  (* ================= THE SPAN ================= *)
  sie_cap_gpr Ma K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.create + 0xa4) : mword 64) -∗
  panic_wp_any -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  SpecDirlink.ic_sleeplocks cn -∗
  ireg_inv γi γfs inodestart nib -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  p_pid pj ↦₄{dq} pidv -∗
  bslots bn 3 -∗
  iref_slot -∗
  (* THE PARENT'S OWN [dev] CELL: the [lw a0,0(s1)] at +0xa6 reads it, and
     it comes straight back.  It is the only piece of the locked parent the
     span touches. *)
  i_dev (ientry kd) ↦₄{dqp} dev -∗
  log_opS γ (S u) Sb -∗
  wp_next true pj (fun (CIDo : CpuId) =>
  ∀ (Mo : regfile) (alloc : bool)
    (kslot : nat) (q : Qp) (g : gname) (inum : mword 32)
    (gil gisl : gname) (dn : dinode) (bm : blkmap),
      ⌜cr_cs_but_s3 Ma Mo⌝ -∗
      sie_cap_gpr Mo K b pj -∗
      cpu_own 0 eb pj b lks -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      p_pid pj ↦₄{dq} pidv -∗
      bslots bn 3 -∗
      i_dev (ientry kd) ↦₄{dqp} dev -∗
      (if alloc
       then
         (* ---- CONTROL IS AT +0xb4, THE INODE IS LOCKED AND FILLED ---- *)
         ⌜Mo !!! Regidx (mword_of_int 19 : mword 5) = ientry kslot
          /\ (kslot < NINODE)%nat
          /\ 0 < bv_unsigned inum < ninodes
          /\ bv_unsigned inum < 16 * Z.of_nat nib
          (* THE ONE ASSUMED FACT.  Everything else in this arm is
             [wp_ialloc_gen]'s or [wp_ilock_sconf]'s own postcondition. *)
          /\ di_type dn = ty
          (* ...and this is ILOCK's, at the [filled] the line above pins:
             NOT assumed -- see the header. *)
          /\ fresh_shape dn⌝ ∗
         pc_is (mword_of_int (KernelSyms.create + 0xb4) : mword 64) ∗
         is_sleeplock_gen gil gisl (i_lock (ientry kslot)) "inode"%string
                          (ic_tok cn kslot) (slh_tok (icfg_isl kslot)) ∗
         sleeplocked_q gisl (q/2)%Qp ∗
         sl_pid (i_lock (ientry kslot)) ↦₄ pidv ∗
         ic_deposit cn kslot (DepShr (q/2)%Qp dev inum g) ∗
         i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev ∗
         i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} inum ∗
         i_valid (ientry kslot) ↦₄ valid_word true ∗
         ic_loaded γfs γi cov logstart kslot inum dn bm ∗
         ity_shot g (di_type dn) ∗
         inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev inum g ∗
         (* ialloc's [ia_spend = 1], and the membership create's own
            [iupdate(ip)] and every [dirlink] on [ip] credit against *)
         log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})
       else
         (* ---- CONTROL IS AT +0xec, ARM A-FAIL: nothing was claimed ---- *)
         ⌜Mo !!! Regidx (mword_of_int 19 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗
         pc_is (mword_of_int (KernelSyms.create + 0xec) : mword 64) ∗
         iref_slot ∗
         log_opS γ (S u) Sb) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CREATE_FRESH_TY.
  Parameter create_fresh_ty :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (kd : nat) (dqp : dfrac)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (Ma : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      create_fresh_ty_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty kd dqp
                           u Sb pidv dq dqs dqn Ma K eb b lks.
End CREATE_FRESH_TY.
