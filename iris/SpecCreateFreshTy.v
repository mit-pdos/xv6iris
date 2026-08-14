(* SpecCreateFreshTy.v -- D₀'s ONE assumed fact, and the span at which it is
   the only consistent way to state it.

   ==== WHAT IS ASSUMED, IN ONE LINE =====================================

   At create's `ilock(ip)` (+0xb0), on the inode its own `ialloc` (+0xa8)
   has just claimed, the record the fill returns is the record the claim
   wrote: [di_type dn = ty].  Nothing else.

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

   A carrier for "no free-and-reclaim since my claim" (fs-icache.md §20.7),
   which needs either the kernel's F2 (move [ialloc]'s [brelse] after its
   [iget], so licence (e) covers [ProofIalloc.v:1622] and licence (d) is
   unnecessary) or a refutation of §20.17.6(B) at the withdraw.  Those are
   the two doors.  When one opens, this file and its [Axiom] are what get
   deleted, and [ProofCreate] loses one hypothesis and gains four
   instructions. *)
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
Require Import SpecCreate.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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
      ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
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
    (Ma : regfile) (K : nat) (eb : bool) (C : iProp Σ)
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
     (m' : regfile) (K' : nat) (eb' : bool) (C' : iProp Σ) (b' : bool)
     (lks' : gset string),
     wp_ialloc_gen_body (CID := CIDa) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                        γ' γfs' γi' cn' gtl' γpr' cov' logstart' inodestart'
                        ninodes' nib' dev' ty' u' Sb' pidv' dq' dqs' dqn'
                        m' K' eb' C' b' lks') ->
  (forall `{CIDl : CpuId}
     (γs' : list gname) (j' : nat) (γl' : gname)
     (γu' : uart_names) (γd' : disk_names) (γk' : gname)
     (pd' pav' pu' : mword 64) (bn' : bio_names)
     (γfs' : fs_names) (γi' : gname) (cn' : ic_names) (gil' gisl' : gname)
     (cov' : gset Z) (logstart' inodestart' : Z) (nib' : nat)
     (k' : nat) (s' : Qp) (g' : gname) (dev' inum' : mword 32)
     (pidv' : mword 32) (dq' dqs' : dfrac)
     (m' : regfile) (K' : nat) (eb' : bool) (C' : iProp Σ) (b' : bool)
     (lks' : gset string),
     wp_ilock_sconf_body (CID := CIDl) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                         γfs' γi' cn' gil' gisl' cov' logstart' inodestart'
                         nib' k' s' g' dev' inum' pidv' dq' dqs'
                         m' K' eb' C' b' lks') ->
  (* ================= THE SPAN ================= *)
  sie_cap_gpr Ma K b pj -∗
  cpu_own 0 eb pj C b lks -∗
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
      cpu_own 0 eb pj C b lks -∗
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
         is_sleeplock gil gisl (i_lock (ientry kslot)) "inode"%string
                      (ic_tok cn kslot) ∗
         sleeplocked gisl ∗
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
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}
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
      (Ma : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string),
      create_fresh_ty_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty kd dqp
                           u Sb pidv dq dqs dqn Ma K eb C b lks.
End CREATE_FRESH_TY.
