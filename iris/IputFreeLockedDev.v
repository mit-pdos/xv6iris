(* ============================================================================
   DEV SCRATCH: ip_free_locked -- the WP walk for the LOCKED truncate+free
   block of iput at the NEW CodeIput pin:  iput +0x5a .. +0xa6, whose fall-
   through target +0xa8 is EXACTLY [OfflockDev.ip_free_offlock]'s entry.

   Developed as a functor over BREAD / LOG_WRITE / BRELSE (as OfflockDev is),
   so it compiles against the pre-built cone.  It instantiates OfflockDev with
   the same three params and DISCHARGES the +0xa8 fall-through by applying
   [OFF.ip_free_offlock] -- hence this lemma is self-contained and, when
   finished, admit-free.

   ==========================================================================
   STATUS (2026-08-17, end of the eviction session).  The WHOLE WALK
   0x5a .. 0xa6 IS PROVEN, [OFF.ip_free_offlock] IS APPLIED at 0xa8, and its
   0x30 post is re-shaped into this lemma's.  TWO [admit]s remain, and NEITHER
   is a tactic gap -- both are design debts of the REORDER, recorded here so
   the next session does not re-derive them:

   (B1) THE NON-LAST-CLOSE ARM (the [cnt2 <> 1] branch at +0x8a).  The
        reordered iput RELEASES itable.lock at +0x66 and re-acquires it at
        +0x82, so the REF-1 fact the caller supplies ([Mt !! k = Some (q,1)])
        is about the OLD map.  After the re-acquire all that is derivable is
        [IcacheInv.iref_lookup]'s biconditional ([cnt2 = 1 <-> q = qt2]), and
        NOTHING in the held resources forces it: an iget in the window can
        split a fresh reference out of the table's retained share (the mass
        ledger balances at q + (1/2 - qt2) + 1/2 = 1 for ANY q <= qt2).
        design/fs-icache.md §17.6.1 CERTIFIES that trace as machine-reachable,
        so no resource may forbid it (§19.7's rule).  On that arm the escrow
        stays PARKED, [ic_open_auth_ref] is unusable (it takes REF-1 as a
        premise), and the off-lock [ifree] the C runs unconditionally would be
        freeing an inode another thread still references.  This is the
        reorder's own hazard, not a proof-engineering miss; it needs a design
        ruling (strengthen the free-path guard, or make [ifree] guarded).
        This is the SAME wall projects/iget-licence.md records as its
        NON-GOAL -- "the free-side wall is untouched; §7.1.6's death
        certificate stands" -- met here at the +0x82 re-acquire.  The licence
        enumeration constrains which igets are VERIFIED, which is a
        whole-program fact and not a resource this lemma can hold.

   (B2) ONE BUNDLE, TWO CONSUMERS (the [admit] at the eviction).  Spelled out
        in full at its site; in one line: the eviction hands back exactly one
        [ipool_shape], and the reorder needs BOTH the itable free-pool entry
        (at the +0x94 release, because [ic_ci_wf] forces [delete k ci] and the
        pool set therefore GROWS by [inum]) and the record
        [dinode_at γi inum dn] (for the +0xba [ireg_free_deposit_au], which
        consumes it) out of that one bundle -- and [ipool_shape_np]
        existentially erases which arm and which record it is.  The other two
        [ipool_shape] arms are unreachable here: [imark] is inside [ireg_inv]
        until the deposit, and [pool_pending] needs the [committedA] only the
        deposit mints.  The structural fix is the (None, Some) arm of
        [IcacheEscrow.islot2] that the definition's OWN header describes but
        the three-arm code (plus [ic_ci_wf]'s [dom ci = dom M]) does not
        implement: keep the evicted entry in [ci], the pool does not grow, and
        the record rides to 0xa8 unchallenged.

   Statement changes forced by the walk, flagged for the splice: [3 <= u]
   (was 2 -- itrunc's post must leave [1 <= u'] so the off-lock flush's
   [log_opSe γ (S u) ..] has an [S]); a new [Z.of_nat u + 2 < 2^31]; and the
   0x30 continuation now threads [OFF.ipo_thr] (NOT [callee_saved]: s1 holds
   the off-lock tail's [bp] and is restored only by the epilogue after 0x30)
   at [sie_cap_gpr .. (K-6)], and hands back the [ipool_shape] the off-lock
   deposit parks.
   ==========================================================================

   ---- THE EXACT INSTRUCTION STREAM (from CodeIput.v at HEAD 38911e05f4;
        RTYPE decode order is (rs2, rs1, rd, op)) ------------------------------
   0x5a  JAL  ra, acquiresleep         ; a0 = s3 = &ip->lock  (set at 0x56/0x58)
   0x5e  AUIPC a0 ; 0x62 ADDI a0,a0    ; a0 := &itable
   0x66  JAL  ra, release              ; release(&itable.lock)
   0x6a  ADD  a0 := s1                 ; a0 = ip
   0x6c  JAL  ra, itrunc               ; itrunc(ip)
   0x70  SW   zero, 64(s1)             ; ip->type = 0  (in-mem; offset 64)
   0x74  ADD  a0 := s3                 ; a0 = &ip->lock
   0x76  JAL  ra, releasesleep         ; releasesleep(&ip->lock)
   0x7a  AUIPC a0 ; 0x7e ADDI a0,a0    ; a0 := &itable
   0x82  JAL  ra, acquire              ; acquire(&itable.lock)
   0x86  LW   a5, 8(s1)                ; a5 = ip->ref
   0x88  ADDIW a5, a5, -1              ; a5 = ref - 1
   0x8a  SW   a5, 8(s1)                ; ip->ref = ref-1  (1 -> 0: EVICTION)
   0x8c  AUIPC a0 ; 0x90 ADDI a0,a0    ; a0 := &itable
   0x94  JAL  ra, release              ; release(&itable.lock)
   0x98  SRLIW a5, s2, 4               ; a5 = inum >> 4  (= inum / IPB)
   0x9c  AUIPC a1 ; 0xa0 LW a1,1236(a1); a1 := sb.inodestart
   0xa4  ADDW  a1 := a1 + a5           ; a1 = IBLOCK inum inodestart
   0xa6  ADD   a0 := s4                ; a0 = dev
   0xa8  JAL  ra, bread                ; == OFF.ip_free_offlock ENTRY (a0=dev,
                                       ;    a1=IBLOCK, s2=inum)
   ---------------------------------------------------------------------------

   ---- STRUCTURAL-REORG FINDING (important for whoever grinds this) ----------
   The NEW pin is a REORGANISATION of iput vs the stale ProofIput.v proof, so
   ProofIput.v is a TACTIC-PATTERN reference ONLY, never a liftable body:
     * ref-- moved LATE: stale did it at +0x20..+0x24 (lemma [ip_tail],
       anchored +0x20); the new pin does it at 0x86..0x8a UNDER a re-acquired
       itable.lock (0x82 acquire ... 0x94 release).
     * iupdate is GONE from the free path: the stale pin flushed type=0 via a
       [iupdate] call at +0x6c; the new pin flushes it MANUALLY with the
       bread/sh-zero-88/log_write/brelse block at 0xa8.. -- i.e. OffLockDev.
     * Hence the ref-1 EVICTION machinery (ic_open_auth_ref / ic_close_to_empty
       / iref_close_last_store_au / ipool_insert) that [ip_tail]'s "REF-1 last
       close" arm runs at +0x24 is what THIS lemma must run at 0x8a.

   ---- SPEC SIGNATURES TO APPLY (all confirmed present in the lane) ----------
   * OFF.ip_free_offlock  (this file's OFF module) at 0xa8 -- byte-identical
       precondition is the EXIT target; see IputOfflockDev.v:144.
   * ASL.wp_acquiresleep_nb_sconf  (SpecAcquiresleep wp_acquiresleep_nb_body):
       args  j gil gisl "inode" (ic_tok cn k) (icfg_isl k) q  m pidv av eb dq n lks
       needs is_sleeplock_gen gil gisl (i_lock ip) "inode" (ic_tok cn k)
             (slh_tok (icfg_isl k))  +  slh_auth (icfg_isl k) None (the FREE
       evidence, minted from the slot authority via [slh_return_last] under the
       held itable.lock, EXACTLY as ProofIput.v ~1830-1900 does at stale +0x50).
   * Release.wp_release_sconf   (ProofRelease.v:506) -- release(&itable.lock).
   * IT.wp_itrunc_gen  (ProofItrunc.v:2535 / SpecItrunc.v:516) -- consumes the
       inode payload (i_dev,i_inum,inode_meta,inode_map,inode_blocks,dinode_at
       dn0, bitmap_res, sb_bmapstart, log_credit cru, log_opSe (it_entry crb u)),
       returns dinode_at (di_trunc dn), inode_meta (di_trunc dn), bm_empty,
       bitmap_res (used ∖ bm_blocks bm), and a log_opS existential.
   * Releasesleep.wp_releasesleep_gen_sconf  (ProofReleasesleep.v:74).
   * Acquire.wp_acquire_sconf  (ProofAcquire.v:836) -- re-acquire itable @0x82.

   ---- LOG-LEDGER RE-CREDIT (the subtle bit) --------------------------------
   itrunc's POST hands back [log_opS γ u' Sb'] (a CLOSED epoch).  But
   OFF.ip_free_offlock's ENTRY wants [log_opSe γ (S u) Sb e0] + [log_credit γ
   cru Sb e0 ...] + [log_epoch_lb γ v]  (an OPEN epoch, for its own manual
   inode flush).  So between itrunc's post (after +0x6c) and 0xa8 the op must
   be RE-OPENED: convert log_opS -> log_opSe at a fresh birth epoch and mint the
   flush credit.  iput_units budgets itrunc's units PLUS this one flush unit
   (see [ip_budget_bounds]/[ip_spend_w] in ProofIput.v).  Grep LogInv for
   [log_opSe_opS] (used the other direction at ProofIput.v:1471) and its
   inverse / [log_opS_named] for the re-open lemma.

   ---- ESCROW MINT ----------------------------------------------------------
   Anywhere before 0xa8, call [EscrowInode.escA_alloc ⊤ γi (bv_unsigned inum)]
   ( ⊢ |={⊤}=> ∃ ge gr, escA_inv ge gr γi (bv_unsigned inum) ∗ redeem_ticketA
   gr ).  Feeds OFF.ip_free_offlock's [escA_inv]/[redeem_ticketA] premises.
   ========================================================================== *)

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import BufOwn.
Require Import WpLock.
Require Import SleepLock.
Require Import InodeLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSconfSrliw.
Require Import WpAu4 MinstretInv.
Require Import WpSmodeHalf.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BcacheInv BioInv.
Require Import FsBlocks LogInv LogDefs.
Require Import BitmapInv.
Require Import DirView DirLinks FsTree.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import DinodeSlot.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import EscrowDefs.
Require Import EscrowInode.
Require Import EscrowDeposit.
Require Import CodeIput.
From Kernel Require KernelSyms.
Require Import ProcAvail.
(* the six call specs and the icache-table invariants *)
Require Import SpecAcquire SpecRelease SpecAcquiresleep SpecReleasesleep.
Require Import SpecItrunc SpecIupdate.
Require Import SpecIput.
Require Import IputOfflockDev.
Local Open Scope Z_scope.

Set Printing Depth 40.

Module FreeLockedDev (Acquire : ACQUIRE) (Release : RELEASE)
                     (ASL : ACQUIRESLEEP) (RS : RELEASESLEEP) (IT : ITRUNC)
                     (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE).

(* the off-lock free tail, over the SAME three leaf specs *)
Module OFF := OfflockDev BR LW BL.

Section FreeLockedDev.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).
  Notation Rs4  := (mword_of_int 20 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz  := vm_compute; discriminate.
  Local Ltac regne := reg_ne_side.

  Lemma ip_trunc32_zero : trunc32 (zero_reg : mword 64) = (mword_of_int 0 : mword 32).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma ip_pred_sub (z : Z) : (1 <= z)%Z -> (z < 2 ^ 31)%Z ->
    subrange_vec_dec
       (add_vec (sign_extend' 64 (mword_of_int z : mword 32))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0
    = (mword_of_int (z - 1) : mword 32).
  Proof.
    intros Hz1 Hb.
    rewrite <- trunc32_subrange. rewrite trunc32_add. rewrite trunc32_sext.
    assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                 = (mword_of_int (2 ^ 32 - 1) : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite HK.
    apply bv_eq.
    unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    rewrite (moi32_small z ltac:(change (2^32) with (2*2^31); lia)).
    rewrite (moi32_small (2 ^ 32 - 1) ltac:(lia)).
    rewrite moi32_unsigned.
    assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
    change (2^31) with 2147483648%Z in Hb.
    rewrite E32.
    unfold bv_wrap, bv_modulus. change (Z.of_N (MachineWord.Z_idx 32)) with 32%Z.
    rewrite E32.
    rewrite (_ : (z + (4294967296 - 1))%Z = (z - 1 + 1 * 4294967296)%Z); [|lia].
    rewrite Z.mod_add; [|lia].
    rewrite !Z.mod_small; lia.
  Qed.

  Lemma ip_storeval_pred (z : Z) : (1 <= z)%Z -> (z < 2 ^ 31)%Z ->
    trunc32 (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 (mword_of_int z : mword 32))
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
    = (mword_of_int (z - 1) : mword 32).
  Proof. intros H1 H2. rewrite trunc32_sext. exact (ip_pred_sub z H1 H2). Qed.

  (* ProofIput.v's [ip_rest_sum], module-local there; inlined here. *)
  Lemma ip_rest_sum (kk : nat) (qt : Qp) (dv nu : mword 32) :
    islot_rest_at kk qt dv nu -∗ ⌜∃ qr : Qp, (1/2)%Qp = (qt + qr)%Qp⌝.
  Proof.
    rewrite /islot_rest_at. destruct (1/2 - qt)%Qp as [q'|] eqn:Et.
    - iIntros "_". iPureIntro. exists q'. by apply Qp.sub_Some in Et.
    - iIntros "[]".
  Qed.

  (* ProofIput.v's pure set/word helpers at the LAST CLOSE, inlined here
     (they are top-level in ProofIput.v, which this file does not import). *)
  Lemma fl_moi_inum (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
  Proof.
    apply bv_eq. rewrite moi32_unsigned.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  Lemma fl_notin_diff (P S : gset Z) (z : Z) : z ∈ S -> z ∉ P ∖ S.
  Proof. set_solver. Qed.

  Lemma fl_diff_sub (X Y : gset Z) : X ∖ Y ⊆ X.
  Proof. set_solver. Qed.

  Lemma fl_pool_set (P S : gset Z) (z : Z) :
    z ∈ P -> z ∈ S -> P ∖ (S ∖ {[z]}) = {[z]} ∪ (P ∖ S).
  Proof.
    intros Hp Hs. apply set_eq. intros x. set_unfold.
    destruct (decide (x = z)) as [->|Hne]; naive_solver.
  Qed.

  Lemma fl_ci_inums_delete (ci : gmap nat (mword 32 * mword 32))
      (kk : nat) (d i : mword 32) :
    ci !! kk = Some (d, i) ->
    (forall (k1 k2 : nat) (p1 p2 : mword 32 * mword 32),
       ci !! k1 = Some p1 -> ci !! k2 = Some p2 ->
       bv_unsigned (snd p1) = bv_unsigned (snd p2) -> k1 = k2) ->
    ci_inums (delete kk ci) = ci_inums ci ∖ {[ bv_unsigned i ]}.
  Proof.
    intros Hk Hinj. apply set_eq. intros z.
    rewrite elem_of_difference elem_of_singleton !ci_inums_spec. split.
    - intros (k2 & p & Hk2 & ->).
      rewrite lookup_delete_Some in Hk2. destruct Hk2 as [Hne Hk2].
      split; [by exists k2, p |].
      intro Hc. apply Hne. symmetry.
      apply (Hinj k2 kk p (d, i) Hk2 Hk). cbn [snd]. exact Hc.
    - intros [(k2 & p & Hk2 & ->) Hz].
      exists k2, p. rewrite lookup_delete_Some. split; [| reflexivity].
      split; [| exact Hk2].
      intros ->. apply Hz. rewrite Hk in Hk2. injection Hk2 as <-. reflexivity.
  Qed.

  (* ==========================================================================
     DRAFT STATEMENT.  Entry at iput+0x5a with itable.lock HELD and the inode
     slot CHECKED OUT.  Assembled from:
       - itrunc's precondition  (the inode payload + bitmap + log credit),
       - ip_tail's itable-held bundle (locked / itable_half / iref_slots_auth /
         isl_pool / islot2-list / ipool / inode_ref / is_lock itable),
       - wp_iput_gen_body's [is_sleeplock_gen] (the sleeplock for acquiresleep),
       - offlock's environmental resources (kernel_text/data, panic_env, bio_ctx,
         log_ctx, dev_inv, disk_geom, is_lock virtio, procs_inv, p_pid, the
         6-slot frame, cpu_own/sie_cap_gpr/trap_csrs/cpu_claim).
     The continuation is iput's real +0x30 post (ip_tail's post shape).
     NOTE: register/frame facts and the exact packaged-vs-opened form of the
     slot still need to be reconciled against the body; treat as a first cut.

     COMPOSITION SMOKE-TEST (2026-08-17): the ENTRY-CHECK block's exit and
     this lemma's entry are now SHAPE-IDENTICAL.  The icache-table group of
     premises below -- [locked] / [itable_half] / [iref_slots_auth] /
     [isl_pool] / [ipool] / ⌜ci !! k = Some (dev, inum)⌝ / [iref_tok] /
     [ic_id] / the re-assembly wand -- is a verbatim copy of
     [IputFreeEntryDev.ip_free_entry]'s EXIT B (cdcd2c86f5,
     IputFreeEntryDev.v:428-467), in the same order and with the same
     arguments.  ip_free_entry's Exit-B continuation therefore discharges
     this entry by [iApply] with nothing re-derived on either side; the
     islot2 big-op and [IcacheRef.inode_ref] that used to sit here are
     UNSATISFIABLE at 0x5a and no longer appear (see the i_inum-split note at
     the premise site, and the 586 site in the body where the surplus half is
     now fed to the wand instead of dropped).
     ========================================================================== *)
  Lemma ip_free_locked `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl gil gisl g1 : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8))
      (Mt : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (u : nat) (Sb : gset Z) (crb cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqd dqn dqb dqs : dfrac)
      (sp0 vra vs0 vs1 vs2 vs3 vs4 : mword 64)
      (m : regfile) (K : nat) (eb b : bool) (lks : gset string) :
    let ip := ientry k in
    let pj := proc_addr j in
    (* ---- pure premises (union of itrunc's + the icache-table facts) ---- *)
    (K_iput <= K)%nat ->
    (* itrunc's cone reserve: K_itrunc(68) <= K-6 (iput holds 6 for its own
       frame), i.e. K >= 74.  Stronger than K_iput=72; flagged for splice. *)
    (K_itrunc <= K - 6)%nat ->
    (k < NINODE)%nat ->
    (* iput_units = 3: itrunc's two plus the off-lock inode flush's one.  The
       [3] (not [2]) is what makes itrunc's post leave [1 <= u'], i.e. an
       [S _] for [OFF.ip_free_offlock]'s [log_opSe γ (S u) Sb e0]. *)
    (3 <= u)%nat ->
    (Z.of_nat u + 2 < 2 ^ 31)%Z ->
    (crb = true -> bmapstart ∈ Sb) ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart -> bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_type dn) <> 0 ->
    bv_unsigned (di_nlink dn) = 0 ->
    dinode_wf dn ->
    blkmap_wf cov logstart bm ->
    cov_below cov size ->
    (forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE) ->
    di_addrs dn = bm_cells bm ->
    icM_wf Mt ->
    ic_ci_wf Mt ci nib dev ->
    (* FREE-PATH GUARD: this is the LAST reference (ref==1). *)
    Mt !! k = Some (q, 1%positive) ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    sp0 = m !!! Regidx csp_rs1 ->
    m !!! Regidx Ra0 = (i_lock ip : mword 64) ->
    m !!! Regidx Rs1 = (ip : mword 64) ->
    m !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64) ->
    m !!! Regidx Rs3 = (i_lock ip : mword 64) ->
    m !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64) ->
    locks_below lks "log" ->
    "itable" ∉ lks ->
    sie_cap_gpr m (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay 0 eb pj -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (KernelSyms.iput + 0x5a) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    (* the itable, HELD *)
    is_lock gtl itable_lock "itable"%string (itable_res2 cn γfs γi cov logstart nib dev) -∗
    itable_inv -∗
    ic_escrow cn γfs γi cov logstart k -∗
    locked gtl cpu_id -∗
    itable_half Mt -∗
    iref_slots_auth -∗
    isl_pool Mt -∗
    ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
    (* ================================================================
       THE WINDOW'S i_inum SPLIT -- the entry can NOT ask for the islot2
       big-op and [inode_ref] here, and the reason is forced, not a
       proof-engineering choice.  At 0x5a the payload is OUT, so the escrow
       sits on its HELD arm, and [IcacheEscrow.ic_held] owns [i_inum] AT
       DFRAC 1 by design (the arm's own 1/2 PLUS the closer's [q] PLUS the
       table's [1/2 - q]) -- i.e. exactly the two [i_inum] shares that live
       inside [IcacheRef.inode_ref] and inside [islot2 cn Mt ci k]'s
       [islot_rest_at].  Neither of those two resources exists at this pc.
       The fingerprint of the over-count was in this file's own body: the
       0x76 [ic_open_held] returns [i_inum] WHOLE and the surplus half was
       DROPPED on the floor.

       What is taken instead is the pieces that DO exist plus a RE-ASSEMBLY
       WAND: fed the surplus half (now no longer dropped) and the borrowed
       [ic_id], it rebuilds the islot2 list and the reference's identity
       exactly.  This block is a VERBATIM copy of
       [IputFreeEntryDev.ip_free_entry]'s EXIT B (IputFreeEntryDev.v:461-467
       at cdcd2c86f5), so the Exit-B -> entry hand-off is SHAPE-IDENTICAL:
       the integration passes Exit B's four arguments straight through with
       no re-derivation on either side.
       ================================================================ *)
    ⌜ci !! k = Some (dev, inum)⌝ -∗
    iref_tok k q -∗
    ic_id cn k (1/2) true dev inum -∗
    (i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
     ic_id cn k (1/2) true dev inum -∗
       ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) ∗
       IcacheRef.inode_ident k (DfracOwn q) dev inum) -∗
    (* the sleeplock for the acquiresleep at 0x5a *)
    is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                     (slh_tok (icfg_isl k)) -∗
    (* THE ESCROW-HELD STATE (design fork RESOLVED, take 2): at 0x5a the
       inode was checked out by iput's prologue (to read nlink at +0x44), so
       the loaded content rides in hand AS [ic_payload_at] at its generation
       [g1], together with the escrow's own liveness half [live_gen k ½ g1].
       This is NOT the itrunc-clean decomposition: the deposit dance the
       releasesleep at 0x76 needs runs [ic_open_held], which CONSUMES exactly
       these two (plus iref_frag/live_frac out of the [iref_tok] above and
       the [ic_id] the entry now takes directly, the two pieces that used to
       be popped from [inode_ref] and from the islot2 big-op before the
       i_inum-split note above retired both); the clean subset cannot
       rebuild [ic_payload_at] (it lacks
       the dir-link ledger, the disk-data cells and the well-formedness).
       The body UNPACKS [ic_payload_at] -> inode_meta/map/blocks/i_dev/i_inum
       to feed itrunc after the deposit is placed. *)
    ic_payload_at γfs γi cov logstart k inum g1 dn bm -∗
    live_gen k (1/2) g1 -∗
    (* the checkout's OTHER half of the valid cell (the prologue's), joined
       with ic_open_held's half at the +0x70 ip->valid=0 store *)
    i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) -∗
    ireg_inv γi γfs inodestart nib -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    p_pid pj ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    log_epoch_lb γ v -∗
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ u Sb e0 -∗
    (* the 6-slot frame: ra/s0/s1 ride to the epilogue; s2/s3/s4 restored at 0x30 *)
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈ vra -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈ vs0 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈ vs1 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈ vs2 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ vs3 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ vs4 -∗
    (* THE CALLER'S CONTINUATION at 0x30 (iput's real post; ip_tail's shape) *)
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z) (w : bool),
        (* the register threading is [OFF.ipo_thr]'s, not [callee_saved]:
           s1 holds the off-lock tail's [bp] and is restored by the epilogue
           AFTER 0x30, so nothing at 0x30 may claim it back. *)
        ⌜OFF.ipo_thr m mf /\ mf !!! Regidx csp_rs1 = sp0
          /\ mf !!! Regidx Rs2 = vs2 /\ mf !!! Regidx Rs3 = vs3
          /\ mf !!! Regidx Rs4 = vs4⌝ -∗
        sie_cap_gpr (CID := CID) mf (K - 6)%nat eb pj -∗
        cpu_own (CID := CID) 0 eb pj eb lks -∗
        trap_csrs_ext (CID := CID) eb -∗
        cpu_claim_ext (CID := CID) eb pj -∗
        pc_is (CID := CID) (mword_of_int (KernelSyms.iput + 0x30) : mword 64) -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res γfs bmapstart cov logstart size used'' -∗
        (* the off-lock deposit's parked pool entry, on its pending arm *)
        ipool_shape γfs γi cov logstart inum -∗
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜w = true -> bmapstart ∈ Sb''⌝ -∗
        ⌜crb = true -> w = false⌝ -∗
        log_opS γ n'' Sb'' -∗
        iref_slot -∗
        (* frame ra/s0/s1 slots, still saved, for the epilogue *)
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈ vra -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈ vs0 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈ vs1 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈ vs2 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈ vs3 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈ vs4 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ip pj HK HKit Hk Hu2 Hubnd Hcrb Hgeom Hsize Hbmpos Hbmcov Hbmlog Histpos Hicov Hilog
           Hnib Hdtnz Hnl0 Hdnwf Hbmwf Hbelow Hdlen Hadr HMwf Hciwf HMk1 Hj Hgl
           Hsp0 Ha0 Hs1v Hs2v Hs3v Hs4v Hlkbelow Hitnotin.
    iIntros "Hcg Hcnt Hpay Hextc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx
             #Hitlk #Hitinv #Hesc Htok Hhalf Hiauth Hipool Hpool %Hcik Hrtok Hgid Hwand
             #Hslk Hpayl Hlvh Hvb #Hireg Hbms Hins Hbm Hppid
             #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots #Hvlb Hcrd Hop
             Hra Hs0f Hs1f Hs2f Hs3f Hs4f Hcont".
    (* ===== +0x5a jal acquiresleep -- the ref-1 NON-BLOCKING lock ===== *)
    iPoseProof (ipi_5a with "Htext") as "Hi5a".
    assert (Hslfresh : "sleep lock"%string ∉ ({["itable"%string]} ∪ lks : gset string)).
    { apply not_elem_of_union. split.
      - apply not_elem_of_singleton. discriminate.
      - apply (locks_below_not_elem lks "sleep lock"%string). lkbelow. }
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x5a)) Rra
              (mword_of_int 2986 : mword 21) m (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x5a) : mword 64) 4)]> m).
    assert (Htgtasl : add_vec (mword_of_int (KernelSyms.iput + 0x5a) : mword 64)
                        (sign_extend' 64 (mword_of_int 2986 : mword 21))
                      = mword_of_int KernelSyms.acquiresleep) by pcw.
    iEval (rewrite Htgtasl) in "Hpc".
    assert (HR0a0 : R0 !!! Regidx Ra0 = (i_lock ip : mword 64))
      by (rewrite /R0 upd_ne; [exact Ha0 | nz]).
    assert (HR0ra : R0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x5a) : mword 64) 4)
      by (rewrite /R0; apply upd_eq).
    (* mint the LOCK-FREE evidence: return the whole ref share to the slot authority *)
    iDestruct (isl_pool_acc_upd Mt k Hk with "Hipool") as "[Hisl Hislback]".
    rewrite (isl_slot_some Mt k q 1%positive HMk1).
    iDestruct "Hrtok" as "(Hrfrg & Hrlv & Hrslh)".
    iMod (slh_return_last (icfg_isl k) q with "Hisl Hrslh") as "Hisl".
    iApply (ASL.wp_acquiresleep_nb_sconf (dq := dq) j gil gisl "inode"%string
              (ic_tok cn k) (icfg_isl k) q R0 pidv (trap_res eb + (K - 6))%nat eb 0%nat
              ({["itable"]} ∪ lks)
              ltac:(lia) ltac:(cbn; lia) Hslfresh
              with "Hcg Hcnt Htext Hpc [] Hisl Hppid").
    { iEval (rewrite HR0a0). iExact "Hslk". }
    (* ===== acquiresleep returns: place the deposit, re-park, release itable ===== *)
    iApply wp_next_off_intro.
    iIntros (mfa) "%Hcsa Hcg Hcnt Hpc Hstok Hisl Hspid Hictok Hppid".
    rewrite -(isl_slot_some Mt k q 1%positive HMk1).
    iDestruct ("Hislback" $! Mt with "[%] Hisl") as "Hipool"; [ done |].
    iEval (rewrite HR0a0) in "Hspid".
    assert (Hpc5e : ret_pc (R0 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x5e))
      by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc5e) in "Hpc".
    pose proof Hcsa as Hcsa_cs.
    assert (Hmfas1 : mfa !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite (callee_saved_lookup Hcsa_cs Rs1 ltac:(vm_compute; reflexivity)); exact Hs1v).
    assert (Hmfas2 : mfa !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hcsa_cs Rs2 ltac:(vm_compute; reflexivity)); exact Hs2v).
    assert (Hmfas3 : mfa !!! Regidx Rs3 = (i_lock ip : mword 64))
      by (rewrite (callee_saved_lookup Hcsa_cs Rs3 ltac:(vm_compute; reflexivity)); exact Hs3v).
    assert (Hmfas4 : mfa !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hcsa_cs Rs4 ltac:(vm_compute; reflexivity)); exact Hs4v).
    assert (Hmfasp : mfa !!! Regidx csp_rs1 = sp0)
      by (rewrite (callee_saved_lookup Hcsa_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact (eq_sym Hsp0)).
    (* ---- open the escrow, bump the generation, check out a deposit ---- *)
    iApply fupd_wp.
    (* [Hcik], [Hgid] and the islot2 list's OWN re-assembly all come straight
       from the entry now (Exit B's four arguments): at this pc the escrow's
       HELD arm owns [i_inum] whole, so there is no islot2 big-op and no
       [inode_ref] to pop -- see the statement's i_inum-split note.  The
       accessor/agreement/[1/2 - q] dance those two used to need is inside
       the wand, which is discharged three lines below the [ic_open_held]. *)
    iRename "Hrfrg" into "Hfrg". iRename "Hrlv" into "Hlvq".
    iMod (live_slot_regen ⊤ Mt k q 1%positive ltac:(solve_ndisj) HMk1
            with "Hitinv Hhalf Hlvq [Hlvh]") as (ga') "(Hhalf & Hlvq & Hlvh & Hpend)";
      [iExists g1; iExact "Hlvh" |].
    iInv "Hesc" as ">Hbody" "Hclose".
    iAssert (live_frac k q) with "[Hlvq]" as "Hlvqf"; [ iExists ga'; iExact "Hlvq" |].
    iMod (ic_open_held cn γfs γi cov logstart k (⊤ ∖ ↑icEscN)
            Mt q ga' g1 dev inum dn bm ltac:(solve_ndisj) HMk1
            with "Hitinv Hbody Hhalf Hfrg Hlvqf Hlvh Hgid Hpayl")
      as "(Hhalf & Hfrg & Hlvq2 & Hlvh & Hgid & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
    (* ---- THE 586 SITE.  [ic_open_held] hands [i_inum] back WHOLE; itrunc
       keeps one half ([Hinh], with [Hidv]) and the SURPLUS half -- which this
       body used to drop on the floor -- is fed to the entry's re-assembly
       wand together with the borrowed [ic_id].  Out come the islot2 list and
       the reference's identity, i.e. exactly the two resources the entry
       could not have asked for; the deposit's cells (q) then come off the
       ident and the re-park's (qr) are already inside the rebuilt list. ---- *)
    iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hnsurp]".
    iDestruct ("Hwand" with "Hnsurp Hgid") as "[Hslots Hrident]".
    iEval (rewrite /IcacheRef.inode_ident) in "Hrident".
    iDestruct "Hrident" as "[Hrd Hrn]".
    iDestruct "Hlvq2" as (gr) "Hlvr".
    iDestruct (live_gen_agree with "Hlvr Hlvh") as %->.
    iMod (ic_dep_checkout cn k (DepRef q dev inum ga') with "Hictok") as "[Hdepa Hdepk]".
    iMod ("Hclose" with "[Hdepa Hfrg Hlvr Hlvh Hrd Hrn Hmt Hgida]") as "_".
    { iApply bi.later_intro.
      iApply (ic_close_out cn γfs γi cov logstart k (DepRef q dev inum ga') dev inum
                with "Hdepa [Hfrg Hlvr Hlvh Hrd Hrn] Hmt Hgida").
      rewrite /ic_dep_res /ic_dep_own /ic_dep_half.
      iSplitR "Hlvh"; [| iExact "Hlvh"].
      iSplitR; [iPureIntro; exact (conj eq_refl eq_refl) |].
      rewrite /IcacheRef.inode_ref_gen_bare /IcacheRef.inode_ident. iFrame. }
    iModIntro.
    iAssert (itable_res2 cn γfs γi cov logstart nib dev)
      with "[Hhalf Hiauth Hipool Hslots Hpool]" as "HRres".
    { iExists Mt, ci. iFrame. iPureIntro. split; assumption. }
    (* ===== +0x5e auipc a0 ; +0x62 addi a0,a0,1306 ; +0x66 jal release ===== *)
    iPoseProof (ipi_5e with "Htext") as "Hi5e".
    iPoseProof (ipi_62 with "Htext") as "Hi62".
    iPoseProof (ipi_66 with "Htext") as "Hi66".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x5e)) Ra0
              (mword_of_int 29 : mword 20) mfa (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (H1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x5e) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> mfa).
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.iput + 0x5e) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x62)) by pcw.
    iEval (rewrite Hpp62) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x62)) Ra0 Ra0
              (mword_of_int 1306 : mword 12) H1 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi62").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (H1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1306 : mword 12)))]> H1).
    assert (HH2a0 : H2 !!! Regidx Ra0 = itable_lock).
    { rewrite /H2 upd_eq /H1 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.iput + 0x62) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x66)) by pcw.
    iEval (rewrite Hpp66) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x66)) Rra
              (mword_of_int 2087012 : mword 21) H2 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (H3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x66) : mword 64) 4)]> H2).
    assert (Htgtrl : add_vec (mword_of_int (KernelSyms.iput + 0x66) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087012 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrl) in "Hpc".
    assert (HH3a0 : H3 !!! Regidx Ra0 = itable_lock)
      by (rewrite /H3 upd_ne; [exact HH2a0 | nz]).
    assert (HH3ra : H3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x66) : mword 64) 4)
      by (rewrite /H3; apply upd_eq).
    assert (HH3thr : forall c : mword 5, is_cs_idx c = true ->
                       H3 !!! Regidx c = mfa !!! Regidx c).
    { intros c Hcs. rewrite /H3 upd_ne; [| regne].
      rewrite /H2 upd_ne; [| regne]. rewrite /H1 upd_ne; [reflexivity | regne]. }
    iApply (Release.wp_release_sconf gtl itable_lock "itable"%string
              (itable_res2 cn γfs γi cov logstart nib dev) H3
              0%nat eb pj (K - 6)%nat ({["itable"]} ∪ lks)
              ltac:(rewrite HH3a0; reflexivity) ltac:(lia)
              with "Hcg Htext Hpc [Hitlk] Htok HRres Hcnt Hpay").
    { iExact "Hitlk". }
    iIntros (CIDrl Hsrl mr1) "Hcg Hpc %Hpins1 Hcnt".
    iEval (rewrite (_ : ({["itable"]} ∪ lks) ∖ {["itable"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hcnt".
    pose proof Hpins1 as Hpins1_cs.
    assert (Hpc6a : ret_pc (H3 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x6a))
      by (rewrite HH3ra; pcw).
    iEval (rewrite Hpc6a) in "Hpc".
    assert (Hmr1c : forall c : mword 5, is_cs_idx c = true ->
                      mr1 !!! Regidx c = mfa !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hpins1_cs c Hcs). exact (HH3thr c Hcs). }
    assert (Hmr1s1 : mr1 !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite (Hmr1c Rs1 ltac:(vm_compute; reflexivity)); exact Hmfas1).
    assert (Hmr1s2 : mr1 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (Hmr1c Rs2 ltac:(vm_compute; reflexivity)); exact Hmfas2).
    assert (Hmr1s3 : mr1 !!! Regidx Rs3 = (i_lock ip : mword 64))
      by (rewrite (Hmr1c Rs3 ltac:(vm_compute; reflexivity)); exact Hmfas3).
    assert (Hmr1s4 : mr1 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite (Hmr1c Rs4 ltac:(vm_compute; reflexivity)); exact Hmfas4).
    assert (Hmr1sp : mr1 !!! Regidx csp_rs1 = sp0)
      by (rewrite (Hmr1c csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmfasp).
    iPoseProof (ipi_6a with "Htext") as "Hi6a".
    iPoseProof (ipi_6c with "Htext") as "Hi6c".
    (* ===== +0x6a c.mv a0,s1 (a0:=ip) ; +0x6c jal itrunc ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x6a)) Ra0 Rs1
              mr1 (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6a").
    iIntros (CIDm1 Hsm1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr1 !!! Regidx Rs1))]> mr1).
    assert (HJ1a0 : J1 !!! Regidx Ra0 = (ip : mword 64)).
    { rewrite /J1 upd_eq. rewrite Hmr1s1. apply add_vec_zero_l. }
    assert (HJ1c : forall c : mword 5, is_cs_idx c = true ->
                     J1 !!! Regidx c = mr1 !!! Regidx c)
      by (intros c Hcs; rewrite /J1 upd_ne; [reflexivity | regne]).
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.iput + 0x6a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x6c)) Rra
              (mword_of_int 2096896 : mword 21) J1 (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6c").
    iIntros (CIDm2 Hsm2) "Hcg Hpc".
    set (J2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x6c) : mword 64) 4)]> J1).
    assert (Htgtit : add_vec (mword_of_int (KernelSyms.iput + 0x6c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096896 : mword 21))
                     = mword_of_int KernelSyms.itrunc) by pcw.
    iEval (rewrite Htgtit) in "Hpc".
    assert (HJ2a0 : J2 !!! Regidx Ra0 = (ip : mword 64))
      by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
    assert (HJ2ra : J2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x6c) : mword 64) 4)
      by (rewrite /J2; apply upd_eq).
    assert (HJ2c : forall c : mword 5, is_cs_idx c = true ->
                     J2 !!! Regidx c = mr1 !!! Regidx c).
    { intros c Hcs. rewrite /J2 upd_ne; [| regne]. exact (HJ1c c Hcs). }
    (* ---- unpack the checked-out payload for itrunc ---- *)
    iEval (rewrite /ic_payload_at) in "Hpayl".
    iDestruct "Hpayl" as "[Hlk2 _]".
    iDestruct "Hlk2" as (data2)
      "(%Hok2 & %Hdok2 & %Hddix2 & %Hdoc2 & %Hduq2 & Hdlk2 & Hdat & Hmeta & Haddrs & Hind & Hblks)".
    pose proof Hok2 as Hok2'.
    destruct Hok2' as (Hbmwf2 & Hcovers2 & Hdiaddrs2 & Htyne2 & Hszcap2 & Hholes2 & Hsized2).
    (* ---- transport the cpu bundle to the itrunc call site (CIDm2) ---- *)
    iDestruct (cpu_own_transport CIDrl CIDm2 0%nat eb pj eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDm2 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDm2 eb pj
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    pose (uit := (u - (if crb then 1 else 2))%nat).
    assert (Hun : it_entry crb uit = u) by (unfold it_entry, uit; destruct crb; lia).
    (* ===== itrunc ===== *)
    iApply (IT.wp_itrunc_gen γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart bmapstart inodestart nib size dev used
              (ip : mword 64) inum dn dn bm data2 uit Sb crb cru e0
              pidv dq (DfracOwn (1/2)) (DfracOwn (1/2)) dqb dqs J2 (K - 6)%nat
              eb eb lks
              HKit Hcrb
              Hgeom Hsize Hbmpos Hbmcov Hbmlog Histpos Hicov Hilog
              Hnib Htyne2
              (InodeRegion.di_type_stable_refl dn)
              (InodeRegion.di_nlink_stable_refl dn Htyne2)
              Hbmwf2 Hbelow Hsized2 Hdiaddrs2 Hj Hgl HJ2a0
              ltac:(lkbelow)
              with "Hcg Hcnt Hextc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hidv Hinh Hmeta
                    [Haddrs Hind] Hblks Hbms Hins Hbm Hireg Hdat Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hbslots Hcrd [Hop]").
    all: try lkbelow.
    { rewrite /inode_map. iFrame. }
    { rewrite Hun. iExact "Hop". }
    iIntros (CIDit Hsit mfi)
      "%Hcsi Hcg Hcnt Hextc Hclm Hpc Hppid Hidv Hinh Hbms Hins Hmeta Hmap Hblks
       Hbm Hdat Hbslots Hopx".
    assert (Hpc70 : ret_pc (J2 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x70))
      by (rewrite HJ2ra; pcw).
    iEval (rewrite Hpc70) in "Hpc".
    pose proof Hcsi as Hcsi_cs.
    assert (Hmfic : forall c : mword 5, is_cs_idx c = true ->
                      mfi !!! Regidx c = mr1 !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsi_cs c Hcs). exact (HJ2c c Hcs). }
    assert (Hmfis1 : mfi !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite (Hmfic Rs1 ltac:(vm_compute; reflexivity)); exact Hmr1s1).
    assert (Hmfis2 : mfi !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (Hmfic Rs2 ltac:(vm_compute; reflexivity)); exact Hmr1s2).
    assert (Hmfis3 : mfi !!! Regidx Rs3 = (i_lock ip : mword 64))
      by (rewrite (Hmfic Rs3 ltac:(vm_compute; reflexivity)); exact Hmr1s3).
    assert (Hmfis4 : mfi !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite (Hmfic Rs4 ltac:(vm_compute; reflexivity)); exact Hmr1s4).
    assert (Hmfisp : mfi !!! Regidx csp_rs1 = sp0)
      by (rewrite (Hmfic csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmr1sp).
    iPoseProof (ipi_70 with "Htext") as "Hi70".
    (* ===== +0x70 sw zero,64(s1) : ip->valid = 0 (plain store) ===== *)
    iDestruct "Hvldx" as (w0) "Hva".
    iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
    iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
    iDestruct (sie_cap_gpr_x0 mfi (K - 6)%nat eb pj Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0u Hcg]".
    assert (Hpa70 : add_vec (rget mfi Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne mfi Rs1 ltac:(nz)) Hmfis1. reflexivity. }
    iEval (rewrite -Hpa70) in "Hvld".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.iput + 0x70)) Rz Rs1
              (mword_of_int 64 : mword 12) mfi (K - 6)%nat (valid_word true) eb
              with "Hcg Hpc Hi70 Hvld").
    iIntros (CIDsw Hssw) "Hcg Hpc Hvld".
    iEval (rewrite Hpa70) in "Hvld".
    assert (Hsv70 : trunc32 (rget mfi Rz) = valid_word false).
    { rewrite (rget_ne mfi Rz ltac:(nz)) Hx0u. exact ip_trunc32_zero. }
    iEval (rewrite Hsv70) in "Hvld".
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.iput + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ---- re-park the slot UNLOADED at the fresh generation ga', at the
       ipool_alloc pool shape (record is di_trunc dn, type<>0, size 0 so all
       dir facts are vacuous -- unlike ProofIput's post-iupdate imark) ---- *)
    assert (Hsz0 : bv_unsigned (di_size (di_trunc dn)) = 0) by (vm_compute; reflexivity).
    assert (Hnl0t : bv_unsigned (di_nlink (di_trunc dn)) = 0) by exact Hnl0.
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    iDestruct "Hmap" as "[Haddrs Hind]".
    iAssert (ic_payload γfs γi cov logstart k inum ga' false)
      with "[Hmeta Haddrs Hdat Hind Hblks Hpend]" as "Hpayf".
    { rewrite /ic_payload /ic_unloaded.
      iSplitR "Hpend"; [| iExact "Hpend"].
      iSplitR "Hdat Hind Hblks".
      - rewrite /inode_raw. iSplitL "Hmeta"; [iExists (di_trunc dn); iExact "Hmeta" |].
        iExists (bm_cells bm_empty).
        iSplitR; [iPureIntro; vm_compute; reflexivity |]. iExact "Haddrs".
      - rewrite /ipool_shape_np. iLeft. rewrite /ipool_alloc.
        iExists (di_trunc dn), bm_empty, (fun _ => replicate BSIZE (bv_0 8)).
        iSplitR.
        { iPureIntro. rewrite /inode_ok. split_and!.
          - exact (bm_empty_wf cov logstart).
          - apply bm_covers_nonpos. rewrite Hsz0. lia.
          - exact (di_trunc_addrs dn).
          - change (di_type (di_trunc dn)) with (di_type dn). exact Hdtnz.
          - rewrite Hsz0. pose proof (Nat2Z.is_nonneg MAXFILE);
              pose proof (Nat2Z.is_nonneg BSIZE); nia.
          - apply bm_empty_holes. intros i. reflexivity.
          - exact inode_sized_zero. }
        iSplitR; [iPureIntro; exact (dir_ok_size_zero icfg_nib (di_trunc dn) _ Hsz0) |].
        iSplitR; [iPureIntro;
                  exact (dir_dots_ix_orphan (bv_unsigned inum) (di_trunc dn) _ Hnl0t) |].
        iSplitR; [iPureIntro; exact (dir_orphan_clean_size_zero (di_trunc dn) _ Hsz0) |].
        iSplitR; [iPureIntro; exact (dir_uniq_size_zero (di_trunc dn) _ Hsz0) |].
        iSplitR "Hdat Hind Hblks";
          [iApply (dir_links_size_zero (bv_unsigned inum) (di_trunc dn)
                     (fun _ => replicate BSIZE (bv_0 8)) Hsz0 ltac:(rewrite Hnl0t; lia)) |].
        iFrame "Hdat Hind Hblks". }
    iMod (ic_swap_park cn γfs γi cov logstart k (DepRef q dev inum ga') ga'
            false dev inum eq_refl with "Hbody Hdepk Hidv Hinh Hvld Hpayf")
      as "(Hbody & Hictok & Hrefo)".
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
    iModIntro.
    iDestruct "Hrefo" as "[_ Href]".
    iPoseProof (ipi_74 with "Htext") as "Hi74".
    iPoseProof (ipi_76 with "Htext") as "Hi76".
    (* ===== +0x74 c.mv a0,s3 ; +0x76 jal releasesleep ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x74)) Ra0 Rs3
              mfi (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
    iIntros (CIDm5 Hsm5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfi !!! Regidx Rs3))]> mfi).
    assert (HJ5a0 : J5 !!! Regidx Ra0 = i_lock ip).
    { rewrite /J5 upd_eq. rewrite Hmfis3. apply add_vec_zero_l. }
    assert (HJ5c : forall c : mword 5, is_cs_idx c = true ->
                     J5 !!! Regidx c = mfi !!! Regidx c)
      by (intros c Hcs; rewrite /J5 upd_ne; [reflexivity | regne]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.iput + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x76)) Rra
              (mword_of_int 3042 : mword 21) J5 (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi76").
    iIntros (CIDm6 Hsm6) "Hcg Hpc".
    set (J6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x76) : mword 64) 4)]> J5).
    assert (Htgtrs : add_vec (mword_of_int (KernelSyms.iput + 0x76) : mword 64)
                       (sign_extend' 64 (mword_of_int 3042 : mword 21))
                     = mword_of_int KernelSyms.releasesleep) by pcw.
    iEval (rewrite Htgtrs) in "Hpc".
    assert (HJ6a0 : J6 !!! Regidx Ra0 = i_lock ip)
      by (rewrite /J6 upd_ne; [exact HJ5a0 | nz]).
    assert (HJ6ra : J6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x76) : mword 64) 4)
      by (rewrite /J6; apply upd_eq).
    assert (HJ6c : forall c : mword 5, is_cs_idx c = true ->
                     J6 !!! Regidx c = mfi !!! Regidx c).
    { intros c Hcs. rewrite /J6 upd_ne; [| regne]. exact (HJ5c c Hcs). }
    iDestruct (cpu_own_transport CIDit CIDm6 0%nat eb pj eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (RS.wp_releasesleep_gen_sconf γs gil gisl "inode"%string (ic_tok cn k)
              (slh_tok (icfg_isl k)) q J6 pidv pj (K - 6)%nat eb eb lks
              ltac:(lia) ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc [] Hstok [Hspid] Hictok Hprocs").
    all: try lkbelow.
    { iEval (rewrite HJ6a0). iExact "Hslk". }
    { iEval (rewrite HJ6a0). iExact "Hspid". }
    iIntros (CIDrs Hsrs mrs) "%Hcsr Hcg Hcnt Hpc Hrslh".
    iAssert (inode_ref k q dev inum) with "[Href Hrslh]" as "Href".
    { rewrite inode_ref_gen_intro. iExists ga'.
      rewrite inode_ref_gen_bare_split. iFrame. }
    assert (Hpc7a : ret_pc (J6 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x7a))
      by (rewrite HJ6ra; pcw).
    iEval (rewrite Hpc7a) in "Hpc".
    pose proof Hcsr as Hcsr_cs.
    assert (Hmrsc : forall c : mword 5, is_cs_idx c = true ->
                      mrs !!! Regidx c = mfi !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsr_cs c Hcs). exact (HJ6c c Hcs). }
    assert (Hitbelow : locks_below lks "itable") by lkbelow.
    iPoseProof (ipi_7a with "Htext") as "Hi7a".
    iPoseProof (ipi_7e with "Htext") as "Hi7e".
    iPoseProof (ipi_82 with "Htext") as "Hi82".
    (* ===== +0x7a auipc a0 ; +0x7e addi a0,a0,1278 ; +0x82 jal acquire ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x7a)) Ra0
              (mword_of_int 29 : mword 20) mrs (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7a").
    iIntros (CIDm7 Hsm7) "Hcg Hpc".
    set (J7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x7a) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> mrs).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.iput + 0x7a) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x7e)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x7e)) Ra0 Ra0
              (mword_of_int 1278 : mword 12) J7 (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e").
    iIntros (CIDm8 Hsm8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (J7 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1278 : mword 12)))]> J7).
    assert (HJ8a0 : J8 !!! Regidx Ra0 = itable_lock).
    { rewrite /J8 upd_eq /J7 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.iput + 0x7e) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x82)) by pcw.
    iEval (rewrite Hpp82) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x82)) Rra
              (mword_of_int 2086848 : mword 21) J8 (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi82").
    iIntros (CIDm9 Hsm9) "Hcg Hpc".
    set (J9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x82) : mword 64) 4)]> J8).
    assert (Htgtac2 : add_vec (mword_of_int (KernelSyms.iput + 0x82) : mword 64)
                        (sign_extend' 64 (mword_of_int 2086848 : mword 21))
                      = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Htgtac2) in "Hpc".
    assert (HJ9a0 : J9 !!! Regidx Ra0 = itable_lock)
      by (rewrite /J9 upd_ne; [exact HJ8a0 | nz]).
    assert (HJ9ra : J9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x82) : mword 64) 4)
      by (rewrite /J9; apply upd_eq).
    assert (HJ9c : forall c : mword 5, is_cs_idx c = true ->
                     J9 !!! Regidx c = mrs !!! Regidx c).
    { intros c Hcs. rewrite /J9 upd_ne; [| regne].
      rewrite /J8 upd_ne; [| regne]. rewrite /J7 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CIDrs CIDm9 0%nat eb pj eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf gtl "itable"%string
              (itable_res2 cn γfs γi cov logstart nib dev) J9
              0%nat eb pj (K - 6)%nat eb lks ltac:(lia) ltac:(lia) Hitbelow
              with "Hcg Hcnt Htext Hpc [Hitlk]").
    all: try lkbelow.
    { iEval (rewrite HJ9a0). iExact "Hitlk". }
    iIntros (CIDac2 Hsac2 ms2 macq2) "%Hmsf2 Hcg Hpc %Hap2 Htok HRres2 Hcnt Hpay".
    assert (Hpc86 : ret_pc (J9 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x86))
      by (rewrite HJ9ra; pcw).
    iEval (rewrite Hpc86) in "Hpc".
    pose proof Hap2 as Hap2_cs.
    assert (Hma2c : forall c : mword 5, is_cs_idx c = true ->
                      macq2 !!! Regidx c = mrs !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hap2_cs c Hcs). exact (HJ9c c Hcs). }
    assert (Hma2s1 : macq2 !!! Regidx Rs1 = (ip : mword 64)).
    { rewrite (Hma2c Rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hmrsc Rs1 ltac:(vm_compute; reflexivity)). exact Hmfis1. }
    assert (Hma2s2 : macq2 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)).
    { rewrite (Hma2c Rs2 ltac:(vm_compute; reflexivity)).
      rewrite (Hmrsc Rs2 ltac:(vm_compute; reflexivity)). exact Hmfis2. }
    (* ===== the ref-- eviction (REF-1): 0x86 lw / 0x88 addiw / 0x8a sw_au ===== *)
    iDestruct "HRres2" as (Mt2 ci2)
      "(Hhalf & %Hwf2 & %Hciwf2 & Hiauth & Hipool & Hslots & Hpool)".
    iDestruct "Href" as "[Hrtok Hrident]".
    iDestruct (iref_lookup with "Hhalf Hrtok") as %(qt2 & cnt2 & HMk2 & Hqt1 & Hone2 & Hone2').
    pose proof (icM_wf_count Mt2 k qt2 cnt2 Hwf2 HMk2) as Hcntb2.
    iPoseProof (ipi_86 with "Htext") as "Hi86".
    iPoseProof (ipi_88 with "Htext") as "Hi88".
    iPoseProof (ipi_8a with "Htext") as "Hi8a".
    assert (Hiw2 : iref_word Mt2 k = (mword_of_int (Z.pos cnt2) : mword 32))
      by (rewrite /iref_word HMk2; reflexivity).
    (* +0x86 lw a5,8(s1) : read ip->ref *)
    assert (Hpa86 : add_vec (rget macq2 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = i_ref (ientry k)).
    { rewrite (rget_ne macq2 Rs1 ltac:(nz)) Hma2s1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x86)) Ra5 Rs1
              (mword_of_int 8 : mword 12) macq2 (trap_res eb + (K - 6))%nat
              (fun v => (⌜v = iref_word Mt2 k⌝ ∗ itable_half Mt2)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi86 [Hhalf]").
    { rewrite Hpa86.
      iMod (iref_load_locked_au (⊤ ∖ ↑minstretN) Mt2 k ltac:(solve_ndisj) Hk
              with "Hitinv Hhalf") as "[Hcell Hback2]".
      iModIntro. iExists (iref_word Mt2 k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback2" with "Hcell") as "Hhalf". iModIntro. by iFrame. }
    iIntros (vld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc [%Hvld Hhalf]".
    subst vld. iEval (rewrite Hiw2) in "Hcg".
    set (F0 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt2) : mword 32))]> macq2).
    assert (HF0a5 : F0 !!! Regidx Ra5
                    = sign_extend' 64 (mword_of_int (Z.pos cnt2) : mword 32))
      by (rewrite /F0; apply upd_eq).
    assert (HF0s1 : F0 !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite /F0 upd_ne; [exact Hma2s1 | nz]).
    assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.iput + 0x86) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x88)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* +0x88 c.addiw a5,a5,-1 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.iput + 0x88)) Ra5
              (mword_of_int 63 : mword 6) F0 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi88").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (F0 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> F0).
    assert (HF1s1 : F1 !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite /F1 upd_ne; [exact HF0s1 | nz]).
    assert (Hstv2 : trunc32 (rget F1 Ra5) = (mword_of_int (Z.pos cnt2 - 1) : mword 32)).
    { rewrite (rget_ne F1 Ra5 ltac:(nz)) /F1 upd_eq. unfold regval_into_reg.
      rewrite HF0a5. exact (ip_storeval_pred (Z.pos cnt2) ltac:(lia) ltac:(lia)). }
    assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.iput + 0x88) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x8a)) by pcw.
    iEval (rewrite Hpp8a) in "Hpc".
    (* ===================================================================
       +0x8a  c.sw a5,8(s1) : ip->ref = ref-1.  On the FREE path this is
       the LAST close, so the slot is EVICTED (the §13.9 dance, ProofIput's
       "REF-1 last close" transplanted from its stale +0x24 anchor).
       =================================================================== *)
    assert (Hpa8a : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = i_ref (ientry k)).
    { rewrite (rget_ne F1 Rs1 ltac:(nz)) HF1s1. reflexivity. }
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.iput + 0x8a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x8c)) by pcw.
    destruct (decide (cnt2 = 1%positive)) as [Hcnt1 | Hcntne].
    2: { (* ---- NOT the last close.  OPEN -- blocker (B1) at the head of the
             file.  [Hone2'] gives [q <> qt2] here, so the STORE itself is
             fine ([iref_close_store_au] with [qt2 - q = Some qrest]); what
             is not fine is everything after it: the escrow stays PARKED,
             [ic_open_auth_ref] refuses to open it without REF-1, so the
             record the +0xba flush consumes is unreachable -- and the flush
             would be freeing an inode a foreign referrer still holds.  The
             re-acquire at +0x82 cannot re-establish REF-1 from anything this
             lemma owns; see §17.6.1. ---- *)
         admit. }
    pose proof (Hone2 Hcnt1) as Hqq.
    rewrite Hcnt1 in HMk2, Hstv2.
    rewrite <- Hqq in HMk2.
    (* ---- the slot's identity, popped from the table's list ---- *)
    assert (Hcik2ex : exists di : mword 32 * mword 32, ci2 !! k = Some di).
    { destruct Hciwf2 as [Hdom2 _].
      assert (Hin : k ∈ dom ci2)
        by (rewrite Hdom2; apply elem_of_dom; rewrite HMk2; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcik2ex as [[cdev2 cinum2] Hcik2].
    iDestruct (islots2_acc_upd cn Mt2 ci2 k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk2 Hcik2) in "Hslot".
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
    iDestruct (ip_rest_sum with "Hrest") as %[qr2 Hsum2].
    iAssert (⌜cdev2 = dev /\ cinum2 = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - q)%Qp as [q'|] eqn:Et2; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    assert (Hqhalf2 : (q ≤ 1/2)%Qp) by (rewrite Hsum2; apply Qp.le_add_l).
    (* ---- the eviction runs BEFORE the store ---- *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    iMod (ic_open_auth_ref cn γfs γi cov logstart k (⊤ ∖ ↑icEscN)
            Mt2 q q dev inum ltac:(solve_ndisj) HMk2
            with "Hitinv Hbody Hhalf Hrtok Hrident")
      as "(Hhalf & Hrtok & Hrident & Harm & _)".
    iDestruct "Harm" as (vv ga2) "(Hidv & Hinv2 & Hvld & Hpayl & Hlvh & Hmt & Hgida)".
    iDestruct (islot_rest_join k q dev inum Hqhalf2 with "Hrident [Hrest]")
      as "[Hdh Hinh]".
    { rewrite /islot_rest. iExists dev, inum. iExact "Hrest". }
    iMod (ic_close_to_empty cn γfs γi cov logstart k vv ga2 dev inum
            with "Hgida Hgid Hidv Hdh Hinv2 Hvld Hpayl Hmt")
      as "(Hbody & Hgidf & Hbundle)".
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
    iModIntro.
    assert (Hinreg : bv_unsigned inum ∈ region_inums nib).
    { apply region_inums_spec. split; [apply bv_unsigned_in_range |].
      destruct Hciwf2 as (_ & _ & Hrange & _).
      exact (Hrange k (dev, inum) Hcik2). }
    assert (Hincid : bv_unsigned inum ∈ ci_inums ci2).
    { apply ci_inums_spec. exists k, (dev, inum). split; [exact Hcik2 | reflexivity]. }
    iDestruct (isl_pool_acc_upd Mt2 k Hk with "Hipool") as "[Hisl Hislback]".
    iPoseProof (ipi_8c with "Htext") as "Hi8c".
    iPoseProof (ipi_90 with "Htext") as "Hi90".
    iPoseProof (ipi_94 with "Htext") as "Hi94".
    iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x8a)) Ra5 Rs1
              (mword_of_int 8 : mword 12) F1 (trap_res eb + (K - 6))%nat
              (itable_half (delete k Mt2) ∗ isl_slot (delete k Mt2) k)%I
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(solve_ndisj)
              with "Hcg Hpc Hi8a [Hhalf Hrtok Hlvh Hisl]").
    { rewrite Hpa8a Hstv2.
      replace (Z.pos 1 - 1)%Z with 0%Z by lia.
      iMod (iref_close_last_store_au (⊤ ∖ ↑minstretN) Mt2 k q
              ltac:(solve_ndisj) HMk2 with "Hitinv Hhalf Hrtok [Hlvh] Hisl")
        as "[Hcell Hback2]".
      { iExists ga2. iExact "Hlvh". }
      iModIntro. iExists (iref_word Mt2 k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback2" with "Hcell") as "[Hhalf Hisl]". iModIntro. iFrame. }
    iApply wp_next_off_intro. iIntros "Hcg Hpc [Hhalf Hisl]".
    iDestruct ("Hislback" $! (delete k Mt2) with "[%] Hisl") as "Hipool".
    { intros i0 Hi0. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    iEval (rewrite Hpp8c) in "Hpc".
    (* the table's slot re-forms as [islot_empty]; the unit the arm parked
       is the one the caller gets back *)
    iDestruct ("Hback" $! (delete k Mt2) (delete k ci2)
                 with "[%] [%] [Hinh Hgidf]") as "Hslots".
    { intros i0 Hi0. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    { intros i0 Hi0. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
    { rewrite /islot2 !lookup_delete. rewrite /islot_empty.
      iExists dev, inum. iFrame. }
    assert (Hp1 : Pos.to_nat 1 = 1%nat) by reflexivity.
    iEval (rewrite Hp1) in "Hiu".
    (* ===================================================================
       THE ONE OPEN DESIGN DEBT OF THE REORDER (see the blocker note at the
       head of the file).  The eviction hands back exactly ONE
       [ipool_shape], and the reordered free path needs TWO things out of
       it at once:

         (i)  the itable's free pool must show [region_inums nib ∖
              ci_inums (delete k ci2)] -- one entry MORE than before -- at
              the +0x94 release, and

         (ii) [OFF.ip_free_offlock] needs the record itself,
              [dinode_at γi inum dn2] with [dinode_wf] and nlink 0, because
              in this pin the disk type=0 write is DEFERRED to +0xba
              ([ireg_free_deposit_au], which consumes the fragment).

       The bundle carries the record on its [ipool_alloc] arm, so (i) and
       (ii) compete for it; and [ipool_shape]'s other two arms are both out
       of reach here ([imark] is inside [ireg_inv] until the deposit,
       [pool_pending] needs the [committedA] the deposit mints).  On top of
       that [ipool_shape_np] existentially quantifies BOTH the arm and the
       record, so even the identity [dn2 = di_trunc dn] we parked at +0x70
       is erased.

       The fix is structural and lives in IcacheEscrow.v, not here: the
       (None, Some) arm of [islot2] that the definition's OWN header
       describes ("the CACHED, REF-0 entry iput's last close leaves behind
       -- payload still parked in the escrow, so its inum must stay OUT of
       the pool, which is exactly what keeping it in [ci] does") and which
       the three-arm code plus [ic_ci_wf]'s [dom ci = dom M] does not
       implement.  With it, (i) disappears (ci keeps the entry, the pool
       does not grow) and the record travels to +0xa8 unchallenged.
       =================================================================== *)
    iAssert (∃ dn2 : dinode,
               ⌜dinode_wf dn2⌝ ∗ ⌜bv_unsigned (di_nlink dn2) = 0⌝ ∗
               dinode_at γi inum dn2 ∗
               ipool_shape γfs γi cov logstart inum)%I
      with "[Hbundle]" as (dn2) "(%Hdn2wf & %Hdn2nl & Hdn2 & Hgap)".
    { admit. }
    iDestruct (ipool_insert γfs γi cov logstart
                 (region_inums nib ∖ ci_inums ci2) (bv_unsigned inum)
                 ltac:(apply fl_notin_diff; exact Hincid) with "[Hgap] Hpool") as "Hpool".
    { rewrite fl_moi_inum. iExact "Hgap". }
    assert (Hpoolset : region_inums nib ∖ ci_inums (delete k ci2)
                       = {[ bv_unsigned inum ]} ∪ (region_inums nib ∖ ci_inums ci2)).
    { destruct Hciwf2 as (_ & Hinj & _ & _).
      rewrite (fl_ci_inums_delete ci2 k dev inum Hcik2 Hinj).
      apply fl_pool_set; [exact Hinreg | exact Hincid]. }
    iEval (rewrite -Hpoolset) in "Hpool".
    iAssert (itable_res2 cn γfs γi cov logstart nib dev)
      with "[Hhalf Hiauth Hipool Hslots Hpool]" as "HRres3".
    { iExists (delete k Mt2), (delete k ci2). iFrame. iPureIntro. split.
      { destruct Hwf2 as [Hdom Hcnt']. split.
        - intros i0 Hi0. apply Hdom. destruct Hi0 as [e He].
          exists e. rewrite lookup_delete_Some in He. apply He.
        - intros i0 qi ni Hi0. rewrite lookup_delete_Some in Hi0.
          destruct Hi0 as [_ Hi0]. by apply (Hcnt' i0 qi). }
      { destruct Hciwf2 as (Hdom & Hinj & Hrange & Hdv). split_and!.
        - rewrite !dom_delete_L Hdom. reflexivity.
        - intros k1 k2 p1 p2 Hp1' Hp2' Heq.
          rewrite lookup_delete_Some in Hp1'. rewrite lookup_delete_Some in Hp2'.
          exact (Hinj k1 k2 p1 p2 (proj2 Hp1') (proj2 Hp2') Heq).
        - intros k1 p1 Hp1'. rewrite lookup_delete_Some in Hp1'.
          exact (Hrange k1 p1 (proj2 Hp1')).
        - intros k1 p1 Hp1'. rewrite lookup_delete_Some in Hp1'.
          exact (Hdv k1 p1 (proj2 Hp1')). } }
    (* ===== +0x8c auipc a0 ; +0x90 addi a0,a0,1260 ; +0x94 jal release ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x8c)) Ra0
              (mword_of_int 29 : mword 20) F1 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x8c) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> F1).
    assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.iput + 0x8c) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x90)) by pcw.
    iEval (rewrite Hpp90) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x90)) Ra0 Ra0
              (mword_of_int 1260 : mword 12) G1 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (G2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (G1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1260 : mword 12)))]> G1).
    assert (HG2a0 : G2 !!! Regidx Ra0 = itable_lock).
    { rewrite /G2 upd_eq /G1 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.iput + 0x90) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x94)) by pcw.
    iEval (rewrite Hpp94) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x94)) Rra
              (mword_of_int 2086966 : mword 21) G2 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi94").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (G3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x94) : mword 64) 4)]> G2).
    assert (Htgtrl2 : add_vec (mword_of_int (KernelSyms.iput + 0x94) : mword 64)
                        (sign_extend' 64 (mword_of_int 2086966 : mword 21))
                      = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrl2) in "Hpc".
    assert (HG3a0 : G3 !!! Regidx Ra0 = itable_lock)
      by (rewrite /G3 upd_ne; [exact HG2a0 | nz]).
    assert (HG3ra : G3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x94) : mword 64) 4)
      by (rewrite /G3; apply upd_eq).
    assert (HG3thr : forall c : mword 5, is_cs_idx c = true ->
                       G3 !!! Regidx c = F1 !!! Regidx c).
    { intros c Hcs. rewrite /G3 upd_ne; [| regne].
      rewrite /G2 upd_ne; [| regne]. rewrite /G1 upd_ne; [reflexivity | regne]. }
    iApply (Release.wp_release_sconf gtl itable_lock "itable"%string
              (itable_res2 cn γfs γi cov logstart nib dev) G3
              0%nat eb pj (K - 6)%nat ({["itable"]} ∪ lks)
              ltac:(rewrite HG3a0; reflexivity) ltac:(lia)
              with "Hcg Htext Hpc [Hitlk] Htok HRres3 Hcnt Hpay").
    { iExact "Hitlk". }
    iIntros (CIDrl2 Hsrl2 mr2) "Hcg Hpc %Hpins2 Hcnt".
    iEval (rewrite (_ : ({["itable"]} ∪ lks) ∖ {["itable"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hcnt".
    assert (Hpc98 : ret_pc (G3 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x98))
      by (rewrite HG3ra; pcw).
    iEval (rewrite Hpc98) in "Hpc".
    pose proof Hpins2 as Hpins2_cs.
    assert (Hmr2c : forall c : mword 5, is_cs_idx c = true ->
                      mr2 !!! Regidx c = F1 !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hpins2_cs c Hcs). exact (HG3thr c Hcs). }
    assert (HF1c : forall c : mword 5, is_cs_idx c = true ->
                     F1 !!! Regidx c = macq2 !!! Regidx c).
    { intros c Hcs. rewrite /F1 upd_ne; [| regne].
      rewrite /F0 upd_ne; [reflexivity | regne]. }
    assert (Hmr2cs : forall c : mword 5, is_cs_idx c = true ->
                       mr2 !!! Regidx c = mfi !!! Regidx c).
    { intros c Hcs. rewrite (Hmr2c c Hcs) (HF1c c Hcs) (Hma2c c Hcs).
      exact (Hmrsc c Hcs). }
    assert (Hmr2s1 : mr2 !!! Regidx Rs1 = (ip : mword 64))
      by (rewrite (Hmr2cs Rs1 ltac:(vm_compute; reflexivity)); exact Hmfis1).
    assert (Hmr2s2 : mr2 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (Hmr2cs Rs2 ltac:(vm_compute; reflexivity)); exact Hmfis2).
    assert (Hmr2s3 : mr2 !!! Regidx Rs3 = (i_lock ip : mword 64))
      by (rewrite (Hmr2cs Rs3 ltac:(vm_compute; reflexivity)); exact Hmfis3).
    assert (Hmr2s4 : mr2 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite (Hmr2cs Rs4 ltac:(vm_compute; reflexivity)); exact Hmfis4).
    assert (Hmr2sp : mr2 !!! Regidx csp_rs1 = sp0)
      by (rewrite (Hmr2cs csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmfisp).
    (* ---- the IBLOCK arithmetic's pure side, ProofIupdate's +0x10..+0x1c ---- *)
    pose proof Hgeom as Hgeom2. destruct Hgeom2 as [Hcovok Hlogsub].
    destruct (Hcovok _ Hicov) as [Hibpos Hiblt].
    assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
    iPoseProof (ipi_98 with "Htext") as "Hi98".
    iPoseProof (ipi_9c with "Htext") as "Hi9c".
    iPoseProof (ipi_a0 with "Htext") as "Hia0".
    iPoseProof (ipi_a4 with "Htext") as "Hia4".
    iPoseProof (ipi_a6 with "Htext") as "Hia6".
    (* ===== +0x98 srliw a5,s2,0x4 : a5 := inum / IPB ===== *)
    iApply (wp_srliw_s_sconf (mword_of_int (KernelSyms.iput + 0x98)) Ra5 Rs2
              (mword_of_int 4 : mword 5)
              (mword_of_int (bv_unsigned inum / 16) : mword 64)
              mr2 (K - 6)%nat eb ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite Hmr2s2; apply iu_srliw4)
              with "Hcg Hpc Hi98").
    iIntros (CIDp1 Hqp1) "Hcg Hpc".
    set (P1 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (bv_unsigned inum / 16) : mword 64)]> mr2).
    assert (HP1a5 : P1 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (HP1c : forall c : mword 5, is_cs_idx c = true ->
                     P1 !!! Regidx c = mr2 !!! Regidx c)
      by (intros c Hcs; rewrite /P1 upd_ne; [reflexivity | regne]).
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.iput + 0x98) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x9c)) by pcw.
    iEval (rewrite Hpp9c) in "Hpc".
    (* ===== +0x9c auipc a1,0x1d ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x9c)) Ra1
              (mword_of_int 29 : mword 20) P1 (K - 6)%nat eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c").
    iIntros (CIDp2 Hqp2) "Hcg Hpc".
    set (P2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x9c) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> P1).
    assert (HP2a1 : P2 !!! Regidx Ra1
                    = add_vec (mword_of_int (KernelSyms.iput + 0x9c) : mword 64)
                        (auipc_off (mword_of_int 29 : mword 20)))
      by (rewrite /P2; apply upd_eq).
    assert (HP2a5 : P2 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1a5 | nz]).
    assert (HP2c : forall c : mword 5, is_cs_idx c = true ->
                     P2 !!! Regidx c = mr2 !!! Regidx c).
    { intros c Hcs. rewrite /P2 upd_ne; [| regne]. exact (HP1c c Hcs). }
    assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.iput + 0x9c) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0xa0)) by pcw.
    iEval (rewrite Hppa0) in "Hpc".
    (* ===== +0xa0 lw a1,1236(a1) : a1 := sb.inodestart ===== *)
    assert (Hsbadr : add_vec (rget P2 Ra1)
                       (sign_extend' 64 (mword_of_int 1236 : mword 12))
                     = sb_inodestart).
    { rgne. rewrite HP2a1. rewrite /sb_inodestart /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hsbadr) in "Hins".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.iput + 0xa0)) Ra1 Ra1
              (mword_of_int 1236 : mword 12) P2 (K - 6)%nat
              (mword_of_int inodestart : mword 32) eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia0 Hins").
    iIntros (CIDp3 Hqp3) "Hcg Hpc Hins".
    iEval (rewrite Hsbadr) in "Hins".
    set (P3 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int inodestart : mword 32))]> P2).
    assert (HP3a1 : P3 !!! Regidx Ra1
                    = (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64))
      by (rewrite /P3; apply upd_eq).
    assert (HP3a5 : P3 !!! Regidx Ra5
                    = (mword_of_int (bv_unsigned inum / 16) : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2a5 | nz]).
    assert (HP3c : forall c : mword 5, is_cs_idx c = true ->
                     P3 !!! Regidx c = mr2 !!! Regidx c).
    { intros c Hcs. rewrite /P3 upd_ne; [| regne]. exact (HP2c c Hcs). }
    assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.iput + 0xa0) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0xa4)) by pcw.
    iEval (rewrite Hppa4) in "Hpc".
    (* ===== +0xa4 c.addw a1,a1,a5 : a1 := IBLOCK(inum, sb) ===== *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.iput + 0xa4)) Ra1 Ra5
              P3 (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4").
    iIntros (CIDp4 Hqp4) "Hcg Hpc".
    set (P4 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget P3 Ra1) 31 0 : mword 32)
                              (subrange_vec_dec (rget P3 Ra5) 31 0 : mword 32)))]> P3).
    assert (HP4a1 : P4 !!! Regidx Ra1
                    = (sign_extend' 64
                         (mword_of_int (IBLOCK inum inodestart) : mword 32) : mword 64)).
    { rewrite /P4 upd_eq. rgne. rgne. rewrite HP3a1 HP3a5.
      exact (iu_addw_ibl inum inodestart Histpos Hib). }
    assert (HP4c : forall c : mword 5, is_cs_idx c = true ->
                     P4 !!! Regidx c = mr2 !!! Regidx c).
    { intros c Hcs. rewrite /P4 upd_ne; [| regne]. exact (HP3c c Hcs). }
    assert (HP4s4 : P4 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite (HP4c Rs4 ltac:(vm_compute; reflexivity)); exact Hmr2s4).
    assert (Hppa6 : add_vec_int (mword_of_int (KernelSyms.iput + 0xa4) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xa6)) by pcw.
    iEval (rewrite Hppa6) in "Hpc".
    (* ===== +0xa6 c.mv a0,s4 : a0 := dev ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0xa6)) Ra0 Rs4
              P4 (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia6").
    iIntros (CIDp5 Hqp5) "Hcg Hpc".
    set (P5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (P4 !!! Regidx Rs4))]> P4).
    assert (HP5a0 : P5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64)).
    { rewrite /P5 upd_eq. rewrite HP4s4. apply add_vec_zero_l. }
    assert (HP5a1 : P5 !!! Regidx Ra1
                    = (sign_extend' 64
                         (mword_of_int (IBLOCK inum inodestart) : mword 32) : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4a1 | nz]).
    assert (HP5c : forall c : mword 5, is_cs_idx c = true ->
                     P5 !!! Regidx c = mr2 !!! Regidx c).
    { intros c Hcs. rewrite /P5 upd_ne; [| regne]. exact (HP4c c Hcs). }
    assert (HP5s2 : P5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite (HP5c Rs2 ltac:(vm_compute; reflexivity)); exact Hmr2s2).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = sp0)
      by (rewrite (HP5c csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmr2sp).
    assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.iput + 0xa6) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xa8)) by pcw.
    iEval (rewrite Hppa8) in "Hpc".
    (* ===================================================================
       THE LOG RE-CREDIT and the ESCROW MINT, then the hand-off at +0xa8.
       =================================================================== *)
    iDestruct "Hopx" as (wbm u' Sb')
      "(%Hsub' & %Hibin' & %Hwbm' & %Hcrbw' & %Hbud & Hop)".
    assert (Hu'1 : (1 <= u')%nat).
    { destruct Hbud as [Hlo _]. rewrite Hun in Hlo.
      unfold it_bm, it_iu in Hlo. destruct wbm, cru; lia. }
    assert (Hu'le : (u' <= u)%nat).
    { destruct Hbud as [_ Hhi]. rewrite Hun in Hhi.
      unfold it_iu in Hhi. destruct cru; lia. }
    (* the op count, in the [S _] form the off-lock flush's contract wants *)
    destruct u' as [| uoff]; [exfalso; lia |].
    iDestruct (log_opS_named with "Hop") as (e0') "Hop".
    iPoseProof (log_opSe_lb with "Hop") as "#Hvlb2".
    iAssert (log_credit γ cru Sb' e0' (IBLOCK inum inodestart)) as "#Hcrd2".
    { iApply log_credit_own. intros _. exact Hibin'. }
    (* the EMPTY escrow the +0xba deposit fills *)
    iApply fupd_wp.
    iMod (escA_alloc ⊤ γi (bv_unsigned inum)) as (ge gr) "[#Hescr Htk]".
    iModIntro.
    (* the off-lock tail runs on two of our three bio slots *)
    iEval (rewrite (_ : 3%nat = (1 + 2)%nat); [| reflexivity]) in "Hbslots".
    iDestruct (bslots_op bn 1 2 with "Hbslots") as "[Hbs1 Hbs2]".
    (* the cpu bundle, transported to the call site *)
    iDestruct (cpu_own_transport CIDrl2 CIDp5 0%nat eb pj eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDit CIDp5 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDit CIDp5 eb pj
                 ltac:(wp_next_chain) with "Hclm") as "Hclm".
    (* ===== +0xa8 .. j 0x30 : OFF.ip_free_offlock ===== *)
    iApply (OFF.ip_free_offlock γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart inodestart nib dev inum dn2 ge gr
              uoff Sb' cru e0' e0' pidv dq dqs
              sp0 vra vs0 vs1 vs2 vs3 vs4 P5 (K - 6)%nat eb eb lks
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(change (2 ^ 31)%Z with 2147483648%Z in Hubnd |- *; lia)
              Hgeom Histpos Hicov Hilog Hnib Hdn2wf Hdn2nl Hj Hgl
              ltac:(exact (eq_sym HP5sp)) HP5a0 HP5a1 HP5s2 Hlkbelow
              with "Hcg Hcnt Hextc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hireg
                    Hdn2 Hescr Htk Hppid Hprocs Hdevi Hdgeom Hdlock Hins Hbs2
                    Hvlb2 Hcrd2 Hop Hra Hs0f Hs1f Hs2f Hs3f Hs4f [-]").
    (* ---- the continuation: offlock's post at 0x30, re-shaped into ours ---- *)
    iIntros (CIDf Hstf).
    iIntros (mf) "%Hthr Hcg Hcnt Hextc Hclm Hpc Hppid Hins Hpp Hbs2 Hop2 Hwit
                  Hra Hs0f Hs1f Hs2f Hs3f Hs4f".
    (* the whole walk never touched a callee-saved register, so [P5] agrees
       with [m] on all of them and offlock's threading composes to ours *)
    assert (Hmfam : forall c : mword 5, is_cs_idx c = true ->
                      mfa !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsa_cs c Hcs).
      rewrite /R0 upd_ne; [reflexivity | regne]. }
    assert (HP5m : forall c : mword 5, is_cs_idx c = true ->
                     P5 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs. rewrite (HP5c c Hcs) (Hmr2cs c Hcs) (Hmfic c Hcs)
                            (Hmr1c c Hcs). exact (Hmfam c Hcs). }
    destruct Hthr as (Hthr5 & Hmfsp & Hmfs2 & Hmfs3 & Hmfs4).
    assert (Hthrm : OFF.ipo_thr m mf).
    { intros c Hcs N1 N2 N3 N4 N5.
      rewrite (Hthr5 c Hcs N1 N2 N3 N4 N5). exact (HP5m c Hcs). }
    iDestruct (bslots_op bn 1 2 with "[Hbs1 Hbs2]") as "Hbslots";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    iEval (rewrite (_ : (1 + 2)%nat = 3%nat); [| reflexivity]) in "Hbslots".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDf)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iSpecialize ("Hcont" $! CIDf with "[]"); [iPureIntro; wp_next_chain |].
    iApply ("Hcont" $! mf (if cru then S uoff else uoff)
                       (used ∖ bm_blocks bm) (Sb' ∪ {[IBLOCK inum inodestart]}) wbm
              with "[%] Hcg Hcnt Hextc Hclm Hpc Hppid Hbms Hins [%] Hbm Hpp Hbslots
                    [%] [%] [%] Hop2 Hiu Hra Hs0f Hs1f Hs2f Hs3f Hs4f").
    { split_and!; [exact Hthrm | exact Hmfsp | exact Hmfs2 | exact Hmfs3 | exact Hmfs4]. }
    { exact (fl_diff_sub used (bm_blocks bm)). }
    { exact (union_subseteq_l' _ _ _ Hsub'). }
    { intros Hw. apply elem_of_union_l. exact (Hwbm' Hw). }
    { exact Hcrbw'. }
  Admitted.

End FreeLockedDev.

End FreeLockedDev.
