(* ProofIput.v -- iput(), proven instruction by instruction.

     void iput(struct inode *ip) {
       acquire(&itable.lock);
       if(ip->ref == 1 && ip->valid && ip->nlink == 0){
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

   ---- THE SHAPE: FOUR ENTRIES INTO ONE TAIL ----------------------------

   The [ref--] at [+0x20 .. +0x2e] and the epilogue behind it are reached
   FOUR ways, and that is why they are a lemma ([ip_tail]) rather than a
   stretch of the main proof:

     +0x1c  beq a4,a5,+32   FALLS THROUGH   (ref != 1)
     +0x3e  c.beqz a5,-30   TAKEN           (!ip->valid)
     +0x44  c.bnez a5,-36   TAKEN           (ip->nlink != 0)
     +0x88  c.j -104                        (after the truncate)

   The first three arrive on the ENTRY hart with the lock just taken; the
   fourth has been through [acquiresleep] / [itrunc] / [iupdate] /
   [releasesleep], every one of which can park, so it arrives on a hart
   nobody knew about at +0x14.  [ip_tail] is therefore anchored at the
   function's entry hart in [ProofAcquiresleep.asl_exit]'s style -- its own
   ambient [CID] is a fresh binder, the caller's continuation is a
   [wp_next (CID0 := CID0)] premise, and the chained equality comes in as
   [Hanch].  Nothing else in the file needs that.

   The tail also splits INTERNALLY on the count, which is what lets all four
   entries share it: at [Pos.succ n] it is [IcacheInv.iref_close_store_au]
   and nothing else moves; at [1] it is REF-1, the last close, and the
   EVICTION (§13.9) -- [ic_close_to_empty], [ipool_insert], [ci] and [M]
   deleting together, the table's slot re-forming as [islot_empty].

   ---- THE WINDOW (design §13.13) ---------------------------------------

   iput reads [ip->valid] at +0x3c holding only itable.lock, and CANNOT use
   the answer at the checkout twenty bytes later: [ic_open_auth_ref] re-seals
   the parked arm with its polarity existentially bound, and no ghost can pin
   it from the itable side.  So the +0x3c read does not re-seal at PARKED at
   all on the arm that matters: it closes at [IcacheEscrow.ic_held], leaving
   the CELLS in the escrow (with the inum cell joined to FULL, which is what
   blocks a concurrent checkout) and taking the PAYLOAD out at the polarity
   just observed.  A resource in this proof's own context is not re-bound by
   anything, so there is nothing left to be stable.

   The window is closed on both exits, and the exits are why its credential
   is REF-1 rather than the checkout token: at +0x44 (nlink != 0) it must be
   undone with no [acquiresleep] having run.

   ---- WHAT ELSE IS WORTH KNOWING BEFORE READING ------------------------

   * [b] is pinned [true]: the contract enters at noff 0 with [eb = true],
     and [ip_sie_b_agree] reads the shared ghost eighth off [sie_cap_gpr].
     Prologue and epilogue are hart-generic at [b]; the whole body between
     the two [acquire]s runs at the literal [false] and collapses through
     [wp_next_off_intro]; the stretch between the release at +0x5c and the
     re-acquire at +0x82 is back at [b] and is the only place a hart moves.
   * The [ip->ref] word lives in [IcacheInv.itable_inv], not in the lock's
     resource, so its load and store are ATOMIC-UPDATE leaves -- ProofIdup's
     two, restated here for the same reason it restated ProofBreadParts'.
   * [ip->valid] and [ip->nlink] live in the ESCROW, so +0x3c is an AU leaf
     over [icEscN]; +0x40's [lh] is NOT, because by then the payload (hence
     [inode_meta], hence [i_nlink]) is in hand.
   * The budget is spend-at-most 3: itrunc's two and iput's own iupdate.
     The three close arms spend nothing, and the postcondition's interval
     covers both. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock SleepLock.
Require Import RiscvExtras.
Require Import RegFile.
Require Import InstrBytes.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpAu4.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import DinodeEnc.
Require Import DinodeSlot.
Require Import InodeLock.
Require Import InodeRegion.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FdSlots.
Require Import CodeIput.
Require Import SpecAcquire SpecRelease.
Require Import SpecAcquiresleep SpecReleasesleep.
Require Import BcacheInv BioInv.
Require Import BufOwn.
Require Import ByteBuf.
Require Import BlockWords.
Require Import DiskInv.
Require Import DirView DirLinks FsTree.
Require Import LogDefs.
Require Import KernelDataInv.
Require Import RiscvModelBytes.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpSconfSrliw.
Require Import EscrowDefs.
Require Import EscrowInode.
Require Import EscrowDeposit.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite.
Require Import SpecItrunc SpecIupdate.
Require Import SpecIput.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  THE PURE ARITHMETIC                                               *)
(* ===================================================================== *)

(* [ProofIget.ig_sext_eqv], restated: a proof file may not import a proof
   file.  The [beq] at +0x1c compares two SIGN-EXTENDED 32-bit words. *)
Lemma ip_sext_eqv (a b : mword 32) :
  eq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 b) = eq_vec a b.
Proof.
  destruct (eq_vec a b) eqn:Hab.
  - apply eq_vec_true_iff in Hab. subst b. apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff in Hab. apply eq_vec_false_iff.
    intro Hc. apply Hab. exact (sext64_32_inj a b Hc).
Qed.

(* [ProofIlock.il_sext64_16_inj], restated for the same reason, and the
   halfword ZERO test it gives.  The [c.bnez] at +0x44 falls through
   exactly when [ip->nlink] is zero, and §20's (L3) needs that as a VALUE
   fact about the record iput is holding -- which, since [ic_open_held]
   went record-parametric (§20.14's (R1)), is the same record the free
   flushes.  Without it the free cannot certify "nothing names this
   inum". *)
Lemma ip_sext64_16_inj (a c : mword 16) :
  (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
Proof.
  intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity.
Qed.

Lemma ip_nlink_zero (w : mword 16) :
  neq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false ->
  bv_unsigned w = 0.
Proof.
  intro H. unfold neq_vec in H. apply negb_false_iff in H.
  apply eq_vec_true_iff in H.
  assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz in H. apply ip_sext64_16_inj in H.
  rewrite H. vm_compute. reflexivity.
Qed.

(* THE TEST AT +0x1c, decided by the COUNT.  [c.li a5,1] leaves the literal
   one in a5 and the [c.lw] left the sign-extended ref word in a4, so the
   branch is taken exactly on a slot whose count is one -- i.e. exactly when
   the opener's own reference is the whole outstanding share (REF-1). *)
Lemma ip_cnt_eq_one (cnt : positive) :
  (Z.pos cnt < 2 ^ 31)%Z ->
  eq_vec (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32) : mword 64)
         (mword_of_int 1 : mword 64)
  = (if decide (cnt = 1%positive) then true else false).
Proof.
  intro Hb.
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hb.
  replace (mword_of_int 1 : mword 64)
    with (sign_extend' 64 (mword_of_int 1 : mword 32) : mword 64)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite ip_sext_eqv.
  destruct (decide (cnt = 1%positive)) as [->|Hne].
  - by apply eq_vec_true_iff.
  - apply eq_vec_false_iff. intro Hc.
    apply (f_equal (@bv_unsigned 32)) in Hc.
    rewrite (moi32_small (Z.pos cnt) ltac:(rewrite E32; lia)) in Hc.
    rewrite (moi32_small 1 ltac:(rewrite E32; lia)) in Hc.
    apply Hne. lia.
Qed.

(* [ProofFilecloseParts.fc_pred_sub], restated for the same reason: the
   [c.addiw a5,a5,-1] at +0x22, whose 6-bit immediate is [63].  This is
   [VcGen.moi32_storeval_succ]'s mirror and the only arithmetic content of
   "-- on an int field". *)
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

Lemma ip_moi_inum (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  apply bv_eq. rewrite moi32_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ip_trunc32_zero : trunc32 (zero_reg : mword 64) = (mword_of_int 0 : mword 32).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ip_trunc16_zero : trunc16 (zero_reg : mword 64) = (mword_of_int 0 : mword 16).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* the +0x3e / +0x44 branch readings.  [valid] is the escrow's own bool
   ([InodeLock.valid_word_eqz] does the work); [nlink] is a HALFWORD, so the
   [c.bnez] tests its sign extension. *)
Lemma ip_valid_beqz (v : bool) :
  eq_vec (sign_extend' 64 (valid_word v) : mword 64) (zero_reg : mword 64) = negb v.
Proof. exact (valid_word_eqz v). Qed.

Lemma ip_h_neqz_zero :
  neq_vec (sign_extend' 64 (mword_of_int 0 : mword 16) : mword 64)
          (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- the pure set step at the LAST CLOSE: [ci] loses one entry, and the
   pool gains exactly that inum.  [ProofIget.ig_ci_inums_insert] run
   backwards, and INJECTIVITY is what makes it true: without it a second
   live slot could still be caching the departing inum. ---- *)
Lemma ip_ci_inums_delete (ci : gmap nat (mword 32 * mword 32))
    (k : nat) (d i : mword 32) :
  ci !! k = Some (d, i) ->
  (forall (k1 k2 : nat) (p1 p2 : mword 32 * mword 32),
     ci !! k1 = Some p1 -> ci !! k2 = Some p2 ->
     bv_unsigned (snd p1) = bv_unsigned (snd p2) -> k1 = k2) ->
  ci_inums (delete k ci) = ci_inums ci ∖ {[ bv_unsigned i ]}.
Proof.
  intros Hk Hinj. apply set_eq. intros z.
  rewrite elem_of_difference elem_of_singleton !ci_inums_spec. split.
  - intros (k2 & p & Hk2 & ->).
    rewrite lookup_delete_Some in Hk2. destruct Hk2 as [Hne Hk2].
    split; [by exists k2, p |].
    intro Hc. apply Hne. symmetry.
    apply (Hinj k2 k p (d, i) Hk2 Hk). cbn [snd]. exact Hc.
  - intros [(k2 & p & Hk2 & ->) Hz].
    exists k2, p. rewrite lookup_delete_Some. split; [| reflexivity].
    split; [| exact Hk2].
    intros ->. apply Hz. rewrite Hk in Hk2. injection Hk2 as <-. reflexivity.
Qed.

(* the two set side conditions the whole-function proof needs, as NAMED
   lemmas.  [set_solver] ends in [naive_solver], which searches every
   hypothesis in scope -- at this file's altitude the context is ~200
   register-chain facts over large mword terms, and ONE such call at the
   +0x88 tail hand-off measured 284 s (durable-notes' capstone rule). *)
Lemma ip_diff_sub (X Y : gset Z) : X ∖ Y ⊆ X.
Proof. set_solver. Qed.

Lemma ip_notin_diff (P S : gset Z) (z : Z) : z ∈ S -> z ∉ P ∖ S.
Proof. set_solver. Qed.

Lemma ip_pool_set (P S : gset Z) (z : Z) :
  z ∈ P -> z ∈ S -> P ∖ (S ∖ {[z]}) = {[z]} ∪ (P ∖ S).
Proof.
  intros Hp Hs. apply set_eq. intros x. set_unfold.
  destruct (decide (x = z)) as [->|Hne]; naive_solver.
Qed.

(* the growth [ip_tail] wants at the +0x88 hand-off: itrunc's post says the
   op's set only grew, and iput's own iupdate grows it once more *)
Lemma ip_sub_union_l (A B S : gset Z) : A ⊆ B -> A ⊆ B ∪ S.
Proof. intros H. exact (union_subseteq_l' _ _ _ H). Qed.

(* ...and the same hand-off's two BUDGET premises.  [ip_spend_max] is
   [it_spend] under another name, so both bounds are itrunc's own post read
   at [it_entry crb uit = n].  Proven here over nat VARIABLES because the
   [unfold ... in *; destruct; simpl in *; lia] that closes it in place runs
   against every hypothesis of a whole-function proof. *)
Lemma ip_budget_bounds (w cru crz : bool) (n u' : nat) :
  (n - (it_bm w + it_iu (cru || crz)) <= u')%nat ->
  (u' + it_iu (cru || crz) <= n)%nat ->
  ((n - ip_spend_w w cru crz)%nat <= u')%nat /\ (u' <= n)%nat.
Proof.
  unfold ip_spend_w, ip_bm, it_bm, it_iu. destruct w, cru, crz; simpl; lia.
Qed.


(* ===================================================================== *)
(*  2.  THE TAIL'S REGISTER INVARIANT                                     *)
(* ===================================================================== *)

(* [ProofAcquiresleep.asl_regs]' shape.  s1 is the entry cursor, sp is the
   pushed frame base, and s2..s11 are the caller's -- s2 because the truncate
   arm saves and restores it across [+0x46, +0x86], the rest because nothing
   touches them.  ra, s0 and s1 are NOT here: the epilogue reloads all three
   off the frame, so what the tail is entered with does not matter. *)
Definition iput_regs (m M : regfile) (spd : mword 64) (k : nat) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = ientry k /\
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

Lemma iput_regs_cs (m M1 M2 : regfile) (spd : mword 64) (k : nat) :
  callee_saved M1 M2 -> iput_regs m M1 spd k -> iput_regs m M2 spd k.
Proof.
  intros Hcs Ha. unfold iput_regs in *.
  destruct Ha as (A&B&C&E&F&G&H&I&J&L&N&O).
  repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact H.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact I.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). exact J.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). exact L.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). exact N.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). exact O.
Qed.

(* ===================================================================== *)

(* THE ORDER OBLIGATION THIS FILE USED TO ADMIT -- and no longer does.

   iput holds itable.lock (14) across [acquiresleep], whose spinlock is
   "sleep lock" (4), and no ranking can license that edge: kfork holds
   np->lock across idup, so "itable" must sit ABOVE "proc" (9), and
   acquiresleep's BLOCKING path runs sleep_prepare while holding the
   sleeplock's own spinlock, so "sleep lock" must sit BELOW "proc".  Nothing
   fits between them (claude-notes/completed/lock-set.md, "THE ONE UNLICENSED
   EDGE").  For a long time this file carried an axiom asserting the
   obligation anyway -- a FALSE one, so everything downstream of iput was
   vacuous.

   THE DISCHARGE CHANGED THE OBLIGATION rather than assuming it, which is
   what xv6's own comment at fs.c:339 always said it should: "ip->ref == 1
   means no other process can have ip locked, so this acquiresleep() won't
   block (or deadlock)".  The entry's sleeplock is TRACKED -- a holder has
   deposited a share of somebody's REFERENCE in it -- so REF-1's "your [q] is
   the whole outstanding share" turns into "no deposit exists", and
   [Acquiresleep.wp_acquiresleep_nb_sconf] takes that in place of any rank
   bound.  See claude-notes/projects/iput-acquiresleep.md; the call site is
   the one marked THE STEP THIS FILE EXISTS FOR. *)

(* ===================================================================== *)

Module IputProof (Acquire : ACQUIRE) (Release : RELEASE)
                 (ASL : ACQUIRESLEEP) (RS : RELEASESLEEP)
                 (IT : ITRUNC) (IU : IUPDATE)
                 (* the off-lock tail's three leaves, new at the splice: the
                    reordered free path flushes [ip->type = 0] MANUALLY
                    (bread / sh / log_write / brelse at +0xa8) instead of
                    calling iupdate, so iput takes them directly. *)
                 (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE) : IPUT.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz  := vm_compute; discriminate.

Section IputCommon.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* [ProofIdup.sie_b_agree], verbatim. *)
  Lemma ip_sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool)
      `{GEN : GenId} `{CID : CpuId} (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 m K0 b p -∗ cpu_own n eb p b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "%Hb". destruct Hb as (-> & -> & _). done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[_ Hint]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm & _) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  (* THE FRACTION FACT [IcacheInv.iref_lookup] DOES NOT EXPOSE, and which
     the NON-last close needs: at a count above one the closer's own share is
     STRICTLY below the outstanding total, so [qt - q] exists and
     [iref_close_store_au]'s side condition is dischargeable.  [iref_lookup]
     keeps only the [q = qt <-> n = 1] equivalence; this is the same
     [singleton_included_l] argument, keeping the strict branch's witness. *)
  Lemma ip_ref_sub (M : gmap nat (Qp * positive)) (k : nat) (q : Qp) :
    itable_half M -∗ iref_tok k q -∗
    ⌜∃ (qt : Qp) (nn : positive), M !! k = Some (qt, nn) /\
       (nn = 1%positive \/ ∃ qr : Qp, (qt - q)%Qp = Some qr)⌝.
  Proof.
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha (Hf & _ & _)".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[_ [Hincl _]]%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as [y [Hy Hle]].
    apply leibniz_equiv in Hy. destruct y as [qt nn]. exists qt, nn.
    split; [exact Hy|].
    apply Some_included in Hle as [Heq | Hlt].
    - destruct Heq as [_ Hn]; cbn in Hn.
      left. symmetry. exact Hn.
    - apply pair_included in Hlt as [Hq _]; cbn in Hq.
      apply frac_included in Hq.
      right. apply Qp.lt_sum in Hq as [qr Hqr].
      exists qr. apply Qp.sub_Some. exact Hqr.
  Qed.

  (* the retained share is STRICTLY positive (§13.8), so a slot's identity
     budget always leaves the table something -- which is what makes
     [islot_rest_join]'s premise dischargeable and the window's FULL inum
     cell assemblable. *)
  Lemma ip_rest_sum (k : nat) (qt : Qp) (dev inum : mword 32) :
    islot_rest_at k qt dev inum -∗ ⌜∃ qr : Qp, (1/2)%Qp = (qt + qr)%Qp⌝.
  Proof.
    rewrite /islot_rest_at. destruct (1/2 - qt)%Qp as [q'|] eqn:Et.
    - iIntros "_". iPureIntro. exists q'. by apply Qp.sub_Some in Et.
    - iIntros "[]".
  Qed.

End IputCommon.

(* ===================================================================== *)
(*  3.  THE SHARED [ref--] TAIL, +0x20 .. +0x3a                           *)
(* ===================================================================== *)

Section IputTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* ---- the part BEHIND the store: +0x26 (a0 := &itable) .. +0x3a (c.ret).
     Factored out because the two close arms differ only in the store's
     atomic update and the ghost step riding with it; from +0x26 on they are
     the same instructions over the same resources. ---- *)
  (* ---- THE EPILOGUE, +0x30 .. +0x38 ------------------------------------

     c.ldsp ra/s0/s1 out of the frame, c.addi16sp the 48 bytes back, c.ret.
     BOTH tails run it and they run it identically: the two close arms reach
     +0x30 as [release(&itable.lock)]'s return address ([ip_tail_exit] below),
     and the FREE path reaches it from the off-lock tail's [c.j 0x30] --
     which is the whole reason the reordered iput has one epilogue and not
     two.  So it is a lemma, and neither caller carries a copy.

     IT THREADS NOTHING BUT THE PC, THE GPR CAPABILITY AND THE FRAME.  Every
     other resource either does not exist at this altitude or is the caller's
     to transport across the epilogue's hart hops itself ([cpu_own_transport]
     / [trap_csrs_ext_transport] under the [wp_next] wrapper below) -- which
     is exactly what [ip_tail_exit] did inline before the factoring, and what
     lets the two callers keep completely different posts. *)
  Lemma ip_epilogue `{GEN : GenId} `{CID : CpuId}
      (j : nat) (D : regfile) (K : nat) (eb : bool)
      (sp0 v1 v2 v3 v4 v5 v6 : mword 64) :
    let pj := proc_addr j in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (6 <= K)%nat ->
    D !!! Regidx csp_rs1 = spd ->
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x30) : mword 64) -∗
    sie_cap_gpr KT1 D (K - 6)%nat eb pj -∗
    pa_stk sp0 1 ↦₈[KT1] v1 -∗
    pa_stk sp0 2 ↦₈[KT1] v2 -∗
    pa_stk sp0 3 ↦₈[KT1] v3 -∗
    pa_stk sp0 4 ↦₈[KT1] v4 -∗
    pa_stk sp0 5 ↦₈[KT1] v5 -∗
    pa_stk sp0 6 ↦₈[KT1] v6 -∗
    (* ANCHORED AT THIS LEMMA'S OWN ENTRY HART, AT [eb] -- not at the
       caller's [CID0] and not at [true].  The four instructions can park
       only when interrupts are enabled, so the chain they hand the caller
       has to be the [eb]-indexed one, or the caller's own [eb]-indexed
       transports ([cpu_own_transport]) cannot use it.  Anchoring at [CID]
       also spares the lemma an anchor premise: the caller composes this
       chain with its own. *)
    wp_next (CID0 := CID) eb pj (fun (CIDf : CpuId) =>
      ∀ P : regfile,
        ⌜P !!! Regidx Rra = v1
         /\ P !!! Regidx Rs0 = v2
         /\ P !!! Regidx Rs1 = v3
         /\ P !!! Regidx csp_rs1 = sp0
         /\ (forall c : mword 5, is_cs_idx c = true ->
               c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
               P !!! Regidx c = D !!! Regidx c)⌝ -∗
        sie_cap_gpr (CID := CIDf) KT1 P K eb pj -∗
        pc_is (CID := CIDf) (ret_pc v1) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj spd HK Hsp.
    iIntros "#Htext Hpc Hcg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hcont".
    iPoseProof (ipi_30 with "Htext") as "Hi32".
    iPoseProof (ipi_32 with "Htext") as "Hi34".
    iPoseProof (ipi_34 with "Htext") as "Hi36".
    iPoseProof (ipi_36 with "Htext") as "Hi38".
    iPoseProof (ipi_38 with "Htext") as "Hi3a".
    (* the six saved-slot addresses, in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb5 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb6 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    iEval (rewrite -Hb5) in "Hg5". iEval (rewrite -Hb6) in "Hg6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x30))
              (mword_of_int 5 : mword 6) Rra D (K - 6)%nat v1 eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32 [Hr24]").
    { iEval (rewrite Hsp). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite Hsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg v1]> D).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1 upd_ne; [exact Hsp | nz]).
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.iput + 0x30) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x32)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x32))
              (mword_of_int 4 : mword 6) Rs0 P1 (K - 6)%nat v2 eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi34 [Hr16]").
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg v2]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spd)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.iput + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x34)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x34))
              (mword_of_int 3 : mword 6) Rs1 P2 (K - 6)%nat v3 eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi36 [Hr8]").
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg v3]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spd)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.iput + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x36)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
    { rewrite HP3sp. unfold spd. apply frame_cancel_48. }
    assert (Hpop : P3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HP3sp. unfold spd, pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hr24 Hr16 Hr8 Hg4 Hg5 Hg6]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4); iExists _; iExact "Hg4"|].
      iSplitL "Hg5";  [iEval (rewrite -Hb5); iExists _; iExact "Hg5"|].
      iSplitL "Hg6";  [iEval (rewrite -Hb6); iExists _; iExact "Hg6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iput + 0x36))
              (mword_of_int 3 : mword 6) P3 (K - 6)%nat 6 eb Hpop
              with "Hcg Hpc Hi38 Hframe4").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P3).
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P3) with P4.
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.iput + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x38)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = v1).
    { rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iput + 0x38)) Rra P4 K eb
              ltac:(nz) with "Hcg Hpc Hi3a").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HP4ra) in "Hpc".
    iSpecialize ("Hcont" $! CIDe5 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! P4 with "[%] Hcg Hpc").
    assert (Hc2 : P4 !!! Regidx csp_rs1 = sp0).
    { rewrite /P4 upd_eq. rewrite HP3sp. unfold regval_into_reg, spd.
      apply frame_cancel_48. }
    assert (Hc8 : P4 !!! Regidx Rs0 = v2).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Hc9 : P4 !!! Regidx Rs1 = v3).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
    split_and!; [exact HP4ra | exact Hc8 | exact Hc9 | exact Hc2 |].
    intros c Hcs N2 N8 N9.
    rewrite /P4 upd_ne; [| regne].
    rewrite /P3 upd_ne; [| regne].
    rewrite /P2 upd_ne; [| regne].
    rewrite /P1 upd_ne; [reflexivity | regne].
  Qed.

  Lemma ip_tail_exit `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (j : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used' Sb Sb' : gset Z)
      (k n n' : nat) (spf : bool -> nat) (wb crb0 : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m D : regfile) (K : nat) (eb : bool)
      (sp0 vg4 vg5 vg6 : mword 64) (lks : gset string) :
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx Rra) in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (K_iput <= K)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp0 = m !!! Regidx csp_rs1 ->
    iput_regs m D spd k ->
    ((n - spf wb)%nat <= n')%nat ->
    (n' <= n)%nat ->
    used' ⊆ used ->
    Sb ⊆ Sb' ->
    (* THE PAID-BITMAP REPORT (G-4c): what this run of iput did with the
       bitmap unit, carried to the contract's post verbatim, with §G.25's
       credited-caller clause beside it. *)
    (wb = true -> bmapstart ∈ Sb') ->
    (crb0 = true -> wb = false) ->
    (* THE FRESHNESS PREMISE: the entry resource below already carries
       [itable]'s rank ([ref--; release(&itable.lock)] is the tail this
       lemma proves); [lks] is the caller's OWN held set, below it. *)
    locks_below lks "itable" ->
    kernel_text -∗
    is_lock gtl itable_lock "itable"%string
      (itable_res2 cn gfs gi cov logstart nib dev) -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x24) : mword 64) -∗
    sie_cap_gpr KT1 D (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay KT1 0 eb pj -∗
    (* the trap-CSR complement: a PURE PASS-THROUGH, threaded from the
       caller's own entry straight to release's continuation -- iput never
       itself needs the bare pair, since every one of its sleeping callees
       (acquiresleep_nested excepted -- it never parks) takes the complement
       directly.  See claude-notes/completed/eb-generic-sweep.md. *)
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    locked gtl cpu_id -∗
    itable_res2 cn gfs gi cov logstart nib dev -∗
    iref_slot -∗
    (* RULING G (iclaim-ledger.md §6′): the REGIME, borrowed and returned.
       Nothing in this tail touches it -- the freeze is the free path's -- but
       [SpecIput]'s post promises it back on EVERY arm, so it rides through
       here exactly as the frame slots do. *)
    (ireg_open ∨ ireg_boot) -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈[KT1] vg4 -∗
    pa_stk sp0 5 ↦₈[KT1] vg5 -∗
    pa_stk sp0 6 ↦₈[KT1] vg6 -∗
    p_pid pj ↦₄{dq} pidv -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used' -∗
    bslots bn 3 -∗
    log_opS g n' Sb' -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z) (w : bool),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        pc_is ret_tgt -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used'' -∗
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜w = true -> bmapstart ∈ Sb''⌝ -∗
        ⌜crb0 = true -> w = false⌝ -∗
        ⌜((n - spf w)%nat <= n'')%nat /\ (n'' <= n)%nat⌝ -∗
        log_opS g n'' Sb'' -∗
        iref_slot -∗
        (* RULING G: the regime, handed back (see the premise). *)
        (ireg_open ∨ ireg_boot) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj ret_tgt spd HK Hanch Hsp0 Hregs Hlo Hhi Hsub Hssub Hwm Hwc Hfresh.
    
    destruct Hregs as (HDs1 & HDsp & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok HRres Hislot Hgreg
             Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm Hbslots Hop Hcont".
    iPoseProof (ipi_24 with "Htext") as "Hi26".
    iPoseProof (ipi_28 with "Htext") as "Hi2a".
    iPoseProof (ipi_2c with "Htext") as "Hi2e".
    iPoseProof (ipi_30 with "Htext") as "Hi32".
    iPoseProof (ipi_32 with "Htext") as "Hi34".
    iPoseProof (ipi_34 with "Htext") as "Hi36".
    iPoseProof (ipi_36 with "Htext") as "Hi38".
    iPoseProof (ipi_38 with "Htext") as "Hi3a".
    (* the frame's slot spellings are [ip_epilogue]'s business now. *)
    (* ===== +0x26 / +0x2a : a0 := &itable ; +0x2e jal release ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x24)) Ra0
              (mword_of_int 29 : mword 20) D (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x24) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> D).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iput + 0x24) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x28)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x28)) Ra0 Ra0
              (mword_of_int 1364 : mword 12) D3 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1364 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = itable_lock).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iput + 0x28) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x2c)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x2c)) Rra
              (mword_of_int 2087070 : mword 21) D4 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x2c) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.iput + 0x2c) : mword 64)
                        (sign_extend' 64 (mword_of_int 2087070 : mword 21))
                      = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HD5a0 : D5 !!! Regidx Ra0 = itable_lock)
      by (rewrite /D5 upd_ne; [exact HD4a0 | nz]).
    assert (HD5ra : D5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x2c) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true ->
                       D5 !!! Regidx c = D !!! Regidx c).
    { intros c Hcs.
      rewrite /D5 upd_ne; [| regne].
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [reflexivity | regne]. }
    assert (HD5sp : D5 !!! Regidx csp_rs1 = spd)
      by (rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HDsp).
    iApply (Release.wp_release_sconf KT1 gtl itable_lock "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) D5
              0%nat eb pj (K - 6)%nat ({["itable"]} ∪ lks)
              ltac:(rewrite HD5a0; reflexivity) ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    pose proof (locks_below_not_elem _ _ Hfresh) as Hfresh_ne.
    iEval (rewrite (_ : ({["itable"]} ∪ lks) ∖ {["itable"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hcnt".
    pose proof Hrelpins as Hrelpins_cs.
    assert (Hpc32 : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x30))
      by (rewrite HD5ra; pcw).
    iEval (rewrite Hpc32) in "Hpc".
    (* ===== EPILOGUE (index [true]): the shared +0x30 .. +0x38 lemma ===== *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HD5sp).
    iApply (ip_epilogue j mr K eb sp0 (m !!! Regidx Rra) (m !!! Regidx Rs0)
              (m !!! Regidx Rs1) vg4 vg5 vg6
              ltac:(lia) Hmrsp
              with "Htext Hpc Hcg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6").
    iIntros (CIDe5 Hse5 P4) "%Hep Hcg Hpc".
    destruct Hep as (HP4ra & Hc8 & Hc9 & Hc2 & Hthread0).
    assert (Hretf : ret_pc (m !!! Regidx Rra) = ret_tgt) by reflexivity.
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CIDr CIDe5 0%nat eb pj eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [Hextc]/[Hextm] were never re-derived across the nested (level >= 1)
       stretch above -- nothing there threads them, and none of it can move
       the hart anyway ([wp_next_off_intro]) -- so they are still exactly
       what the caller of [ip_tail_exit] handed in, at the ENTRY hart [CID].
       One wide hop straight to [CIDe5] covers the release call and the
       whole (possibly hart-moving) epilogue in a single step. *)
    iDestruct (trap_csrs_ext_transport CID CIDe5 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDe5 eb pj
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CIDe5 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! P4 n' used' Sb' wb
              with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins [%] Hbm Hbslots [%] [%] [%] [%] Hop Hislot Hgreg").
    6:{ split; [exact Hlo | exact Hhi]. }
    5:{ exact Hwc. }
    4:{ exact Hwm. }
    3:{ exact Hssub. }
    2:{ exact Hsub. }
    (* callee_saved m P4: the epilogue's own threading, composed with the
       release's and the +0x24 .. +0x2c stretch's *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              P4 !!! Regidx c = D !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite (Hthread0 c Hcs N2 N8 N9).
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      exact (HD5thr c Hcs). }
    unfold callee_saved.
    rewrite Hsp0 in Hc2.
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9
            | rewrite Hthread;
              [ assumption | vm_compute; reflexivity | nz | nz | nz ] ].
  Qed.

  (* ---- THE TAIL PROPER: +0x20 (the re-read) .. +0x24 (the close) ---- *)
  Lemma ip_tail `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (j : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used' Sb Sb' : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (Mt : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (n n' : nat) (spf : bool -> nat) (wb crb0 : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool)
      (sp0 vg4 vg5 vg6 : mword 64) (lks : gset string) :
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx Rra) in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (K_iput <= K)%nat ->
    (k < NINODE)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp0 = m !!! Regidx csp_rs1 ->
    iput_regs m M spd k ->
    M !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k) ->
    icM_wf Mt ->
    ic_ci_wf Mt ci nib dev ->
    ((n - spf wb)%nat <= n')%nat ->
    (n' <= n)%nat ->
    used' ⊆ used ->
    Sb ⊆ Sb' ->
    (* THE PAID-BITMAP REPORT (G-4c): what this run of iput did with the
       bitmap unit, carried to the contract's post verbatim, with §G.25's
       credited-caller clause beside it. *)
    (wb = true -> bmapstart ∈ Sb') ->
    (crb0 = true -> wb = false) ->
    (* THE FRESHNESS PREMISE -- see [ip_tail_exit]; this lemma's own entry
       is already past iput's FIRST [acquire(&itable.lock)]. *)
    locks_below lks "itable" ->
    kernel_text -∗
    is_lock gtl itable_lock "itable"%string
      (itable_res2 cn gfs gi cov logstart nib dev) -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart k -∗
    (* THE REGION, NEW AT §2.2/§2.3: every count move now reaches the [icnt]
       half that rides in [InodeRegion.ireg_slot], so both close AUs take the
       region invariant and open it beside [itable_inv].  Persistent. *)
    ireg_inv gi gfs inodestart nib -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x20) : mword 64) -∗
    sie_cap_gpr KT1 M (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay KT1 0 eb pj -∗
    (* pure pass-through, exactly as in [ip_tail_exit] above *)
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    locked gtl cpu_id -∗
    itable_half Mt -∗
    iref_slots_auth -∗
    isl_pool Mt -∗
    ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
    ipool gfs gi cov logstart (region_inums nib ∖ ci_inums ci) -∗
    IcacheRef.inode_ref k q dev inum -∗
    (* THE CLOSING REFERENCE's PROVENANCE UNIT (RULING R, item 7a-wire): both
       close AUs surrender it in the ghost step that moves the count, which is
       what [InodeRegion.ireg_ref_ok]'s (R1) demands.  [SpecIput]'s premise
       verbatim; the flavour is the plain one and iput does not care. *)
    runit_any (bv_unsigned inum) -∗
    (* RULING G (iclaim-ledger.md §6′): the REGIME, borrowed and returned.
       Nothing in this tail touches it -- the freeze is the free path's -- but
       [SpecIput]'s post promises it back on EVERY arm, so it rides through
       here exactly as the frame slots do. *)
    (ireg_open ∨ ireg_boot) -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈[KT1] vg4 -∗
    pa_stk sp0 5 ↦₈[KT1] vg5 -∗
    pa_stk sp0 6 ↦₈[KT1] vg6 -∗
    p_pid pj ↦₄{dq} pidv -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used' -∗
    bslots bn 3 -∗
    log_opS g n' Sb' -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z) (w : bool),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        pc_is ret_tgt -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used'' -∗
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜w = true -> bmapstart ∈ Sb''⌝ -∗
        ⌜crb0 = true -> w = false⌝ -∗
        ⌜((n - spf w)%nat <= n'')%nat /\ (n'' <= n)%nat⌝ -∗
        log_opS g n'' Sb'' -∗
        iref_slot -∗
        (* RULING G: the regime, handed back (see the premise). *)
        (ireg_open ∨ ireg_boot) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj ret_tgt spd HK Hk Hanch Hsp0 Hregs HMa5 Hwf Hciwf Hlo Hhi Hsub Hssub Hwm Hwc Hfresh.
    pose proof HK as HK'. 
    pose proof Hregs as Hregs0.
    destruct Hregs as (HMs1 & HMsp & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlock #Hinv #Hesc #Hireg Hpc Hcg Hcnt Hpay Hextc Hextm Htok
             Hhalf Hiauth Hipool Hslots Hpool Href Hru Hgreg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6
             Hppid Hbms Hins Hbm Hbslots Hop Hcont".
    iPoseProof (ipi_20 with "Htext") as "Hi22".
    iPoseProof (ipi_22 with "Htext") as "Hi24".
    iDestruct "Href" as "[Hrtok Hrident]".
    iDestruct (iref_lookup with "Hhalf Hrtok") as %(qt & cnt & HMk & Hqt1 & Hone & Hone').
    iDestruct (ip_ref_sub with "Hhalf Hrtok") as %(qt2 & cnt2 & HMk2 & Hsubq).
    rewrite HMk in HMk2. injection HMk2 as <- <-.
    pose proof (icM_wf_count Mt k qt cnt Hwf HMk) as Hcntb.
    assert (Hcik : exists di : mword 32 * mword 32, ci !! k = Some di).
    { destruct Hciwf as [Hdom _].
      assert (Hin : k ∈ dom ci) by (rewrite Hdom; apply elem_of_dom; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcik as [[cdev cinum] Hcik].
    iDestruct (islots2_acc_upd cn Mt ci k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk Hcik) in "Hslot".
    (* FIVE conjuncts since §2.2/A⁗: the [icnt] slot half and the FREEZE
       MIRROR's lock half ride in the live arm beside the three the pre-ledger
       walk knew.  [Hcnt1] is what both close AUs move; [Hpark] is [q]-vestigial
       under R-e, so the NOT-LAST close carries it through untouched and only
       the REF-1 arm has to decide it. *)
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid & Hcnt1 & Hpark)".
    iDestruct (ip_rest_sum with "Hrest") as %[qr Hsum].
    iAssert (⌜cdev = dev /\ cinum = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - qt)%Qp as [q'|] eqn:Et; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    (* the region bound both close AUs need, off [ic_ci_wf]'s third clause *)
    assert (Hinnib : bv_unsigned inum < 16 * Z.of_nat nib).
    { destruct Hciwf as (_ & _ & Hrange & _). exact (Hrange k (dev, inum) Hcik). }
    assert (Ert : (1/2 - qt)%Qp = Some qr) by (apply Qp.sub_Some; exact Hsum).
    assert (Hqthalf : (qt ≤ 1/2)%Qp) by (rewrite Hsum; apply Qp.le_add_l).
    assert (Hiw : iref_word Mt k = (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /iref_word HMk; reflexivity).
    (* ===== +0x22 c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.iput + 0x20)) Ra5
              (mword_of_int 63 : mword 6) M (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (M !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> M).
    assert (HD2s1 : D2 !!! Regidx Rs1 = ientry k)
      by (rewrite /D2 upd_ne; [exact HMs1 | nz]).
    assert (HD2regs : iput_regs m D2 spd k).
    { unfold iput_regs in Hregs0 |- *.
      destruct Hregs0 as (A&B&Cc&E&F&G&H&I&J&L&N&O).
      repeat split;
        (rewrite /D2 upd_ne; [| nz]); assumption. }
    assert (Hstv : trunc32 (rget D2 Ra5) = (mword_of_int (Z.pos cnt - 1) : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(nz)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HMa5 Hiw.
      exact (ip_storeval_pred (Z.pos cnt) ltac:(lia) ltac:(lia)). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.iput + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x22)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = i_ref (ientry k)).
    { rewrite (rget_ne D2 Rs1 ltac:(nz)) HD2s1. reflexivity. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.iput + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x24)) by pcw.
    (* ===== +0x24 c.sw a5,8(s1) : THE CLOSE, split on the count ===== *)
    destruct (decide (cnt = 1%positive)) as [->|Hnotone].
    - (* ---- THE LAST CLOSE: REF-1, and the EVICTION (§13.9) ---- *)
      specialize (Hone eq_refl). subst q.
      assert (Hp1 : Pos.to_nat 1 = 1%nat) by reflexivity.
      iEval (rewrite Hp1) in "Hcnt1".
      (* ---- THE REF-1 PARK DECISION (A⁗, iclaim-ledger.md §3.16) ----
         [islot2]'s live arm carries either the ordinary OFF mirror or the free
         path's FROZEN PARK, and at REF-1 it cannot be the latter: the park
         holds the slot's whole outstanding liveness and this thread's own
         slice would be one too many ([IcacheInv.frz_park_ref1_off], xv6's
         REF-1 argument made available to the proof).  No region open, no
         token.  The [false] mirror half it yields goes into the evicted
         inum's pool bundle; the selector half is what the last close spends. *)
      iDestruct "Hrtok" as "(Hrfrg0 & Hrlv0 & Hrslh0)".
      iApply fupd_wp.
      iMod (frz_park_ref1_off ⊤ k (bv_unsigned inum) qt
              ltac:(solve_ndisj) Hk with "Hinv Hrlv0 Hpark")
        as "(Hrlv0 & Hmirf & Hself)".
      iAssert (iref_tok k qt) with "[Hrfrg0 Hrlv0 Hrslh0]" as "Hrtok";
        [ rewrite /iref_tok; iFrame |].
      (* the eviction runs BEFORE the store: [ic_open_auth_ref] wants the
         authority still showing the slot, and the store deletes it. *)
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_auth_ref cn gfs gi cov logstart k (⊤ ∖ ↑icEscN)
              Mt qt qt dev inum ltac:(solve_ndisj) HMk
              with "Hinv Hbody Hhalf Hrtok Hrident")
        as "(Hhalf & Hrtok & Hrident & Harm & _)".
      iDestruct "Harm" as (v ga) "(Hidv & Hinv2 & Hvld & Harmt & Hmt & Hgida)".
      (* THE ARM's TAIL, DECIDED THE ORDINARY WAY (A⁗): its frozen
         alternative carries the SELECTOR's quarter UP, and the park has just
         handed this walk the [false] half ([IcacheRef.frzsel_agree]).  What
         comes out is the payload, the inum's still-unfrozen token and the
         arm's liveness half -- the three the retirement below consumes. *)
      iDestruct "Harmt" as "[(Hpayl & Hoff & Hlvh) | [_ Hselt]]"; last first.
      { iDestruct (frzsel_agree with "Hself Hselt") as %Hb. discriminate. }
      iDestruct (islot_rest_join k qt dev inum Hqthalf with "Hrident [Hrest]")
        as "[Hdh Hinh]".
      { rewrite /islot_rest. iExists dev, inum. iExact "Hrest". }
      (* the LATE flavour: the pool bundle's three ledger outputs -- the count
         at zero, the mirror down, the unfrozen token -- do not exist until
         the [sw] has fired, so what comes back here is the wand that takes
         them (IcacheEscrow's [ic_close_to_empty_late], §3.16's ordering). *)
      iMod (ic_close_to_empty_late cn gfs gi cov logstart k v ga dev inum
              with "Hgida Hgid Hidv Hdh Hinv2 Hvld Hpayl Hmt")
        as "(Hbody & Hgidf & Hbundle)".
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
      iModIntro.
      assert (Hinreg : bv_unsigned inum ∈ region_inums nib).
      { apply region_inums_spec. split; [apply bv_unsigned_in_range |].
        destruct Hciwf as (_ & _ & Hrange & _).
        exact (Hrange k (dev, inum) Hcik). }
      (* the slot's share authority, out of the LOCK's resource *)
      iDestruct (isl_pool_acc_upd Mt k Hk with "Hipool") as "[Hisl Hislback]".
      assert (Hincid : bv_unsigned inum ∈ ci_inums ci).
      { apply ci_inums_spec. exists k, (dev, inum). split; [exact Hcik | reflexivity]. }
      iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x22)) Ra5 Rs1
                (mword_of_int 8 : mword 12) D2 (trap_res eb + (K - 6))%nat
                (itable_half (delete k Mt) ∗ isl_slot (delete k Mt) k ∗
                 ifreeze_off (bv_unsigned inum) ∗
                 icnt_half (bv_unsigned inum) 0%nat)%I
                (⊤ ∖ ↑minstretN ∖ ↑icacheN ∖ ↑iregN) false ltac:(solve_ndisj)
                with "Hcg Hpc Hi24 [Hhalf Hrtok Hlvh Hself Hisl Hru Hoff Hcnt1]").
      { rewrite Hpa2 Hstv.
        replace (Z.pos 1 - 1)%Z with 0%Z by lia.
        (* THE RETIREMENT, under the restated ledger (design 17.3 (A) / R-e):
           the closer's own [qt], the invariant's [1/2 - qt] AND the arm's 1/2
           -- which the eviction has just taken out of PARKED -- are together
           the slot's whole unit, and the SELECTOR's two halves retire the
           free arm's bit.  The phase is [FrzOff] throughout (this is the
           ORDINARY last close, no freeze anywhere), so the receipt and the
           mirror trade are both [emp] and [frz_close] is the identity. *)
        iMod (iref_close_last_store_au (⊤ ∖ ↑minstretN) gi gfs inodestart nib
                Mt k inum qt false FrzOff
                ltac:(solve_ndisj) ltac:(solve_ndisj) Hinnib HMk
                with "Hinv Hireg Hhalf Hrtok [Hlvh] Hself Hisl Hru Hoff Hcnt1 [] []")
          as "[Hcell Hback2]".
        { iExists ga. iExact "Hlvh". }
        { rewrite /frz_rcpt_pre. done. }
        { rewrite /frz_mir. done. }
        iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
        iMod ("Hback2" with "Hcell") as "(Hhalf & Hisl & Hoff & Hcnt0 & _)".
        iModIntro. iFrame. }
      iApply wp_next_off_intro. iIntros "Hcg Hpc (Hhalf & Hisl & Hoff & Hcnt0)".
      iDestruct ("Hbundle" with "Hcnt0 Hmirf Hoff") as "Hbundle".
      iDestruct ("Hislback" $! (delete k Mt) with "[%] Hisl") as "Hipool".
      { intros i Hi. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
      iEval (rewrite Hpp26) in "Hpc".
      (* the table's slot re-forms as [islot_empty]; the unit the arm parked
         is the one the caller gets back *)
      iDestruct ("Hback" $! (delete k Mt) (delete k ci)
                   with "[%] [%] [Hinh Hgidf]") as "Hslots".
      { intros i Hi. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
      { intros i Hi. rewrite lookup_delete_ne; [reflexivity | by apply not_eq_sym]. }
      { rewrite /islot2 !lookup_delete. rewrite /islot_empty.
        iExists dev, inum. iFrame. }
      iDestruct (ipool_insert gfs gi cov logstart
                   (region_inums nib ∖ ci_inums ci) (bv_unsigned inum)
                   ltac:(apply ip_notin_diff; exact Hincid) with "[Hbundle] Hpool") as "Hpool".
      { rewrite ip_moi_inum. iExact "Hbundle". }
      assert (Hpoolset : region_inums nib ∖ ci_inums (delete k ci)
                         = {[ bv_unsigned inum ]} ∪ (region_inums nib ∖ ci_inums ci)).
      { destruct Hciwf as (_ & Hinj & _ & _).
        rewrite (ip_ci_inums_delete ci k dev inum Hcik Hinj).
        apply ip_pool_set; [exact Hinreg | exact Hincid]. }
      iEval (rewrite -Hpoolset) in "Hpool".
      iEval (rewrite Hp1) in "Hiu".
      iApply (ip_tail_exit CID0 j bn g gfs gi cn gtl cov logstart bmapstart inodestart
                nib size dev used used' Sb Sb' k n n' spf wb crb0 pidv dq dqb dqs m D2 K eb sp0 vg4 vg5 vg6 lks
                HK Hanch Hsp0 HD2regs Hlo Hhi Hsub Hssub Hwm Hwc Hfresh
                with "Htext Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok [-Hiu Hgreg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm Hbslots Hop Hcont] Hiu Hgreg
                      Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm Hbslots Hop Hcont").
      iExists (delete k Mt), (delete k ci).
      iFrame "Hhalf Hiauth Hslots Hpool Hipool".
      iPureIntro. split.
      { destruct Hwf as [Hdom Hcnt']. split.
        - intros i Hi. apply Hdom. destruct Hi as [e He].
          exists e. rewrite lookup_delete_Some in He. apply He.
        - intros i qi ni Hi. rewrite lookup_delete_Some in Hi.
          destruct Hi as [_ Hi]. by apply (Hcnt' i qi). }
      { destruct Hciwf as (Hdom & Hinj & Hrange & Hdv). split_and!.
        - rewrite !dom_delete_L Hdom. reflexivity.
        - intros k1 k2 p1 p2 Hp1' Hp2' Heq.
          rewrite lookup_delete_Some in Hp1'. rewrite lookup_delete_Some in Hp2'.
          exact (Hinj k1 k2 p1 p2 (proj2 Hp1') (proj2 Hp2') Heq).
        - intros k1 p1 Hp1'. rewrite lookup_delete_Some in Hp1'.
          exact (Hrange k1 p1 (proj2 Hp1')).
        - intros k1 p1 Hp1'. rewrite lookup_delete_Some in Hp1'.
          exact (Hdv k1 p1 (proj2 Hp1')). }
    - (* ---- THE NON-LAST CLOSE: count down, no escrow touch ---- *)
      destruct Hsubq as [Hc1 | [qrest Hqrest]]; [contradiction |].
      pose proof (Pos.succ_pred cnt Hnotone) as Hsucc.
      set (npred := Pos.pred cnt).
      assert (HMk' : Mt !! k = Some (qt, Pos.succ npred))
        by (rewrite /npred Hsucc; exact HMk).
      assert (Hcntn : Pos.to_nat cnt = Pos.to_nat (Pos.succ npred))
        by (rewrite /npred Hsucc; reflexivity).
      assert (Hzs : (Z.pos cnt - 1)%Z = Z.pos npred).
      { rewrite /npred. rewrite <- Hsucc at 1. rewrite Pos2Z.inj_succ. lia. }
      pose proof Hqrest as Hqt'. apply Qp.sub_Some in Hqt'.  (* qt = q + qrest *)
      iDestruct (isl_pool_acc_upd Mt k Hk with "Hipool") as "[Hisl Hislback]".
      iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x22)) Ra5 Rs1
                (mword_of_int 8 : mword 12) D2 (trap_res eb + (K - 6))%nat
                (itable_half (<[k := (qrest, npred)]> Mt) ∗
                 isl_slot (<[k := (qrest, npred)]> Mt) k ∗
                 icnt_half (bv_unsigned inum) (Pos.to_nat npred))%I
                (⊤ ∖ ↑minstretN ∖ ↑icacheN ∖ ↑iregN) false ltac:(solve_ndisj)
                with "Hcg Hpc Hi24 [Hhalf Hrtok Hisl Hru Hcnt1]").
      { rewrite Hpa2 Hstv Hzs.
        (* the count goes down from [Pos.succ npred >= 2], where BOTH phases
           of §2.3's pin are refuted by arithmetic -- so this mover needs no
           freeze token, only the region open its [icnt] half now forces. *)
        iEval (rewrite Hcntn) in "Hcnt1".
        iMod (iref_close_store_au (⊤ ∖ ↑minstretN) gi gfs inodestart nib
                Mt k inum false q qt qrest npred
                ltac:(solve_ndisj) ltac:(solve_ndisj) Hinnib HMk' Hqrest
                with "Hinv Hireg Hhalf Hrtok Hisl Hru Hcnt1")
          as "[Hcell Hback2]".
        iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
        iMod ("Hback2" with "Hcell") as "(Hhalf & Hisl & Hcnt1)".
        iModIntro. iFrame. }
      iApply wp_next_off_intro. iIntros "Hcg Hpc (Hhalf & Hisl & Hcnt1)".
      iDestruct ("Hislback" $! (<[k := (qrest, npred)]> Mt) with "[%] Hisl") as "Hipool".
      { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      iEval (rewrite Hpp26) in "Hpc".
      (* the departing fraction rejoins the table's retained share *)
      assert (Ert2 : (1/2 - qrest)%Qp = Some (q + qr)%Qp).
      { apply Qp.sub_Some. rewrite Hsum Hqt'.
        rewrite (Qp.add_assoc qrest q qr) (Qp.add_comm qrest q).
        by rewrite -(Qp.add_assoc q qrest qr). }
      iEval (rewrite /islot_rest_at Ert) in "Hrest".
      iAssert (islot_rest_at k qrest dev inum)%I with "[Hrest Hrident]" as "Hrest".
      { rewrite /islot_rest_at Ert2.
        iDestruct (inode_ident_split k q qr dev inum) as "[_ Hjoin]".
        iApply "Hjoin". iFrame. }
      assert (Hiun : Pos.to_nat cnt = (1 + Pos.to_nat npred)%nat).
      { rewrite /npred. rewrite <- Hsucc at 1. rewrite Pos2Nat.inj_succ. lia. }
      iEval (rewrite Hiun) in "Hiu".
      iDestruct (iref_slots_split 1 (Pos.to_nat npred) with "Hiu") as "[Hislot Hiu]".
      (* the park rides through: under R-e its [q] is vestigial, so the moved
         share needs no more than [frz_park_mono]'s free weakening *)
      assert (Hqrle : (qrest ≤ qt)%Qp).
      { rewrite Hqt'. first [apply Qp.le_add_l | apply Qp.le_add_r]. }
      iDestruct (frz_park_mono k (bv_unsigned inum) qt qrest Hqrle
                   with "Hpark") as "Hpark".
      iDestruct ("Hback" $! (<[k := (qrest, npred)]> Mt) ci
                   with "[%] [%] [Hrest Hiu Hgid Hcnt1 Hpark]") as "Hslots".
      { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      { intros i Hi. reflexivity. }
      { rewrite /islot2 lookup_insert Hcik. iFrame. }
      iApply (ip_tail_exit CID0 j bn g gfs gi cn gtl cov logstart bmapstart inodestart
                nib size dev used used' Sb Sb' k n n' spf wb crb0 pidv dq dqb dqs m D2 K eb sp0 vg4 vg5 vg6 lks
                HK Hanch Hsp0 HD2regs Hlo Hhi Hsub Hssub Hwm Hwc Hfresh
                with "Htext Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok [-Hislot Hgreg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm Hbslots Hop Hcont] Hislot Hgreg
                      Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm Hbslots Hop Hcont").
      iExists (<[k := (qrest, npred)]> Mt), ci.
      iFrame "Hhalf Hiauth Hslots Hpool Hipool".
      iPureIntro. split.
      { destruct Hwf as [Hdom Hcnt']. split.
        - intros i Hi. destruct (decide (i = k)) as [->|Hne]; [exact Hk|].
          rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
        - intros i qi ni Hi. destruct (decide (i = k)) as [->|Hne].
          + rewrite lookup_insert in Hi. apply Some_inj in Hi.
            injection Hi as _ Hn. subst ni.
            pose proof (Hcnt' k qt cnt HMk) as Hb. rewrite -Hzs. lia.
          + rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
            by apply (Hcnt' i qi). }
      { destruct Hciwf as (Hdom & Hinj & Hrange & Hdv). split_and!;
          [| exact Hinj | exact Hrange | exact Hdv].
        (* NOT [set_solver]: from inside this whole-function proof it
           rescans the entire Iris context -- 38 s for one domain identity
           (this file's own note at [ip_diff_sub] above, and
           optimization.md).  [k] is already in [dom Mt], so the re-insert
           does not move the domain at all. *)
        rewrite (dom_insert_lookup_L Mt k _ (mk_is_Some _ _ HMk)).
        exact Hdom. }
  Qed.

End IputTail.

(* ===================================================================== *)
(*  3b. THE FREE PATH, +0x3a .. +0xca  (task 18's SPLICE)                  *)
(*                                                                        *)
(*  The three lemmas the reordered iput's free arm is made of, folded in   *)
(*  from the development files they were proven in                        *)
(*  (IputFreeEntryDev.v / IputFreeLockedDev.v / IputOfflockDev.v).  They   *)
(*  live HERE, in one section of one file, because the green-gate policy   *)
(*  is monolithic-per-function: a walk that is a module of its own is a    *)
(*  walk whose seams nothing checks.  The off-lock tail was a separate     *)
(*  functor [OfflockDev BR LW BL] in development and is now plain section  *)
(*  content -- [IputProof] takes the three leaf specs itself.              *)
(*                                                                        *)
(*  ORDER MATTERS: [ip_free_offlock] is applied by [ip_free_locked], which *)
(*  is reached from [ip_free_entry]'s EXIT B.                              *)
(* ===================================================================== *)

Section IputFreePath.
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

  Local Ltac regne := reg_ne_side.

  (* ---- (a) the OFF-LOCK TAIL, +0xa8 .. c.j 0x30 ---- *)


  (* the record the [sh zero,88(a5)] leaves in the marked slot: the loaded
     record with its 16-bit type field zeroed, EVERYTHING ELSE verbatim (the
     off-lock free writes ONLY type, unlike iupdate's full flush). *)
  Definition set_ditype0 (d : dinode) : dinode :=
    MkDinode (mword_of_int 0 : mword 16) (di_major d) (di_minor d)
             (di_nlink d) (di_size d) (di_addrs d).

  (* the register-threading invariant across the three calls (bread,
     log_write, brelse): every callee-saved reg but the frame's own
     (s1,s2,s3,s4 -- s1 holds bp across the calls, s2/3/4 restored at the
     tail) rides untouched from entry to 0x30. *)
  Definition ipo_thr (m M : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      c <> csp_rs1 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
      M !!! Regidx c = (m !!! Regidx c : mword 64).

  (* [iu_held_L], inlined (ProofIupdate-module-local otherwise). *)
  Lemma ipo_held_L (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
      (uint bno ↪[fs_L γfs]{#(1/2)} bsl) ∗
      ((uint bno ↪[fs_L γfs]{#(1/2)} bsl) -∗
       bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & Hpay)".
    destruct d.
    - rewrite /fs_mdirty. iDestruct "Hpay" as "[[HL HD] Hq]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD Hq".
    - rewrite /fs_mclean. iDestruct "Hpay" as "[[HL HD] %He]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD". done.
  Qed.

  (* ======================================================================
     ip_free_offlock : the off-lock free tail, iput +0xa8 .. j 0x30.

     ENTRY (the (A) contract, at pc = iput+0xa8, the itable lock RELEASED):
       - a0 = dev, a1 = the IBLOCK word, s2 = inum (sign-extended);
       - s1 will be overwritten with bp; s3/s4 ride the frame;
       - the loaded record [dinode_at gi inum dn] with di_nlink dn = 0;
       - the EMPTY escrow minted at the +0x8a last close, [escA_inv ge gr gd
         gi inum], and its DEPOSIT ticket [redeem_ticketA gd];  [ireg_inv].
         NOT the pool bundle: under the reorder [ip_free_locked] has already
         parked that at the +0x94 release (IVd, see the entry note);
       - bread/log_write/brelse fabric (bio_ctx, log_ctx, disk, procs);
       - the 6-slot frame (ra,s0,s1 held through; s2,s3,s4 restored here).

     POST (at pc = iput+0x30, handed to the iput-return epilogue):
       - the machine restored (s2/s3/s4 <- saved frame values), sp unchanged;
       - the region side parked into [ireg_inv] by the deposit, and the
         escrow left FILLED for whoever redeems it (no pool entry: it was
         parked at +0x94);
       - log ledger grown by the inode block; the frame still held.
     ====================================================================== *)
  Lemma ip_free_offlock `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart inodestart : Z) (nib : nat)
      (dev : mword 32) (inum : mword 32) (dn : dinode)
      (ge gr gd : gname)
      (u : nat) (Sb : gset Z) (cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqs : dfrac)
      (sp0 vra vs0 vs1 vs2 vs3 vs4 : mword 64)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string) :
    let pj := proc_addr j in
    let bno := (mword_of_int (IBLOCK inum inodestart) : mword 32) in
    let dn' := set_ditype0 dn in
    (K_bread <= K)%nat -> (K_log_write <= K)%nat -> (K_brelse <= K)%nat ->
    (* [SpecLogWrite]'s [Z.of_nat n + 2 < 2^31] is a bound on the CPU NESTING
       LEVEL, not on the log's unit count, and this tail calls log_write at
       the literal level 0 -- so the premise this lemma used to carry for it
       was vacuous and is gone.  (It read as a bound on [u] purely because
       the two arguments happen to share a name at the call site.) *)
    log_geom_ok cov logstart ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn ->
    bv_unsigned (di_nlink dn) = 0 ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    sp0 = m !!! Regidx csp_rs1 ->
    m !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64) ->
    m !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64) ->
    m !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64) ->
    locks_below lks "log" ->
    sie_cap_gpr KT1 m K b pj -∗
    cpu_own 0 eb pj b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* ---- THE LEDGER's UNCACHED CAPITAL IS NOT HERE (iclaim-ledger.md IVd),
       and under the REORDER it cannot be.  The count half at zero, the
       mirror's half DOWN and the escrow's REDEEM ticket are the evicted
       inum's POOL BUNDLE, and the reordered iput releases the itable lock at
       +0x94 -- BEFORE this tail runs.  At that release
       [IcacheEscrow.ic_ci_wf]'s [dom ci = dom M] already shows the inum
       uncached, so its bundle must be in the itable's free pool by then, and
       [ip_free_locked] parks it there on the AWAIT arm
       ([IcacheEscrow.ipool_shape_await]) out of the last close's own three
       outputs.  There is exactly one [icnt_half .. 0] and one
       [frzm_h .. false] in the system, so this tail can neither take them nor
       hand one back: the pending arm's [committedA] upgrade belongs to
       whoever later redeems the escrow, not to the depositor.

       WHAT THE DEPOSITOR STILL CARRIES is the escrow itself (persistent) and
       its DEPOSIT ticket, below -- the two things the +0xba fill needs. *)
    escA_inv ge gr gd γi (bv_unsigned inum) -∗
    (* THE DEPOSIT TICKET (A⁗, §3.16), in place of IVa's [ifreeze_post].  The
       standing freeze now lives in the ESCROW's EMPTY state -- it has to,
       because that is the only place from which a RECYCLER peeling the pool's
       await arm can find it and its licence refute it (§1.3) -- so the
       depositor carries the ticket that opens that state instead, and
       [EscrowInode.escA_deposit_acc] hands it the token, takes the retired
       one back, and rules out a second deposit. *)
    redeem_ticketA gd -∗
    p_pid pj ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bslots bn 2 -∗
    log_epoch_lb γ v -∗
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ (S u) Sb e0 -∗
    (* the frame: ra/s0/s1 ride through to the epilogue; s2/s3/s4 restored here *)
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
    (* THE CALLER'S CONTINUATION at 0x30 *)
    wp_next true pj (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜ipo_thr m mf /\ mf !!! Regidx csp_rs1 = sp0
          /\ mf !!! Regidx Rs2 = vs2 /\ mf !!! Regidx Rs3 = vs3
          /\ mf !!! Regidx Rs4 = vs4⌝ -∗
        sie_cap_gpr (CID := CID) KT1 mf K b pj -∗
        cpu_own (CID := CID) 0 eb pj b lks -∗
        trap_csrs_ext (CID := CID) KT1 eb -∗
        cpu_claim_ext (CID := CID) eb pj -∗
        pc_is (CID := CID) (mword_of_int (KernelSyms.iput + 0x30) : mword 64) -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        (* no pool entry: [ip_free_locked] parked it at the +0x94 release,
           on the AWAIT arm -- see the entry note above *)
        bslots bn 2 -∗
        log_opS γ (if cru then S u else u) (Sb ∪ {[IBLOCK inum inodestart]}) -∗
        (∃ e : nat, logged_at γ e (IBLOCK inum inodestart) ∗ ⌜(v <= e)%nat⌝) -∗
        (* RULING G's RETURN LEG (iclaim-ledger.md §6′).  The +0xba deposit
           runs the region open that retires the freeze, and the slot's
           boot-shelter clause is on its SEALED arm there ([FrzPost] refutes
           ⌜f = FrzOff⌝) -- so the regime the caller lent at the mint comes
           back out with the [committedA] marker
           ([EscrowDeposit.ireg_free_deposit_au]'s second fupd). *)
        (ireg_open ∨ ireg_boot) -∗
        (* the frame ra/s0/s1 slots, still saved, for the epilogue *)
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj bno dn' HKbr HKlw HKbl Hgeom Hst Hcov Hlog Hnib Hdnwf Hnl0
           Hj Hgl Hsp0 Ha0 Ha1 Hs2v Hbelow.
    (* ---- pure prelude (mirrors iu_main_gen) ---- *)
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hcov) as [Hibpos Hiblt].
    assert (Hib : 0 <= IBLOCK inum inodestart < 2147483648)
      by (change (2 ^ 31)%Z with 2147483648%Z in Hiblt; lia).
    assert (Hbno : uint bno = IBLOCK inum inodestart).
    { rewrite /bno bb_uint32 moi32_unsigned. apply bvw32_small.
      change (2^32)%Z with 4294967296%Z. lia. }
    assert (Hbnolt : (uint bno < 2147483648)%Z) by (rewrite Hbno; lia).
    assert (Hbnocov : uint bno ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Hbno; exact Hcov).
    pose proof (bv_unsigned_in_range _ inum) as [Hinum0 Hinum1].
    assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm32 in Hinum1.
    assert (Hslotz : Z.of_nat (DinodeEnc.islot inum) = bv_unsigned inum `mod` 16).
    { rewrite /DinodeEnc.islot Z2Nat.id; [reflexivity |].
      pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hz _].
      exact Hz. }
    pose proof (DinodeEnc.islot_lt inum) as Hslotlt.
    assert (Hdn'wf : dinode_wf dn') by (rewrite /dn' /set_ditype0 /dinode_wf /=; exact Hdnwf).
    assert (Hdn'ty : bv_unsigned (di_type dn') = 0) by (vm_compute; reflexivity).
    assert (Hnlst : di_nlink_stable dn' dn).
    { rewrite /di_nlink_stable /dn' /set_ditype0 /=. split; [reflexivity | intros _; exact Hnl0]. }
    iIntros "Hcg Hcnt Htc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx #Hireg Hdn
             #Hesc Hdep Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsb Hsl #Hvlb #Hcrd0 Hop
             Hra Hs0f Hs1f Hs2f Hs3f Hs4f Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
    (* ===== +0xa8 jal ra,bread ===== *)
    iPoseProof (ipi_a8 with "Htext") as "Hia8".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xa8)) Rra
              (mword_of_int 2094910 : mword 21) m K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hia8").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (R0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) 4)]> m).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.iput + 0xa8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094910 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HR0a0 : R0 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R0 upd_ne; [exact Ha0 | nz]).
    assert (HR0a1 : R0 !!! Regidx Ra1 = (sign_extend' 64 bno : mword 64))
      by (rewrite /R0 upd_ne; [exact Ha1 | nz]).
    assert (HR0s2 : R0 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R0 upd_ne; [exact Hs2v | nz]).
    assert (HR0ra : R0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xa8) : mword 64) 4)
      by (rewrite /R0; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CID1 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID1 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID0 CID1 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID1) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    (* ===== bread ===== *)
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bno dq
              R0 K eb b
              lks HKbr Hbnolt eq_refl Hbnocov eq_refl Hj Hgl HR0a0 HR0a1
              ltac:(lkbelow)
              with "Hcg Hcnt Htc Hclm Htext Hkd Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    all: try lkbelow.
    iIntros (CID15 Hq15 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Htc Hclm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc_ac : ret_pc (R0 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xac)) by (rewrite HR0ra; pcw).
    iEval (rewrite Hpc_ac) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)).
    { rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity)). exact HR0s2. }
    (* ---- couple the buffer bytes to the region's parked [ds] ---- *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iDestruct (ipo_held_L with "Hheld") as "[HpL Hheldback0]".
    iApply fupd_wp.
    iMod (ireg_read ⊤ γi γfs inodestart nib inum dn (uint bno) bs0
            ltac:(solve_ndisj) Hnib Hbno
            with "Hireg Hdn HpL") as "(%Hex & Hdn & HpL)".
    iModIntro.
    iDestruct ("Hheldback0" with "HpL") as "Hheld".
    destruct Hex as (ds & Hdswf & Hbs0 & Hslteq).
    subst bs0.
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    iDestruct (iu_buf_bytes (bpa kk) bno (mword_of_int 0 : mword 32) ds Hdswf
                 with "Hbuf") as "[Hby Hbyback]".
    assert (Hslotal : dislot_align
              (pa_add (b_data (bnode kk)) (64 * DinodeEnc.islot inum)%nat)).
    { rewrite /dislot_align.
      assert (E0 : (64 * DinodeEnc.islot inum)%nat = (64 * DinodeEnc.islot inum + 0)%nat) by lia.
      split_and!.
      - rewrite E0. apply iu_align; [exact Hkk | exact Hslotlt | lia | left; reflexivity
                                   | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | left; reflexivity | reflexivity].
      - rewrite pa_add_add. apply iu_align;
          [exact Hkk | exact Hslotlt | lia | right; reflexivity | reflexivity]. }
    iDestruct (diblk_slot_acc (b_data (bpa kk)) ds (DinodeEnc.islot inum)
                 Hdswf Hslotlt Hslotal with "Hby") as "[Hslot Hslotback]".
    iDestruct "Hslot" as "(Hd0 & Hd2 & Hd4 & Hd6 & Hd8 & Hda)".
    (* ===== +0xac c.mv s1,a0 : s1 := bp ===== *)
    iPoseProof (ipi_ac with "Htext") as "Hiac".
    iPoseProof (ipi_ae with "Htext") as "Hiae".
    iPoseProof (ipi_b2 with "Htext") as "Hib2".
    iPoseProof (ipi_b4 with "Htext") as "Hib4".
    iPoseProof (ipi_b6 with "Htext") as "Hib6".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0xac)) Rs1 Ra0
              mB K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiac").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (R1 := <[Regidx Rs1 := regval_into_reg (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HR1s1 : R1 !!! Regidx Rs1 = bnode kk).
    { rewrite /R1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HR1a0 : R1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R1 upd_ne; [exact HmBa0 | nz]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /R1 upd_ne; [exact HmBs2 | nz]).
    assert (Hppae : add_vec_int (mword_of_int (KernelSyms.iput + 0xac) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xae)) by pcw.
    iEval (rewrite Hppae) in "Hpc".
    (* ===== +0xae andi a5,s2,15 : a5 := inum % IPB ===== *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.iput + 0xae)) Ra5 Rs2
              (mword_of_int 15 : mword 12)
              (mword_of_int (bv_unsigned inum `mod` 16) : mword 64)
              R1 K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiae").
    { rgne. rewrite HR1s2.
      replace (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
        with (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)) : mword 64)
        by pcw.
      rewrite iu_andi15 iu_sext_mod16. reflexivity. }
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (R2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (bv_unsigned inum `mod` 16) : mword 64)]> R1).
    assert (HR2a5 : R2 !!! Regidx Ra5 = (mword_of_int (bv_unsigned inum `mod` 16) : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a0 : R2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R2 upd_ne; [exact HR1a0 | nz]).
    assert (Hppb2 : add_vec_int (mword_of_int (KernelSyms.iput + 0xae) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0xb2)) by pcw.
    iEval (rewrite Hppb2) in "Hpc".
    (* ===== +0xb2 c.slli a5,0x6 : a5 := (inum % IPB) * 64 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.iput + 0xb2)) (Regidx Ra5) Ra5
              (mword_of_int 6 : mword 6) R2 K b
              ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib2").
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R3 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (rget R2 Ra5)
                     (subrange_vec_dec (mword_of_int 6 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> R2).
    assert (HR3a5 : R3 !!! Regidx Ra5
                    = (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a5.
      apply iu_slli6.
      - apply Z.mod_pos_bound. lia.
      - apply Z.mod_pos_bound. lia. }
    assert (HR3a0 : R3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.iput + 0xb2) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xb4)) by pcw.
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 c.add a5,a5,a0 : a5 := bp + (inum%IPB)*64 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.iput + 0xb4)) Ra5 Ra0
              R3 K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib4").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget R3 Ra5) (rget R3 Ra0))]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5
                    = add_vec (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)
                              (bnode kk)).
    { rewrite /R4 upd_eq. rgne. rgne. rewrite HR3a5 HR3a0. reflexivity. }
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.iput + 0xb4) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xb6)) by pcw.
    iEval (rewrite Hppb6) in "Hpc".
    (* ===== +0xb6 sh zero,88(a5) : dip->type = 0 ===== *)
    (* the store address is the marked slot's type cell *)
    assert (Hstore : add_vec (rget R4 Ra5) (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat).
    { rgne. rewrite HR4a5.
      rewrite -iu_slot_addr -iu_data_addr.
      change (bpa kk) with (bnode kk).
      apply bv_eq. rewrite !add_vec64_unsigned.
      rewrite !bv_wrap_add_idemp_l.
      assert (Hs88 : bv_unsigned (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64) = 88)
        by (vm_compute; reflexivity).
      assert (Hmoi64 : bv_unsigned (mword_of_int (64 * Z.of_nat (DinodeEnc.islot inum)) : mword 64)
                       = 64 * Z.of_nat (DinodeEnc.islot inum)).
      { apply moi64_small. pose proof (DinodeEnc.islot_lt inum). lia. }
      assert (Hmoi64' : bv_unsigned (mword_of_int (64 * (bv_unsigned inum `mod` 16)) : mword 64)
                        = 64 * (bv_unsigned inum `mod` 16)).
      { apply moi64_small. pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [_ Hb]. lia. }
      rewrite Hs88 Hmoi64 Hmoi64' Hslotz. f_equal. ring. }
    iDestruct (sie_cap_gpr_x0 R4 K b pj (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    iEval (rewrite -Hstore) in "Hd0".
    iApply (wp_sh_s_sconf (mword_of_int (KernelSyms.iput + 0xb6)) Rz Ra5
              (mword_of_int 88 : mword 12) R4 K
              (di_type (ds !!! DinodeEnc.islot inum) : mword 16) b with "Hcg Hpc Hib6 Hd0").
    iIntros (CID20 Hq20) "Hcg Hpc Hd0".
    (* the store wrote 0 = di_type dn' into the type cell *)
    assert (Hstoreval : trunc16 (rget R4 Rz) = (di_type dn' : mword 16)).
    { rgne. rewrite Hx0 /dn' /set_ditype0 /=. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hstore Hstoreval) in "Hd0".
    (* ---- rebuild the slot at [dn'], then the buffer, then the handle ---- *)
    assert (Hmaj : di_major dn' = di_major dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hmin : di_minor dn' = di_minor dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hnlk : di_nlink dn' = di_nlink dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hsz  : di_size  dn' = di_size  dn) by (rewrite /dn' /set_ditype0; reflexivity).
    assert (Hadr : di_addrs dn' = di_addrs dn) by (rewrite /dn' /set_ditype0; reflexivity).
    iEval (rewrite Hslteq) in "Hd2".
    iEval (rewrite Hslteq) in "Hd4".
    iEval (rewrite Hslteq) in "Hd6".
    iEval (rewrite Hslteq) in "Hd8".
    iEval (rewrite Hslteq) in "Hda".
    iAssert (dislot (pa_add (b_data (bpa kk)) (64 * DinodeEnc.islot inum)%nat) dn')
      with "[Hd0 Hd2 Hd4 Hd6 Hd8 Hda]" as "Hslot'".
    { rewrite /dislot Hmaj Hmin Hnlk Hsz Hadr. iFrame "Hd0 Hd2 Hd4 Hd6 Hd8 Hda". }
    iDestruct ("Hslotback" $! dn' with "[%] Hslot'") as "Hby'"; [exact Hdn'wf |].
    iDestruct ("Hbyback" $! (<[DinodeEnc.islot inum := dn']> ds) with "[%] Hby'") as "Hbuf'".
    { exact (diblk_wf_insert ds (DinodeEnc.islot inum) dn' Hdswf Hdn'wf). }
    iDestruct ("Hheldback" with "Hbuf'") as "Hheld".
    (* ===== +0xba jal ra,log_write ===== *)
    iPoseProof (ipi_ba with "Htext") as "Hiba".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xba)) Rra
              (mword_of_int 2524 : mword 21) R4 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hiba").
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xba) : mword 64) 4)]> R4).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.iput + 0xba) : mword 64)
                       (sign_extend' 64 (mword_of_int 2524 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx Ra0 = bnode kk).
    { rewrite /R4 upd_ne; [| nz]. exact HR3a0. }
    assert (HR5a0 : R5 !!! Regidx Ra0 = bnode kk)
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5ra : R5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xba) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    (* ---- the deposit's AU, adapted to log_write's anchor form ---- *)
    iPoseProof (ireg_free_deposit_au ⊤ γi γfs inodestart nib inum dn dn' ds ge gr gd
                  ltac:(solve_ndisj) ltac:(solve_ndisj) Hnib Hdswf Hdn'wf Hdn'ty Hnlst
                  with "Hireg Hesc Hdn Hdep") as "Hau0".
    iEval (rewrite -Hbno) in "Hau0".
    iDestruct (lw_au_lb0 γ γfs (uint bno) (⊤ ∖ ↑iregN)
                 (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) (diblk_bytes ds)
                 (committedA ge ∗ (ireg_open ∨ ireg_boot))%I e0 with "Hau0") as "Hau".
    (* ---- transports around the log_write park ---- *)
    iDestruct (cpu_own_transport CID15 CID21 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID1) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iRename "Hop" into "HopS".
    iAssert (log_credit γ cru Sb e0 (uint bno)) as "#Hcrd";
      [rewrite Hbno; iExact "Hcrd0" |].
    iApply (LW.wp_log_write_au bn γ γfs γd cov logstart dev kk pidv bno
              (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) (diblk_bytes ds) bsd0 d0 u
              cru Sb e0 v (⊤ ∖ ↑iregN) (committedA ge ∗ (ireg_open ∨ ireg_boot))%I
              R5 0%nat eb pj K b
              _ HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HR5a0
              ltac:(rewrite Hbno; exact Hcov)
              ltac:(rewrite Hbno; exact Hlog)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hsl Hvlb Hcrd HopS Hau Hheld").
    all: try lkbelow.
    iIntros (CID22 Hq22 mL) "Hcg Hcnt Hpc %Hcs2 HopS [#Hcom Hgreg] Hlk Hsl".
    (* NO POOL ENTRY IS ASSEMBLED HERE (IVd).  The bundle was parked at the
       +0x94 release on the AWAIT arm, which is the arm's own stated purpose;
       the [committedA] the deposit just produced is not needed to state it
       (the await arm is [pool_pending] minus exactly that fragment) and the
       upgrade, if anyone ever wants it, belongs to the redeemer. *)
    (* ---- the log ledger, in the public form ---- *)
    iEval (rewrite Hbno) in "HopS".
    iDestruct (log_opSwe_opSw with "HopS") as "HopS".
    iDestruct (log_opSw_witness with "HopS") as "[Hop Hwit]".
    (* ---- register facts for [R5] carried through log_write ---- *)
    assert (HR5s1 : R5 !!! Regidx Rs1 = bnode kk).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz]. exact HR1s1. }
    assert (HR5sp : R5 !!! Regidx csp_rs1 = sp0).
    { rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R0 upd_ne; [| nz].
      exact (eq_sym Hsp0). }
    pose proof Hcs2 as Hcs2_cs.
    assert (HmLs1 : mL !!! Regidx Rs1 = bnode kk).
    { rewrite (callee_saved_lookup Hcs2_cs Rs1 ltac:(vm_compute; reflexivity)). exact HR5s1. }
    assert (HmLsp : mL !!! Regidx csp_rs1 = sp0).
    { rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HR5sp. }
    assert (Hpcbe : ret_pc (R5 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xbe)) by (rewrite HR5ra; pcw).
    iEval (rewrite Hpcbe) in "Hpc".
    (* ===== +0xbe c.mv a0,s1 : a0 := bp ===== *)
    iPoseProof (ipi_be with "Htext") as "Hibe".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0xbe)) Ra0 Rs1
              mL K b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibe").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec (zero_reg : mword 64) (rget mL Rs1))]> mL).
    assert (HT0a0 : T0 !!! Regidx Ra0 = bnode kk).
    { rewrite /T0 upd_eq. rgne. rewrite HmLs1. apply add_vec_zero_l. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = sp0)
      by (rewrite /T0 upd_ne; [exact HmLsp | nz]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.iput + 0xbe) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc0)) by pcw.
    iEval (rewrite Hppc0) in "Hpc".
    (* ===== +0xc0 jal ra,brelse ===== *)
    iPoseProof (ipi_c0 with "Htext") as "Hic0".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0xc0)) Rra
              (mword_of_int 2095150 : mword 21) T0 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hic0").
    iIntros (CID24 Hq24) "Hcg Hpc".
    set (T1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0xc0) : mword 64) 4)]> T0).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.iput + 0xc0) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095150 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T1 upd_ne; [exact HT0a0 | nz]).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /T1 upd_ne; [exact HT0sp | nz]).
    assert (HT1ra : T1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0xc0) : mword 64) 4)
      by (rewrite /T1; apply upd_eq).
    (* transports around the brelse park *)
    iDestruct (cpu_own_transport CID22 CID24 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID24) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bno dq T1 K eb pj
              (diblk_bytes (<[DinodeEnc.islot inum := dn']> ds)) bsd0 true b
              lks HKbl Hkk HT1a0 ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hlk").
    all: try lkbelow.
    iIntros (CID25 Hq25 mR) "%Hcs3 Hcg Hcnt Hpc Hppid Hsl1".
    pose proof Hcs3 as Hcs3_cs.
    assert (Hpcc4 : ret_pc (T1 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.iput + 0xc4)) by (rewrite HT1ra; pcw).
    iEval (rewrite Hpcc4) in "Hpc".
    assert (HmRsp : mR !!! Regidx csp_rs1 = sp0).
    { rewrite (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HT1sp. }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    iEval (change (1 + 1)%nat with 2%nat) in "Hsl".
    (* ===== +0xc4/c6/c8 c.ldsp s2/s3/s4 : restore ===== *)
    iPoseProof (ipi_c4 with "Htext") as "Hic4".
    iPoseProof (ipi_c6 with "Htext") as "Hic6".
    iPoseProof (ipi_c8 with "Htext") as "Hic8".
    iPoseProof (ipi_ca with "Htext") as "Hica".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc4)) (mword_of_int 2 : mword 6) Rs2
              mR K vs2 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic4 [Hs2f]").
    { iEval (rewrite HmRsp). iExact "Hs2f". }
    iIntros (CID26 Hq26) "Hcg Hpc Hs2f".
    iEval (rewrite HmRsp) in "Hs2f".
    set (P1 := <[Regidx Rs2 := regval_into_reg vs2]> mR).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P1 upd_ne; [exact HmRsp | nz]).
    assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.iput + 0xc4) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc6)) by pcw.
    iEval (rewrite Hppc6) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc6)) (mword_of_int 1 : mword 6) Rs3
              P1 K vs3 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic6 [Hs3f]").
    { iEval (rewrite HP1sp). iExact "Hs3f". }
    iIntros (CID27 Hq27) "Hcg Hpc Hs3f".
    iEval (rewrite HP1sp) in "Hs3f".
    set (P2 := <[Regidx Rs3 := regval_into_reg vs3]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hppc8 : add_vec_int (mword_of_int (KernelSyms.iput + 0xc6) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xc8)) by pcw.
    iEval (rewrite Hppc8) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xc8)) (mword_of_int 0 : mword 6) Rs4
              P2 K vs4 b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic8 [Hs4f]").
    { iEval (rewrite HP2sp). iExact "Hs4f". }
    iIntros (CID28 Hq28) "Hcg Hpc Hs4f".
    iEval (rewrite HP2sp) in "Hs4f".
    set (P3 := <[Regidx Rs4 := regval_into_reg vs4]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = sp0)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hppca : add_vec_int (mword_of_int (KernelSyms.iput + 0xc8) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0xca)) by pcw.
    iEval (rewrite Hppca) in "Hpc".
    (* ===== +0xca c.j 0x30 : into the iput-return epilogue ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iput + 0xca))
              (sign_extend' 21 (concat_vec (mword_of_int 1971 : mword 11) ('b"0")))
              P3 K b ltac:(vm_compute; reflexivity) with "Hcg Hpc Hica").
    iIntros (CID29 Hst29). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt30 : add_vec (mword_of_int (KernelSyms.iput + 0xca) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1971 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.iput + 0x30)) by pcw.
    iEval (rewrite Htgt30) in "Hpc".
    (* the final callee-saved threading, m -> P3, off the frame regs *)
    assert (Hthr : ipo_thr m P3).
    { intros c Hcs Ncsp Ns1 Ns2 Ns3 Ns4.
      rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs3_cs c Hcs).
      rewrite /T1 upd_ne; [| regne].
      rewrite /T0 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      rewrite /R0 upd_ne; [| regne]. reflexivity. }
    assert (HP3s2 : P3 !!! Regidx Rs2 = vs2).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_ne; [| nz].
      rewrite /P1; apply upd_eq. }
    assert (HP3s3 : P3 !!! Regidx Rs3 = vs3).
    { rewrite /P3 upd_ne; [| nz]. rewrite /P2; apply upd_eq. }
    assert (HP3s4 : P3 !!! Regidx Rs4 = vs4) by (rewrite /P3; apply upd_eq).
    (* the final hart hop for the pass-through complement + cpu_own *)
    iDestruct (cpu_own_transport CID25 CID29 0 eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID15 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Htc") as "Htc".
    iDestruct (cpu_claim_ext_transport CID15 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclm") as "Hclm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID24) (CIDb := CID29) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    iSpecialize ("Hcont" $! CID29 with "[]"); [iPureIntro; wp_next_chain |].
    iApply ("Hcont" $! P3 with "[%] Hcg Hcnt Htc Hclm Hpc Hppid Hsb Hsl Hop Hwit
                                Hgreg Hra Hs0f Hs1f Hs2f Hs3f Hs4f").
    { split_and!; [exact Hthr | exact HP3sp | exact HP3s2 | exact HP3s3 | exact HP3s4]. }
  Qed.

  (* ---- (b) the LOCKED BLOCK, +0x5a .. +0xa6, ending in the tail above ---- *)


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
      (u : nat) (Sb : gset Z) (crb cru crz : bool) (bfl : bool) (e0 v : nat)
      (* [dqd]/[dqn] were dead binders and are gone: nothing in this
         statement mentions them. *)
      (pidv : mword 32) (dq dqb dqs : dfrac)
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
       [S _] for [ip_free_offlock]'s [log_opSe γ (S u) Sb e0]. *)
    (3 <= u)%nat ->
    (* the vacuous [Z.of_nat u + 2 < 2^31] is GONE: log_write's bound is on
       the CPU NESTING LEVEL and the off-lock tail calls it at level 0. *)
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
    sie_cap_gpr KT1 m (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay KT1 0 eb pj -∗
    trap_csrs_ext KT1 eb -∗
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
     (* ...AND THE LIVE ARM's FIFTH CONJUNCT (iclaim-ledger.md §3.16, A⁗):
        the FROZEN PARK, which this body builds at the +0x62 re-park out of
        the mirror half the mint handed it and the two live slices it is
        about to stop needing.  It cannot be built inside the wand: the mint
        at +0x50 has already flipped the bit, so from that instant nothing
        but the park itself satisfies [islot2]'s live arm. *)
     frz_park k (bv_unsigned inum) q -∗
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
    (* ---- THE LEDGER's UNCACHED CAPITAL, threaded to the off-lock tail
       (iclaim-ledger.md §1.4, and §1.5's cost table row for this file:
       "[ifreeze] threaded through [ip_free_locked]'s entry -- statement
       level").  [ip_free_offlock] hands them to
       [EscrowDeposit.ireg_free_deposit_au], which retires the freeze against
       its type-0 write, and to the pool entry the tail parks.

       PASSED STRAIGHT THROUGH FOR NOW, and that is the recorded seam.  The
       phase step this block owns (+0x8a's last close, FrzPre -> FrzPost via
       [IcacheInv.iref_close_last_freeze_store_au]) and the [icnt] half that
       close produces are the iput integration's; so is the mint that makes
       the premise satisfiable ([IputFreeEntryDev]'s Exit-B) and the
       [ic_payload] widening that lets a MID-FREE park carry [ifreeze_pre]
       rather than [ifreeze_off] (iclaim-ledger.md §3.10, DEVIATION 1). *)
    (* ---- WHAT THE MINT LEFT STANDING (iclaim-ledger.md §3.16, A⁗) ------

       IVa's two premises are GONE, and their deletion is the THIRD FINDING
       of §3.15 acted on: [ifreeze_post] and [icnt_half z 0] were VACUOUS
       from +0x82 on -- the re-acquire's own live arm produces
       [icnt_half z (Pos.to_nat cnt2)] with [cnt2 >= 1], and [icnt_agree]
       against a passed-through zero is [False].  They are the +0x8a close's
       OUTPUTS, not its inputs, and this body now produces them.

       What arrives instead is the three things [ip_free_entry]'s mint
       produced at +0x50, and each has exactly one job here:

         [ifreeze_pre] -- kept IN HAND from the mint to +0x8a.  It decides
           the escrow arm's tail at the +0x70 store and at the eviction
           ([IcacheEscrow.ic_payload_arm_decide_frz]); it reclaims the frozen
           park at +0x82 ([IcacheInv.frz_park_pre_reclaim]); it PINS THE
           COUNT there ([IcacheInv.icnt_freeze_forces_one], which is B1's
           whole answer); and it is what the last close steps to [FrzPost].
         the RECEIPT -- parked in the escrow's frozen alternative at the
           +0x5e window exit and taken home by the last close.
         the MIRROR's half UP -- what the +0x62 re-park puts in [islot2]'s
           FROZEN PARK, where a foreign [idup] collides with the mass beside
           it (OPEN(2.6b)). *)
    ifreeze_pre (bv_unsigned inum) -∗
    frzown (bv_unsigned inum) -∗
    frzm_h (bv_unsigned inum) true -∗
    (* RULING R-e (iclaim-ledger.md §5⁗⁗): the FREEZE SELECTOR's OFF half,
       which [frz_park_ref1_off] peeled out of [islot2]'s live arm at the
       +0x3a window-entering read.  The +0x62 re-park spends it: joined with
       [live_slot]'s own half it flips the slot's alternative to FROZEN, and
       the two quarters that come back are the park's and the escrow tail's. *)
    IcacheRef.frzsel k (1/2)%Qp false -∗
    (* RULING R, WIRED (iclaim-ledger.md §5‴): the LAST close surrenders the
       dying reference's PROVENANCE UNIT, which is what
       [IcacheInv.iref_close_last_freeze_store_au] has demanded since item
       7a-wire and what this walk never carried -- the file has been stale at
       its +0x8a call since [IcacheInv.v] gained the premise.  Threaded, not
       invented: the caller (task 18's [ProofIput] splice) owns it. *)
    IcacheRef.runit bfl (bv_unsigned inum) -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res γfs bmapstart cov logstart size used -∗
    p_pid pj ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    bslots bn 3 -∗
    (* THE GROUP CREDIT (fs-log.md §G.18's chain, §G.21's tier; [SpecIput]'s
       [wp_iput_gen_body] premise verbatim).  At [crz = false] this is [emp]
       and every landed caller passes nothing.  At [crz = true] it is the
       walker's persistent, inum-keyed observation -- "at epoch [e0], inside MY
       still-open op, this inum's record had a NONZERO nlink" -- and this body
       cashes it with [InodeRegion.ireg_obs_use] at the record its caller's
       +0x44 test found ZERO, buying the unit ITRUNC's tail flush would
       otherwise spend.  It is that unit and not the off-lock flush's: the
       off-lock flush is credited unconditionally, off the membership itrunc's
       own post hands out ([Hibin'] below). *)
    (if crz then nlz_obs (bv_unsigned inum) e0 ∗ ⌜γ = icfg_log⌝ ∗
                 ⌜inodestart = icfg_ist⌝
     else emp) -∗
    log_epoch_lb γ v -∗
    log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
    log_opSe γ u Sb e0 -∗
    (* the 6-slot frame: ra/s0/s1 ride to the epilogue; s2/s3/s4 restored at 0x30 *)
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
    add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
    (* THE CALLER'S CONTINUATION at 0x30 (iput's real post; ip_tail's shape) *)
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z) (w : bool),
        (* the register threading is [ipo_thr]'s, not [callee_saved]:
           s1 holds the off-lock tail's [bp] and is restored by the epilogue
           AFTER 0x30, so nothing at 0x30 may claim it back. *)
        ⌜ipo_thr m mf /\ mf !!! Regidx csp_rs1 = sp0
          /\ mf !!! Regidx Rs2 = vs2 /\ mf !!! Regidx Rs3 = vs3
          /\ mf !!! Regidx Rs4 = vs4⌝ -∗
        sie_cap_gpr (CID := CID) KT1 mf (K - 6)%nat eb pj -∗
        cpu_own (CID := CID) 0 eb pj eb lks -∗
        trap_csrs_ext (CID := CID) KT1 eb -∗
        cpu_claim_ext (CID := CID) eb pj -∗
        pc_is (CID := CID) (mword_of_int (KernelSyms.iput + 0x30) : mword 64) -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res γfs bmapstart cov logstart size used'' -∗
        (* NO [ipool_shape] HERE (IVd).  Under the REORDER the itable lock goes
           at +0x94, BEFORE the +0xba deposit, and [IcacheEscrow.ic_ci_wf]'s
           [dom ci = dom M] then forces the evicted inum's pool entry into the
           itable's own free pool AT THAT RELEASE -- the entry is parked on the
           AWAIT arm ([ipool_shape_await]), which is exactly what that arm's
           header describes ("the entry a FREER has parked ON ITS WAY TO the
           off-lock deposit").  There is only one [icnt_half .. 0] and one
           [frzm_h .. false] in existence, so nothing pool-shaped can leave
           this lemma. *)
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜w = true -> bmapstart ∈ Sb''⌝ -∗
        ⌜crb = true -> w = false⌝ -∗
        (* THE BUDGET CLAUSE, which this post used to be missing outright and
           without which [wp_iput_gen]'s own post cannot be stated.  The figure
           is [SpecIput.ip_spend_w]'s: the bitmap unit if this run logged it,
           plus ITRUNC's tail flush unless one of the two credits paid for it.
           The off-lock flush is NOT in it -- see the [true] handed to
           [ip_free_offlock] below. *)
        ⌜((u - ip_spend_w w cru crz)%nat <= n'')%nat /\ (n'' <= u)%nat⌝ -∗
        log_opS γ n'' Sb'' -∗
        iref_slot -∗
        (* RULING G's RETURN LEG (iclaim-ledger.md §6′): the regime the caller
           lent at the +0x50 mint, handed back by the +0xba deposit. *)
        (ireg_open ∨ ireg_boot) -∗
        (* frame ra/s0/s1 slots, still saved, for the epilogue *)
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) ↦₈[KT1] vra -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) ↦₈[KT1] vs0 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) ↦₈[KT1] vs1 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) ↦₈[KT1] vs2 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) ↦₈[KT1] vs3 -∗
        add_vec sp0 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) ↦₈[KT1] vs4 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ip pj HK HKit Hk Hu2 Hcrb Hgeom Hsize Hbmpos Hbmcov Hbmlog Histpos Hicov Hilog
           Hnib Hdtnz Hnl0 Hdnwf Hbmwf Hbelow Hdlen Hadr HMwf Hciwf HMk1 Hj Hgl
           Hsp0 Ha0 Hs1v Hs2v Hs3v Hs4v Hlkbelow Hitnotin.
    iIntros "Hcg Hcnt Hpay Hextc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx
             #Hitlk #Hitinv #Hesc Htok Hhalf Hiauth Hipool Hpool %Hcik Hrtok Hgid Hwand
             #Hslk Hpayl Hlvh Hvb #Hireg Hpre Hrcpt Hmirt Hselo Hru Hbms Hins Hbm Hppid
             #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots Hnlz #Hvlb Hcrd Hop
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
            with "Hitinv Hbody Hhalf Hfrg Hlvqf Hlvh Hgid Hvb Hpayl")
      as "(Hhalf & Hfrg & Hlvq2 & Hlvh & Hgid & Hvb & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
    (* ---- THE 586 SITE.  [ic_open_held] hands [i_inum] back WHOLE; itrunc
       keeps one half ([Hinh], with [Hidv]) and the SURPLUS half -- which this
       body used to drop on the floor -- is fed to the entry's re-assembly
       wand together with the borrowed [ic_id] and the FROZEN PARK. ---- *)
    iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hnsurp]".
    iDestruct "Hlvq2" as (gr) "Hlvr".
    iDestruct (live_gen_agree with "Hlvr Hlvh") as %->.
    (* ================================================================
       THE +0x62 RE-PARK (iclaim-ledger.md §3.16, RULING A⁗).  The itable
       lock is about to go at +0x66, so this is the LAST instant at which
       [islot2] is reachable -- and it is where the mint's mirror half and
       the dying reference's two live slices (its own [q], now at the fresh
       generation, and the escrow arm's [1/2]) go into the FROZEN PARK.

       They stay there for the whole lock-free span +0x66..+0x82, which is
       exactly the span in which a foreign [idup] can run: it takes this
       lock, finds the park, and its own share is then one slice past the
       slot's unit ([IcacheInv.live_whole_share_absurd]).  That is
       [ProofIdup]'s OPEN(2.6b), closed by placement rather than by a
       licence -- and it is also why NOTHING is deposited into the escrow's
       OUT arm here: the freer keeps the count fragment and the identity in
       its own hand and parks only the RECEIPT.
       ================================================================ *)
    iMod (frz_slot_freeze (⊤ ∖ ↑icEscN) Mt k q 1%positive
            ltac:(solve_ndisj) HMk1 with "Hitinv Hhalf [Hlvr] [Hlvh] Hselo")
      as "(Hhalf & Hselp & Hsele)";
      [iExists ga'; iExact "Hlvr" | iExists ga'; iExact "Hlvh" |].
    iAssert (frz_park k (bv_unsigned inum) q) with "[Hmirt Hselp]" as "Hpark".
    { iApply (frz_park_intro_on with "Hmirt Hselp"). }
    iDestruct ("Hwand" with "Hnsurp Hgid Hpark") as "[Hslots Hrident]".
    (* ================================================================
       THE +0x5e WINDOW EXIT, at [IcacheEscrow.ic_out]'s SECOND
       ALTERNATIVE (iclaim-ledger.md IVd).

       What goes into the escrow is a reference MINUS its two live slices --
       they are in the frozen park built two lines above and must STAY there
       for the whole lock-free span -- i.e. the COUNT FRAGMENT and the
       IDENTITY slice, plus the RECEIPT the mint produced.  The descriptor
       is [DepFrz q dev inum]: it says what the arm holds, names the
       fraction the +0x70 park will want back, and refutes this arm at every
       ordinary parker and borrower (they all name a descriptor with a
       generation).

       WHAT STAYS IN THIS THREAD'S HAND is exactly what the next four
       instructions need: the ½ dev and inum cells and the payload, because
       [itrunc] reads ip->dev for its [bread] and writes ip->addrs/ip->size;
       and the WHOLE valid cell, because the +0x70 store is this thread's
       own, not an atomic update on the escrow.  OUT is the only escrow arm
       that keeps no cells, which is why this span lives here and not at
       [ic_parked]'s frozen alternative -- that one is entered at the +0x70
       park, where the ordinary path enters it too.
       ================================================================ *)
    iDestruct "Hvldx" as (w0) "Hva".
    iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
    iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
    iMod (ic_dep_checkout cn k (DepFrz q dev inum) with "Hictok")
      as "[Hdep Hdepa]".
    iMod ("Hclose" with "[Hdepa Hfrg Hrident Hrcpt Hsele Hmt Hgida]") as "_".
    { iApply bi.later_intro.
      iApply (ic_close_out_frz cn γfs γi cov logstart k dev inum q
                with "Hdepa Hfrg Hrident Hrcpt Hsele Hmt Hgida"). }
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
    iApply (Release.wp_release_sconf KT1 gtl itable_lock "itable"%string
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
    (* ---- THE GROUP CREDIT, CASHED (fs-log.md §G.18/§G.20) ----
       itrunc's tail-flush credit is a RESOURCE at a NAMED birth epoch, and
       iput is one link of the thread that carries it.  iput's OWN claim is the
       pure own-set one; a [crz] caller one tier up presents a GROUP witness
       instead, which is the point of the tier -- and cashing it HERE, at the
       record the caller's +0x44 test found with [nlink = 0], is what makes
       [ip_spend_w]'s [if cru || crz then 0 else 1] the truth. *)
    iDestruct (log_opSe_pos with "Hop") as %He0pos.
    iApply fupd_wp.
    iAssert (|={⊤}=> dinode_at γi inum dn ∗
                     log_credit γ (cru || crz) Sb e0 (IBLOCK inum inodestart))%I
      with "[Hdat Hnlz Hcrd]" as ">[Hdat #Hcrui]".
    { destruct crz.
      - (* THE GROUP ARM: the observation was taken at [e0] inside THIS op, the
           record has [nlink = 0], and genesis-positivity comes off the
           reservation itself -- so the region returns a witness at an epoch no
           earlier than the op's birth, i.e. [log_credit]'s right disjunct. *)
        iEval (cbn beta iota) in "Hnlz".
        iDestruct "Hnlz" as "(#Hobs & %Hgeq & %Histeq)".
        iMod (InodeRegion.ireg_obs_use ⊤ γi γfs inodestart nib inum dn γ e0
                ltac:(solve_ndisj) Hnib Hgeq Hnl0 He0pos
                with "Hireg Hdat Hobs") as "[Hdat #Hwit]".
        iDestruct "Hwit" as (e) "[%Hle #Hlog]".
        iModIntro. iFrame "Hdat". rewrite Histeq.
        iApply (log_credit_group γ (cru || true) Sb e0 e (IBLOCK inum icfg_ist)
                  Hle with "Hlog").
      - (* the OWN-SET arm: the caller's own credit, unchanged *)
        iModIntro. iFrame "Hdat". rewrite orb_false_r. iExact "Hcrd". }
    iModIntro.
    (* ===== itrunc ===== *)
    iApply (IT.wp_itrunc_gen γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart bmapstart inodestart nib size dev used
              (ip : mword 64) inum dn dn bm data2 uit Sb crb (cru || crz)%bool e0
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
                    Hdevi Hdgeom Hdlock Hbslots Hcrui [Hop]").
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
    (* ===================================================================
       +0x70 sw zero,64(s1) : ip->valid = 0.

       SINCE IVd THIS IS THIS THREAD'S OWN CELL, and the store opens nothing:
       from the +0x5e window exit the escrow sits on [IcacheEscrow.ic_out]'s
       FROZEN alternative, which -- like every OUT arm -- owns NO cells at
       all, so the whole valid word has been in this thread's hand across
       [itrunc].  The atomic-update form is kept only because that is the
       [sw] rule this pin uses; its update opens no invariant.

       THE PARK FOLLOWS THE STORE, three lines below: [ic_swap_park_frz]
       moves OUT's frozen alternative to [ic_parked]'s (the RECEIPT never
       leaves the escrow), gives the cells back, rejoins the two descriptor
       halves into the [ic_tok] releasesleep wants at +0x76, and returns the
       count fragment and the identity slice AT THE [q] the window exit named
       -- the eviction at +0x82/+0x8a reads the map off the fragment
       ([IcacheInv.iref_frag_lookup]) and rebuilds [iref_tok k q].

       WHAT IS *NOT* HERE ANY MORE, and it is B2's dissolution: the old body
       re-parked the whole payload at [ic_swap_park_arm], handing the record
       back into the escrow -- which is exactly why the +0x8a eviction then
       had one bundle and two consumers.  It does not: [inode_raw], the
       block resources and [dinode_at (di_trunc dn)] stay in this thread's
       hand, named and un-existentialised, all the way to the +0xba deposit.
       =================================================================== *)
    iDestruct (sie_cap_gpr_x0 mfi (K - 6)%nat eb pj Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0u Hcg]".
    assert (Hpa70 : add_vec (rget mfi Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne mfi Rs1 ltac:(nz)) Hmfis1. reflexivity. }
    assert (Hsv70 : trunc32 (rget mfi Rz) = valid_word false).
    { rewrite (rget_ne mfi Rz ltac:(nz)) Hx0u. exact ip_trunc32_zero. }
    iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.iput + 0x70)) Rz Rs1
              (mword_of_int 64 : mword 12) mfi (K - 6)%nat
              (i_valid (ientry k) ↦₄ valid_word false)%I
              (⊤ ∖ ↑minstretN) eb ltac:(solve_ndisj)
              with "Hcg Hpc Hi70 [Hvld]").
    { rewrite Hpa70 Hsv70.
      iModIntro. iExists (valid_word true). iFrame "Hvld". iIntros "Hvld".
      iModIntro. iExact "Hvld". }
    iIntros (CIDsw Hssw) "Hcg Hpc Hvld".
    (* ---- THE PARK: OUT's frozen alternative -> [ic_parked]'s (IVd) ---- *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    iMod (ic_swap_park_frz cn γfs γi cov logstart k false q dev inum
            with "Hbody Hdep Hidv Hinh Hvld")
      as "(Hbody & Hictok & Hfrg & Hrident)".
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
    iModIntro.
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.iput + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
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
    (* the sleeplock's share comes home, but NOT the live slice: that one is
       in [islot2]'s frozen park until +0x82.  So what this thread holds
       across the lock-free span is the REDUCED reference -- the count
       fragment, the identity slice and the sleeplock share -- and the map
       lookup at the re-acquire reads the fragment alone
       ([IcacheInv.iref_frag_lookup]). *)
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
    iApply (Acquire.wp_acquire_sconf KT1 gtl "itable"%string
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
    (* the map is read off the BARE COUNT FRAGMENT (A⁗, §3.16): the live
       slice this reference used to carry is in [islot2]'s frozen park, so
       there is no [iref_tok] here to look it up with -- and there never
       needed to be ([IcacheInv.iref_frag_lookup]). *)
    iDestruct (iref_frag_lookup with "Hhalf Hfrg")
      as %(qt2 & cnt2 & HMk2 & Hqt1 & Hone2 & Hone2').
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
    (* ===================================================================
       B1 IS PAID HERE (iclaim-ledger.md §3.16, and it is the first of this
       file's two admits gone).

       IVa's wall: the reordered iput released itable.lock at +0x66 and
       re-acquired it at +0x82, so the REF-1 fact the caller supplied is about
       the OLD map, and the live arm's [cnt2] is about the new one.  Nothing
       in the held resources forced [cnt2 = 1]: an iget in the window can
       split a fresh reference out of the table's retained share, and
       design/fs-icache.md §17.6.1 CERTIFIES that trace machine-reachable, so
       no invariant may forbid it.

       A⁗'s answer is not to forbid the trace but to make the WINDOW carry a
       pin the whole way: the mint at +0x50 put this inum's f column at
       [FrzPre], the region's own [ireg_frz_ok] says a [FrzPre] column has
       in-core count ONE, and this thread has held [ifreeze_pre] since.  So
       [cnt2 = 1] is a REGION FACT, read in one open
       ([IcacheInv.icnt_freeze_forces_one]) -- and the foreign iget the trace
       describes is refuted where it belongs, at its OWN up-count, by the
       frozen park this window left in [islot2] (OPEN(2.6b)).
       =================================================================== *)
    (* ---- the slot's identity and its live arm, popped from the table ---- *)
    assert (Hcik2ex : exists di : mword 32 * mword 32, ci2 !! k = Some di).
    { destruct Hciwf2 as [Hdom2 _].
      assert (Hin : k ∈ dom ci2)
        by (rewrite Hdom2; apply elem_of_dom; rewrite HMk2; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcik2ex as [[cdev2 cinum2] Hcik2].
    iDestruct (islots2_acc_upd cn Mt2 ci2 k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk2 Hcik2) in "Hslot".
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid & Hicnt & Hpark)".
    iDestruct (ip_rest_sum with "Hrest") as %[qr2 Hsum2].
    iAssert (⌜cdev2 = dev /\ cinum2 = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - qt2)%Qp as [q'|] eqn:Et2; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    iApply fupd_wp.
    iMod (icnt_freeze_forces_one ⊤ γi γfs inodestart nib inum (Pos.to_nat cnt2)
            ltac:(solve_ndisj) Hnib with "Hireg Hpre Hicnt")
      as "(%Hc1 & Hpre & Hicnt)".
    assert (Hcnt1 : cnt2 = 1%positive).
    { pose proof (Pos2Nat.is_pos cnt2) as Hp. lia. }
    assert (Hpos1 : Pos.to_nat 1 = 1%nat) by reflexivity.
    iEval (rewrite Hcnt1 Hpos1) in "Hicnt".
    (* ---- and the FROZEN PARK comes home: the mint's mirror half and the two
       live slices, which together with the invariant's retained (1/2 - q) are
       the whole unit the last close surrenders (ZZProbeFrz P5) ---- *)
    iMod (frz_park_pre_reclaim ⊤ γi γfs inodestart nib inum k qt2
            ltac:(solve_ndisj) Hnib with "Hireg Hpre Hpark")
      as "(Hpre & Hmirt & Hselp)".
    iModIntro.
    pose proof (Hone2 Hcnt1) as Hqq.
    rewrite Hcnt1 in HMk2, Hstv2.
    rewrite <- Hqq in HMk2, Hsum2.
    assert (Hqhalf2 : (q ≤ 1/2)%Qp) by (rewrite Hsum2; apply Qp.le_add_l).
    (* ---- the eviction runs BEFORE the store ---- *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    iMod (ic_open_auth_frz cn γfs γi cov logstart k (⊤ ∖ ↑icEscN)
            Mt2 q q dev inum ltac:(solve_ndisj) Hk HMk2
            with "Hitinv Hbody Hhalf Hfrg Hselp Hrident")
      as "(Hhalf & Hfrg & Hselp & Hrident & Harm & _)".
    iDestruct "Harm" as (vv ga2) "(Hidv & Hinv2 & Hvld & Harmt & Hmt & Hgida)".
    (* THE ARM IS ON A⁗'s FROZEN ALTERNATIVE, decided by the [ifreeze_pre]
       this thread has held since the mint at +0x50: what comes out is the
       RECEIPT and nothing else, and the receipt goes home three lines below,
       inside the last close's own phase step. *)
    iDestruct (ic_payload_arm_decide_frz with "Hpre Harmt")
      as "(Hpre & Hrcpt & Hsele)".
    iDestruct (islot_rest_join k q dev inum Hqhalf2 with "Hrident [Hrest]")
      as "[Hdh Hinh]".
    (* the slot's retained share is stated at the map's [qt2], which REF-1 has
       just identified with this reference's own [q] ([Hqq]) *)
    { rewrite /islot_rest. iExists dev, inum. rewrite Hqq. iExact "Hrest". }
    (* B2's DISSOLUTION, cashed: the payload never went back into the escrow
       at the +0x70 park, so the EMPTY arm's raw cells are peeled off the
       bundle THIS THREAD is still carrying -- itrunc handed [inode_meta] at
       [di_trunc dn] and [inode_map] at [bm_empty] straight back -- and the
       RECORD stays here, named, all the way to +0xa8. *)
    iDestruct "Hmap" as "[Haddrs Hind]".
    iAssert (inode_raw (ientry k)) with "[Hmeta Haddrs]" as "Hraw".
    { rewrite /inode_raw. iSplitL "Hmeta".
      - iExists (di_trunc dn). iExact "Hmeta".
      - iExists (bm_cells bm_empty). iSplitR;
          [iPureIntro; rewrite /bm_cells length_app
             (blkmap_wf_dir_len cov logstart bm_empty (bm_empty_wf cov logstart));
           reflexivity |].
        iExact "Haddrs". }
    iMod (ic_close_to_empty_frz cn γfs γi cov logstart k vv dev inum
            with "Hgida Hgid Hidv Hdh Hinv2 Hvld Hraw Hmt Hrcpt")
      as "(Hbody & Hgidf & Hrcpt)".
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
              (itable_half (delete k Mt2) ∗ isl_slot (delete k Mt2) k ∗
               ifreeze_post (bv_unsigned inum) ∗
               icnt_half (bv_unsigned inum) 0%nat ∗
               frzm_h (bv_unsigned inum) false)%I
              (⊤ ∖ ↑minstretN ∖ ↑icacheN ∖ ↑iregN) false ltac:(solve_ndisj)
              with "Hcg Hpc Hi8a [Hhalf Hfrg Hrslh Hselp Hsele Hisl Hru Hpre Hicnt Hrcpt Hmirt]").
    { rewrite Hpa8a Hstv2.
      replace (Z.pos 1 - 1)%Z with 0%Z by lia.
      (* THE LAST CLOSE IS THE PHASE STEP (A⁗): [FrzPre -> FrzPost], the
         receipt back to the region, the mirror's lock half DOWN, and the
         uncached ledger pair out -- the three outputs the pool bundle and the
         off-lock deposit are built from. *)
      (* RULING R-e: the two quarters of the selector -- the park's, home at
         +0x82, and the escrow tail's, handed back by the eviction just above
         -- rejoin here, and they are the WHOLE payment for the retirement.
         No live slice changes hands: the unit never left [live_slot]. *)
      iDestruct (frzsel_quarters k true with "Hselp Hsele") as "Hsel12".
      iMod (iref_close_last_freeze_store_au (⊤ ∖ ↑minstretN) γi γfs inodestart
              nib Mt2 k inum q bfl
              ltac:(solve_ndisj) ltac:(solve_ndisj) Hnib HMk2
              with "Hitinv Hireg Hhalf Hfrg Hrslh Hsel12 Hisl Hru Hpre Hicnt Hrcpt Hmirt")
        as "[Hcell Hback2]".
      iModIntro. iExists (iref_word Mt2 k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback2" with "Hcell") as "(Hhalf & Hisl & Hfzpost & Hcnt0 & Hfzp)".
      iModIntro. iFrame. }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc (Hhalf & Hisl & Hfzpost & Hcnt0 & Hfzp)".
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
    iEval (rewrite Hcnt1 Hp1) in "Hiu".
    (* ===================================================================
       THE ONE OPEN DESIGN DEBT OF THE REORDER (see the blocker note at the
       head of the file).  The eviction hands back exactly ONE
       [ipool_shape], and the reordered free path needs TWO things out of
       it at once:

         (i)  the itable's free pool must show [region_inums nib ∖
              ci_inums (delete k ci2)] -- one entry MORE than before -- at
              the +0x94 release, and

         (ii) [ip_free_offlock] needs the record itself,
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
    (* ---- THE RECORD, and only the record: B2's admit is HALF gone.  The
       bundle never went back into the escrow, so [dn2] is [di_trunc dn]
       LITERALLY -- no existential, no lost [nlink = 0]. ---- *)
    set (dn2 := di_trunc dn).
    assert (Hdn2wf : dinode_wf dn2) by (unfold dn2; apply di_trunc_wf).
    assert (Hdn2nl : bv_unsigned (di_nlink dn2) = 0) by (unfold dn2; exact Hnl0).
    iRename "Hdat" into "Hdn2".
    (* ---- ...AND THE POOL ENTRY, WHICH IS PARKED HERE AND NOT BY THE TAIL.
       This is the whole of what was left of B2, and the REORDER decides it:
       the itable lock goes at +0x94, BEFORE the +0xba deposit, and
       [ic_ci_wf]'s [dom ci = dom M] makes the evicted inum uncached AT THAT
       RELEASE -- so its bundle must be in the itable's free pool by then.
       The last close's three outputs are exactly the bundle's: the freeze
       token mints the escrow the deposit will fill, and the count and mirror
       halves ride beside it on the AWAIT arm.  The DEPOSIT ticket does not go
       into the pool: it travels with the record to +0xa8. ---- *)
    iApply fupd_wp.
    iMod (escA_alloc ⊤ γi (bv_unsigned inum) with "Hfzpost")
      as (ge gr gd) "(#Hescr & Htkr & Htkd)".
    iModIntro.
    iDestruct (ipool_shape_await γfs γi cov logstart inum ge gr gd
                 with "Hcnt0 Hfzp Hescr Htkr") as "Hgap".
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
    iApply (Release.wp_release_sconf KT1 gtl itable_lock "itable"%string
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
    (* THE WALK-TIER IDIOM (iclaim-ledger.md §3.14): the ACCESS PATH is KT1
       (sp-migration phase D) while the superblock cell stays at
       [curktier_default]/KT0, exactly as the identity cells do. *)
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (KernelSyms.iput + 0xa0)) Ra1 Ra1
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
      unfold it_bm, it_iu in Hlo. destruct wbm, cru, crz; cbn in Hlo |- *; lia. }
    assert (Hu'le : (u' <= u)%nat).
    { destruct Hbud as [_ Hhi]. rewrite Hun in Hhi.
      unfold it_iu in Hhi. destruct cru, crz; cbn in Hhi |- *; lia. }
    (* THE BUDGET, AS THIS LEMMA'S POST STATES IT.  itrunc's lower bound is
       exactly [ip_spend_w]'s figure once the group credit has bought its tail
       flush, and the off-lock flush below adds nothing -- it runs credited. *)
    assert (Hbudlo : (u - ip_spend_w wbm cru crz <= u')%nat).
    { destruct Hbud as [Hlo _]. rewrite Hun in Hlo.
      unfold it_bm, it_iu in Hlo. unfold ip_spend_w, ip_bm.
      destruct wbm, cru, crz; cbn in Hlo |- *; lia. }
    (* the op count, in the [S _] form the off-lock flush's contract wants *)
    destruct u' as [| uoff]; [exfalso; lia |].
    iDestruct (log_opS_named with "Hop") as (e0') "Hop".
    iPoseProof (log_opSe_lb with "Hop") as "#Hvlb2".
    (* THE OFF-LOCK FLUSH IS CREDITED, UNCONDITIONALLY (fs-log.md §G.22, and
       [SpecIput]'s own note: "itrunc's post hands out [IBLOCK inum inodestart
       ∈ Sb'] determinately, so iput's [ip->type = 0] flush runs credited for
       free").  That is what makes [ip_spend_w] -- which counts the bitmap unit
       and itrunc's tail flush and NOT this one -- the honest figure, and
       without it this lemma's budget clause could not close. *)
    iAssert (log_credit γ true Sb' e0' (IBLOCK inum inodestart)) as "#Hcrd2".
    { iApply log_credit_own. intros _. exact Hibin'. }
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
    (* ===== +0xa8 .. j 0x30 : ip_free_offlock ===== *)
    iApply (ip_free_offlock γs j γl γu γd γk pd pav pu bn γ γfs γi
              cov logstart inodestart nib dev inum dn2 ge gr gd
              uoff Sb' true e0' e0' pidv dq dqs
              sp0 vra vs0 vs1 vs2 vs3 vs4 P5 (K - 6)%nat eb eb lks
              ltac:(lia) ltac:(lia) ltac:(lia)
              Hgeom Histpos Hicov Hilog Hnib Hdn2wf Hdn2nl Hj Hgl
              ltac:(exact (eq_sym HP5sp)) HP5a0 HP5a1 HP5s2 Hlkbelow
              with "Hcg Hcnt Hextc Hclm Htext Hkd Hpc Hpenv Hbio Hlctx Hireg
                    Hdn2 Hescr Htkd Hppid Hprocs Hdevi Hdgeom Hdlock Hins Hbs2
                    Hvlb2 Hcrd2 Hop Hra Hs0f Hs1f Hs2f Hs3f Hs4f [-]").
    (* ---- the continuation: offlock's post at 0x30, re-shaped into ours ---- *)
    iIntros (CIDf Hstf).
    iIntros (mf) "%Hthr Hcg Hcnt Hextc Hclm Hpc Hppid Hins Hbs2 Hop2 Hwit Hgreg
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
    assert (Hthrm : ipo_thr m mf).
    { intros c Hcs N1 N2 N3 N4 N5.
      rewrite (Hthr5 c Hcs N1 N2 N3 N4 N5). exact (HP5m c Hcs). }
    iDestruct (bslots_op bn 1 2 with "[Hbs1 Hbs2]") as "Hbslots";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    iEval (rewrite (_ : (1 + 2)%nat = 3%nat); [| reflexivity]) in "Hbslots".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CIDf)
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iSpecialize ("Hcont" $! CIDf with "[]"); [iPureIntro; wp_next_chain |].
    iApply ("Hcont" $! mf (S uoff)
                       (used ∖ bm_blocks bm) (Sb' ∪ {[IBLOCK inum inodestart]}) wbm
              with "[%] Hcg Hcnt Hextc Hclm Hpc Hppid Hbms Hins [%] Hbm Hbslots
                    [%] [%] [%] [%] Hop2 Hiu Hgreg Hra Hs0f Hs1f Hs2f Hs3f Hs4f").
    { split_and!; [exact Hthrm | exact Hmfsp | exact Hmfs2 | exact Hmfs3 | exact Hmfs4]. }
    { exact (fl_diff_sub used (bm_blocks bm)). }
    { exact (union_subseteq_l' _ _ _ Hsub'). }
    { intros Hw. apply elem_of_union_l. exact (Hwbm' Hw). }
    { exact Hcrbw'. }
    { split; [exact Hbudlo | exact Hu'le]. }
  Qed.

  (* ---- (c) the ENTRY CHECK, +0x3a .. +0x58, with its two exits ---- *)



  (* ---- pure helpers, all VERBATIM from ProofIput (which is red at lane
     HEAD and cannot be imported); at integration they collapse back. ---- *)

  (* ProofIput.ip_sext64_16_inj / ip_nlink_zero (:170-186): the [c.bnez] at
     0x4e falls through exactly on a zero nlink halfword. *)
  Lemma fe_sext64_16_inj (a c : mword 16) :
    (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
  Proof. intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity. Qed.

  Lemma fe_nlink_zero (w : mword 16) :
    neq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false ->
    bv_unsigned w = 0.
  Proof.
    intro H. unfold neq_vec in H. apply negb_false_iff in H.
    apply eq_vec_true_iff in H.
    assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hz in H. apply fe_sext64_16_inj in H.
    rewrite H. vm_compute. reflexivity.
  Qed.

  (* ProofIput.ip_valid_beqz (:270) *)
  Lemma fe_valid_beqz (v : bool) :
    eq_vec (sign_extend' 64 (valid_word v) : mword 64) (zero_reg : mword 64) = negb v.
  Proof. exact (valid_word_eqz v). Qed.

  (* ProofIput.ip_rest_sum / IputFreeLockedDev.ip_rest_sum *)
  Lemma fe_rest_sum (kk : nat) (qt : Qp) (dv nu : mword 32) :
    islot_rest_at kk qt dv nu -∗ ⌜∃ qr : Qp, (1/2)%Qp = (qt + qr)%Qp⌝.
  Proof.
    rewrite /islot_rest_at. destruct (1/2 - qt)%Qp as [q'|] eqn:Et.
    - iIntros "_". iPureIntro. exists q'. by apply Qp.sub_Some in Et.
    - iIntros "[]".
  Qed.

  (* THE HEADER'S FLAGGED SEAM, RESOLVED: [dinode_wf] IS extractable from the
     payload -- [inode_ok]'s [di_addrs dn = bm_cells bm] plus [blkmap_wf]'s
     direct-cell count.  Same derivation as IcacheEscrow.v:1519. *)
  Lemma fe_dinode_wf (cov : gset Z) (logstart : Z) (dn : dinode) (bm : blkmap) :
    blkmap_wf cov logstart bm -> di_addrs dn = bm_cells bm -> dinode_wf dn.
  Proof.
    intros Hwf Hda. rewrite /dinode_wf Hda /bm_cells length_app.
    rewrite (blkmap_wf_dir_len _ _ _ Hwf). reflexivity.
  Qed.

  (* ==========================================================================
     ip_free_entry.  Entry at iput+0x3a: itable.lock HELD, ref==1 known
     (Mt !! k = Some (q, 1)), NOTHING checked out; a5 still carries the ref
     word from the +0x18 load.  [m] is iput's ORIGINAL entry regfile (the
     frame slots and iput_regs are stated against it, as ip_tail does); [M] is
     the regfile HERE.  Exits: see the header.
     ========================================================================== *)
  Lemma ip_free_entry `{GEN : GenId} `{CID0 : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl gil gisl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (k : nat) (q : Qp) (inum : mword 32)
      (Mt : gmap nat (Qp * positive)) (ci : gmap nat (mword 32 * mword 32))
      (u : nat) (Sb : gset Z) (crb cru : bool) (e0 v : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (vg4 vg5 vg6 : mword 64)
      (m M : regfile) (K : nat) (eb : bool) (lks : gset string) :
    let ip := ientry k in
    let pj := proc_addr j in
    let sp0 := (m !!! Regidx csp_rs1 : mword 64) in
    let spd := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))) in
    (K_iput <= K)%nat ->
    (* SPLICE: itrunc's cone reserve => the final contract carries K >= 74. *)
    (K_itrunc <= K - 6)%nat ->
    (k < NINODE)%nat ->
    (* RE-SYNCED to [ip_free_locked]'s post-60cc0136b1 premise list: [3] (not
       [2]) is what makes itrunc's post leave [1 <= u'], i.e. an [S _] for the
       off-lock flush's [log_opSe γ (S u) Sb e0]; the bound is its companion. *)
    (3 <= u)%nat ->
    (* the vacuous [Z.of_nat u + 2 < 2^31] is GONE (see [ip_free_locked]) *)
    (crb = true -> bmapstart ∈ Sb) ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart -> bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    icM_wf Mt ->
    ic_ci_wf Mt ci nib dev ->
    (* FREE-PATH GUARD: the +0x1c branch was TAKEN -- this is the last ref. *)
    Mt !! k = Some (q, 1%positive) ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    iput_regs m M spd k ->
    M !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k) ->
    locks_below lks "log" ->
    "itable" ∉ lks ->
    sie_cap_gpr KT1 M (trap_res eb + (K - 6))%nat false pj -∗
    cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
    arm_pay KT1 0 eb pj -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x3a) : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    is_lock gtl itable_lock "itable"%string (itable_res2 cn γfs γi cov logstart nib dev) -∗
    itable_inv -∗
    ic_escrow cn γfs γi cov logstart k -∗
    locked gtl cpu_id -∗
    itable_half Mt -∗
    iref_slots_auth -∗
    isl_pool Mt -∗
    ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
    ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
    IcacheRef.inode_ref k q dev inum -∗
    is_sleeplock_gen gil gisl (i_lock ip) "inode"%string (ic_tok cn k)
                     (slh_tok (icfg_isl k)) -∗
    ireg_inv γi γfs inodestart nib -∗
    (* THE SEALED REGIME (fs-fragments.md §7.12, §2.3's boot-shelter clause),
       new at A⁗ and forced by the MINT: [InodeRegion.ireg_freeze_au] takes
       [ireg_open ∨ ireg_boot] because a RUNTIME freezer must exhibit the seal
       that ireclaim's boot freeze exhibits with its exclusive token instead.
       Persistent, so it costs the caller nothing but having it; RULING B
       fires the seal once, after fsinit and before [kexec("/init")], so every
       runtime iput has it.

       RULING G (iclaim-ledger.md §6′): BORROWED, not persistent.  ireclaim
       freezes at BOOT, where the seal has not been fired and what it carries
       instead is the exclusive [ireg_boot] -- so a contract that demanded the
       left arm outright would shut the boot thread out of iput entirely.  The
       disjunction goes in, the mint spends it, and the off-lock deposit hands
       it back out of the slot's own boot-shelter clause
       ([EscrowDeposit.ireg_free_deposit_au]'s second fupd); on the two Exit-A
       arms, which never reach the mint, it comes straight back below. *)
    (ireg_open ∨ ireg_boot) -∗
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
    (* the 6-slot frame: ra/s0/s1 already saved by the prologue; 4/5/6 are
       the s2/s3/s4 slots, still holding prologue garbage *)
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈[KT1] vg4 -∗
    pa_stk sp0 5 ↦₈[KT1] vg5 -∗
    pa_stk sp0 6 ↦₈[KT1] vg6 -∗
    (* ===== THE TWO EXITS, JOINED BY [∧] AND NOT BY [∗] ==================
       They are ALTERNATIVES -- the walk reaches exactly one of them -- and
       the caller's own post (and the reference's provenance unit) is a single
       spatial resource that BOTH have to end in.  Under [∗] the caller would
       have to split it in two and could not; under [∧] it proves each arm
       from the whole context, which is exactly the truth of the matter.  The
       body eliminates whichever side its branch reached and drops the other.
       ==================================================================== *)
    ((* ===== EXIT A: pc +0x20, the ip_tail seam (valid==0 OR nlink!=0);
       the bundle goes back UNTOUCHED, the payload is re-parked ===== *)
     (∀ (M' : regfile) (vg4' vg5' vg6' : mword 64),
       ⌜iput_regs m M' spd k⌝ -∗
       ⌜M' !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k)⌝ -∗
       sie_cap_gpr KT1 M' (trap_res eb + (K - 6))%nat false pj -∗
       cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
       arm_pay KT1 0 eb pj -∗
       trap_csrs_ext KT1 eb -∗
       cpu_claim_ext eb pj -∗
       pc_is (mword_of_int (KernelSyms.iput + 0x20) : mword 64) -∗
       locked gtl cpu_id -∗
       itable_half Mt -∗
       iref_slots_auth -∗
       isl_pool Mt -∗
       ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
       IcacheRef.inode_ref k q dev inum -∗
       (* RULING G: both Exit-A arms turn back BEFORE the +0x50 mint, so the
          regime the caller lent has not been spent and comes straight back. *)
       (ireg_open ∨ ireg_boot) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslots bn 3 -∗
       log_epoch_lb γ v -∗
       log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
       log_opSe γ u Sb e0 -∗
       pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx Rra) -∗
       pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx Rs0) -∗
       pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx Rs1) -∗
       pa_stk sp0 4 ↦₈[KT1] vg4' -∗
       pa_stk sp0 5 ↦₈[KT1] vg5' -∗
       pa_stk sp0 6 ↦₈[KT1] vg6' -∗
       WP (Loop : expr riscv_lang))
     ∧
     (* ===== EXIT B: pc +0x5a, byte-compatible with ip_free_locked's ENTRY
       (IputFreeLockedDev.v:247).  dn/bm/data/g1 are the body's discoveries
       from opening the payload; the pure block is FreeLocked's dn-dependent
       premise list verbatim ===== *)
    (∀ (M5 : regfile) (g1 : gname) (dn : dinode) (bm : blkmap)
       (data : nat -> list (bv 8)),
       ⌜bv_unsigned (di_type dn) <> 0⌝ -∗
       ⌜bv_unsigned (di_nlink dn) = 0⌝ -∗
       ⌜dinode_wf dn⌝ -∗
       ⌜blkmap_wf cov logstart bm⌝ -∗
       ⌜forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE⌝ -∗
       ⌜di_addrs dn = bm_cells bm⌝ -∗
       ⌜spd = M5 !!! Regidx csp_rs1⌝ -∗
       ⌜M5 !!! Regidx Ra0 = (i_lock ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs1 = (ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs3 = (i_lock ip : mword 64)⌝ -∗
       ⌜M5 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64)⌝ -∗
       (* s5..s11 untouched: what the integration's end-to-end callee_saved
          chain needs beyond FreeLocked's own callee_saved *)
       ⌜M5 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
        M5 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
        M5 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
        M5 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
        M5 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
        M5 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
        M5 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)⌝ -∗
       sie_cap_gpr KT1 M5 (trap_res eb + (K - 6))%nat false pj -∗
       cpu_own 1 eb pj false ({["itable"]} ∪ lks) -∗
       arm_pay KT1 0 eb pj -∗
       trap_csrs_ext KT1 eb -∗
       cpu_claim_ext eb pj -∗
       pc_is (mword_of_int (KernelSyms.iput + 0x5a) : mword 64) -∗
       locked gtl cpu_id -∗
       itable_half Mt -∗
       iref_slots_auth -∗
       isl_pool Mt -∗
       ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
       (* ================================================================
          THE WINDOW'S i_inum SPLIT -- the ONE place this Exit B is NOT
          byte-identical to [ip_free_locked]'s entry, and it is FORCED, not
          a proof-engineering choice.  See the header's EXIT B note.

          At 0x5a the payload is OUT, so the escrow is on its HELD arm, and
          [IcacheEscrow.ic_held] owns [i_inum] AT DFRAC 1 by design -- "both
          [ic_mid_arm] and [ic_held] are refuted by a FULL [i_inum] cell"
          (IcacheEscrow.v, the §17.3 (A) note above [ic_parked]).  That whole
          cell is the arm's own 1/2 PLUS the closer's [q] PLUS the table's
          [1/2 - q], i.e. exactly the two shares that live inside
          [inode_ref k q dev inum] and inside [islot2 cn Mt ci k]'s
          [islot_rest_at].  So NEITHER of those two resources exists here:
          each is short precisely its [i_inum] share, and no other escrow arm
          accepts "payload out, i_inum at a half" (PARKED holds the payload,
          MID holds [i_inum] whole too, OUT needs a deposit the sleeplock has
          not minted yet, EMPTY needs a dead slot).

          What is handed instead is the pieces that DO exist plus the
          RE-ASSEMBLY WAND.  [ip_free_locked] re-opens the HELD arm at its
          own 0x76 [ic_open_held] regardless, and that returns [i_inum ↦₄
          inum] WHOLE -- whose surplus half its body TODAY DROPS on the floor
          (IputFreeLockedDev.v:586, [iDestruct (word4_pointsto_half_split
          with "Hnfull") as "[Hinh _]"]).  Feeding that dropped half and the
          borrowed [ic_id] to this wand rebuilds both resources exactly.
          FLAGGED SEAM: ip_free_locked's premise list needs the matching
          three-line repair before the two lemmas can be composed.
          ================================================================ *)
       ⌜ci !! k = Some (dev, inum)⌝ -∗
       iref_tok k q -∗
       ic_id cn k (1/2) true dev inum -∗
       (i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
        ic_id cn k (1/2) true dev inum -∗
        (* ...AND THE ARM's FIFTH CONJUNCT (A⁗, §3.16): the caller supplies
           the FROZEN PARK it builds out of the mint's mirror half and the two
           live slices it is about to stop needing.  It cannot be built here:
           the mint has already flipped the bit, so nothing but the park
           itself satisfies [islot2]'s live arm from +0x50 on. *)
        frz_park k (bv_unsigned inum) q -∗
          ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) ∗
          IcacheRef.inode_ident k (DfracOwn q) dev inum) -∗
       ic_payload_at γfs γi cov logstart k inum g1 dn bm -∗
       live_gen k (1/2) g1 -∗
       (* ---- WHAT THE MINT LEFT STANDING (iclaim-ledger.md §3.16, A⁗) ----
          §3.14's token slot is gone from this seam: the free path no longer
          hands the disjunction on unresolved, it hands on the THREE things
          the mint at +0x50 produced.

          [ifreeze_pre] is kept IN HAND all the way to +0x8a -- it decides the
          escrow arm's tail at the +0x70 park and at the eviction
          ([IcacheEscrow.ic_payload_arm_decide_frz]), it pins the count across
          the lock-free span (B1, [IcacheInv.icnt_freeze_forces_one]) and it
          is what [iref_close_last_freeze_store_au] steps.
          The RECEIPT is what the +0x5e window exit parks in the escrow's
          FROZEN alternative, and the last close takes it home.
          The MIRROR's half UP is what [islot2]'s FROZEN PARK selects on --
          the park the re-assembly wand above demands. *)
       ifreeze_pre (bv_unsigned inum) -∗
       frzown (bv_unsigned inum) -∗
       frzm_h (bv_unsigned inum) true -∗
       (* ...AND THE SELECTOR's OFF HALF (RULING R-e, iclaim-ledger.md §5⁗⁗).
          [frz_park_ref1_off] peeled it out of [islot2]'s live arm at the
          +0x3a window-entering read; the two Exit-A arms put it straight back
          ([frz_park_intro_off]), and on THIS arm the mint has already flipped
          the bit, so it must ride out to [ip_free_locked]'s +0x62 re-park,
          which is the one thing that can spend it. *)
       IcacheRef.frzsel k (1/2)%Qp false -∗
       i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) -∗
       sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
       sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
       bitmap_res γfs bmapstart cov logstart size used -∗
       p_pid pj ↦₄{dq} pidv -∗
       bslots bn 3 -∗
       log_epoch_lb γ v -∗
       log_credit γ cru Sb e0 (IBLOCK inum inodestart) -∗
       log_opSe γ u Sb e0 -∗
       pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx Rra) -∗
       pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx Rs0) -∗
       pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx Rs1) -∗
       pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx Rs2) -∗
       pa_stk sp0 5 ↦₈[KT1] (m !!! Regidx Rs3) -∗
       pa_stk sp0 6 ↦₈[KT1] (m !!! Regidx Rs4) -∗
       WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros ip pj sp0 spd HK HKit Hk Hu3 Hcrb Hgeom Hsize Hbmpos Hbmcov Hbmlog
           Histpos Hicov Hilog Hnib Hbelow HMwf Hciwf HMk1 Hj Hgl Hregs Ha5
           Hlkbelow Hitnotin.
    iIntros "Hcg Hcnt Hpay Hextc Hclm #Htext #Hkd Hpc #Hpenv #Hbio #Hlctx
             #Hitlk #Hitinv #Hesc Htok Hhalf Hiauth Hipool Hslots Hpool Href
             #Hslk #Hireg Hropen Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock
             Hbslots #Hvlb Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6 Hex".
    pose proof Hregs as Hregs'.
    destruct Hregs' as (HMs1 & HMsp & _).
    iPoseProof (ipi_3a with "Htext") as "Hi3a".
    iPoseProof (ipi_3c with "Htext") as "Hi3c".
    (* the slot's own share comes out of the lock's big-op, exactly as the
       stale walk's +0x3c does (ProofIput.v:1503-1520) *)
    assert (Hcikex : exists di : mword 32 * mword 32, ci !! k = Some di).
    { destruct Hciwf as [Hdom _].
      assert (Hin : k ∈ dom ci)
        by (rewrite Hdom; apply elem_of_dom; rewrite HMk1; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcikex as [[cdev cinum] Hcik].
    iDestruct (islots2_acc_upd cn Mt ci k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk1 Hcik) in "Hslot".
    (* FOUR conjuncts, not three: [islot2]'s live arm carries the [icnt] slot
       half beside the identification ghost since iclaim-ledger.md §2.2, and
       the count half must be split out explicitly (IIIe's own observation at
       the iget hit).  It rides UNMOVED through this whole span. *)
    (* FIVE conjuncts since A⁗ (iclaim-ledger.md §3.16): the live arm also
       carries the FREEZE MIRROR's lock half, on its ordinary alternative or
       on a FROZEN PARK.  At REF-1 it cannot be the latter -- the park would
       hold the whole outstanding share and the escrow arm's half, and this
       thread's OWN share is then one slice too many -- so the walk decides it
       here, with no region open and no token
       ([IcacheInv.frz_park_ref1_off], xv6's REF-1 argument made available to
       the proof).  The [false] half it yields is what takes the payload's
       [ifreeze_off] out of the window-entering read below (P2) and what the
       MINT at +0x50 flips. *)
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid & Hcnt1 & Hpark)".
    iDestruct (fe_rest_sum with "Hrest") as %[qr Hsum].
    iDestruct "Href" as "[Hrtok Hrident]".
    iAssert (⌜cdev = dev /\ cinum = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - q)%Qp as [q'|] eqn:Et; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    assert (Ert : (1/2 - q)%Qp = Some qr) by (apply Qp.sub_Some; exact Hsum).
    (* ---- THE REF-1 PARK DECISION (A⁗, §3.16) ---- *)
    iDestruct "Hrtok" as "(Hrfrg0 & Hrlv0 & Hrslh0)".
    iApply fupd_wp.
    iMod (frz_park_ref1_off ⊤ k (bv_unsigned inum) q
            ltac:(solve_ndisj) Hk with "Hitinv Hrlv0 Hpark")
      as "(Hrlv0 & Hmirf & Hself)".
    iModIntro.
    iAssert (iref_tok k q) with "[Hrfrg0 Hrlv0 Hrslh0]" as "Hrtok";
      [ rewrite /iref_tok; iFrame |].
    (* ===== +0x3a c.lw a4,64(s1) : the read that ENTERS the window ===== *)
    assert (Hpa3a : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne M Rs1 ltac:(nz)) HMs1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x3a)) Ra4 Rs1
              (mword_of_int 64 : mword 12) M (trap_res eb + (K - 6))%nat
              (fun w => (∃ v : bool, ⌜w = valid_word v⌝ ∗
                  itable_half Mt ∗ iref_tok k q ∗
                  (if v
                   then i_dev (ientry k) ↦₄{DfracOwn q} dev ∗
                        i_dev (ientry k) ↦₄{DfracOwn qr} dev ∗
                        i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) ∗
                        (∃ ga : gname,
                           (* THE ARM's TAIL, DECIDED (A⁗, §3.16 / ZZProbeFrz
                              P2).  The tail is a disjunction since §3.14's
                              DEVIATION 1, widened by A⁗; its FROZEN
                              alternative is the receipt, and the [false]
                              mirror half this walk just extracted refutes it
                              through the region's own receipt clause
                              ([InodeRegion.ireg_frzown_off_absurd]).  So what
                              comes out is the payload, the inum's UNFROZEN
                              token -- which is exactly what the MINT at +0x50
                              consumes -- and the arm's liveness half. *)
                           ic_payload_np γfs γi cov logstart k inum ga true ∗
                           ifreeze_off (bv_unsigned inum) ∗
                           live_gen k (1/2) ga)
                   else IcacheRef.inode_ident k (DfracOwn q) dev inum ∗
                        islot_rest_at k q dev inum) ∗
                  frzm_h (bv_unsigned inum) false)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi3a [Hhalf Hrtok Hrident Hrest Hmirf]").
    { rewrite Hpa3a.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_auth_ref cn γfs γi cov logstart k
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) Mt q q dev inum
              ltac:(solve_ndisj) HMk1 with "Hitinv Hbody Hhalf Hrtok Hrident")
        as "(Hhalf & Hrtok & Hrident & Harm & _)".
      iDestruct "Harm" as (vld ga) "(Hidv & Hinh & Hvld & Hpayl & Hmt & Hgida)".
      iModIntro. iExists (valid_word vld). iFrame "Hvld". iIntros "Hvld".
      destruct vld.
      - (* LOADED: the payload leaves with us; the FULL inum cell stays *)
        rewrite /ic_payload_arm.
        iDestruct "Hpayl" as "[(Hpayl & Hoff & Hlvh) | [Hrc _]]"; last first.
        { iMod (ireg_frzown_off_absurd (⊤ ∖ ↑minstretN ∖ ↑icEscN)
                  γi γfs inodestart nib inum ltac:(solve_ndisj) Hnib
                  with "Hireg Hmirf Hrc") as "[]". }
        iDestruct "Hrident" as "[Hrd Hrn]".
        iEval (rewrite /islot_rest_at Ert) in "Hrest".
        iDestruct "Hrest" as "[Htd Htn]".
        iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum) as "[_ Hjn]".
        iDestruct ("Hjn" with "[$Hrn $Htn]") as "Hn2".
        iEval (rewrite -Hsum) in "Hn2".
        iDestruct (word4_pointsto_half_join with "Hinh Hn2") as "Hnfull".
        iDestruct (word4_pointsto_half_split with "Hvld") as "[Hva Hvb]".
        iMod ("Hclose" with "[Hidv Hnfull Hva Hmt Hgida]") as "_".
        { iApply bi.later_intro. iApply ic_close_held. rewrite /ic_held.
          iExists dev, inum, (valid_word true). iFrame. }
        iModIntro. iExists true. iFrame "Hhalf Hrtok Hrd Htd Hvb Hmirf".
        iSplitR; [done |]. iExists ga.
        iSplitL "Hpayl"; [iExact "Hpayl" |].
        iSplitL "Hoff"; [iExact "Hoff" | iExact "Hlvh"].
      - (* UNLOADED: read-only, everything goes straight back -- the tail is
           re-parked exactly as it came out, undecided. *)
        iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hmt Hgida]") as "_".
        { iApply bi.later_intro. iApply ic_close_parked.
          iApply (ic_mk_parked_arm cn γfs γi cov logstart k dev inum false ga
                    with "Hidv Hinh Hvld Hpayl Hmt Hgida"). }
        iModIntro. iExists false. iFrame. done. }
    iIntros (wvld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc HPsi".
    iDestruct "HPsi" as (vv) "(%Hwv & Hhalf & Hrtok & Hrem & Hmirf)".
    subst wvld.
    set (F1 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (valid_word vv))]> M).
    assert (HF1a4 : F1 !!! Regidx Ra4 = (sign_extend' 64 (valid_word vv) : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1a5 : F1 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F1 upd_ne; [exact Ha5 | nz]).
    assert (HF1s1 : F1 !!! Regidx Rs1 = ientry k)
      by (rewrite /F1 upd_ne; [exact HMs1 | nz]).
    assert (HF1regs : iput_regs m F1 spd k).
    { unfold iput_regs in Hregs |- *.
      destruct Hregs as (A&B&Cc&Ee&F&G&H&I&Jj&L&N&O).
      repeat split; (rewrite /F1 upd_ne; [| nz]); assumption. }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.iput + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c c.beqz a4 : !valid goes to the tail (EXIT A) ===== *)
    destruct vv.
    2:{ (* valid == 0 : the window was never entered *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x3c))
                (mword_of_int 242 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                F1 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF1a4; exact (fe_valid_beqz false))
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3c").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20b : add_vec (mword_of_int (KernelSyms.iput + 0x3c) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 242 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20b) in "Hpc".
      iDestruct "Hrem" as "[Hrident Hrest]".
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Hrest Hiu Hgid Hcnt1 Hmirf Hself]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. iFrame "Hiu Hgid Hcnt1".
        iSplitL "Hrest"; [iExact "Hrest" |].
        iApply (frz_park_intro_off with "Hmirf Hself"). }
      iDestruct "Hex" as "[HcA _]".
      iApply ("HcA" $! F1 vg4 vg5 vg6
                with "[%] [%] Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool
                      Hslots Hpool [Hrtok Hrident] Hropen Hbms Hins Hbm Hppid Hbslots Hvlb
                      Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
      { exact HF1regs. }
      { exact HF1a5. }
      { rewrite /IcacheRef.inode_ref. iFrame. } }
    (* ===== valid == 1: fall through, WITH the payload in hand ===== *)
    iDestruct "Hrem" as "(Hrd & Htd & Hvb & (%ga & Hpayl & Hoff & Hlvh))".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x3c))
              (mword_of_int 242 : mword 8) (Cregidx (mword_of_int 6)) Ra4
              F1 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF1a4; exact (fe_valid_beqz true))
              with "Hcg Hpc Hi3c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.iput + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* the three scratch slots, in [pa_stk] spelling; the bridge equalities are
       wp_iput_gen's Hb4/Hb5/Hb6 (ProofIput.v:1249-1258), pcw-provable *)
    assert (Hb4 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hb5 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hb6 : add_vec spd (zero_extend' 64
                    (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iPoseProof (ipi_3e with "Htext") as "Hi3e".
    iPoseProof (ipi_40 with "Htext") as "Hi40".
    iPoseProof (ipi_42 with "Htext") as "Hi42".
    assert (HF1sp : F1 !!! Regidx csp_rs1 = spd)
      by (destruct HF1regs as (_ & B & _); exact B).
    assert (HF1s2 : F1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (destruct HF1regs as (_ & _ & C & _); exact C).
    assert (HF1s3 : F1 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (destruct HF1regs as (_ & _ & _ & D & _); exact D).
    assert (HF1s4 : F1 !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (destruct HF1regs as (_ & _ & _ & _ & E & _); exact E).
    assert (HF1hi : F1 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F1 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF1regs as (_&_&_&_&_&G1&G2&G3&G4'&G5&G6&G7).
      split_and!; assumption. }
    (* ===== +0x3e c.sdsp s2,16(sp) ===== *)
    iEval (rewrite -Hb4 -HF1sp) in "Hg4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x3e))
              (mword_of_int 2 : mword 6) Rs2 F1 (trap_res eb + (K - 6))%nat vg4 false
              with "Hcg Hpc Hi3e Hg4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
    iEval (rgne) in "Hg4".
    iEval (rewrite HF1s2 HF1sp Hb4) in "Hg4".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.iput + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 c.sdsp s4,0(sp) ===== *)
    iEval (rewrite -Hb6 -HF1sp) in "Hg6".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x40))
              (mword_of_int 0 : mword 6) Rs4 F1 (trap_res eb + (K - 6))%nat vg6 false
              with "Hcg Hpc Hi40 Hg6").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg6".
    iEval (rgne) in "Hg6".
    iEval (rewrite HF1s4 HF1sp Hb6) in "Hg6".
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.iput + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x42)) by pcw.
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 lw s4,0(s1) : ip->dev, a PLAIN read off our own [q] share ===== *)
    assert (Hpa42 : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev (ientry k)).
    { rewrite (rget_ne F1 Rs1 ltac:(nz)) HF1s1. reflexivity. }
    iEval (rewrite -Hpa42) in "Hrd".
    (* THE WALK-TIER IDIOM (iclaim-ledger.md §3.14; template ProofIget.v:1704
       / :1776).  An identity-cell machine load instantiates the wp at
       [(kt := KT1) (ktd := KT0)]: the ACCESS PATH is KT1 (sp-migration phase
       D), while the icache's identity cells stay at [curktier_default]/KT0 --
       [IcacheRef.inode_ident] is stated there and must NOT be retiered. *)
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (KernelSyms.iput + 0x42)) Rs4 Rs1
              (mword_of_int 0 : mword 12) F1 (trap_res eb + (K - 6))%nat dev false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi42 Hrd").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hrd".
    iEval (rewrite Hpa42) in "Hrd".
    set (F2 := <[Regidx Rs4 := regval_into_reg (sign_extend' 64 dev)]> F1).
    assert (HF2s4 : F2 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F2; apply upd_eq).
    assert (HF2s1 : F2 !!! Regidx Rs1 = ientry k)
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2sp : F2 !!! Regidx csp_rs1 = spd)
      by (rewrite /F2 upd_ne; [exact HF1sp | nz]).
    assert (HF2s2 : F2 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /F2 upd_ne; [exact HF1s2 | nz]).
    assert (HF2s3 : F2 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F2 upd_ne; [exact HF1s3 | nz]).
    assert (HF2a5 : F2 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F2 upd_ne; [exact HF1a5 | nz]).
    assert (HF2hi : F2 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F2 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF1hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F2 upd_ne; [| nz]); assumption. }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.iput + 0x42) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* the loaded bundle, at the record we are holding.  Since A⁗ the arm's
       tail comes out DECIDED (see the +0x3a AU), so what is in hand is the
       payload proper plus the inum's UNFROZEN token -- the one the mint at
       +0x50 spends. *)
    iEval (rewrite /ic_payload_np) in "Hpayl".
    iDestruct "Hpayl" as (dn bm) "Hpayl".
    iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm) with "[Hpayl]" as "Hpayl";
      [ rewrite /ic_payload_at; iExact "Hpayl" |].
    (* ===================================================================
       +0x46 lw s2,4(s1) : ip->inum.  THE REORDER'S NEW AU.  The stale pin
       never read [ip->inum] inside the window (it got dev/inum elsewhere);
       the reordered one does, and by then the escrow's HELD arm owns that
       cell WHOLE -- [ic_held] holds [i_inum] at dfrac 1 by design, since
       "both [ic_mid_arm] and [ic_held] are refuted by a FULL [i_inum] cell"
       (IcacheEscrow.v, §17.3 (A)'s note).  So this load cannot be a plain
       read the way +0x42's [ip->dev] is: it is an ATOMIC UPDATE that
       re-enters the window with [ic_open_held] and closes it right back at
       HELD with [ic_close_held].  Nothing moves; the cell is only borrowed.
       =================================================================== *)
    iPoseProof (ipi_46 with "Htext") as "Hi46".
    assert (Hpa46 : add_vec (rget F2 Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                    = i_inum (ientry k)).
    { rewrite (rget_ne F2 Rs1 ltac:(nz)) HF2s1. reflexivity. }
    iDestruct "Hrtok" as "(Hrfrg & Hrlv & Hrslh)".
    iApply (wp_lw_au_s_sconf false (mword_of_int (KernelSyms.iput + 0x46)) Rs2 Rs1
              (mword_of_int 4 : mword 12) F2 (trap_res eb + (K - 6))%nat
              (fun w => (⌜w = inum⌝ ∗ itable_half Mt ∗ iref_frag k q ∗ live_frac k q ∗
                         live_gen k (1/2) ga ∗ ic_id cn k (1/2) true dev inum ∗
                         i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) ∗
                         ic_payload_at γfs γi cov logstart k inum ga dn bm)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi46 [Hhalf Hrfrg Hrlv Hlvh Hgid Hvb Hpayl]").
    { rewrite Hpa46.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_held cn γfs γi cov logstart k (⊤ ∖ ↑minstretN ∖ ↑icEscN)
              Mt q ga ga dev inum dn bm ltac:(solve_ndisj) HMk1
              with "Hitinv Hbody Hhalf Hrfrg Hrlv Hlvh Hgid Hvb Hpayl")
        as "(Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hvb & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
      iDestruct "Hvldx" as (w0) "Hva".
      iModIntro. iExists inum. iFrame "Hnfull". iIntros "Hnfull".
      iMod ("Hclose" with "[Hidv Hnfull Hva Hmt Hgida]") as "_".
      { iApply bi.later_intro. iApply ic_close_held. rewrite /ic_held.
        iExists dev, inum, w0. iFrame. }
      iModIntro. iFrame. done. }
    iIntros (winum).
    iApply wp_next_off_intro. iIntros "Hcg Hpc HPsi".
    iDestruct "HPsi" as "(%Hwi & Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hvb & Hpayl)".
    subst winum.
    set (F3 := <[Regidx Rs2 := regval_into_reg (sign_extend' 64 inum)]> F2).
    assert (HF3s2 : F3 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F3; apply upd_eq).
    assert (HF3s1 : F3 !!! Regidx Rs1 = ientry k)
      by (rewrite /F3 upd_ne; [exact HF2s1 | nz]).
    assert (HF3sp : F3 !!! Regidx csp_rs1 = spd)
      by (rewrite /F3 upd_ne; [exact HF2sp | nz]).
    assert (HF3s3 : F3 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F3 upd_ne; [exact HF2s3 | nz]).
    assert (HF3s4 : F3 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F3 upd_ne; [exact HF2s4 | nz]).
    assert (HF3a5 : F3 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F3 upd_ne; [exact HF2a5 | nz]).
    assert (HF3hi : F3 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F3 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF2hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F3 upd_ne; [| nz]); assumption. }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.iput + 0x46) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ===== +0x4a lh a4,74(s1) : nlink, a PLAIN read off the held payload ===== *)
    iPoseProof (ipi_4a with "Htext") as "Hi4a".
    iEval (rewrite /ic_payload_at) in "Hpayl".
    iDestruct "Hpayl" as "[Hlk #Hshot]".
    iDestruct "Hlk" as (data)
      "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdat & Hmeta & Haddrs & Hind & Hblks)".
    pose proof Hok as Hok'.
    destruct Hok' as (Hbmwf & Hcovers & Hdiaddrs & Htyne & Hszcap & Hholes & Hsized).
    iEval (rewrite /inode_meta) in "Hmeta".
    iDestruct "Hmeta" as "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    assert (Hpa4a : add_vec (rget F3 Rs1) (sign_extend' 64 (mword_of_int 74 : mword 12))
                    = i_nlink (ientry k)).
    { rewrite (rget_ne F3 Rs1 ltac:(nz)) HF3s1. reflexivity. }
    iEval (rewrite -Hpa4a) in "Hmnl".
    (* the WALK-TIER IDIOM again (§3.14): the metadata cells, like the
       identity cells, stay at the DATA tier while the access path is KT1. *)
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0)
              (mword_of_int (KernelSyms.iput + 0x4a)) Ra4 Rs1
              (mword_of_int 74 : mword 12) F3 (trap_res eb + (K - 6))%nat (di_nlink dn) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4a Hmnl").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hmnl".
    iEval (rewrite Hpa4a) in "Hmnl".
    set (F4 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 (di_nlink dn : mword 16))]> F3).
    assert (HF4a4 : F4 !!! Regidx Ra4 = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /F4; apply upd_eq).
    assert (HF4s1 : F4 !!! Regidx Rs1 = ientry k)
      by (rewrite /F4 upd_ne; [exact HF3s1 | nz]).
    assert (HF4sp : F4 !!! Regidx csp_rs1 = spd)
      by (rewrite /F4 upd_ne; [exact HF3sp | nz]).
    assert (HF4s2 : F4 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s2 | nz]).
    assert (HF4s3 : F4 !!! Regidx Rs3 = m !!! Regidx Rs3)
      by (rewrite /F4 upd_ne; [exact HF3s3 | nz]).
    assert (HF4s4 : F4 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F4 upd_ne; [exact HF3s4 | nz]).
    assert (HF4a5 : F4 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k))
      by (rewrite /F4 upd_ne; [exact HF3a5 | nz]).
    assert (HF4hi : F4 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F4 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF3hi as (G1&G2&G3&G4'&G5&G6&G7).
      repeat split; (rewrite /F4 upd_ne; [| nz]); assumption. }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.iput + 0x4a) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    iPoseProof (ipi_4e with "Htext") as "Hi4e".
    (* ===== +0x4e c.bnez a4 : nlink != 0 UNDOES the window (EXIT A) ===== *)
    destruct (neq_vec (sign_extend' 64 (di_nlink dn : mword 16) : mword 64)
                      (zero_reg : mword 64)) eqn:Hnl0.
    { (* nlink != 0 : re-park at PARKED and take the tail through 0xcc/0xce/0xd0.
         Stale pattern ProofIput.v:1677-1744, with the extra twist that the
         window here was entered at 0x3a and re-entered at 0x46. *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x4e))
                (mword_of_int 63 : mword 8) (Cregidx (mword_of_int 6)) Ra4
                F4 (trap_res eb + (K - 6))%nat false
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF4a4; exact Hnl0)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hppcc : add_vec (mword_of_int (KernelSyms.iput + 0x4e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 63 : mword 8) ('b"0"))))
                      = mword_of_int (KernelSyms.iput + 0xcc)) by pcw.
      iEval (rewrite Hppcc) in "Hpc".
      (* ---- the UNDO: HELD -> PARKED, nothing retyped, no generation bump ---- *)
      iApply fupd_wp.
      iInv "Hesc" as ">Hbody" "Hclose".
      iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm)
        with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
      { rewrite /ic_payload_at.
        iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
        iSplitR; [iPureIntro; exact Hok |].
        iSplitR; [iPureIntro; exact Hdok |].
        iSplitR; [iPureIntro; exact Hddix |].
        iSplitR; [iPureIntro; exact Hdoc |].
        iSplitR; [iPureIntro; exact Hduq |].
        iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
      iMod (ic_open_held cn γfs γi cov logstart k (⊤ ∖ ↑icEscN)
              Mt q ga ga dev inum dn bm ltac:(solve_ndisj) HMk1
              with "Hitinv Hbody Hhalf Hrfrg Hrlv Hlvh Hgid Hvb Hpayl")
        as "(Hhalf & Hrfrg & Hrlv & Hlvh & Hgid & Hvb & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
      iAssert (iref_tok k q) with "[Hrfrg Hrlv Hrslh]" as "Hrtok".
      { rewrite /iref_tok. iFrame. }
      (* re-park at the ARM's tail, on its ORDINARY alternative: the token the
         +0x3a read took goes straight back in (this exit never freezes), and
         so does the arm's liveness half (A⁗, §3.16). *)
      iDestruct (ic_payload_at_pack_np with "Hpayl") as "Hpayl".
      iDestruct "Hvldx" as (w0) "Hva".
      iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
      iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
      (* the FULL inum cell splits back: the arm's half, our q, the table's qr *)
      iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hn2]".
      iEval (rewrite Hsum) in "Hn2".
      iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
        as "[Hrn Htn]".
      iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hoff Hlvh Hmt Hgida]") as "_".
      { iApply bi.later_intro. iApply ic_close_parked.
        iApply (ic_mk_parked_arm cn γfs γi cov logstart k dev inum true ga
                  with "Hidv Hinh Hvld [Hpayl Hoff Hlvh] Hmt Hgida").
        rewrite /ic_payload_arm. iLeft. iFrame "Hpayl Hoff Hlvh". }
      iModIntro.
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid Hcnt1 Hmirf Hself]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. iFrame "Hiu Hgid Hcnt1".
        iSplitR "Hmirf Hself"; [| iApply (frz_park_intro_off with "Hmirf Hself")].
        rewrite /islot_rest_at Ert /IcacheRef.inode_ident. iFrame. }
      (* ===== +0xcc c.ldsp s2,16(sp) ; +0xce c.ldsp s4,0(sp) ===== *)
      iPoseProof (ipi_cc with "Htext") as "Hicc".
      iPoseProof (ipi_ce with "Htext") as "Hice".
      iPoseProof (ipi_d0 with "Htext") as "Hid0".
      iEval (rewrite -Hb4 -HF4sp) in "Hg4".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xcc))
                (mword_of_int 2 : mword 6) Rs2 F4 (trap_res eb + (K - 6))%nat
                (m !!! Regidx Rs2) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hicc Hg4").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
      iEval (rewrite HF4sp Hb4) in "Hg4".
      set (G1 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> F4).
      assert (HG1sp : G1 !!! Regidx csp_rs1 = spd)
        by (rewrite /G1 upd_ne; [exact HF4sp | nz]).
      assert (Hppce : add_vec_int (mword_of_int (KernelSyms.iput + 0xcc) : mword 64) 2
                      = mword_of_int (KernelSyms.iput + 0xce)) by pcw.
      iEval (rewrite Hppce) in "Hpc".
      iEval (rewrite -Hb6 -HG1sp) in "Hg6".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0xce))
                (mword_of_int 0 : mword 6) Rs4 G1 (trap_res eb + (K - 6))%nat
                (m !!! Regidx Rs4) false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hice Hg6").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hg6".
      iEval (rewrite HG1sp Hb6) in "Hg6".
      set (G2 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> G1).
      assert (Hppd0 : add_vec_int (mword_of_int (KernelSyms.iput + 0xce) : mword 64) 2
                      = mword_of_int (KernelSyms.iput + 0xd0)) by pcw.
      iEval (rewrite Hppd0) in "Hpc".
      (* ===== +0xd0 c.j -176 -> +0x20 ===== *)
      assert (Htgtd0 : add_vec (mword_of_int (KernelSyms.iput + 0xd0) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 1960 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iput + 0xd0))
                (sign_extend' 21 (concat_vec (mword_of_int 1960 : mword 11) ('b"0")))
                G2 (trap_res eb + (K - 6))%nat false
                ltac:(rewrite Htgtd0; vm_compute; reflexivity) with "Hcg Hpc Hid0").
      iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgtd0) in "Hpc".
      assert (HG2regs : iput_regs m G2 spd k).
      { destruct HF4hi as (P21&P22&P23&P24&P25&P26&P27).
        unfold iput_regs. split_and!.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4s1.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4sp.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1. apply upd_eq.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4s3.
        - rewrite /G2. apply upd_eq.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P21.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P22.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P23.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P24.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P25.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P26.
        - rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact P27. }
      assert (HG2a5 : G2 !!! Regidx Ra5 = sign_extend' 64 (iref_word Mt k)).
      { rewrite /G2 upd_ne; [| nz]. rewrite /G1 upd_ne; [| nz]. exact HF4a5. }
      iDestruct "Hex" as "[HcA _]".
      iApply ("HcA" $! G2 (m !!! Regidx Rs2) vg5 (m !!! Regidx Rs4)
                with "[%] [%] Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool
                      Hslots Hpool [Hrtok Hrd Hrn] Hropen Hbms Hins Hbm Hppid Hbslots Hvlb
                      Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
      { exact HG2regs. }
      { exact HG2a5. }
      { rewrite /IcacheRef.inode_ref /IcacheRef.inode_ident. iFrame. } }
    (* ===== nlink == 0: fall through at 0x4e -- the FREE path ===== *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x4e))
              (mword_of_int 63 : mword 8) (Cregidx (mword_of_int 6)) Ra4
              F4 (trap_res eb + (K - 6))%nat false
              ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF4a4; exact Hnl0)
              with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.iput + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===================================================================
       THE MINT (iclaim-ledger.md §3.16, RULING A⁗; §1.4/§2.3's f-column
       mover).  The C at +0x50 only saves [s3]; this is the GHOST step that
       rides with it, and +0x50 is the ONE instant at which it can happen --
       the itable lock is HELD (so the mirror's lock half is reachable, and
       [frzm_update] wants both halves), the region can be opened, the walk
       has just DECIDED [ip->nlink == 0] off the payload it is holding, and
       the count is REF-1's ONE.

       What it spends: the payload's [ifreeze_off], the mirror's [false] half
       (peeled at +0x3a), the record (borrowed) and the [icnt] half.  What it
       yields: [ifreeze_pre] -- kept IN HAND to +0x8a, where it decides the
       escrow arm and pays [iref_close_last_freeze_store_au] -- the freeze
       RECEIPT (which the +0x5e window exit parks in the escrow's frozen
       alternative), and the mirror's half UP, which the +0x62 park puts in
       [islot2]'s FROZEN PARK.  From here to +0x8a the column reads [FrzPre],
       and that is what pins the count across the lock-free span (B1) and
       kills a foreign [idup] (2.6b).
       =================================================================== *)
    assert (Hp1nat : Pos.to_nat 1 = 1%nat) by reflexivity.
    iEval (rewrite Hp1nat) in "Hcnt1".
    iApply fupd_wp.
    iMod (ireg_freeze_au ⊤ γi γfs inodestart nib inum dn
            ltac:(solve_ndisj) Hnib (fe_nlink_zero (di_nlink dn) Hnl0) Htyne
            with "Hireg Hropen Hdat Hoff Hcnt1 Hmirf")
      as "(Hdat & Hpre & Hcnt1 & Hrcpt & Hmirt)".
    iModIntro.
    iEval (rewrite -Hp1nat) in "Hcnt1".
    iPoseProof (ipi_50 with "Htext") as "Hi50".
    iPoseProof (ipi_52 with "Htext") as "Hi52".
    iPoseProof (ipi_56 with "Htext") as "Hi56".
    iPoseProof (ipi_58 with "Htext") as "Hi58".
    (* ===== +0x50 c.sdsp s3,8(sp) ===== *)
    iEval (rewrite -Hb5 -HF4sp) in "Hg5".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x50))
              (mword_of_int 1 : mword 6) Rs3 F4 (trap_res eb + (K - 6))%nat vg5 false
              with "Hcg Hpc Hi50 Hg5").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg5".
    iEval (rgne) in "Hg5".
    iEval (rewrite HF4s3 HF4sp Hb5) in "Hg5".
    assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.iput + 0x50) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x52)) by pcw.
    iEval (rewrite Hpp52) in "Hpc".
    (* ===== +0x52 addi a5,s1,16 ; +0x56 c.mv s3,a5 ; +0x58 c.mv a0,a5 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x52)) Ra5 Rs1
              (mword_of_int 16 : mword 12) F4 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi52").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (F5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget F4 Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> F4).
    assert (HF5a5 : F5 !!! Regidx Ra5 = i_lock (ientry k)).
    { rewrite /F5 upd_eq. unfold regval_into_reg.
      rewrite (rget_ne F4 Rs1 ltac:(nz)) HF4s1. reflexivity. }
    assert (HF5s1 : F5 !!! Regidx Rs1 = ientry k)
      by (rewrite /F5 upd_ne; [exact HF4s1 | nz]).
    assert (HF5sp : F5 !!! Regidx csp_rs1 = spd)
      by (rewrite /F5 upd_ne; [exact HF4sp | nz]).
    assert (HF5s2 : F5 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F5 upd_ne; [exact HF4s2 | nz]).
    assert (HF5s4 : F5 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F5 upd_ne; [exact HF4s4 | nz]).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.iput + 0x52) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x56)) Rs3 Ra5
              F5 (trap_res eb + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi56").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F6 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (F5 !!! Regidx Ra5))]> F5).
    assert (HF6s3 : F6 !!! Regidx Rs3 = i_lock (ientry k)).
    { rewrite /F6 upd_eq. rewrite HF5a5. apply add_vec_zero_l. }
    assert (HF6a5 : F6 !!! Regidx Ra5 = i_lock (ientry k))
      by (rewrite /F6 upd_ne; [exact HF5a5 | nz]).
    assert (HF6s1 : F6 !!! Regidx Rs1 = ientry k)
      by (rewrite /F6 upd_ne; [exact HF5s1 | nz]).
    assert (HF6sp : F6 !!! Regidx csp_rs1 = spd)
      by (rewrite /F6 upd_ne; [exact HF5sp | nz]).
    assert (HF6s2 : F6 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F6 upd_ne; [exact HF5s2 | nz]).
    assert (HF6s4 : F6 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F6 upd_ne; [exact HF5s4 | nz]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.iput + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x58)) Ra0 Ra5
              F6 (trap_res eb + (K - 6))%nat false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi58").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (F7 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (F6 !!! Regidx Ra5))]> F6).
    assert (HF7a0 : F7 !!! Regidx Ra0 = i_lock (ientry k)).
    { rewrite /F7 upd_eq. rewrite HF6a5. apply add_vec_zero_l. }
    assert (HF7s1 : F7 !!! Regidx Rs1 = ientry k)
      by (rewrite /F7 upd_ne; [exact HF6s1 | nz]).
    assert (HF7sp : F7 !!! Regidx csp_rs1 = spd)
      by (rewrite /F7 upd_ne; [exact HF6sp | nz]).
    assert (HF7s2 : F7 !!! Regidx Rs2 = (sign_extend' 64 inum : mword 64))
      by (rewrite /F7 upd_ne; [exact HF6s2 | nz]).
    assert (HF7s3 : F7 !!! Regidx Rs3 = i_lock (ientry k))
      by (rewrite /F7 upd_ne; [exact HF6s3 | nz]).
    assert (HF7s4 : F7 !!! Regidx Rs4 = (sign_extend' 64 dev : mword 64))
      by (rewrite /F7 upd_ne; [exact HF6s4 | nz]).
    assert (HF7hi : F7 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
                    F7 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { destruct HF4hi as (P21&P22&P23&P24&P25&P26&P27).
      repeat split;
        (rewrite /F7 upd_ne; [| nz]); (rewrite /F6 upd_ne; [| nz]);
        (rewrite /F5 upd_ne; [| nz]); assumption. }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.iput + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* ===== 0x5a: ip_free_locked's ENTRY.  Re-pack the payload, mint the
       re-assembly wand, hand the bundle over. ===== *)
    iAssert (ic_payload_at γfs γi cov logstart k inum ga dn bm)
      with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
    { rewrite /ic_payload_at.
      iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      iSplitR; [iPureIntro; exact Hddix |].
      iSplitR; [iPureIntro; exact Hdoc |].
      iSplitR; [iPureIntro; exact Hduq |].
      iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
    iAssert (iref_tok k q) with "[Hrfrg Hrlv Hrslh]" as "Hrtok".
    { rewrite /iref_tok. iFrame. }
    iAssert (i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
             ic_id cn k (1/2) true dev inum -∗
             frz_park k (bv_unsigned inum) q -∗
               ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) ∗
               IcacheRef.inode_ident k (DfracOwn q) dev inum)%I
      with "[Htd Hiu Hback Hrd Hcnt1]" as "Hwand".
    { iIntros "Hn2 Hgid2 Hpk".
      iEval (rewrite Hsum) in "Hn2".
      iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
        as "[Hrn Htn]".
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid2 Hcnt1 Hpk]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk1 Hcik. iFrame "Hiu Hgid2 Hcnt1 Hpk".
        rewrite /islot_rest_at Ert /IcacheRef.inode_ident. iFrame. }
      iSplitL "Hslots"; [iExact "Hslots" |].
      rewrite /IcacheRef.inode_ident. iFrame. }
    iDestruct "Hex" as "[_ HcB]".
    iApply ("HcB" $! F7 ga dn bm data
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcg Hcnt Hpay Hextc Hclm Hpc Htok Hhalf Hiauth Hipool Hpool
                    [%] Hrtok Hgid Hwand Hpayl Hlvh Hpre Hrcpt Hmirt Hself Hvb Hbms Hins Hbm
                    Hppid Hbslots Hvlb Hcrd Hop Hr1 Hr2 Hr3 Hg4 Hg5 Hg6").
    { exact Htyne. }
    { exact (fe_nlink_zero (di_nlink dn) Hnl0). }
    { exact (fe_dinode_wf cov logstart dn bm Hbmwf Hdiaddrs). }
    { exact Hbmwf. }
    { exact Hsized. }
    { exact Hdiaddrs. }
    { exact (eq_sym HF7sp). }
    { exact HF7a0. }
    { exact HF7s1. }
    { exact HF7s2. }
    { exact HF7s3. }
    { exact HF7s4. }
    { exact HF7hi. }
    { exact Hcik. }
  Qed.

End IputFreePath.

(* ===================================================================== *)
(*  4.  THE FUNCTION                                                      *)
(* ===================================================================== *)

Section ProofIput.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* the record iput leaves on disk: itrunc's, with the type zeroed by the
     [sh] at +0x66.  [bv_unsigned (di_type ...) = 0] is exactly
     [ipool_shape]'s FREE disjunct, which is what the park deposits. *)
  Definition di_free (d : dinode) : dinode :=
    MkDinode (mword_of_int 0 : mword 16) (di_major d) (di_minor d) (di_nlink d)
             (bv_0 32) (bm_cells bm_empty).

  Lemma di_free_type (d : dinode) : bv_unsigned (di_type (di_free d)) = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma di_free_addrs (d : dinode) : di_addrs (di_free d) = bm_cells bm_empty.
  Proof. reflexivity. Qed.

  (* THE WALK IS THE GEN FORM (GR-2a finding 1, same argument as itrunc's):
     [log_opS] has no auth-monotone shadow, so the set-form contract cannot
     be derived from the counted one outside a walk.  The counted contract
     is the seal after this proof. *)
  Lemma wp_iput_gen
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
      (n : nat) (Sb : gset Z) (crb cru crz : bool) (e0 : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_iput_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                       cov logstart bmapstart inodestart nib size dev used
                       k q inum n Sb crb cru crz e0 pidv dq dqb dqs m K eb b lks.
  Proof.
    cbv beta delta [wp_iput_gen_body].
    intros pcE ip pj ret_tgt HK Hk Hcrb Hcru Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hcovb Hn Hj Hgsj Ha0 Hfresh.
    (* iput's own premise is stated at its cone MINIMUM, "log" (1) -- itrunc
       reaches log_write.  The three steps that touch itable.lock itself (the
       admitted acquiresleep order fact, the re-acquire at +0x82, and the
       shared tail) each want the bound at "itable" (14), which [mono]
       supplies once here rather than three times below. *)
    assert (Hitbelow : locks_below lks "itable") by lkbelow.
    pose proof HK as HK'. 
    unfold iput_units in Hn.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hitab #Hinv #Hesc #Hireg
             Hropen #Hslk Href Hru Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots Hnlz Hop Hcont".
    (* iput enters at level 0, so the live index and the saved base agree;
       keep BOTH names alive as [Hbm], then [subst b] -- unlike the
       [dirlookup]/[namex]-style scaffolding, [b] is not spelled by name
       anywhere below (the whole function used the literal [true] until
       this edit), so nothing downstream breaks, and everything from here
       on reads at the single surviving name [eb].  ([ProofBeginOp.v] is
       the worked example of this exact move.) *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm. subst b.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iPoseProof (ipi_00 with "Htext") as "Hi00".
    iPoseProof (ipi_02 with "Htext") as "Hi02".
    iPoseProof (ipi_04 with "Htext") as "Hi04".
    iPoseProof (ipi_06 with "Htext") as "Hi06".
    iPoseProof (ipi_08 with "Htext") as "Hi08".
    iPoseProof (ipi_0a with "Htext") as "Hi0a".
    iPoseProof (ipi_0c with "Htext") as "Hi0c".
    iPoseProof (ipi_10 with "Htext") as "Hi10".
    iPoseProof (ipi_14 with "Htext") as "Hi14".
    (* ===== PROLOGUE (generic [b] = true) ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 eb
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    iDestruct "S5" as (vg5) "Hg5". iDestruct "S6" as (vg6) "Hg6".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    iEval (rewrite -Hb5) in "Hg5". iEval (rewrite -Hb6) in "Hg6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat vr24 eb with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iput + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat vr16 eb with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iput + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat vr8 eb with "Hcg Hpc Hi06 Hr8").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    (* the three saved slots now hold the CALLER's ra / s0 / s1, at the
       [pa_stk] addresses the tail and the epilogue name them by *)
    assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1v : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1 HR1ra) in "Hr24".
    iEval (rewrite Hb2 HR1s0) in "Hr16".
    iEval (rewrite Hb3 HR1s1v) in "Hr8".
    iEval (rewrite Hb4) in "Hg4".
    iEval (rewrite Hb5) in "Hg5". iEval (rewrite Hb6) in "Hg6".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iput + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iput + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iput + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x0a)) Rs1 Ra0
              R2 (K - 6)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = ientry k).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [| nz].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iput + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x0c)) Ra0 (mword_of_int 29 : mword 20)
              R3 (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.iput + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.iput + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x10)) Ra0 Ra0 (mword_of_int 1388 : mword 12)
              R4 (K - 6)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1388 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = itable_lock).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.iput + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.iput + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x14)) Rra (mword_of_int 2086958 : mword 21)
              R5 (K - 6)%nat eb ltac:(nz) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi14").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.iput + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 2086958 : mword 21))
                      = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAa0 : mA !!! Regidx Ra0 = itable_lock)
      by (rewrite /mA upd_ne; [exact HR5a0 | nz]).
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.iput + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    assert (HmAs1 : mA !!! Regidx Rs1 = ientry k).
    { rewrite /mA upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
      rewrite /R4 upd_ne; [| nz]. exact HR3s1. }
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
      rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz].
      rewrite /R2 upd_ne; [| nz]. exact HspR1. }
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                       mA !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite /mA upd_ne; [| regne]. rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HmAregs : iput_regs m mA spr k).
    { unfold iput_regs. repeat split;
        first [ exact HmAs1 | exact HmAsp
              | rewrite HmAthr;
                [ reflexivity | vm_compute; reflexivity | nz | nz | nz ] ]. }
    iDestruct (cpu_own_transport CID CID9 0%nat eb pj eb ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf KT1 gtl "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) mA
              0%nat eb pj (K - 6)%nat eb lks
              ltac:(lia) ltac:(lia)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc [Hitab]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hitab". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x18)).
    { rewrite HmAra. pcw. }
    iEval (rewrite Hpc18) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmacqregs : iput_regs m macq spr k)
      by (exact (iput_regs_cs m mA macq spr k Hacqpins_cs HmAregs)).
    pose proof Hmacqregs as Hmacqregs0.
    destruct Hmacqregs0 as (Hms1 & Hmsp & Hm18 & Hm19 & Hm20 & Hm21 & Hm22 & Hm23
                            & Hm24 & Hm25 & Hm26 & Hm27).
    (* [Hextc]/[Hextm]: acquire does not thread them (its contract never
       mentions [trap_csrs_ext]/[cpu_claim_ext]) -- one wide hop straight
       from the ENTRY hart to [CIDacq], covering the whole prologue AND the
       acquire call itself in a single step, exactly as [durable-notes.md]'s
       "wide hop, not several narrow ones" rule prescribes.  From here the
       WHOLE critical section is nested ([wp_next_off_intro] throughout, no
       hart can move), so this one hop covers every path out of it: the
       three non-truncating exits below AND the truncating one (which needs
       a further hop once it leaves the lock, at the itrunc call). *)
    iDestruct (trap_csrs_ext_transport CID CIDacq eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDacq eb pj
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    (* ===== the critical section (literal [false]) ===== *)
    iDestruct "HRres" as (Mt ci) "(Hhalf & %Hwf & %Hciwf & Hiauth & Hipool & Hslots & Hpool)".
    iDestruct "Href" as "[Hrtok Hrident]".
    iDestruct (iref_lookup with "Hhalf Hrtok") as %(qt & cnt & HMk & Hqt1 & Hone & Hone').
    pose proof (icM_wf_count Mt k qt cnt Hwf HMk) as Hcntb.
    iPoseProof (ipi_18 with "Htext") as "Hi18".
    iPoseProof (ipi_1a with "Htext") as "Hi1a".
    iPoseProof (ipi_1c with "Htext") as "Hi1c".
    assert (Hiw : iref_word Mt k = (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /iref_word HMk; reflexivity).
    (* ===== +0x18 c.lw a4,8(s1) ===== *)
    assert (Hpa18 : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                    = i_ref (ientry k)).
    { rewrite (rget_ne macq Rs1 ltac:(nz)) Hms1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x18)) Ra5 Rs1
              (mword_of_int 8 : mword 12) macq (trap_res eb + (K - 6))%nat
              (fun v => (⌜v = iref_word Mt k⌝ ∗ itable_half Mt)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi18 [Hhalf]").
    { rewrite Hpa18.
      iMod (iref_load_locked_au (⊤ ∖ ↑minstretN) Mt k
              ltac:(solve_ndisj) Hk with "Hinv Hhalf") as "[Hcell Hback2]".
      iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback2" with "Hcell") as "Hhalf". iModIntro. by iFrame. }
    iIntros (vld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc [%Hvld Hhalf]".
    subst vld. iEval (rewrite Hiw) in "Hcg".
    set (E1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> macq).
    assert (HE1a5 : E1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /E1; apply upd_eq).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.iput + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.iput + 0x1a)) Ra4
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              E1 (trap_res eb + (K - 6))%nat false ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (E2 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> E1).
    assert (HE2a5 : E2 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /E2 upd_ne; [exact HE1a5 | nz]).
    assert (HE2a4 : E2 !!! Regidx Ra4 = (mword_of_int 1 : mword 64))
      by (rewrite /E2; apply upd_eq).
    assert (HE2regs : iput_regs m E2 spr k).
    { unfold iput_regs in Hmacqregs |- *.
      destruct Hmacqregs as (A&B&Cc&Ee&F&G&H&I&Jj&L&N&O).
      repeat split;
        (rewrite /E2 upd_ne; [| nz]); (rewrite /E1 upd_ne; [| nz]); assumption. }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.iput + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c beq a4,a5 : REF-1 or not ===== *)
    assert (Hcmp : eq_vec (rget E2 Ra5) (rget E2 Ra4)
                   = (if decide (cnt = 1%positive) then true else false)).
    { rewrite (rget_ne E2 Ra5 ltac:(nz)) (rget_ne E2 Ra4 ltac:(nz)) HE2a5 HE2a4.
      apply ip_cnt_eq_one. lia. }
    assert (Hsp0eq : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iPoseProof (ipi_1c with "Htext") as "Hi1cb".
    destruct (decide (cnt = 1%positive)) as [Hcone|Hcnone]; last first.
    { (* ---- ref != 1: fall through straight into the tail ---- *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x1c))
                (mword_of_int 30 : mword 13) Ra4 Ra5 E2 (trap_res eb + (K - 6))%nat false
                ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi1cb").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.iput + 0x1c) : mword 64) 4
                      = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20) in "Hpc".
      (* the epoch is FORGOTTEN at the close arms' seam: [ip_tail] is stated
         over [log_opS] and nothing past this point compares epochs. *)
      iDestruct (log_opSe_opS with "Hop") as "Hop".
      iApply (ip_tail (CID := CIDacq) CID j bn g gfs gi cn gtl cov logstart bmapstart
                inodestart nib size dev used used Sb Sb k q inum Mt ci n n
                (fun w => ip_spend_w w cru crz) false crb pidv dq dqb dqs
                m E2 K eb sp0 vg4 vg5 vg6 lks
                HK Hk ltac:(wp_next_chain) Hsp0eq HE2regs ltac:(rewrite Hiw; exact HE2a5) Hwf Hciwf
                ltac:(cbn; lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                ltac:(discriminate) ltac:(intros _; reflexivity) ltac:(lkbelow)
                with "Htext Hitab Hinv Hesc Hireg Hpc Hcg Hcnt Hpay Hextc Hextm Htok Hhalf Hiauth Hipool Hslots
                      Hpool [Hrtok Hrident] Hru Hropen Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm
                      Hbslots Hop Hcont").
      rewrite /IcacheRef.inode_ref. iFrame. }

    (* ---- ref == 1: the branch to +0x3a, and the WINDOW -----------------

       THE TARGET IS +0x3a, NOT +0x3c.  The stale pre-reorder walk asserted
       [Hpp3c] here and that was simply the old image's displacement; the
       reordered iput's [beq] lands one halfword earlier, on the
       [c.lw a4,64(s1)] that ENTERS the checkout window.  From there to the
       [c.j 0x30] at +0xca the whole free path is the three lemmas of section
       IputFreePath, and this block is only their seam. *)
    subst cnt. specialize (Hone eq_refl). subst qt.
    iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x1c))
              (mword_of_int 30 : mword 13) Ra4 Ra5 E2 (trap_res eb + (K - 6))%nat false
              ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1cb").
    iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp3a : add_vec (mword_of_int (KernelSyms.iput + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 30 : mword 13))
                    = mword_of_int (KernelSyms.iput + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* the off-lock tail's manual inode flush wants an epoch FLOOR; iput has
       none of its own to offer, so it mints the trivial one. *)
    iApply fupd_wp. iMod (log_epoch_lb_0 g) as "#Hlb0". iModIntro.
    (* ...and the tail-flush CREDIT in resource form, at this op's own birth
       epoch: iput's claim is the pure own-set one it always was. *)
    iAssert (log_credit g cru Sb e0 (IBLOCK inum inodestart)) as "#Hcrd";
      [ iApply log_credit_own; exact Hcru |].
    assert (Hitne : "itable"%string ∉ lks)
      by exact (locks_below_not_elem _ _ Hitbelow).
    iApply (ip_free_entry gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
              cov logstart bmapstart inodestart nib size dev used
              k q inum Mt ci n Sb crb cru e0 0%nat pidv dq dqb dqs
              vg4 vg5 vg6 m E2 K eb lks
              HK ltac:(lia) Hk ltac:(lia) Hcrb
              Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog Hnib Hcovb
              Hwf Hciwf HMk Hj Hgsj HE2regs ltac:(rewrite Hiw; exact HE2a5)
              Hfresh Hitne
              with "Hcg Hcnt Hpay Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlogc
                    Hitab Hinv Hesc Htok Hhalf Hiauth Hipool Hslots Hpool
                    [Hrtok Hrident] Hslk Hireg Hropen Hbms Hins Hbm Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hbslots Hlb0 Hcrd Hop
                    Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 [-]").
    { rewrite /IcacheRef.inode_ref. iFrame. }
    (* ===================================================================
       THE TWO EXITS.  Joined by [∧] in the lemma because they are
       alternatives and this proof's own post is one spatial resource; here
       that is exactly what lets both arms end in [Hcont].
       =================================================================== *)
    iSplit.
    - (* ===== EXIT A (+0x20): valid == 0 or nlink != 0 -- into the shared
         [ref--] tail, with the bundle untouched and the payload re-parked.
         Everything the tail wants is what came back. ===== *)
      iIntros (M' vg4' vg5' vg6') "%HM'regs %HM'a5 Hcg Hcnt Hpay Hextc Hextm Hpc
                 Htok Hhalf Hiauth Hipool Hslots Hpool Href Hropen Hbms Hins Hbm
                 Hppid Hbslots Hlb Hcrd2 Hop Hr24 Hr16 Hr8 Hg4 Hg5 Hg6".
      (* the epoch is FORGOTTEN at the close arms' seam: [ip_tail] is stated
         over [log_opS] and nothing past this point compares epochs. *)
      iDestruct (log_opSe_opS with "Hop") as "Hop".
      iApply (ip_tail (CID := CIDacq) CID j bn g gfs gi cn gtl cov logstart bmapstart
                inodestart nib size dev used used Sb Sb k q inum Mt ci n n
                (fun w => ip_spend_w w cru crz) false crb pidv dq dqb dqs
                m M' K eb sp0 vg4' vg5' vg6' lks
                HK Hk ltac:(wp_next_chain) Hsp0eq HM'regs HM'a5 Hwf Hciwf
                ltac:(cbn; lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                ltac:(discriminate) ltac:(intros _; reflexivity) ltac:(lkbelow)
                with "Htext Hitab Hinv Hesc Hireg Hpc Hcg Hcnt Hpay Hextc Hextm Htok
                      Hhalf Hiauth Hipool Hslots Hpool Href Hru Hropen
                      Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 Hppid Hbms Hins Hbm
                      Hbslots Hop Hcont").
    - (* ===== EXIT B (+0x5a): the FREE path proper -- the locked block and,
         inside it, the off-lock tail.  The hand-over is shape-identical:
         everything Exit B produces is exactly [ip_free_locked]'s entry. ===== *)
      iIntros (M5 g1 dn bm data) "%Htyne %Hnl0 %Hdnwf %Hbmwf %Hdlen %Hadr
                 %Hspd5 %Ha05 %Hs15 %Hs25 %Hs35 %Hs45 %Hhi5
                 Hcg Hcnt Hpay Hextc Hextm Hpc Htok Hhalf Hiauth Hipool Hpool
                 %Hcik5 Hrtok Hgid Hwand Hpayl Hlvh Hpre Hrcpt Hmirt Hselo Hvb
                 Hbms Hins Hbm Hppid Hbslots Hlb Hcrd2 Hop
                 Hr24 Hr16 Hr8 Hg4 Hg5 Hg6".
      (* the frame, in the locked block's own [add_vec spd] spelling: the
         two are the same six addresses and the bridge is [pcw]. *)
      assert (Hf1 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      assert (Hf2 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      assert (Hf3 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      assert (Hf4 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      assert (Hf5 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      assert (Hf6 : add_vec spr (zero_extend' 64
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
      { unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
      iEval (rewrite -Hf1) in "Hr24". iEval (rewrite -Hf2) in "Hr16".
      iEval (rewrite -Hf3) in "Hr8".  iEval (rewrite -Hf4) in "Hg4".
      iEval (rewrite -Hf5) in "Hg5".  iEval (rewrite -Hf6) in "Hg6".
      iApply (ip_free_locked gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl g1
                cov logstart bmapstart inodestart nib size dev used
                k q inum dn bm data Mt ci n Sb crb cru crz false e0 0%nat
                pidv dq dqb dqs
                spr (m !!! Regidx Rra) (m !!! Regidx Rs0) (m !!! Regidx Rs1)
                (m !!! Regidx Rs2) (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                M5 K eb eb lks
                HK ltac:(lia) Hk ltac:(lia) Hcrb
                Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog Hnib
                Htyne Hnl0 Hdnwf Hbmwf Hcovb Hdlen Hadr Hwf Hciwf HMk Hj Hgsj
                Hspd5 Ha05 Hs15 Hs25 Hs35 Hs45 Hfresh Hitne
                with "Hcg Hcnt Hpay Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlogc
                      Hitab Hinv Hesc Htok Hhalf Hiauth Hipool Hpool [%] Hrtok
                      Hgid Hwand Hslk Hpayl Hlvh Hvb Hireg Hpre Hrcpt Hmirt Hselo
                      Hru Hbms Hins Hbm Hppid Hprocs Hdevi Hdgeom Hdlock Hbslots
                      Hnlz Hlb Hcrd2 Hop Hr24 Hr16 Hr8 Hg4 Hg5 Hg6 [-]").
      { exact Hcik5. }
      (* ===== the +0x30 seam: the shared epilogue, then iput's own post ==== *)
      iIntros (CIDoff Hstoff).
      iIntros (mf n'' used'' Sb'' w) "%Hthr Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins
                 %Husub Hbm Hbslots %Hssub %Hwbm %Hwc %Hbnd Hop Hiu Hgreg
                 Hr24 Hr16 Hr8 Hg4 Hg5 Hg6".
      destruct Hthr as (Hthr5 & Hmfsp & Hmfs2 & Hmfs3 & Hmfs4).
      iEval (rewrite Hf1) in "Hr24". iEval (rewrite Hf2) in "Hr16".
      iEval (rewrite Hf3) in "Hr8".  iEval (rewrite Hf4) in "Hg4".
      iEval (rewrite Hf5) in "Hg5".  iEval (rewrite Hf6) in "Hg6".
      iApply (ip_epilogue j mf K eb sp0 (m !!! Regidx Rra) (m !!! Regidx Rs0)
                (m !!! Regidx Rs1) (m !!! Regidx Rs2) (m !!! Regidx (mword_of_int 19 : mword 5))
                (m !!! Regidx (mword_of_int 20 : mword 5))
                ltac:(lia) Hmfsp
                with "Htext Hpc Hcg Hr24 Hr16 Hr8 Hg4 Hg5 Hg6").
      iIntros (CIDe Hse P4) "%Hep Hcg Hpc".
      destruct Hep as (HP4ra & HP4s0 & HP4s1 & HP4sp & HP4thr).
      assert (Hretf : ret_pc (m !!! Regidx Rra) = ret_tgt) by reflexivity.
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDoff CIDe 0%nat eb pj eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CIDoff CIDe eb pj
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDoff CIDe eb pj
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iSpecialize ("Hcont" $! CIDe with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! P4 n'' used'' Sb'' w
                with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins [%] Hbm Hbslots
                      [%] [%] [%] [%] Hop Hiu Hgreg").
      6:{ exact Hbnd. }
      5:{ exact Hwc. }
      4:{ exact Hwbm. }
      3:{ exact Hssub. }
      2:{ exact Husub. }
      (* callee_saved m P4: the epilogue restored ra/s0/s1 and popped sp; s2,
         s3 and s4 came back out of the frame at +0x30 and s5..s11 rode the
         whole free path untouched ([ipo_thr] plus Exit B's own high-register
         block, which is exactly what that block exists for). *)
      destruct Hhi5 as (Hq21 & Hq22 & Hq23 & Hq24 & Hq25 & Hq26 & Hq27).
      unfold callee_saved.
      repeat split;
        first [ exact HP4sp | exact HP4s0 | exact HP4s1
              | rewrite HP4thr;
                [ first [ exact Hmfs2 | exact Hmfs3 | exact Hmfs4
                        | rewrite Hthr5;
                          [ first [ exact Hq21 | exact Hq22 | exact Hq23
                                  | exact Hq24 | exact Hq25 | exact Hq26
                                  | exact Hq27 ]
                          | vm_compute; reflexivity
                          | nz | nz | nz | nz | nz ] ]
                | vm_compute; reflexivity | nz | nz | nz ] ].
  Qed.


  (* ===================================================================== *)
  (*  THE COUNTED SEAL, derived at the [log_op] existential's OWN WITNESS.  *)
  (*  [ip_spend_w w false false <= 2] and iput's own flush is the third unit*)
  (*  [iput_units] counts -- uncredited, the gen bound                      *)
  (*  [n - 2 <= n' <= n] is WEAKER than the landed [n - iput_units <= n'],  *)
  (*  so the seal's arithmetic goes the easy way and nothing is lost.       *)
  (* ===================================================================== *)
  Lemma wp_iput_sconf
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
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
    : wp_iput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                          cov logstart bmapstart inodestart nib size dev used
                          k q inum n pidv dq dqb dqs m K eb b lks.
  Proof.
    cbv beta delta [wp_iput_sconf_body].
    intros pcE ip pj ret_tgt HK Hk Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hcovb Hn Hj Hgsj Ha0 Hfresh.
    iIntros "Hcg Hcnt Hextc Hextm #Htext #Hkd Hpc #Hpenv #Hbio #Hlogc #Hitab #Hinv #Hesc #Hireg
             Hropen #Hslk Href Hru Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots Hop Hcont".
    (* THE WITNESS: the set the counted reservation was hiding, and the birth
       epoch it was hiding under it ([log_opS_named]).  Both are the gen
       contract's own existentials, so the seal derives with no new fact. *)
    iDestruct "Hop" as (Sb0) "Hop".
    iDestruct (log_opS_named with "Hop") as (e00) "Hop".
    iApply (wp_iput_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
              cov logstart bmapstart inodestart nib size dev used
              k q inum n Sb0 false false false e00 pidv dq dqb dqs m K eb b lks
              HK Hk ltac:(discriminate) ltac:(discriminate)
              Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
              Hnib Hcovb Hn Hj Hgsj Ha0 Hfresh
              with "Hcg Hcnt Hextc Hextm Htext Hkd Hpc Hpenv Hbio Hlogc Hitab Hinv Hesc Hireg
                    Hropen Hslk Href Hru Hbms Hins Hbm Hppid Hprocs Hdevi Hdgeom Hdlock Hbslots [] Hop
                    [Hcont]").
    all: try lkbelow.
    { iEval (cbn beta iota). iEmpIntro. }
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf n' used' Sb' wf) "%Hcs Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins
                               %Husub Hbm Hbslots %Hssub %Hwbm %Hwc %Hbnd Hop Hislot Hgreg".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf n' used' with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins
                     [%] Hbm Hbslots [%] [Hop] Hislot Hgreg").
    { exact Hcs. }
    { exact Husub. }
    { unfold ip_spend_w, ip_bm in Hbnd. unfold iput_units.
      destruct wf; simpl in Hbnd; lia. }
    { iApply (log_opS_op with "Hop"). }
  Qed.

End ProofIput.

End IputProof.
