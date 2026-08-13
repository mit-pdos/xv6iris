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
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FdSlots.
Require Import CodeIput.
Require Import SpecAcquire SpecRelease.
Require Import SpecAcquiresleep SpecReleasesleep.
Require Import SpecItrunc SpecIupdate.
Require Import SpecIput.
From Kernel Require KernelSyms.
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
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact C.
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

Module IputProof (Acquire : ACQUIRE) (Release : RELEASE)
                 (ASL : ACQUIRESLEEP) (RS : RELEASESLEEP)
                 (IT : ITRUNC) (IU : IUPDATE) : IPUT.

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz  := vm_compute; discriminate.

Section IputCommon.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

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
      `{GEN : GenId} `{CID : CpuId} (p : mword 64) (C : iProp Σ) :
    sie_cap_gpr m K0 b p -∗ cpu_own n eb p C b -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "[%Hb _]". destruct Hb as [-> ->]. done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[[_ Hint] _]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm) & _)".
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
    rewrite /itable_half /iref_tok /iref_frag. iIntros "Ha [Hf _]".
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
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.

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
  Lemma ip_tail_exit `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (j : nat) (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used' Sb Sb' : gset Z)
      (k n n' spmax : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m D : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 vg4 : mword 64) :
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx Rra) in
    let spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (K_iput <= K)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp0 = m !!! Regidx csp_rs1 ->
    iput_regs m D spd k ->
    ((n - spmax)%nat <= n')%nat ->
    (n' <= n)%nat ->
    used' ⊆ used ->
    Sb ⊆ Sb' ->
    kernel_text -∗
    is_lock gtl itable_lock "itable"%string
      (itable_res2 cn gfs gi cov logstart nib dev) -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x26) : mword 64) -∗
    sie_cap_gpr D (trap_res eb + (K - 4))%nat false pj -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    (* the trap-CSR complement: a PURE PASS-THROUGH, threaded from the
       caller's own entry straight to release's continuation -- iput never
       itself needs the bare pair, since every one of its sleeping callees
       (acquiresleep_nested excepted -- it never parks) takes the complement
       directly.  See claude-notes/projects/eb-generic-sweep.md. *)
    trap_csrs_ext eb -∗
    cpu_claim_ext eb pj -∗
    locked gtl cpu_id -∗
    itable_res2 cn gfs gi cov logstart nib dev -∗
    iref_slot -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈ vg4 -∗
    p_pid pj ↦₄{dq} pidv -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used' -∗
    bslots bn 3 -∗
    log_opS g n' Sb' -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K eb pj -∗
        cpu_own 0 eb pj C eb -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb pj -∗
        pc_is ret_tgt -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used'' -∗
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜((n - spmax)%nat <= n'')%nat /\ (n'' <= n)%nat⌝ -∗
        log_opS g n'' Sb'' -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj ret_tgt spd HK Hanch Hsp0 Hregs Hlo Hhi Hsub Hssub.
    unfold K_iput in HK.
    destruct Hregs as (HDs1 & HDsp & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok HRres Hislot
             Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm Hbslots Hop Hcont".
    iPoseProof (ipi_26 with "Htext") as "Hi26".
    iPoseProof (ipi_2a with "Htext") as "Hi2a".
    iPoseProof (ipi_2e with "Htext") as "Hi2e".
    iPoseProof (ipi_32 with "Htext") as "Hi32".
    iPoseProof (ipi_34 with "Htext") as "Hi34".
    iPoseProof (ipi_36 with "Htext") as "Hi36".
    iPoseProof (ipi_38 with "Htext") as "Hi38".
    iPoseProof (ipi_3a with "Htext") as "Hi3a".
    (* the four saved-slot addresses, in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spd, pa_stk, add_vec_int. rewrite add_vec_off2. apply f_equal. pcw. }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    (* ===== +0x26 / +0x2a : a0 := &itable ; +0x2e jal release ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x26)) Ra0
              (mword_of_int 29 : mword 20) D (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x26) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> D).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iput + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x2a)) Ra0 Ra0
              (mword_of_int 1330 : mword 12) D3 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (D3 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1330 : mword 12)))]> D3).
    assert (HD4a0 : D4 !!! Regidx Ra0 = itable_lock).
    { rewrite /D4 upd_eq /D3 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iput + 0x2a) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x2e)) Rra
              (mword_of_int 2087068 : mword 21) D4 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x2e) : mword 64) 4)]> D4).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.iput + 0x2e) : mword 64)
                        (sign_extend' 64 (mword_of_int 2087068 : mword 21))
                      = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HD5a0 : D5 !!! Regidx Ra0 = itable_lock)
      by (rewrite /D5 upd_ne; [exact HD4a0 | nz]).
    assert (HD5ra : D5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x2e) : mword 64) 4)
      by (rewrite /D5; apply upd_eq).
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true ->
                       D5 !!! Regidx c = D !!! Regidx c).
    { intros c Hcs.
      rewrite /D5 upd_ne; [| regne].
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [reflexivity | regne]. }
    assert (HD5sp : D5 !!! Regidx csp_rs1 = spd)
      by (rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HDsp).
    iApply (Release.wp_release_sconf gtl itable_lock "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) D5
              0%nat eb pj C (K - 4)%nat
              ltac:(rewrite HD5a0; reflexivity) ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
    pose proof Hrelpins as Hrelpins_cs.
    assert (Hpc32 : ret_pc (D5 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x32))
      by (rewrite HD5ra; pcw).
    iEval (rewrite Hpc32) in "Hpc".
    (* ===== EPILOGUE (index [true]) ===== *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spd)
      by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HD5sp).
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x32))
              (mword_of_int 3 : mword 6) Rra mr (K - 4)%nat (m !!! Regidx Rra) eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32 [Hr24]").
    { iEval (rewrite Hmrsp). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite Hmrsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra)]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1 upd_ne; [exact Hmrsp | nz]).
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.iput + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x34)) by pcw.
    iEval (rewrite Hpp34) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x34))
              (mword_of_int 2 : mword 6) Rs0 P1 (K - 4)%nat (m !!! Regidx Rs0) eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi34 [Hr16]").
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spd)
      by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.iput + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x36))
              (mword_of_int 1 : mword 6) Rs1 P2 (K - 4)%nat (m !!! Regidx Rs1) eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi36 [Hr8]").
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spd)
      by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.iput + 0x36) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x38)) by pcw.
    iEval (rewrite Hpp38) in "Hpc".
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HP3sp. unfold spd. apply frame_cancel_32. }
    assert (Hpop : P3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp. unfold spd, pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iput + 0x38))
              (mword_of_int 2 : mword 6) P3 (K - 4)%nat 4 eb Hpop
              with "Hcg Hpc Hi38 Hframe4").
    iIntros (CIDe4 Hse4) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.iput + 0x38) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = m !!! Regidx Rra).
    { rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_ne; [| nz].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iput + 0x3a)) Rra P4 K eb
              ltac:(nz) with "Hcg Hpc Hi3a").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra) = ret_tgt) by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    iDestruct (cpu_own_transport CIDr CIDe5 0%nat eb pj C eb
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
    iApply ("Hcont" $! P4 n' used' Sb'
              with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins [%] Hbm Hbslots [%] [%] Hop Hislot").
    4:{ split; [exact Hlo | exact Hhi]. }
    3:{ exact Hssub. }
    2:{ exact Hsub. }
    (* callee_saved m P4 *)
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              P4 !!! Regidx c = D !!! Regidx c).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      exact (HD5thr c Hcs). }
    unfold callee_saved.
    assert (Hc2 : P4 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { rewrite /P4 upd_eq. rewrite HP3sp. unfold regval_into_reg, spd.
      rewrite Hsp0. apply frame_cancel_32. }
    assert (Hc8 : P4 !!! Regidx Rs0 = m !!! Regidx Rs0).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Hc9 : P4 !!! Regidx Rs1 = m !!! Regidx Rs1).
    { rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
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
      (n n' spmax : nat)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 vg4 : mword 64) :
    let pj := proc_addr j in
    let ret_tgt := ret_pc (m !!! Regidx Rra) in
    let spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (K_iput <= K)%nat ->
    (k < NINODE)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    sp0 = m !!! Regidx csp_rs1 ->
    iput_regs m M spd k ->
    icM_wf Mt ->
    ic_ci_wf Mt ci nib dev ->
    ((n - spmax)%nat <= n')%nat ->
    (n' <= n)%nat ->
    used' ⊆ used ->
    Sb ⊆ Sb' ->
    kernel_text -∗
    is_lock gtl itable_lock "itable"%string
      (itable_res2 cn gfs gi cov logstart nib dev) -∗
    itable_inv -∗
    ic_escrow cn gfs gi cov logstart k -∗
    pc_is (mword_of_int (KernelSyms.iput + 0x20) : mword 64) -∗
    sie_cap_gpr M (trap_res eb + (K - 4))%nat false pj -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    (* pure pass-through, exactly as in [ip_tail_exit] above *)
    trap_csrs_ext eb -∗
    cpu_claim_ext eb pj -∗
    locked gtl cpu_id -∗
    itable_half Mt -∗
    iref_slots_auth -∗
    ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn Mt ci i0) -∗
    ipool gfs gi cov logstart (region_inums nib ∖ ci_inums ci) -∗
    IcacheRef.inode_ref k q dev inum -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx Rra) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx Rs0) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx Rs1) -∗
    pa_stk sp0 4 ↦₈ vg4 -∗
    p_pid pj ↦₄{dq} pidv -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used' -∗
    bslots bn 3 -∗
    log_opS g n' Sb' -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (n'' : nat) (used'' Sb'' : gset Z),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K eb pj -∗
        cpu_own 0 eb pj C eb -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb pj -∗
        pc_is ret_tgt -∗
        p_pid pj ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        ⌜used'' ⊆ used⌝ -∗
        bitmap_res gfs bmapstart cov logstart size used'' -∗
        bslots bn 3 -∗
        ⌜Sb ⊆ Sb''⌝ -∗
        ⌜((n - spmax)%nat <= n'')%nat /\ (n'' <= n)%nat⌝ -∗
        log_opS g n'' Sb'' -∗
        iref_slot -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj ret_tgt spd HK Hk Hanch Hsp0 Hregs Hwf Hciwf Hlo Hhi Hsub Hssub.
    pose proof HK as HK'. unfold K_iput in HK'.
    pose proof Hregs as Hregs0.
    destruct Hregs as (HMs1 & HMsp & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlock #Hinv #Hesc Hpc Hcg Hcnt Hpay Hextc Hextm Htok
             Hhalf Hiauth Hslots Hpool Href Hr24 Hr16 Hr8 Hg4
             Hppid Hbms Hins Hbm Hbslots Hop Hcont".
    iPoseProof (ipi_20 with "Htext") as "Hi20".
    iPoseProof (ipi_22 with "Htext") as "Hi22".
    iPoseProof (ipi_24 with "Htext") as "Hi24".
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
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
    iDestruct (ip_rest_sum with "Hrest") as %[qr Hsum].
    iAssert (⌜cdev = dev /\ cinum = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - qt)%Qp as [q'|] eqn:Et; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    assert (Ert : (1/2 - qt)%Qp = Some qr) by (apply Qp.sub_Some; exact Hsum).
    assert (Hqthalf : (qt ≤ 1/2)%Qp) by (rewrite Hsum; apply Qp.le_add_l).
    assert (Hiw : iref_word Mt k = (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /iref_word HMk; reflexivity).
    (* ===== +0x20 c.lw a5,8(s1) : the ATOMIC-UPDATE read ===== *)
    assert (Hpa : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                  = i_ref (ientry k)).
    { rewrite (rget_ne M Rs1 ltac:(nz)) HMs1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x20)) Ra5 Rs1
              (mword_of_int 8 : mword 12) M (trap_res eb + (K - 4))%nat
              (fun v => (⌜v = iref_word Mt k⌝ ∗ itable_half Mt)%I)
              (⊤ ∖ ↑minstretN ∖ ↑icacheN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi20 [Hhalf]").
    { rewrite Hpa.
      iMod (iref_load_locked_au (⊤ ∖ ↑minstretN) Mt k
              ltac:(solve_ndisj) Hk with "Hinv Hhalf") as "[Hcell Hback2]".
      iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
      iMod ("Hback2" with "Hcell") as "Hhalf". iModIntro. by iFrame. }
    iIntros (vld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc [%Hvld Hhalf]".
    subst vld. iEval (rewrite Hiw) in "Hcg".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> M).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /D1; apply upd_eq).
    assert (HD1s1 : D1 !!! Regidx Rs1 = ientry k)
      by (rewrite /D1 upd_ne; [exact HMs1 | nz]).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.iput + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.addiw a5,a5,-1 ===== *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.iput + 0x22)) Ra5
              (mword_of_int 63 : mword 6) D1 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (D1 !!! Regidx Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> D1).
    assert (HD2s1 : D2 !!! Regidx Rs1 = ientry k)
      by (rewrite /D2 upd_ne; [exact HD1s1 | nz]).
    assert (HD2regs : iput_regs m D2 spd k).
    { unfold iput_regs in Hregs0 |- *.
      destruct Hregs0 as (A&B&Cc&E&F&G&H&I&J&L&N&O).
      repeat split;
        (rewrite /D2 upd_ne; [| nz]); (rewrite /D1 upd_ne; [| nz]); assumption. }
    assert (Hstv : trunc32 (rget D2 Ra5) = (mword_of_int (Z.pos cnt - 1) : mword 32)).
    { rewrite (rget_ne D2 Ra5 ltac:(nz)).
      rewrite /D2 upd_eq. unfold regval_into_reg. rewrite HD1a5.
      exact (ip_storeval_pred (Z.pos cnt) ltac:(lia) ltac:(lia)). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.iput + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    assert (Hpa2 : add_vec (rget D2 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = i_ref (ientry k)).
    { rewrite (rget_ne D2 Rs1 ltac:(nz)) HD2s1. reflexivity. }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.iput + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x26)) by pcw.
    (* ===== +0x24 c.sw a5,8(s1) : THE CLOSE, split on the count ===== *)
    destruct (decide (cnt = 1%positive)) as [->|Hnotone].
    - (* ---- THE LAST CLOSE: REF-1, and the EVICTION (§13.9) ---- *)
      specialize (Hone eq_refl). subst q.
      (* the eviction runs BEFORE the store: [ic_open_auth_ref] wants the
         authority still showing the slot, and the store deletes it. *)
      iApply fupd_wp.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_auth_ref cn gfs gi cov logstart k (⊤ ∖ ↑icEscN)
              Mt qt qt dev inum ltac:(solve_ndisj) HMk
              with "Hinv Hbody Hhalf Hrtok Hrident")
        as "(Hhalf & Hrtok & Hrident & Harm & _)".
      iDestruct "Harm" as (v ga) "(Hidv & Hinv2 & Hvld & Hpayl & Hlvh & Hmt & Hgida)".
      iDestruct (islot_rest_join k qt dev inum Hqthalf with "Hrident [Hrest]")
        as "[Hdh Hinh]".
      { rewrite /islot_rest. iExists dev, inum. iExact "Hrest". }
      iMod (ic_close_to_empty cn gfs gi cov logstart k v ga dev inum
              with "Hgida Hgid Hidv Hdh Hinv2 Hvld Hpayl Hmt")
        as "(Hbody & Hgidf & Hbundle)".
      iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
      iModIntro.
      assert (Hinreg : bv_unsigned inum ∈ region_inums nib).
      { apply region_inums_spec. split; [apply bv_unsigned_in_range |].
        destruct Hciwf as (_ & _ & Hrange & _).
        exact (Hrange k (dev, inum) Hcik). }
      assert (Hincid : bv_unsigned inum ∈ ci_inums ci).
      { apply ci_inums_spec. exists k, (dev, inum). split; [exact Hcik | reflexivity]. }
      iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x24)) Ra5 Rs1
                (mword_of_int 8 : mword 12) D2 (trap_res eb + (K - 4))%nat
                (itable_half (delete k Mt))
                (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(solve_ndisj)
                with "Hcg Hpc Hi24 [Hhalf Hrtok Hlvh]").
      { rewrite Hpa2 Hstv.
        replace (Z.pos 1 - 1)%Z with 0%Z by lia.
        (* THE RETIREMENT, under the restated ledger (design 17.3 (A)): the
           closer's own [qt], the invariant's [1/2 - qt] AND the arm's 1/2 --
           which the eviction has just taken out of PARKED -- are together
           the slot's whole unit. *)
        iMod (iref_close_last_store_au (⊤ ∖ ↑minstretN) Mt k qt
                ltac:(solve_ndisj) HMk with "Hinv Hhalf Hrtok [Hlvh]")
          as "[Hcell Hback2]".
        { iExists ga. iExact "Hlvh". }
        iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
        iMod ("Hback2" with "Hcell") as "Hhalf". by iModIntro. }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hhalf".
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
      assert (Hp1 : Pos.to_nat 1 = 1%nat) by reflexivity.
      iEval (rewrite Hp1) in "Hiu".
      iApply (ip_tail_exit CID0 j bn g gfs gi cn gtl cov logstart bmapstart inodestart
                nib size dev used used' Sb Sb' k n n' spmax pidv dq dqb dqs m D2 K eb C sp0 vg4
                HK Hanch Hsp0 HD2regs Hlo Hhi Hsub Hssub
                with "Htext Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok [-Hiu Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm Hbslots Hop Hcont] Hiu
                      Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm Hbslots Hop Hcont").
      iExists (delete k Mt), (delete k ci). iFrame "Hhalf Hiauth Hslots Hpool".
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
      assert (Hzs : (Z.pos cnt - 1)%Z = Z.pos npred).
      { rewrite /npred. rewrite <- Hsucc at 1. rewrite Pos2Z.inj_succ. lia. }
      pose proof Hqrest as Hqt'. apply Qp.sub_Some in Hqt'.  (* qt = q + qrest *)
      iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x24)) Ra5 Rs1
                (mword_of_int 8 : mword 12) D2 (trap_res eb + (K - 4))%nat
                (itable_half (<[k := (qrest, npred)]> Mt))
                (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(solve_ndisj)
                with "Hcg Hpc Hi24 [Hhalf Hrtok]").
      { rewrite Hpa2 Hstv Hzs.
        iMod (iref_close_store_au (⊤ ∖ ↑minstretN) Mt k q qt qrest npred
                ltac:(solve_ndisj) HMk' Hqrest with "Hinv Hhalf Hrtok") as "[Hcell Hback2]".
        iModIntro. iExists (iref_word Mt k). iFrame "Hcell". iIntros "Hcell".
        iMod ("Hback2" with "Hcell") as "Hhalf". by iModIntro. }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hhalf".
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
      iDestruct ("Hback" $! (<[k := (qrest, npred)]> Mt) ci
                   with "[%] [%] [Hrest Hiu Hgid]") as "Hslots".
      { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
      { intros i Hi. reflexivity. }
      { rewrite /islot2 lookup_insert Hcik. iFrame. }
      iApply (ip_tail_exit CID0 j bn g gfs gi cn gtl cov logstart bmapstart inodestart
                nib size dev used used' Sb Sb' k n n' spmax pidv dq dqb dqs m D2 K eb C sp0 vg4
                HK Hanch Hsp0 HD2regs Hlo Hhi Hsub Hssub
                with "Htext Hlock Hpc Hcg Hcnt Hpay Hextc Hextm Htok [-Hislot Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm Hbslots Hop Hcont] Hislot
                      Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm Hbslots Hop Hcont").
      iExists (<[k := (qrest, npred)]> Mt), ci. iFrame "Hhalf Hiauth Hslots Hpool".
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
(*  4.  THE FUNCTION                                                      *)
(* ===================================================================== *)

Section ProofIput.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
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
      (n : nat) (Sb : gset Z) (crb cru : bool)
      (pidv : mword 32) (dq dqb dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_iput_gen_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                       cov logstart bmapstart inodestart nib size dev used
                       k q inum n Sb crb cru pidv dq dqb dqs m K eb C b.
  Proof.
    cbv beta delta [wp_iput_gen_body].
    intros pcE ip pj ret_tgt HK Hk Hcrb Hcru Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hcovb Hn Hj Hgsj Ha0.
    pose proof HK as HK'. unfold K_iput in HK'.
    unfold iput_units in Hn.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlogc #Hitab #Hinv #Hesc #Hireg #Hslk
             Href Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots Hop Hcont".
    (* iput enters at level 0, so the live index and the saved base agree;
       keep BOTH names alive as [Hbm], then [subst b] -- unlike the
       [dirlookup]/[namex]-style scaffolding, [b] is not spelled by name
       anywhere below (the whole function used the literal [true] until
       this edit), so nothing downstream breaks, and everything from here
       on reads at the single surviving name [eb].  ([ProofBeginOp.v] is
       the worked example of this exact move.) *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm. cbn in Hbm. subst b.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
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
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 eb
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 eb with "Hcg Hpc Hi02 Hr24").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iput + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 eb with "Hcg Hpc Hi04 Hr16").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iput + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 eb with "Hcg Hpc Hi06 Hr8").
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
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iput + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iput + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iput + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.iput + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat eb ltac:(nz) ltac:(rdok)
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
              R3 (K - 4)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.iput + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.iput + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x10)) Ra0 Ra0 (mword_of_int 1356 : mword 12)
              R4 (K - 4)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 1356 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = itable_lock).
    { rewrite /R5 upd_eq /R4 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.iput + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.iput + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x14)) Rra (mword_of_int 2086958 : mword 21)
              R5 (K - 4)%nat eb ltac:(nz) ltac:(rdok)
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
    iDestruct (cpu_own_transport CID CID9 0%nat eb pj C eb ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf gtl "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) mA
              0%nat eb pj C (K - 4)%nat eb
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hitab] Hpanic").
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
    iDestruct "HRres" as (Mt ci) "(Hhalf & %Hwf & %Hciwf & Hiauth & Hslots & Hpool)".
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
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x18)) Ra4 Rs1
              (mword_of_int 8 : mword 12) macq (trap_res eb + (K - 4))%nat
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
    set (E1 := <[Regidx Ra4 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))]> macq).
    assert (HE1a4 : E1 !!! Regidx Ra4 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /E1; apply upd_eq).
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.iput + 0x18) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.iput + 0x1a)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              E1 (trap_res eb + (K - 4))%nat false ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi1a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (E2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> E1).
    assert (HE2a4 : E2 !!! Regidx Ra4 = sign_extend' 64 (mword_of_int (Z.pos cnt) : mword 32))
      by (rewrite /E2 upd_ne; [exact HE1a4 | nz]).
    assert (HE2a5 : E2 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
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
    assert (Hcmp : eq_vec (rget E2 Ra4) (rget E2 Ra5)
                   = (if decide (cnt = 1%positive) then true else false)).
    { rewrite (rget_ne E2 Ra4 ltac:(nz)) (rget_ne E2 Ra5 ltac:(nz)) HE2a4 HE2a5.
      apply ip_cnt_eq_one. lia. }
    assert (Hsp0eq : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iPoseProof (ipi_1c with "Htext") as "Hi1cb".
    destruct (decide (cnt = 1%positive)) as [Hcone|Hcnone]; last first.
    { (* ---- ref != 1: fall through straight into the tail ---- *)
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x1c))
                (mword_of_int 32 : mword 13) Ra5 Ra4 E2 (trap_res eb + (K - 4))%nat false
                ltac:(nz) ltac:(nz) Hcmp with "Hcg Hpc Hi1cb").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.iput + 0x1c) : mword 64) 4
                      = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20) in "Hpc".
      iApply (ip_tail (CID := CIDacq) CID j bn g gfs gi cn gtl cov logstart bmapstart
                inodestart nib size dev used used Sb Sb k q inum Mt ci n n
                (ip_spend_max crb cru) pidv dq dqb dqs
                m E2 K eb C sp0 vg4
                HK Hk ltac:(wp_next_chain) Hsp0eq HE2regs Hwf Hciwf
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                with "Htext Hitab Hinv Hesc Hpc Hcg Hcnt Hpay Hextc Hextm Htok Hhalf Hiauth Hslots
                      Hpool [Hrtok Hrident] Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm
                      Hbslots Hop Hcont").
      rewrite /IcacheRef.inode_ref. iFrame. }

    (* ---- ref == 1: the branch to +0x3c, and the WINDOW (§13.13) ---- *)
    subst cnt. specialize (Hone eq_refl). subst qt.
    iPoseProof (ipi_3c with "Htext") as "Hi3c".
    iPoseProof (ipi_3e with "Htext") as "Hi3e".
    iPoseProof (ipi_40 with "Htext") as "Hi40".
    iPoseProof (ipi_44 with "Htext") as "Hi44".
    iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x1c))
              (mword_of_int 32 : mword 13) Ra5 Ra4 E2 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(nz) Hcmp ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1cb").
    iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp3c : add_vec (mword_of_int (KernelSyms.iput + 0x1c) : mword 64)
                      (sign_extend' 64 (mword_of_int 32 : mword 13))
                    = mword_of_int (KernelSyms.iput + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* the slot's own share comes out of the lock's big-op *)
    assert (Hcik : exists di : mword 32 * mword 32, ci !! k = Some di).
    { destruct Hciwf as [Hdom _].
      assert (Hin : k ∈ dom ci) by (rewrite Hdom; apply elem_of_dom; by eexists).
      apply elem_of_dom in Hin. exact Hin. }
    destruct Hcik as [[cdev cinum] Hcik].
    iDestruct (islots2_acc_upd cn Mt ci k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /islot2 HMk Hcik) in "Hslot".
    iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
    iDestruct (ip_rest_sum with "Hrest") as %[qr Hsum].
    iAssert (⌜cdev = dev /\ cinum = inum⌝)%I as %[-> ->].
    { iEval (rewrite /islot_rest_at) in "Hrest".
      destruct (1/2 - q)%Qp as [q'|] eqn:Et; [| iDestruct "Hrest" as "[]"].
      iApply (inode_ident_agree with "Hrest Hrident"). }
    assert (Ert : (1/2 - q)%Qp = Some qr) by (apply Qp.sub_Some; exact Hsum).
    assert (HE2s1 : E2 !!! Regidx Rs1 = ientry k).
    { rewrite /E2 upd_ne; [| nz]. rewrite /E1 upd_ne; [exact Hms1 | nz]. }
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2 upd_ne; [| nz]. rewrite /E1 upd_ne; [exact Hmsp | nz]. }
    (* ===== +0x3c c.lw a5,64(s1) : the read that ENTERS the window ===== *)
    assert (Hpa3c : add_vec (rget E2 Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne E2 Rs1 ltac:(nz)) HE2s1. reflexivity. }
    iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iput + 0x3c)) Ra5 Rs1
              (mword_of_int 64 : mword 12) E2 (trap_res eb + (K - 4))%nat
              (fun w => (∃ v : bool, ⌜w = valid_word v⌝ ∗
                  itable_half Mt ∗ iref_tok k q ∗
                  (if v
                   then i_dev (ientry k) ↦₄{DfracOwn q} dev ∗
                        i_dev (ientry k) ↦₄{DfracOwn qr} dev ∗
                        i_valid (ientry k) ↦₄{DfracOwn (1/2)} (valid_word true) ∗
                        (∃ ga : gname,
                           ic_payload gfs gi cov logstart k inum ga true ∗
                           live_gen k (1/2) ga)
                   else IcacheRef.inode_ident k (DfracOwn q) dev inum ∗
                        islot_rest_at k q dev inum))%I)
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) false
              ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
              with "Hcg Hpc Hi3c [Hhalf Hrtok Hrident Hrest]").
    { rewrite Hpa3c.
      iInv "Hesc" as ">Hbody" "Hclose".
      iMod (ic_open_auth_ref cn gfs gi cov logstart k
              (⊤ ∖ ↑minstretN ∖ ↑icEscN) Mt q q dev inum
              ltac:(solve_ndisj) HMk with "Hinv Hbody Hhalf Hrtok Hrident")
        as "(Hhalf & Hrtok & Hrident & Harm & _)".
      (* the window arm holds NO liveness slice (design 17.3 (A) as built):
         it is iput's own exclusive window between two stores, and the 1/2
         rides in iput's hand across it, exactly as the recycler's does
         across MID. *)
      iDestruct "Harm" as (v ga) "(Hidv & Hinh & Hvld & Hpayl & Hlvh & Hmt & Hgida)".
      iModIntro. iExists (valid_word v). iFrame "Hvld". iIntros "Hvld".
      destruct v.
      - (* LOADED: the payload leaves with us; the cells stay, inum FULL *)
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
        iModIntro. iExists true. iFrame "Hhalf Hrtok Hrd Htd Hvb".
        iSplitR; [done |]. iExists ga. iFrame.
      - (* UNLOADED: read-only, everything goes straight back *)
        iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida]") as "_".
        { iApply bi.later_intro. iApply ic_close_parked.
          iApply (ic_mk_parked cn gfs gi cov logstart k dev inum false ga
                    with "Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida"). }
        iModIntro. iExists false. iFrame. done. }
    iIntros (wvld).
    iApply wp_next_off_intro. iIntros "Hcg Hpc HPsi".
    iDestruct "HPsi" as (vv) "(%Hwv & Hhalf & Hrtok & Hrem)".
    subst wvld.
    set (F1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (valid_word vv))]> E2).
    assert (HF1a5 : F1 !!! Regidx Ra5 = (sign_extend' 64 (valid_word vv) : mword 64))
      by (rewrite /F1; apply upd_eq).
    assert (HF1s1 : F1 !!! Regidx Rs1 = ientry k)
      by (rewrite /F1 upd_ne; [exact HE2s1 | nz]).
    assert (HF1regs : iput_regs m F1 spr k).
    { unfold iput_regs in HE2regs |- *.
      destruct HE2regs as (A&B&Cc&Ee&F&G&H&I&Jj&L&N&O).
      repeat split; (rewrite /F1 upd_ne; [| nz]); assumption. }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.iput + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x3e c.beqz a5 : !valid goes to the tail ===== *)
    destruct vv.
    2:{ (* valid == 0 : the window was never entered *)
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x3e))
                (mword_of_int 241 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                F1 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF1a5; exact (ip_valid_beqz false))
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3e").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20b : add_vec (mword_of_int (KernelSyms.iput + 0x3e) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 241 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20b) in "Hpc".
      iDestruct "Hrem" as "[Hrident Hrest]".
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Hrest Hiu Hgid]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk Hcik. iFrame. }
      iApply (ip_tail (CID := CIDacq) CID j bn g gfs gi cn gtl cov logstart bmapstart
                inodestart nib size dev used used Sb Sb k q inum Mt ci n n
                (ip_spend_max crb cru) pidv dq dqb dqs
                m F1 K eb C sp0 vg4
                HK Hk ltac:(wp_next_chain) Hsp0eq HF1regs Hwf Hciwf
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                with "Htext Hitab Hinv Hesc Hpc Hcg Hcnt Hpay Hextc Hextm Htok Hhalf Hiauth Hslots
                      Hpool [Hrtok Hrident] Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm
                      Hbslots Hop Hcont").
      rewrite /IcacheRef.inode_ref. iFrame. }
    (* ===== valid == 1: fall through, WITH the payload in hand ===== *)
    iDestruct "Hrem" as "(Hrd & Htd & Hvb & (%ga & Hpayl & Hlvh))".
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x3e))
              (mword_of_int 241 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              F1 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF1a5; exact (ip_valid_beqz true))
              with "Hcg Hpc Hi3e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.iput + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* the loaded bundle, opened: [i_nlink] is one of its five scalars *)
    iEval (rewrite /ic_payload) in "Hpayl".
    (* the LOADED polarity's type witness (design §17.6 (1)) rides out with
       the bundle; both re-park sites below hand it straight back, and on the
       free path it dies with the generation [live_slot_regen] retires. *)
    iDestruct "Hpayl" as (dn bm) "[Hlk #Hshot]".
    iDestruct "Hlk" as (data)
      "(%Hok & %Hdok & Hdlk & Hdat & Hmeta & Haddrs & Hind & Hblks)".
    pose proof Hok as Hok'.
    destruct Hok' as (Hbmwf & Hcovers & Hdiaddrs & Htyne & Hszcap & Hholes & Hsized).
    iEval (rewrite /inode_meta) in "Hmeta".
    iDestruct "Hmeta" as "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    (* ===== +0x40 lh a5,74(s1) : nlink, a PLAIN read now ===== *)
    assert (Hpa40 : add_vec (rget F1 Rs1) (sign_extend' 64 (mword_of_int 74 : mword 12))
                    = i_nlink (ientry k)).
    { rewrite (rget_ne F1 Rs1 ltac:(nz)) HF1s1. reflexivity. }
    iEval (rewrite -Hpa40) in "Hmnl".
    iApply (wp_lh_s_sconf (mword_of_int (KernelSyms.iput + 0x40)) Ra5 Rs1
              (mword_of_int 74 : mword 12) F1 (trap_res eb + (K - 4))%nat (di_nlink dn) false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi40 Hmnl").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hmnl".
    iEval (rewrite Hpa40) in "Hmnl".
    set (F2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (di_nlink dn : mword 16))]> F1).
    assert (HF2a5 : F2 !!! Regidx Ra5 = (sign_extend' 64 (di_nlink dn : mword 16) : mword 64))
      by (rewrite /F2; apply upd_eq).
    assert (HF2s1 : F2 !!! Regidx Rs1 = ientry k)
      by (rewrite /F2 upd_ne; [exact HF1s1 | nz]).
    assert (HF2regs : iput_regs m F2 spr k).
    { unfold iput_regs in HF1regs |- *.
      destruct HF1regs as (A&B&Cc&Ee&F&G&H&I&Jj&L&N&O).
      repeat split; (rewrite /F2 upd_ne; [| nz]); assumption. }
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.iput + 0x40) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x44)) by pcw.
    iEval (rewrite Hpp44) in "Hpc".
    (* ===== +0x44 c.bnez a5 : nlink != 0 UNDOES the window ===== *)
    destruct (neq_vec (sign_extend' 64 (di_nlink dn : mword 16) : mword 64) (zero_reg : mword 64))
      eqn:Hnl0.
    { (* nlink != 0 : close the window back at PARKED and take the tail.
         There is no [acquiresleep] here, which is why the window's
         credential is REF-1 and not the checkout token. *)
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.iput + 0x44))
                (mword_of_int 238 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                F2 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HF2a5; exact Hnl0)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi44").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp20c : add_vec (mword_of_int (KernelSyms.iput + 0x44) : mword 64)
                         (sign_extend' 64 (sign_extend' 13
                            (concat_vec (mword_of_int 238 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
      iEval (rewrite Hpp20c) in "Hpc".
      iApply fupd_wp.
      iInv "Hesc" as ">Hbody" "Hclose".
      (* THE nlink UNDO TAKES NO BUMP (design §17.6 (3)): nothing is retyped
         on this path, the loaded payload and its shot go straight back into
         PARKED, and the two gnames [ic_open_held] now takes are equal. *)
      iAssert (ic_payload_at gfs gi cov logstart k inum ga dn bm)
        with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
      { rewrite /ic_payload_at.
        iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
        iSplitR; [iPureIntro; exact Hok |].
        iSplitR; [iPureIntro; exact Hdok |].
        iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
      iMod (ic_open_held cn gfs gi cov logstart k (⊤ ∖ ↑icEscN)
              Mt q ga ga dev inum dn bm ltac:(solve_ndisj) HMk
              with "Hinv Hbody Hhalf Hrtok Hlvh Hgid Hpayl")
        as "(Hhalf & Hrtok & Hlvh & Hgid & Hpayl & Hidv & Hnfull & Hvldx & Hmt & Hgida)".
      iDestruct (ic_payload_at_pack with "Hpayl") as "Hpayl".
      iDestruct "Hvldx" as (w0) "Hva".
      iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
      iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
      (* the FULL inum cell splits back: the arm's half, our q, the table's qr *)
      iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hn2]".
      iEval (rewrite Hsum) in "Hn2".
      iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
        as "[Hrn Htn]".
      iMod ("Hclose" with "[Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida]") as "_".
      { iApply bi.later_intro. iApply ic_close_parked.
        iApply (ic_mk_parked cn gfs gi cov logstart k dev inum true ga
                  with "Hidv Hinh Hvld Hpayl Hlvh Hmt Hgida"). }
      iModIntro.
      iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid]") as "Hslots";
        [ intros i Hi; reflexivity | intros i Hi; reflexivity | | ].
      { rewrite /islot2 HMk Hcik. rewrite /islot_rest_at Ert /IcacheRef.inode_ident.
        iFrame. }
      iApply (ip_tail (CID := CIDacq) CID j bn g gfs gi cn gtl cov logstart bmapstart
                inodestart nib size dev used used Sb Sb k q inum Mt ci n n
                (ip_spend_max crb cru) pidv dq dqb dqs
                m F2 K eb C sp0 vg4
                HK Hk ltac:(wp_next_chain) Hsp0eq HF2regs Hwf Hciwf
                ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                with "Htext Hitab Hinv Hesc Hpc Hcg Hcnt Hpay Hextc Hextm Htok Hhalf Hiauth Hslots
                      Hpool [Hrtok Hrd Hrn] Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm
                      Hbslots Hop Hcont").
      rewrite /IcacheRef.inode_ref /IcacheRef.inode_ident. iFrame. }

    (* ===== nlink == 0: TRUNCATE.  +0x44 falls through ===== *)
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.iput + 0x44))
              (mword_of_int 238 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              F2 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rgne; rewrite HF2a5; exact Hnl0)
              with "Hcg Hpc Hi44").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.iput + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    iPoseProof (ipi_46 with "Htext") as "Hi46".
    iPoseProof (ipi_48 with "Htext") as "Hi48".
    iPoseProof (ipi_4c with "Htext") as "Hi4c".
    iPoseProof (ipi_4e with "Htext") as "Hi4e".
    iPoseProof (ipi_50 with "Htext") as "Hi50".
    iPoseProof (ipi_54 with "Htext") as "Hi54".
    iPoseProof (ipi_58 with "Htext") as "Hi58".
    iPoseProof (ipi_5c with "Htext") as "Hi5c".
    pose proof Hb4 as Hbx4. rewrite HspR1 in Hbx4.
    assert (HF2sp : F2 !!! Regidx csp_rs1 = spr)
      by (destruct HF2regs as (_ & B & _); exact B).
    assert (HF2s2 : F2 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (destruct HF2regs as (_ & _ & Cc & _); exact Cc).
    (* ===== +0x46 c.sdsp s2,0(sp) ===== *)
    iEval (rewrite -Hbx4 -HF2sp) in "Hg4".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iput + 0x46)) (mword_of_int 0 : mword 6) Rs2
              F2 (trap_res eb + (K - 4))%nat vg4 false with "Hcg Hpc Hi46 Hg4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
    iEval (rgne) in "Hg4".
    iEval (rewrite HF2s2 HF2sp Hbx4) in "Hg4".
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.iput + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x48)) by pcw.
    iEval (rewrite Hpp48) in "Hpc".
    (* ===== +0x48 addi a5,s1,16 ; +0x4c c.mv s2,a5 ; +0x4e c.mv a0,a5 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x48)) Ra5 Rs1
              (mword_of_int 16 : mword 12) F2 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi48").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (G1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget F2 Rs1) (sign_extend' 64 (mword_of_int 16 : mword 12)))]> F2).
    assert (HG1a5 : G1 !!! Regidx Ra5 = i_lock (ientry k)).
    { rewrite /G1 upd_eq. unfold regval_into_reg.
      rewrite (rget_ne F2 Rs1 ltac:(nz)) HF2s1. reflexivity. }
    assert (HG1s1 : G1 !!! Regidx Rs1 = ientry k)
      by (rewrite /G1 upd_ne; [exact HF2s1 | nz]).
    assert (HG1sp : G1 !!! Regidx csp_rs1 = spr)
      by (rewrite /G1 upd_ne; [exact HF2sp | nz]).
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.iput + 0x48) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x4c)) by pcw.
    iEval (rewrite Hpp4c) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x4c)) Rs2 Ra5
              G1 (trap_res eb + (K - 4))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (G2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Ra5))]> G1).
    assert (HG2s2 : G2 !!! Regidx Rs2 = i_lock (ientry k)).
    { rewrite /G2 upd_eq. rewrite HG1a5. apply add_vec_zero_l. }
    assert (HG2a5 : G2 !!! Regidx Ra5 = i_lock (ientry k))
      by (rewrite /G2 upd_ne; [exact HG1a5 | nz]).
    assert (HG2s1 : G2 !!! Regidx Rs1 = ientry k)
      by (rewrite /G2 upd_ne; [exact HG1s1 | nz]).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = spr)
      by (rewrite /G2 upd_ne; [exact HG1sp | nz]).
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.iput + 0x4c) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x4e)) by pcw.
    iEval (rewrite Hpp4e) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x4e)) Ra0 Ra5
              G2 (trap_res eb + (K - 4))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (G3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Ra5))]> G2).
    assert (HG3a0 : G3 !!! Regidx Ra0 = i_lock (ientry k)).
    { rewrite /G3 upd_eq. rewrite HG2a5. apply add_vec_zero_l. }
    assert (HG3s2 : G3 !!! Regidx Rs2 = i_lock (ientry k))
      by (rewrite /G3 upd_ne; [exact HG2s2 | nz]).
    assert (HG3s1 : G3 !!! Regidx Rs1 = ientry k)
      by (rewrite /G3 upd_ne; [exact HG2s1 | nz]).
    assert (HG3sp : G3 !!! Regidx csp_rs1 = spr)
      by (rewrite /G3 upd_ne; [exact HG2sp | nz]).
    assert (HG3thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                       G3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G3 upd_ne; [| regne]. rewrite /G2 upd_ne; [| regne].
      rewrite /G1 upd_ne; [| regne]. rewrite /F2 upd_ne; [| regne].
      rewrite /F1 upd_ne; [| regne]. rewrite /E2 upd_ne; [| regne].
      rewrite /E1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs).
      exact (HmAthr c Hcs N2 N8 N9). }
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.iput + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x50 jal acquiresleep -- THE NESTED ONE (§13.12(a)) ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x50)) Rra
              (mword_of_int 2910 : mword 21) G3 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x50) : mword 64) 4)]> G3).
    assert (Htgtasl : add_vec (mword_of_int (KernelSyms.iput + 0x50) : mword 64)
                        (sign_extend' 64 (mword_of_int 2910 : mword 21))
                      = mword_of_int KernelSyms.acquiresleep) by pcw.
    iEval (rewrite Htgtasl) in "Hpc".
    assert (HG4a0 : G4 !!! Regidx Ra0 = i_lock (ientry k))
      by (rewrite /G4 upd_ne; [exact HG3a0 | nz]).
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x50) : mword 64) 4)
      by (rewrite /G4; apply upd_eq).
    assert (HG4s2 : G4 !!! Regidx Rs2 = i_lock (ientry k))
      by (rewrite /G4 upd_ne; [exact HG3s2 | nz]).
    assert (HG4s1 : G4 !!! Regidx Rs1 = ientry k)
      by (rewrite /G4 upd_ne; [exact HG3s1 | nz]).
    assert (HG4sp : G4 !!! Regidx csp_rs1 = spr)
      by (rewrite /G4 upd_ne; [exact HG3sp | nz]).
    assert (HG4thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                       G4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18. rewrite /G4 upd_ne; [| regne].
      exact (HG3thr c Hcs N2 N8 N9 N18). }
    iApply (ASL.wp_acquiresleep_nested_sconf (dq := dq) gs j gil gisl "inode"%string
              (ic_tok cn k) G4 pidv (trap_res eb + (K - 4))%nat eb C 0%nat
              Hj ltac:(lia) ltac:(cbn; lia)
              with "Hcg Hcnt Htext Hpc [] Hpanic Hppid Hprocs").
    { iEval (rewrite HG4a0). iExact "Hslk". }
    iApply wp_next_off_intro.
    iIntros (mfa) "%Hcsa Hcg Hcnt Hpc Hstok Hspid Hictok Hppid".
    iEval (rewrite HG4a0) in "Hspid".
    assert (Hpc54 : ret_pc (G4 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x54))
      by (rewrite HG4ra; pcw).
    iEval (rewrite Hpc54) in "Hpc".
    pose proof Hcsa as Hcsa_cs.
    assert (Hmfas1 : mfa !!! Regidx Rs1 = ientry k)
      by (rewrite (callee_saved_lookup Hcsa_cs Rs1 ltac:(vm_compute; reflexivity)); exact HG4s1).
    assert (Hmfas2 : mfa !!! Regidx Rs2 = i_lock (ientry k))
      by (rewrite (callee_saved_lookup Hcsa_cs Rs2 ltac:(vm_compute; reflexivity)); exact HG4s2).
    assert (Hmfasp : mfa !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsa_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HG4sp).
    assert (Hmfathr : forall c : mword 5, is_cs_idx c = true ->
                        c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                        mfa !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcsa_cs c Hcs). exact (HG4thr c Hcs N2 N8 N9 N18). }
    (* ---- THE WINDOW EXITS: HELD -> OUT, the reference deposited ---- *)
    iApply fupd_wp.
    (* ================================================================
       THE SECOND GENERATION BUMP (design §17.6, ratified §17.7).

       The free path is committed (+0x44 fell through), and this slot is
       about to be re-parked UNLOADED with its region record retyped -- the
       state §17.6.1 shows a SECOND FILL can reach, inside what would
       otherwise be one generation: ialloc's claim retags the very same inum
       through the buffer (no cache lock, §16.1) and its [iget] HITS the
       still-cached entry, so the slot never goes free and no recycle
       intervenes.  A generation that is filled twice cannot carry a type.

       This is the LAST instant at which the slot's whole liveness unit
       exists: REF-1 says the closer's [q] IS the map's [qt]
       ([iref_lookup]), the escrow arm's 1/2 has been in our hand since
       +0x3c, and the table's [1/2 - qt] is in [live_slot].  Bumping at the
       re-park (+0x70) is dead -- no [itable_half] there (§17.3) -- and
       bumping at [ip->ref--] (+0x7c) is dead too: by then the killer
       sequence's [iget] has moved [qt], and the assembly falls short of one.

       The ITABLE LOCK is the whole serialisation argument: iput holds it
       from its [acquire] through the [release] at +0x5c, and this call is
       inside that window, so every reference minted after it -- including
       ialloc's -- names the NEW generation, and every one that existed
       before is refuted by REF-1.  The count [1] is a parameter
       [live_slot_regen] never reads.
       ================================================================ *)
    iDestruct "Hrtok" as "[Hfrg Hlvq]".
    iMod (live_slot_regen ⊤ Mt k q 1%positive ltac:(solve_ndisj) HMk
            with "Hinv Hhalf Hlvq [Hlvh]") as (ga') "(Hhalf & Hlvq & Hlvh & Hpend)";
      [iExists ga; iExact "Hlvh" |].
    iAssert (iref_tok k q) with "[Hfrg Hlvq]" as "Hrtok".
    { rewrite /iref_tok. iSplitL "Hfrg"; [iExact "Hfrg" |].
      iExists ga'. iExact "Hlvq". }
    iInv "Hesc" as ">Hbody" "Hclose".
    (* the payload in hand is still the LOADED one at the OLD generation, and
       it must stay there: restating it at [ga'] would spend the fresh
       pending the +0x74 park needs.  Hence [ic_open_held]'s two gnames. *)
    iAssert (ic_payload_at gfs gi cov logstart k inum ga dn bm)
      with "[Hdat Hmty Hmmaj Hmmin Hmnl Hmsz Haddrs Hind Hblks Hdlk]" as "Hpayl".
    { rewrite /ic_payload_at.
      iSplitR "Hshot"; [| iExact "Hshot"]. iExists data.
      iSplitR; [iPureIntro; exact Hok |].
      iSplitR; [iPureIntro; exact Hdok |].
      iSplitL "Hdlk"; [iExact "Hdlk" |]. rewrite /inode_meta. iFrame. }
    iMod (ic_open_held cn gfs gi cov logstart k (⊤ ∖ ↑icEscN)
            Mt q ga' ga dev inum dn bm ltac:(solve_ndisj) HMk
            with "Hinv Hbody Hhalf Hrtok Hlvh Hgid Hpayl")
      as "(Hhalf & Hrtok & Hlvh & Hgid & Hpayl & Hidv & Hnfull & Hvldx & Hmt
           & Hgida)".
    iDestruct "Hvldx" as (w0) "Hva".
    iDestruct (word4_pointsto_agree with "Hvb Hva") as %<-.
    iDestruct (word4_pointsto_half_join with "Hvb Hva") as "Hvld".
    (* the inum cell goes back three ways: the arm's ½, the deposited
       reference's q, and the table's (½ - q) *)
    iDestruct (word4_pointsto_half_split with "Hnfull") as "[Hinh Hn2]".
    iEval (rewrite Hsum) in "Hn2".
    iDestruct (word4_pointsto_frac_split (i_inum (ientry k)) q qr inum with "Hn2")
      as "[Hrn Htn]".
    (* ...and so does the dev cell: the arm's half was never ours *)
    (* THE DEPOSIT'S DESCRIPTOR (§14.8): the sleeplock's variable becomes
       [DepRef q dev inum], half goes into the arm and half travels with us to
       the park at +0x70 -- which is what tells iput's arm from iunlock's
       there. *)
    (* the descriptor records the GENERATION too (design 17.3 (A1)), and the
       arm's own 1/2 goes back into the arm beside the deposit.  The
       depositor's slice is generation-named by [live_gen_agree] against
       that 1/2 -- two slices of one slot always name one generation. *)
    iDestruct "Hrtok" as "[Hfrg Hlvr]".
    iDestruct "Hlvr" as (gr) "Hlvr".
    iDestruct (live_gen_agree with "Hlvr Hlvh") as %->.
    iMod (ic_dep_checkout cn k (DepRef q dev inum ga') with "Hictok")
      as "[Hdepa Hdepk]".
    iMod ("Hclose" with "[Hdepa Hfrg Hlvr Hlvh Hrd Hrn Hmt Hgida]") as "_".
    { iApply bi.later_intro. iApply (ic_close_out cn gfs gi cov logstart k (DepRef q dev inum ga')
                       dev inum with "Hdepa [Hfrg Hlvr Hlvh Hrd Hrn] Hmt Hgida").
      rewrite /ic_dep_res /ic_dep_own /ic_dep_half.
      iSplitR "Hlvh"; [| iExact "Hlvh"].
      iSplitR; [iPureIntro; done |].
      rewrite /IcacheRef.inode_ref_gen /IcacheRef.inode_ident. iFrame. }
    iModIntro.
    (* the lock's resource re-forms, unchanged, and is released at +0x5c *)
    iDestruct ("Hback" $! Mt ci with "[%] [%] [Htd Htn Hiu Hgid]") as "Hslots";
      [ intros i0 Hi0; reflexivity | intros i0 Hi0; reflexivity | | ].
    { rewrite /islot2 HMk Hcik. rewrite /islot_rest_at Ert /IcacheRef.inode_ident.
      iFrame. }
    iAssert (itable_res2 cn gfs gi cov logstart nib dev)
      with "[Hhalf Hiauth Hslots Hpool]" as "HRres".
    { iExists Mt, ci. iFrame. iPureIntro. split; assumption. }
    (* ===== +0x54 / +0x58 : a0 := &itable ; +0x5c jal release ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x54)) Ra0
              (mword_of_int 29 : mword 20) mfa (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi54").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (H1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x54) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> mfa).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.iput + 0x54) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x58)) Ra0 Ra0
              (mword_of_int 1284 : mword 12) H1 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi58").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (H2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (H1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1284 : mword 12)))]> H1).
    assert (HH2a0 : H2 !!! Regidx Ra0 = itable_lock).
    { rewrite /H2 upd_eq /H1 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.iput + 0x58) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x5c)) Rra
              (mword_of_int 2087022 : mword 21) H2 (trap_res eb + (K - 4))%nat false
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (H3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x5c) : mword 64) 4)]> H2).
    assert (Htgtrl : add_vec (mword_of_int (KernelSyms.iput + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2087022 : mword 21))
                     = mword_of_int KernelSyms.release) by pcw.
    iEval (rewrite Htgtrl) in "Hpc".
    assert (HH3a0 : H3 !!! Regidx Ra0 = itable_lock)
      by (rewrite /H3 upd_ne; [exact HH2a0 | nz]).
    assert (HH3ra : H3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x5c) : mword 64) 4)
      by (rewrite /H3; apply upd_eq).
    assert (HH3thr : forall c : mword 5, is_cs_idx c = true ->
                       H3 !!! Regidx c = mfa !!! Regidx c).
    { intros c Hcs. rewrite /H3 upd_ne; [| regne].
      rewrite /H2 upd_ne; [| regne]. rewrite /H1 upd_ne; [reflexivity | regne]. }
    iApply (Release.wp_release_sconf gtl itable_lock "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) H3
              0%nat eb pj C (K - 4)%nat
              ltac:(rewrite HH3a0; reflexivity) ltac:(lia)
              with "Hcg Htext Hpc [Hitab] Htok HRres Hcnt Hpay").
    { iExact "Hitab". }
    iIntros (CIDrl Hsrl mr1) "Hcg Hpc %Hpins1 Hcnt".
    pose proof Hpins1 as Hpins1_cs.
    assert (Hpc60 : ret_pc (H3 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x60))
      by (rewrite HH3ra; pcw).
    iEval (rewrite Hpc60) in "Hpc".
    assert (Hmr1c : forall c : mword 5, is_cs_idx c = true ->
                      mr1 !!! Regidx c = mfa !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hpins1_cs c Hcs).
      exact (HH3thr c Hcs). }
    assert (Hmr1s1 : mr1 !!! Regidx Rs1 = ientry k)
      by (rewrite (Hmr1c Rs1 ltac:(vm_compute; reflexivity)); exact Hmfas1).
    assert (Hmr1s2 : mr1 !!! Regidx Rs2 = i_lock (ientry k))
      by (rewrite (Hmr1c Rs2 ltac:(vm_compute; reflexivity)); exact Hmfas2).
    assert (Hmr1sp : mr1 !!! Regidx csp_rs1 = spr)
      by (rewrite (Hmr1c csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmfasp).

    iPoseProof (ipi_60 with "Htext") as "Hi60".
    iPoseProof (ipi_62 with "Htext") as "Hi62".
    iPoseProof (ipi_66 with "Htext") as "Hi66".
    iPoseProof (ipi_6a with "Htext") as "Hi6a".
    iPoseProof (ipi_6c with "Htext") as "Hi6c".
    iPoseProof (ipi_70 with "Htext") as "Hi70".
    iPoseProof (ipi_74 with "Htext") as "Hi74".
    iPoseProof (ipi_76 with "Htext") as "Hi76".
    iPoseProof (ipi_7a with "Htext") as "Hi7a".
    iPoseProof (ipi_7e with "Htext") as "Hi7e".
    iPoseProof (ipi_82 with "Htext") as "Hi82".
    iPoseProof (ipi_86 with "Htext") as "Hi86".
    iPoseProof (ipi_88 with "Htext") as "Hi88".
    (* ===== +0x60 c.mv a0,s1 ; +0x62 jal itrunc ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x60)) Ra0 Rs1
              mr1 (K - 4)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi60").
    iIntros (CIDm1 Hsm1) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mr1 !!! Regidx Rs1))]> mr1).
    assert (HJ1a0 : J1 !!! Regidx Ra0 = ientry k).
    { rewrite /J1 upd_eq. rewrite Hmr1s1. apply add_vec_zero_l. }
    assert (HJ1c : forall c : mword 5, is_cs_idx c = true ->
                     J1 !!! Regidx c = mr1 !!! Regidx c)
      by (intros c Hcs; rewrite /J1 upd_ne; [reflexivity | regne]).
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.iput + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x62)) by pcw.
    iEval (rewrite Hpp62) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x62)) Rra
              (mword_of_int 2096906 : mword 21) J1 (K - 4)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi62").
    iIntros (CIDm2 Hsm2) "Hcg Hpc".
    set (J2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x62) : mword 64) 4)]> J1).
    assert (Htgtit : add_vec (mword_of_int (KernelSyms.iput + 0x62) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096906 : mword 21))
                     = mword_of_int KernelSyms.itrunc) by pcw.
    iEval (rewrite Htgtit) in "Hpc".
    assert (HJ2a0 : J2 !!! Regidx Ra0 = ientry k)
      by (rewrite /J2 upd_ne; [exact HJ1a0 | nz]).
    assert (HJ2ra : J2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x62) : mword 64) 4)
      by (rewrite /J2; apply upd_eq).
    assert (HJ2c : forall c : mword 5, is_cs_idx c = true ->
                     J2 !!! Regidx c = mr1 !!! Regidx c).
    { intros c Hcs. rewrite /J2 upd_ne; [| regne]. exact (HJ1c c Hcs). }
    (* the checked-out bundle, opened for itrunc.  [inode_sized] is
       [inode_ok]'s seventh conjunct (§13.12(b)) -- iput's discharge of the
       one premise SpecItrunc could not otherwise get. *)
    iEval (rewrite /ic_payload_at) in "Hpayl".
    (* the OLD generation's shot is dropped here -- [live_slot_regen] already
       retired [ga], and itrunc + [ip->type = 0] are about to turn this
       [ic_loaded] into raw cells and a marker (design §17.6 (4)).

       THE RECORD IS THE SAME ONE (design §20.14's (R1)).  [ic_open_held] is
       record-parametric, so what comes back out of the window is [dn], not
       a fresh existential -- which is what carries the [ip->nlink == 0] the
       +0x44 branch test established ([Hnl0] below) all the way down to the
       region free at +0x74, where (L3) needs it. *)
    iDestruct "Hpayl" as "[Hlk2 _]".
    iDestruct "Hlk2" as (data2)
      "(%Hok2 & %Hdok2 & Hdlk2 & Hdat & Hmeta & Haddrs & Hind & Hblks)".
    (* [Hdlk2] -- the link-ledger fragments this directory's own records held
       (design §20.3/§20.6's itrunc row) -- is SHED here and never re-parked:
       the free path's exit is [ipool_shape]'s marker arm, which carries no
       data and therefore no twin.  Dropping is sound (the logic is affine)
       and it is what itrunc's [dir_links_size_zero] says at the pure level.
       What it COSTS is liveness, not soundness, and the reachable-trace
       argument is §20.6's: a file has no records, and a directory reaches
       [nlink = 0] only through sys_unlink, which refuses a non-empty one --
       so the only survivors are ["."] (exempt) and [".."] (already grey).
       S7 owes that as a named obligation at the record zeroing. *)
    pose proof Hok2 as Hok2'.
    destruct Hok2' as (Hbmwf2 & Hcovers2 & Hdiaddrs2 & Htyne2 & Hszcap2 & Hholes2 & Hsized2).
    iDestruct (bslots_op bn 2 1) as "[Hbsp _]".
    iDestruct ("Hbsp" with "Hbslots") as "[Hbs2 Hbs1]".
    (* CREDITED, so the level itrunc enters at depends on [crb]: paid up
       front it is handed one unit less, and [it_entry] is what says so. *)
    pose (uit := (n - (if crb then 1 else 2))%nat).
    assert (Hun : it_entry crb uit = n)
      by (unfold it_entry, uit; destruct crb; lia).
    iDestruct (cpu_own_transport CIDrl CIDm2 0%nat eb pj C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [Hextc]/[Hextm] have sat at [CIDacq] since the wide hop right after
       the first acquire -- nothing between there and here (acquiresleep's
       nested, non-parking arm; the interior release; this mv+jal stretch)
       threads them, and none of it can move the hart except the release
       and this last stretch, both already covered by [wp_next_chain]. *)
    iDestruct (trap_csrs_ext_transport CIDacq CIDm2 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDacq CIDm2 eb pj
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iApply (IT.wp_itrunc_gen gs j gl gu gd gk pd pav pu bn g gfs gi
              cov logstart bmapstart inodestart nib size dev used
              (ientry k) inum dn dn bm data2 uit Sb crb cru
              pidv dq (DfracOwn (1/2)) (DfracOwn (1/2)) dqb dqs J2 (K - 4)%nat
              eb C eb
              ltac:(unfold K_itrunc; lia) Hcrb Hcru
              Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
              Hnib Htyne2
              (* §19.6 Part 1: iput hands itrunc ONE record for both slots. *)
              (InodeRegion.di_type_stable_refl dn)
              (InodeRegion.di_nlink_stable_refl dn Htyne2)
              Hbmwf2 Hcovb Hsized2 Hdiaddrs2 Hj Hgsj HJ2a0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlogc Hidv Hinh Hmeta
                    [Haddrs Hind] Hblks Hbms Hins Hbm Hireg Hdat Hppid Hprocs
                    Hdevi Hdgeom Hdlock [Hbs2 Hbs1] [Hop]").
    { rewrite /inode_map. iFrame. }
    { iApply (bslots_op bn 2 1). iFrame. }
    { rewrite Hun. iExact "Hop". }
    iIntros (CIDit Hsit mfi)
      "%Hcsi Hcg Hcnt Hextc Hextm Hpc Hppid Hidv Hinh Hbms Hins Hmeta Hmap Hblks Hbm Hdat Hbslots Hopx".
    (* [Hib1] IS what makes iput's own flush free: itrunc's tail iupdate
       logged this inum's block unconditionally, so the [ip->type = 0]
       iupdate below runs CREDITED and spends nothing.  That is the second
       [iu_spend] term of [CreateBudget.ip_spend], and without this
       membership iput could not hit [ip_spend_max]. *)
    iDestruct "Hopx" as (u' Sb1) "(%Hsub1 & %Hib1 & %Hu' & Hop)".
    assert (Hpc66 : ret_pc (J2 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x66))
      by (rewrite HJ2ra; pcw).
    iEval (rewrite Hpc66) in "Hpc".
    pose proof Hcsi as Hcsi_cs.
    assert (Hmfic : forall c : mword 5, is_cs_idx c = true ->
                      mfi !!! Regidx c = mr1 !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsi_cs c Hcs). exact (HJ2c c Hcs). }
    assert (Hmfis1 : mfi !!! Regidx Rs1 = ientry k)
      by (rewrite (Hmfic Rs1 ltac:(vm_compute; reflexivity)); exact Hmr1s1).
    (* ===== +0x66 sh zero,68(s1) : ip->type = 0 ===== *)
    iEval (rewrite /inode_meta) in "Hmeta".
    iDestruct "Hmeta" as "(Hmty & Hmmaj & Hmmin & Hmnl & Hmsz)".
    iDestruct (sie_cap_gpr_x0 mfi (K - 4)%nat eb pj Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    assert (Hpa66 : add_vec (rget mfi Rs1) (sign_extend' 64 (mword_of_int 68 : mword 12))
                    = i_type (ientry k)).
    { rewrite (rget_ne mfi Rs1 ltac:(nz)) Hmfis1. reflexivity. }
    iEval (rewrite -Hpa66) in "Hmty".
    iApply (wp_sh_s_sconf (mword_of_int (KernelSyms.iput + 0x66)) Rz Rs1
              (mword_of_int 68 : mword 12) mfi (K - 4)%nat
              (di_type (di_trunc dn)) eb with "Hcg Hpc Hi66 Hmty [-]").
    iIntros (CIDsh Hssh) "Hcg Hpc Hmty".
    iEval (rewrite Hpa66) in "Hmty".
    assert (Hsv66 : trunc16 (rget mfi Rz) = (mword_of_int 0 : mword 16)).
    { rewrite (rget_ne mfi Rz ltac:(nz)) Hx0. exact ip_trunc16_zero. }
    iEval (rewrite Hsv66) in "Hmty".
    (* the record iupdate will flush: the truncated one, with type zeroed *)
    iAssert (inode_meta (ientry k) (di_free dn))
      with "[Hmty Hmmaj Hmmin Hmnl Hmsz]" as "Hmeta".
    { rewrite /inode_meta /di_free /di_trunc.
      cbn [di_type di_major di_minor di_nlink di_size]. iFrame. }
    assert (Hpp6a : add_vec_int (mword_of_int (KernelSyms.iput + 0x66) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x6a)) by pcw.
    iEval (rewrite Hpp6a) in "Hpc".
    (* ===== +0x6a c.mv a0,s1 ; +0x6c jal iupdate ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x6a)) Ra0 Rs1
              mfi (K - 4)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6a").
    iIntros (CIDm3 Hsm3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfi !!! Regidx Rs1))]> mfi).
    assert (HJ3a0 : J3 !!! Regidx Ra0 = ientry k).
    { rewrite /J3 upd_eq. rewrite Hmfis1. apply add_vec_zero_l. }
    assert (HJ3c : forall c : mword 5, is_cs_idx c = true ->
                     J3 !!! Regidx c = mfi !!! Regidx c)
      by (intros c Hcs; rewrite /J3 upd_ne; [reflexivity | regne]).
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.iput + 0x6a) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x6c)) by pcw.
    iEval (rewrite Hpp6c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x6c)) Rra
              (mword_of_int 2096478 : mword 21) J3 (K - 4)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi6c").
    iIntros (CIDm4 Hsm4) "Hcg Hpc".
    set (J4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x6c) : mword 64) 4)]> J3).
    assert (Htgtiu : add_vec (mword_of_int (KernelSyms.iput + 0x6c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096478 : mword 21))
                     = mword_of_int KernelSyms.iupdate) by pcw.
    iEval (rewrite Htgtiu) in "Hpc".
    assert (HJ4a0 : J4 !!! Regidx Ra0 = ientry k)
      by (rewrite /J4 upd_ne; [exact HJ3a0 | nz]).
    assert (HJ4ra : J4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x6c) : mword 64) 4)
      by (rewrite /J4; apply upd_eq).
    assert (HJ4c : forall c : mword 5, is_cs_idx c = true ->
                     J4 !!! Regidx c = mfi !!! Regidx c).
    { intros c Hcs. rewrite /J4 upd_ne; [| regne]. exact (HJ3c c Hcs). }
    assert (Hu'1 : S (u' - 1)%nat = u')
      by (unfold it_entry, it_spend, it_iu, uit in Hu', Hun;
          destruct crb, cru; simpl in *; lia).
    iDestruct (bslots_op bn 2 1) as "[Hbsp2 _]".
    iDestruct ("Hbsp2" with "Hbslots") as "[Hbs2 Hbs1]".
    iDestruct (cpu_own_transport CIDit CIDm4 0%nat eb pj C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* itrunc IS one of the already-generalized threading callees, so this
       hop is NORMAL -- the same span as [Hcnt]'s own, matching the entry
       hart itrunc's own contract just delivered them at. *)
    iDestruct (trap_csrs_ext_transport CIDit CIDm4 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDit CIDm4 eb pj
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iApply (IU.wp_iupdate_credgen gs j gl gu gd gk pd pav pu bn g gfs gi
              cov logstart inodestart nib dev (ientry k) inum
              (di_free dn) (di_trunc dn) bm_empty (u' - 1)%nat Sb1 true
              pidv dq (DfracOwn (1/2)) (DfracOwn (1/2)) dqs J4 (K - 4)%nat
              eb C eb
              ltac:(unfold K_iupdate; lia)
              ltac:(intros _; exact Hib1)
              Hgeom Hist Hicov Hilog Hnib
              (* §19.6 Part 1, THE LEFT DISJUNCT: this is the free path's
                 [ip->type = 0] flush, the one place in the kernel where a
                 record's type legitimately moves, and it moves to ZERO. *)
              (InodeRegion.di_type_stable_zero (di_free dn) (di_trunc dn)
                 (di_free_type dn))
              (* §20.6's iput row, and §20.14's (R1) cashed.  [di_free] and
                 [di_trunc] both rebuild the record with [di_nlink dn]
                 verbatim, and [dn] IS the record whose [nlink] halfword
                 the [c.bnez] at +0x44 found zero -- it survives the
                 sleeplock window because [ic_open_held] is
                 record-parametric.  So the region learns [di_nlink = 0] of
                 the record it is about to type-zero, which is (L3), and
                 (L1) then collapses to [w = 0]: nothing names this inum. *)
              (InodeRegion.di_nlink_stable_free (di_free dn) (di_trunc dn)
                 eq_refl (ip_nlink_zero (di_nlink dn) Hnl0))
              (di_free_addrs dn) ltac:(reflexivity) Hj Hgsj HJ4a0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlogc Hidv Hinh Hmeta Hmap
                    Hins Hireg Hdat Hppid Hprocs Hdevi Hdgeom Hdlock Hbs2 [Hop]").
    { rewrite Hu'1. iExact "Hop". }
    iIntros (CIDiu Hsiu mfu)
      "%Hcsu Hcg Hcnt Hextc Hextm Hpc Hppid Hidv Hinh Hmeta Hmap Hins Hdat Hbs2 Hop".
    (* THE FREE PATH'S PAYOUT (§16.4): the flushed record has type 0, so
       iupdate ran [InodeRegion.ireg_free_au] -- the fragment went back INTO
       the region invariant and what comes out is the MARKER, which is
       exactly what the park below deposits. *)
    iDestruct (ireg_out_free_inv gi inum (di_free dn) (di_free_type dn)
                 with "Hdat") as "Hdat".
    assert (Hpc70 : ret_pc (J4 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x70))
      by (rewrite HJ4ra; pcw).
    iEval (rewrite Hpc70) in "Hpc".
    pose proof Hcsu as Hcsu_cs.
    assert (Hmfuc : forall c : mword 5, is_cs_idx c = true ->
                      mfu !!! Regidx c = mfi !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsu_cs c Hcs). exact (HJ4c c Hcs). }
    assert (Hmfus1 : mfu !!! Regidx Rs1 = ientry k)
      by (rewrite (Hmfuc Rs1 ltac:(vm_compute; reflexivity)); exact Hmfis1).
    assert (Hmfus2 : mfu !!! Regidx Rs2 = i_lock (ientry k))
      by (rewrite (Hmfuc Rs2 ltac:(vm_compute; reflexivity));
          rewrite (Hmfic Rs2 ltac:(vm_compute; reflexivity)); exact Hmr1s2).
    assert (Hmfusp : mfu !!! Regidx csp_rs1 = spr)
      by (rewrite (Hmfuc csp_rs1 ltac:(vm_compute; reflexivity));
          rewrite (Hmfic csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmr1sp).
    (* ===== +0x70 sw zero,64(s1) : ip->valid = 0.  A PLAIN store: the cell
       is in THIS thread's hands for the whole checkout window. ===== *)
    iDestruct (sie_cap_gpr_x0 mfu (K - 4)%nat eb pj Rz
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0u Hcg]".
    assert (Hpa70 : add_vec (rget mfu Rs1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                    = i_valid (ientry k)).
    { rewrite (rget_ne mfu Rs1 ltac:(nz)) Hmfus1. reflexivity. }
    iEval (rewrite -Hpa70) in "Hvld".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.iput + 0x70)) Rz Rs1
              (mword_of_int 64 : mword 12) mfu (K - 4)%nat (valid_word true) eb
              with "Hcg Hpc Hi70 Hvld").
    iIntros (CIDsw Hssw) "Hcg Hpc Hvld".
    iEval (rewrite Hpa70) in "Hvld".
    assert (Hsv70 : trunc32 (rget mfu Rz) = valid_word false).
    { rewrite (rget_ne mfu Rz ltac:(nz)) Hx0u. exact ip_trunc32_zero. }
    iEval (rewrite Hsv70) in "Hvld".
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.iput + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x74)) by pcw.
    iEval (rewrite Hpp74) in "Hpc".
    (* ---- THE PARK, at the FREE POOL SHAPE (§13.13's closing note): the
       flush retagged this inum's region record to the type-0 one, which IS
       [ipool_shape]'s free disjunct, and the truncated cells rebuild
       [inode_raw]. ---- *)
    iApply fupd_wp.
    iInv "Hesc" as ">Hbody" "Hclose".
    (* the re-park is at the FRESH generation and carries ITS pending token
       (design §17.6 (3)): the next fill of this slot -- ialloc's, on §16.4's
       claim-box branch -- therefore has one to spend, and can never be asked
       to agree with the dead [ga]'s type. *)
    iAssert (ic_payload gfs gi cov logstart k inum ga' false)
      with "[Hmeta Hmap Hdat Hpend]" as "Hpayf".
    { rewrite /ic_payload /ic_unloaded. rewrite /inode_map.
      iDestruct "Hmap" as "[Haddrs Hind]".
      iSplitR "Hpend"; [| iExact "Hpend"].
      iSplitR "Hdat".
      - rewrite /inode_raw. iSplitL "Hmeta"; [by iExists (di_free dn) |].
        iExists (bm_cells bm_empty). iSplitR; [iPureIntro; reflexivity |].
        iExact "Haddrs".
      - rewrite /ipool_shape. iRight. iExact "Hdat". }
    iMod (ic_swap_park cn gfs gi cov logstart k (DepRef q dev inum ga') ga'
                 false dev inum eq_refl with "Hbody Hdepk Hidv Hinh Hvld Hpayf")
      as "(Hbody & Hictok & Hrefo)".
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext |].
    iModIntro.
    (* the descriptor pins the fraction: what comes back is the reference we
       deposited, at [q], not at some existential [q2] (§14.8) -- and its
       liveness slice comes back generation-named (§17.3 (A)), which the
       contract states in the arity-preserving form. *)
    iDestruct "Hrefo" as "[_ Href]".
    iAssert (inode_ref k q dev inum) with "[Href]" as "Href".
    { rewrite inode_ref_gen_intro. iExists ga'. iExact "Href". }
    (* ===== +0x74 c.mv a0,s2 ; +0x76 jal releasesleep ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iput + 0x74)) Ra0 Rs2
              mfu (K - 4)%nat eb ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
    iIntros (CIDm5 Hsm5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mfu !!! Regidx Rs2))]> mfu).
    assert (HJ5a0 : J5 !!! Regidx Ra0 = i_lock (ientry k)).
    { rewrite /J5 upd_eq. rewrite Hmfus2. apply add_vec_zero_l. }
    assert (HJ5c : forall c : mword 5, is_cs_idx c = true ->
                     J5 !!! Regidx c = mfu !!! Regidx c)
      by (intros c Hcs; rewrite /J5 upd_ne; [reflexivity | regne]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.iput + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x76)) by pcw.
    iEval (rewrite Hpp76) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x76)) Rra
              (mword_of_int 2956 : mword 21) J5 (K - 4)%nat eb
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi76").
    iIntros (CIDm6 Hsm6) "Hcg Hpc".
    set (J6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iput + 0x76) : mword 64) 4)]> J5).
    assert (Htgtrs : add_vec (mword_of_int (KernelSyms.iput + 0x76) : mword 64)
                       (sign_extend' 64 (mword_of_int 2956 : mword 21))
                     = mword_of_int KernelSyms.releasesleep) by pcw.
    iEval (rewrite Htgtrs) in "Hpc".
    assert (HJ6a0 : J6 !!! Regidx Ra0 = i_lock (ientry k))
      by (rewrite /J6 upd_ne; [exact HJ5a0 | nz]).
    assert (HJ6ra : J6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.iput + 0x76) : mword 64) 4)
      by (rewrite /J6; apply upd_eq).
    assert (HJ6c : forall c : mword 5, is_cs_idx c = true ->
                     J6 !!! Regidx c = mfu !!! Regidx c).
    { intros c Hcs. rewrite /J6 upd_ne; [| regne]. exact (HJ5c c Hcs). }
    iDestruct (cpu_own_transport CIDiu CIDm6 0%nat eb pj C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (RS.wp_releasesleep_sconf gs gil gisl "inode"%string (ic_tok cn k)
              J6 pidv pj (K - 4)%nat eb C eb ltac:(lia)
              with "Hcg Hcnt Htext Hpc [] Hstok [Hspid] Hictok Hpanic Hprocs").
    { iEval (rewrite HJ6a0). iExact "Hslk". }
    { iEval (rewrite HJ6a0). iExact "Hspid". }
    iIntros (CIDrs Hsrs mrs) "%Hcsr Hcg Hcnt Hpc".
    assert (Hpc7a : ret_pc (J6 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x7a))
      by (rewrite HJ6ra; pcw).
    iEval (rewrite Hpc7a) in "Hpc".
    pose proof Hcsr as Hcsr_cs.
    assert (Hmrsc : forall c : mword 5, is_cs_idx c = true ->
                      mrs !!! Regidx c = mfu !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hcsr_cs c Hcs). exact (HJ6c c Hcs). }
    (* ===== +0x7a / +0x7e : a0 := &itable ; +0x82 jal acquire ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iput + 0x7a)) Ra0
              (mword_of_int 29 : mword 20) mrs (K - 4)%nat eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7a").
    iIntros (CIDm7 Hsm7) "Hcg Hpc".
    set (J7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iput + 0x7a) : mword 64)
                     (auipc_off (mword_of_int 29 : mword 20)))]> mrs).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.iput + 0x7a) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x7e)) by pcw.
    iEval (rewrite Hpp7e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iput + 0x7e)) Ra0 Ra0
              (mword_of_int 1246 : mword 12) J7 (K - 4)%nat eb
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e").
    iIntros (CIDm8 Hsm8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (J8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (J7 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 1246 : mword 12)))]> J7).
    assert (HJ8a0 : J8 !!! Regidx Ra0 = itable_lock).
    { rewrite /J8 upd_eq /J7 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.iput + 0x7e) : mword 64) 4
                    = mword_of_int (KernelSyms.iput + 0x82)) by pcw.
    iEval (rewrite Hpp82) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iput + 0x82)) Rra
              (mword_of_int 2086848 : mword 21) J8 (K - 4)%nat eb
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
    iDestruct (cpu_own_transport CIDrs CIDm9 0%nat eb pj C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf gtl "itable"%string
              (itable_res2 cn gfs gi cov logstart nib dev) J9
              0%nat eb pj C (K - 4)%nat eb
              ltac:(lia) ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hitab] Hpanic").
    { iEval (rewrite HJ9a0). iExact "Hitab". }
    iIntros (CIDac2 Hsac2 ms2 macq2) "%Hmsf2 Hcg Hpc %Hap2 Htok HRres2 Hcnt Hpay".
    (* [Hextc]/[Hextm] were last actually re-derived at [CIDiu] (iupdate's
       own return, since it threads them); neither the post-iupdate field
       stores, releasesleep, NOR this second acquire mention them at all,
       so they are still exactly iupdate's own delivery, stranded at
       [CIDiu].  One wide hop straight to [CIDac2] covers all of that in a
       single step. *)
    iDestruct (trap_csrs_ext_transport CIDiu CIDac2 eb pj
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDiu CIDac2 eb pj
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    assert (Hpc86 : ret_pc (J9 !!! Regidx Rra) = mword_of_int (KernelSyms.iput + 0x86))
      by (rewrite HJ9ra; pcw).
    iEval (rewrite Hpc86) in "Hpc".
    pose proof Hap2 as Hap2_cs.
    assert (Hma2c : forall c : mword 5, is_cs_idx c = true ->
                      macq2 !!! Regidx c = mrs !!! Regidx c).
    { intros c Hcs. rewrite (callee_saved_lookup Hap2_cs c Hcs). exact (HJ9c c Hcs). }
    assert (Hma2all : forall c : mword 5, is_cs_idx c = true ->
                        macq2 !!! Regidx c = mfu !!! Regidx c).
    { intros c Hcs. rewrite (Hma2c c Hcs). exact (Hmrsc c Hcs). }
    assert (Hma2sp : macq2 !!! Regidx csp_rs1 = spr)
      by (rewrite (Hma2all csp_rs1 ltac:(vm_compute; reflexivity)); exact Hmfusp).
    assert (Hma2s1 : macq2 !!! Regidx Rs1 = ientry k)
      by (rewrite (Hma2all Rs1 ltac:(vm_compute; reflexivity)); exact Hmfus1).
    (* ===== +0x86 c.ldsp s2,0(sp) : s2 comes back ===== *)
    iEval (rewrite -Hbx4 -Hma2sp) in "Hg4".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iput + 0x86))
              (mword_of_int 0 : mword 6) Rs2 macq2 (trap_res eb + (K - 4))%nat
              (m !!! Regidx Rs2) false ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi86 Hg4").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hg4".
    iEval (rewrite Hma2sp Hbx4) in "Hg4".
    set (J10 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> macq2).
    assert (HJ10s1 : J10 !!! Regidx Rs1 = ientry k)
      by (rewrite /J10 upd_ne; [exact Hma2s1 | nz]).
    assert (HJ10sp : J10 !!! Regidx csp_rs1 = spr)
      by (rewrite /J10 upd_ne; [exact Hma2sp | nz]).
    assert (HJ10s2 : J10 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /J10 upd_eq; reflexivity).
    assert (HJ10thr : forall c : mword 5, is_cs_idx c = true ->
                        c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                        J10 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /J10 upd_ne; [| regne].
      rewrite (Hma2all c Hcs) (Hmfuc c Hcs) (Hmfic c Hcs) (Hmr1c c Hcs).
      exact (Hmfathr c Hcs N2 N8 N9 N18). }
    assert (HJ10regs : iput_regs m J10 spr k).
    { unfold iput_regs. repeat split;
        first [ exact HJ10s1 | exact HJ10sp | exact HJ10s2
              | rewrite HJ10thr;
                [ reflexivity | vm_compute; reflexivity | nz | nz | nz | nz ] ]. }
    assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.iput + 0x86) : mword 64) 2
                    = mword_of_int (KernelSyms.iput + 0x88)) by pcw.
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x88 c.j -104 : into the shared tail ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iput + 0x88))
              (sign_extend' 21 (concat_vec (mword_of_int 1996 : mword 11) ('b"0")))
              J10 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi88").
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Hpp20d : add_vec (mword_of_int (KernelSyms.iput + 0x88) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1996 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.iput + 0x20)) by pcw.
    iEval (rewrite Hpp20d) in "Hpc".
    iDestruct "HRres2" as (Mt2 ci2) "(Hhalf2 & %Hwf2 & %Hciwf2 & Hiauth2 & Hslots2 & Hpool2)".
    (* the credited flush paid nothing, so the level that survives is [u']
       itself -- iupdate handed back [S (u' - 1)], which is the same nat *)
    iEval (rewrite Hu'1) in "Hop".
    iApply (ip_tail (CID := CIDac2) CID j bn g gfs gi cn gtl cov logstart bmapstart
              inodestart nib size dev used (used ∖ bm_blocks bm)
              Sb (Sb1 ∪ {[IBLOCK inum inodestart]}) k q inum Mt2 ci2
              n u' (ip_spend_max crb cru) pidv dq dqb dqs m J10 K eb C sp0
              (m !!! Regidx Rs2)
              HK Hk ltac:(wp_next_chain) Hsp0eq HJ10regs Hwf2 Hciwf2
              ltac:(unfold ip_spend_max, it_entry, it_spend, it_iu, uit in *;
                    destruct crb, cru; simpl in *; lia)
              ltac:(unfold it_entry, it_spend, it_iu, uit in *;
                    destruct crb, cru; simpl in *; lia)
              ltac:(apply ip_diff_sub)
              ltac:(set_solver)
              with "Htext Hitab Hinv Hesc Hpc Hcg Hcnt Hpay Hextc Hextm Htok Hhalf2 Hiauth2
                    Hslots2 Hpool2 Href Hr24 Hr16 Hr8 Hg4 Hppid Hbms Hins Hbm
                    [Hbs2 Hbs1] Hop Hcont").
    iApply (bslots_op bn 2 1). iFrame.

  Qed.

  (* ===================================================================== *)
  (*  THE COUNTED SEAL, derived at the [log_op] existential's OWN WITNESS.  *)
  (*  [ip_spend_max false false = 2] and iput's own flush is the third unit *)
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
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_iput_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
                          cov logstart bmapstart inodestart nib size dev used
                          k q inum n pidv dq dqb dqs m K eb C b.
  Proof.
    cbv beta delta [wp_iput_sconf_body].
    intros pcE ip pj ret_tgt HK Hk Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
           Hnib Hcovb Hn Hj Hgsj Ha0.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlogc #Hitab #Hinv #Hesc #Hireg #Hslk
             Href Hbms Hins Hbm Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hbslots Hop Hcont".
    (* THE WITNESS: the set the counted reservation was hiding *)
    iDestruct "Hop" as (Sb0) "Hop".
    iApply (wp_iput_gen gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl gil gisl
              cov logstart bmapstart inodestart nib size dev used
              k q inum n Sb0 false false pidv dq dqb dqs m K eb C b
              HK Hk ltac:(discriminate) ltac:(discriminate)
              Hgeom Hsz Hbm0 Hbmcov Hbmlog Hist Hicov Hilog
              Hnib Hcovb Hn Hj Hgsj Ha0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlogc Hitab Hinv Hesc Hireg Hslk
                    Href Hbms Hins Hbm Hppid Hprocs Hdevi Hdgeom Hdlock Hbslots Hop [Hcont]").
    iEval (rewrite /wp_next).
    iIntros (CIDf) "%Hchain".
    iIntros (mf n' used' Sb') "%Hcs Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins
                               %Husub Hbm Hbslots %Hssub %Hbnd Hop Hislot".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [exact Hchain|].
    iApply ("Hcont" $! mf n' used' with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hbms Hins
                     [%] Hbm Hbslots [%] [Hop] Hislot").
    { exact Hcs. }
    { exact Husub. }
    { unfold ip_spend_max in Hbnd. unfold iput_units. simpl in Hbnd. lia. }
    { iApply (log_opS_op with "Hop"). }
  Qed.

End ProofIput.

End IputProof.
