(* ProofIget.v -- iget(), proven instruction by instruction.

   iget is the function that MINTS inode references, and the only one that
   writes an entry's identity cells.  Its shape:

     acquire(&itable.lock);
     empty = 0;
     for (ip = &itable.inode[0]; ip < &itable.inode[NINODE]; ip++) {
       if (ip->ref > 0 && ip->dev == dev && ip->inum == inum) { ip->ref++; ... }
       if (empty == 0 && ip->ref == 0) empty = ip;
     }
     if (empty == 0) panic("iget: no inodes");
     ip = empty; ip->dev = dev; ip->inum = inum; ip->ref = 1; ip->valid = 0;

   ---- THE THREE THINGS THAT MAKE THIS FILE DIFFERENT FROM ProofIdup -----

   (1) A SCAN.  The do-while at [+0x44 .. +0x40] is a FUEL induction on
       [NINODE - cursor] (fdalloc's rule, claude-notes/projects/
       proc-struct-resources.md), and it is much cheaper here than there
       for one reason: the whole loop sits INSIDE the critical section, so
       [b = false] and every leaf collapses through [wp_next_off_intro]
       with NO hart threading at all.  The entry hart does not have to ride
       the induction's universal; only [fuel], the cursor and the regfile
       do.  [M] and [ci] are FIXED across the scan -- the scan writes
       nothing -- so [itable_half], [iref_slots_auth], the [islot2] big-op
       and the pool thread through unchanged and each iteration borrows its
       slot read-only through [islots2_acc_upd] at [M' := M, ci' := ci].

   (2) TWO EXITS THAT MEET, and a continuation that rides the loop.  The
       cache HIT returns at [+0x66] and the RECYCLE falls out at [+0x8c];
       both funnel through the same nine-instruction tail, so the tail is
       proven ONCE, before the loop, as the loop's own last [-∗]
       ([Hcont2] below).  Proving it early is what keeps the six stack
       cells out of the induction: the tail already owns them.

   (3) THE RECYCLE'S GHOST CHOREOGRAPHY, four stores wide (design §13.1c,
       §13.9, §13.10):

         +0x6e  sw dev    [ic_open_empty_dev]  -- and the ghost RE-TAG that
                          carries the stored device to the next store: the
                          empty arm owns the dev cell WHOLE (it is the arm's
                          discriminator) so no fraction may be kept, and
                          §13.10's identity-carrying [ic_id] is the only
                          thing that can name the value at +0x72.
         +0x72  sw inum   [ic_open_empty_free] + [ic_close_mid]: the table's
                          inum half joins in, the pool's bundle for the
                          requested inum comes out ([ipool_acc]) and goes
                          into the MID arm, and the identification ghost
                          flips false -> true at the entry's NEW identity.
                          The recycler keeps a dev half and the table's
                          ghost half; the latter is what pins the MID arm's
                          FULL inum cell at +0x7c.
         +0x78  sw 1      [iref_alloc_step] at q = 1/4, inside the
                          [itable_inv] opening -- the ref word and the
                          authority move together, which is the atomicity.
         +0x7c  sw 0      [ic_open_mid] + [ic_close_mid_to_parked]: the
                          window closes at a normal parked arm, unloaded.

       NO eviction and NO [ipool_insert]: under §13.9 a recycled slot is
       not live, so its arm is EMPTY and there is nothing to evict -- that
       is iput's job, where the flush semantics hold.

   ---- WHY THE SCAN'S INVARIANT NEEDS THE TABLE'S DEVICE (§13.11) --------

   The scan's hit test is on the PAIR, and the dev compare at +0x4c
   short-circuits BEFORE [ip->inum] is loaded, so a full scan proves only
   "no live slot carries (dev, inum)".  The pool is keyed on the inum
   ALONE.  [is_itable2] therefore carries the table's device and iget
   instantiates it at its own [dev]: with [ic_ci_wf]'s fourth clause the
   two readings coincide and the sentinel's invariant IS [ipool_acc]'s
   membership premise.

   ---- THE PANIC AT +0x9e IS LIVE ---------------------------------------

   [SpecIget.v]'s header says why.  The branch is at [+0x6a]; the call it
   reaches is at [+0x9e], AFTER the epilogue.                            *)
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
Require Import RiscvExtras.
Require Import RiscvFetchExec.
Require Import MemAccessGen.
Require Import RegFile.
Require Import InstrBytes.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.
Require Import KptGhost.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSconfVc.
Require Import WpAu4.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import InodeInv.
Require Import DiskPtsto.
Require Import FsBlocks LogInv FsCrash.
Require Import DinodeEnc.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import CodeIget.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease.
Require Import SpecIget.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  THE SCAN's ARITHMETIC, in an mword-free context                   *)
(* ===================================================================== *)

(* the two 64-bit compares at +0x4c / +0x52 read [c.lw]ed cells, so what
   they test is the SIGN EXTENSION of a 32-bit identity value.
   [BreadLru.bd_sext_neqv]'s two lines, restated so this file need not
   import the bio layer. *)
Lemma ig_sext_eqv (a b : mword 32) :
  eq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 b) = eq_vec a b.
Proof.
  destruct (eq_vec a b) eqn:Hab.
  - apply eq_vec_true_iff in Hab. subst b. apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff in Hab. apply eq_vec_false_iff.
    intro Hc. apply Hab. exact (sext64_32_inj a b Hc).
Qed.

Lemma ig_sext_neqv (a b : mword 32) :
  neq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 b) = neq_vec a b.
Proof. unfold neq_vec. by rewrite ig_sext_eqv. Qed.

Lemma ig_neqv_eq (a b : mword 32) :
  neq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 b) = false -> a = b.
Proof.
  rewrite ig_sext_neqv. unfold neq_vec. intro H.
  apply negb_false_iff in H. by apply eq_vec_true_iff in H.
Qed.

Lemma ig_neqv_refl (a : mword 32) :
  neq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 a) = false.
Proof.
  rewrite ig_sext_neqv. unfold neq_vec.
  by rewrite (proj2 (eq_vec_true_iff a a) eq_refl).
Qed.

Lemma ig_neqv_ne (a b : mword 32) :
  a <> b -> neq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 b) = true.
Proof.
  intro H. rewrite ig_sext_neqv. unfold neq_vec.
  apply negb_true_iff. by apply eq_vec_false_iff.
Qed.

(* ---- the [ref] word's two branch readings ----
   A live slot's word is positive and in range, so [bge x0,a5] at +0x46
   FALLS THROUGH; a free slot's word is zero, so the branch is TAKEN and
   the [c.bnez a5] at +0x34 falls through in turn. *)
Lemma ig_ref_spos (n : positive) :
  (Z.pos n < 2 ^ 31)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64)
              (sign_extend' 64 (mword_of_int (Z.pos n) : mword 32)) = false.
Proof.
  intro Hn. apply inode_ref_spos.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  rewrite E31 in Hn. rewrite (moi32_small (Z.pos n) ltac:(rewrite E32; lia)).
  rewrite E31. lia.
Qed.

Lemma ig_ref_bge_zero :
  zopz0zKzJ_s (zero_reg : mword 64)
              (sign_extend' 64 (mword_of_int 0 : mword 32)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ig_ref_neqz_zero :
  neq_vec (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)
          (zero_reg : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- the cursor: step, sentinel, and "an entry address is never null" ---- *)

(* the [addi s1,s1,136] at +0x3c, in the form the leaf leaves behind *)
Lemma ig_cursor_step (j : nat) :
  add_vec (ientry j) (sign_extend' 64 (mword_of_int 136 : mword 12)) = ientry (S j).
Proof.
  rewrite ientry_step /add_vec_int.
  f_equal; apply bv_eq; vm_compute; reflexivity.
Qed.

(* the [beq s1,a3] at +0x40: [a3] is [&itable.inode[NINODE]], which IS the
   next symbol ([IcacheRef.ientry_sentinel]), so the exit test is the index
   test the induction runs on. *)
Lemma ig_sentinel_eq (j : nat) :
  (j <= NINODE)%nat ->
  eq_vec (ientry j) (mword_of_int KernelSyms.log : mword 64) = Nat.eqb j NINODE.
Proof.
  intros Hj. rewrite -ientry_sentinel.
  destruct (Nat.eqb j NINODE) eqn:E.
  - apply Nat.eqb_eq in E. subst j. by apply eq_vec_true_iff.
  - apply Nat.eqb_neq in E. apply eq_vec_false_iff. intro Hc.
    apply (ientry_inj j NINODE Hj ltac:(unfold NINODE; lia)) in Hc. contradiction.
Qed.

(* the [beq s3,zero] at +0x6a, on the arm where [empty] IS an entry *)
Lemma ig_entry_nonzero (e : nat) :
  (e <= NINODE)%nat -> eq_vec (ientry e) (zero_reg : mword 64) = false.
Proof.
  intros He. apply eq_vec_false_iff. intro Hc.
  apply (f_equal (@bv_unsigned 64)) in Hc.
  rewrite (ientry_unsigned e He) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz in Hc. unfold ISLOTSZ, KernelSyms.itable in Hc. lia.
Qed.

Lemma ig_zero_eqz : eq_vec (zero_reg : mword 64) (zero_reg : mword 64) = true.
Proof. by apply eq_vec_true_iff. Qed.

Lemma ig_zero_neqz : neq_vec (zero_reg : mword 64) (zero_reg : mword 64) = false.
Proof. unfold neq_vec. by rewrite ig_zero_eqz. Qed.

Lemma ig_entry_neqz (e : nat) :
  (e <= NINODE)%nat -> neq_vec (ientry e) (zero_reg : mword 64) = true.
Proof.
  intros He. unfold neq_vec. by rewrite (ig_entry_nonzero e He).
Qed.

(* the pool's key round-trips: [ipool_acc] hands the bundle out at
   [mword_of_int z] and the escrow wants it at the inum itself. *)
Lemma ig_trunc32_zero : trunc32 (zero_reg : mword 64) = (mword_of_int 0 : mword 32).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ig_moi_inum (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  apply bv_eq. rewrite moi32_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ---- the two fraction facts the mint needs (§13.1b's budget) ---- *)

Lemma ig_frac_valid (qt qr : Qp) :
  (1/2)%Qp = (qt + qr)%Qp -> ✓ (qt + qr/2)%Qp.
Proof.
  intro Hs. apply frac_valid.
  assert (Hstep : ((qt + qr/2) + qr/2)%Qp = (1/2)%Qp).
  { rewrite -Qp.add_assoc (Qp.div_2 qr). by rewrite Hs. }
  trans (1/2)%Qp; [ rewrite -Hstep; apply Qp.le_add_l | compute_done ].
Qed.

(* the liveness pool's counterpart of [ig_frac_valid]: the arm [1 - qt] has
   room for the minted slice, which is what [IcacheInv.iref_incr_store_au]
   now asks for in place of the bare [valid (qt + qn)] (design 14.6 -- the
   pool's arm is an exact complement, so its remainder must be POSITIVE). *)
Lemma ig_frac_lt1 (qt qr : Qp) :
  (1/2)%Qp = (qt + qr)%Qp -> (qt + qr/2 < 1)%Qp.
Proof.
  intro Hs. apply Qp.lt_sum. exists (qr/2 + 1/2)%Qp.
  rewrite Qp.add_assoc.
  assert (Hstep : ((qt + qr/2) + qr/2)%Qp = (1/2)%Qp).
  { rewrite -Qp.add_assoc (Qp.div_2 qr). by rewrite Hs. }
  rewrite Hstep. by rewrite Qp.half_half.
Qed.

Lemma ig_frac_rest (qt qr : Qp) :
  (1/2)%Qp = (qt + qr)%Qp -> (1/2 - (qt + qr/2))%Qp = Some (qr/2)%Qp.
Proof.
  intro Hs. apply Qp.sub_Some.
  rewrite -Qp.add_assoc (Qp.div_2 qr). exact Hs.
Qed.

Lemma ig_quarter_le : ((1/2/2)%Qp ≤ 1/2)%Qp.
Proof. compute_done. Qed.

Lemma ig_quarter_rest : (1/2 - 1/2/2)%Qp = Some (1/2/2)%Qp.
Proof. apply Qp.sub_Some. compute_done. Qed.

(* ---- the pure set step at the recycle: [ci] gains one entry, and the
   pool loses exactly that inum ---- *)
Lemma ig_ci_inums_insert (ci : gmap nat (mword 32 * mword 32))
    (k : nat) (d i : mword 32) :
  ci !! k = None ->
  ci_inums (<[k := (d, i)]> ci) = {[ bv_unsigned i ]} ∪ ci_inums ci.
Proof.
  intros Hk. apply set_eq. intros z.
  rewrite elem_of_union elem_of_singleton !ci_inums_spec. split.
  - intros (k2 & p & Hk2 & ->).
    destruct (decide (k2 = k)) as [->|Hne].
    + rewrite lookup_insert in Hk2. injection Hk2 as <-. by left.
    + rewrite lookup_insert_ne in Hk2; [| by apply not_eq_sym].
      right. by exists k2, p.
  - intros [-> | (k2 & p & Hk2 & ->)].
    + exists k, (d, i). rewrite lookup_insert. split; [reflexivity | reflexivity].
    + exists k2, p. rewrite lookup_insert_ne;
        [ split; [exact Hk2 | reflexivity] |].
      intros ->. rewrite Hk in Hk2. discriminate.
Qed.

Lemma ig_pool_set (P : gset Z) (S : gset Z) (z : Z) :
  P ∖ ({[z]} ∪ S) = (P ∖ S) ∖ {[z]}.
Proof. set_solver. Qed.


(* ===================================================================== *)
(*  2.  THE FUNCTION                                                      *)
(* ===================================================================== *)

Module IgetProof (Acquire : ACQUIRE) (Release : RELEASE) : IGET.

Section ProofIget.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, ICFG : icfg, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra3  := (mword_of_int 13 : mword 5).
  Notation Ra4  := (mword_of_int 14 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).
  Notation Rs4  := (mword_of_int 20 : mword 5).
  Notation Rz   := (mword_of_int 0 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz  := vm_compute; discriminate.

  Local Ltac regne := reg_ne_side.

  (* [ProofIdup.sie_b_agree], verbatim. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool) (p : mword 64) (C : iProp Σ) :
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

  Lemma wp_iget_sconf
      (γl : gname) (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (nib : nat)
      (dev inum : mword 32)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool)
    : wp_iget_sconf_body γl cn γfs γi cov logstart nib dev inum
                         m n eb p C K b.
  Proof.
    cbv beta delta [wp_iget_sconf_body].
    intros pcE ret_tgt HK HnZ Hnib Ha0 Ha1.
    unfold K_iget in HK.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hlock #Hinv #Hescs #Hpanic Hislot Hcont".
    iDestruct (sie_b_agree m n K eb b p C with "Hcg Hcnt") as %Houtb.
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    iPoseProof (igi_00 with "Htext") as "Hi00".
    iPoseProof (igi_02 with "Htext") as "Hi02".
    iPoseProof (igi_04 with "Htext") as "Hi04".
    iPoseProof (igi_06 with "Htext") as "Hi06".
    iPoseProof (igi_08 with "Htext") as "Hi08".
    iPoseProof (igi_0a with "Htext") as "Hi0a".
    iPoseProof (igi_0c with "Htext") as "Hi0c".
    iPoseProof (igi_0e with "Htext") as "Hi0e".
    iPoseProof (igi_10 with "Htext") as "Hi10".
    iPoseProof (igi_12 with "Htext") as "Hi12".
    iPoseProof (igi_14 with "Htext") as "Hi14".
    iPoseProof (igi_18 with "Htext") as "Hi18".
    iPoseProof (igi_1c with "Htext") as "Hi1c".
    (* ===== PROLOGUE (generic [b]): a SIX-slot frame ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (w1) "Hf1". iDestruct "S2" as (w2) "Hf2".
    iDestruct "S3" as (w3) "Hf3". iDestruct "S4" as (w4) "Hf4".
    iDestruct "S5" as (w5) "Hf5". iDestruct "S6" as (w6) "Hf6".
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
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { rewrite HspR1. unfold spr, sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3". iEval (rewrite -Hb4) in "Hf4".
    iEval (rewrite -Hb5) in "Hf5". iEval (rewrite -Hb6) in "Hf6".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat w1 b with "Hcg Hpc Hi02 Hf1 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hf1".
    iEval (rgne) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.iget + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat w2 b with "Hcg Hpc Hi04 Hf2 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hf2".
    iEval (rgne) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.iget + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat w3 b with "Hcg Hpc Hi06 Hf3 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hf3".
    iEval (rgne) in "Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.iget + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat w4 b with "Hcg Hpc Hi08 Hf4 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hf4".
    iEval (rgne) in "Hf4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.iget + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat w5 b with "Hcg Hpc Hi0a Hf5 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc Hf5".
    iEval (rgne) in "Hf5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.iget + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.iget + 0x0c)) (mword_of_int 0 : mword 6) Rs4
              R1 (K - 6)%nat w6 b with "Hcg Hpc Hi0c Hf6 [-]").
    iIntros (CID7 Hs7) "Hcg Hpc Hf6".
    iEval (rgne) in "Hf6".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.iget + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.iget + 0x0e)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.iget + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s2,a0 ; +0x12 c.mv s4,a1 -- the two arguments to callee-saved *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iget + 0x10)) Rs2 Ra0
              R2 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s2 : R3 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64)).
    { rewrite /R3 upd_eq. rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
      rewrite Ha0. apply add_vec_zero_l. }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.iget + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iget + 0x12)) Rs4 Ra1
              R3 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (HR4s4 : R4 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64)).
    { rewrite /R4 upd_eq. rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      rewrite /R1 upd_ne; [| nz]. rewrite Ha1. apply add_vec_zero_l. }
    assert (HR4s2 : R4 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s2 | nz]).
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.iget + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14/+0x18 a0 := &itable ; +0x1c jal acquire *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x14)) Ra0 (mword_of_int 30 : mword 20)
              R4 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iget + 0x14) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R4).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.iget + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x18)) by pcw.
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x18)) Ra0 Ra0 (mword_of_int 2290 : mword 12)
              R5 (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi18 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R5 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 2290 : mword 12)))]> R5).
    assert (HR6a0 : R6 !!! Regidx Ra0 = itable_lock).
    { rewrite /R6 upd_eq /R5 upd_eq. rewrite /itable_lock. pcw. }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.iget + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iget + 0x1c)) Rra (mword_of_int 2088066 : mword 21)
              R6 (K - 6)%nat b ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.iget + 0x1c) : mword 64) 4)]> R6).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.iget + 0x1c) : mword 64)
                        (sign_extend' 64 (mword_of_int 2088066 : mword 21))
                      = mword_of_int KernelSyms.acquire) by pcw.
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1 = spr).
    { rewrite /mA upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
      rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. rewrite /R2 upd_ne; [| nz].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = itable_lock)
      by (rewrite /mA upd_ne; [exact HR6a0 | nz]).
    assert (HmAs2 : mA !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64)).
    { rewrite /mA upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. exact HR4s2. }
    assert (HmAs4 : mA !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64)).
    { rewrite /mA upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. exact HR4s4. }
    assert (HmAra : mA !!! Regidx Rra = add_vec_int (mword_of_int (KernelSyms.iget + 0x1c) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    (* the callee-saved registers the prologue itself did NOT move *)
    assert (HmAcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 ->
              mA !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N20.
      rewrite /mA upd_ne; [| regne]. rewrite /R6 upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne]. rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne]. rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CID CID13 n eb p C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Acquire.wp_acquire_sconf γl "itable"%string
              (itable_res2 cn γfs γi cov logstart nib dev) mA
              n eb p C (K - 6)%nat b HnZ ltac:(lia)
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic [-]").
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc20 : ret_pc (mA !!! Regidx Rra) = mword_of_int (KernelSyms.iget + 0x20)).
    { rewrite HmAra. pcw. }
    iEval (rewrite Hpc20) in "Hpc".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hmsp : macq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HmAsp).
    assert (Hms2 : macq !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact HmAs2).
    assert (Hms4 : macq !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
      by (rewrite (callee_saved_lookup Hacqpins_cs (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact HmAs4).
    assert (Hmcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 ->
              macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N20.
      rewrite (callee_saved_lookup Hacqpins_cs c Hcs). by apply HmAcs. }
    (* ===== the critical section: [b] is literally [false] from here to
       the release, so every leaf collapses through [wp_next_off_intro] and
       NO hart moves -- which is what keeps the scan's induction free of a
       [CpuId] universal. ===== *)
    iPoseProof (igi_20 with "Htext") as "Hi20".
    iPoseProof (igi_22 with "Htext") as "Hi22".
    iPoseProof (igi_26 with "Htext") as "Hi26".
    iPoseProof (igi_2a with "Htext") as "Hi2a".
    iPoseProof (igi_2e with "Htext") as "Hi2e".
    iPoseProof (igi_32 with "Htext") as "Hi32".
    (* +0x20 c.li s3,0 : [empty = 0] *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.iget + 0x20)) Rs3
              (mword_of_int 0 : mword 6) (zero_reg : mword 64) macq (trap_res b + (K - 6))%nat false
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D1 := <[Regidx Rs3 := regval_into_reg (zero_reg : mword 64)]> macq).
    assert (HD1s3 : D1 !!! Regidx Rs3 = (zero_reg : mword 64))
      by (rewrite /D1; apply upd_eq).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.iget + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22/+0x26 s1 := &itable.inode[0] = [ientry 0] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x22)) Rs1 (mword_of_int 30 : mword 20)
              D1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi22 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iget + 0x22) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> D1).
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.iget + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x26)) Rs1 Rs1 (mword_of_int 2300 : mword 12)
              D2 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (D2 !!! Regidx Rs1) (sign_extend' 64 (mword_of_int 2300 : mword 12)))]> D2).
    assert (HD3s1 : D3 !!! Regidx Rs1 = ientry 0).
    { rewrite /D3 upd_eq /D2 upd_eq. rewrite /ientry. pcw. }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.iget + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a/+0x2e a3 := &itable.inode[NINODE], which IS [KernelSyms.log] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x2a)) Ra3 (mword_of_int 31 : mword 20)
              D3 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D4 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.iget + 0x2a) : mword 64)
                     (auipc_off (mword_of_int 31 : mword 20)))]> D3).
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.iget + 0x2a) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x2e)) Ra3 Ra3 (mword_of_int 900 : mword 12)
              D4 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D5 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (D4 !!! Regidx Ra3) (sign_extend' 64 (mword_of_int 900 : mword 12)))]> D4).
    assert (HD5a3 : D5 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64)).
    { rewrite /D5 upd_eq /D4 upd_eq. pcw. }
    (* PEEL BOTH LAYERS.  [D5] and [D4] both write a3, so peeling only [D5]
       and closing with [exact HD3s1] leaves the [D4] layer to CONVERSION --
       [rf_upd D3 (Regidx Ra3) v (Regidx Rs1)] against [D3 (Regidx Rs1)],
       decided in the kernel over the transparent update tower.  That single
       missing [rewrite /D4 upd_ne] was 401 s in CI, the most expensive
       statement in the build, while the peel below it (four explicit layers
       to a syntactically matching [exact]) costs nothing.  Never let an
       [exact] cross an update layer; see optimization.md. *)
    assert (HD5s1 : D5 !!! Regidx Rs1 = ientry 0).
    { rewrite /D5 upd_ne; [| nz]. rewrite /D4 upd_ne; [exact HD3s1 | nz]. }
    assert (HD5s3 : D5 !!! Regidx Rs3 = (zero_reg : mword 64)).
    { rewrite /D5 upd_ne; [| nz]. rewrite /D4 upd_ne; [| nz].
      rewrite /D3 upd_ne; [| nz]. rewrite /D2 upd_ne; [| nz]. exact HD1s3. }
    assert (HD5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> Rs1 -> c <> Rs3 -> D5 !!! Regidx c = macq !!! Regidx c).
    { intros c Hcs N9 N19.
      rewrite /D5 upd_ne; [| regne]. rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [| regne]. rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [reflexivity | regne]. }
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.iget + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.iget + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* +0x32 c.j : into the do-while at +0x44 *)
    assert (Htgt44 : add_vec (mword_of_int (KernelSyms.iget + 0x32) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.iget + 0x44)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iget + 0x32))
              (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")))
              D5 (trap_res b + (K - 6))%nat false ltac:(rewrite Htgt44; vm_compute; reflexivity)
              with "Hcg Hpc Hi32 [-]").
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt44) in "Hpc".
    (* ================================================================= *)
    (*  THE SHARED TAIL, +0x8c .. +0x9c, proven ONCE and handed to the    *)
    (*  loop as its continuation.  Both exits reach it after their own    *)
    (*  release, so it is [b]-generic; proving it HERE is what keeps the  *)
    (*  six stack cells out of the scan's induction.                      *)
    (* ================================================================= *)
    iEval (rewrite HspR1) in "Hf1". iEval (rewrite HspR1) in "Hf2".
    iEval (rewrite HspR1) in "Hf3". iEval (rewrite HspR1) in "Hf4".
    iEval (rewrite HspR1) in "Hf5". iEval (rewrite HspR1) in "Hf6".
    iPoseProof (igi_8c with "Htext") as "Hi8c".
    iPoseProof (igi_8e with "Htext") as "Hi8e".
    iPoseProof (igi_90 with "Htext") as "Hi90".
    iPoseProof (igi_92 with "Htext") as "Hi92".
    iPoseProof (igi_94 with "Htext") as "Hi94".
    iPoseProof (igi_96 with "Htext") as "Hi96".
    iPoseProof (igi_98 with "Htext") as "Hi98".
    iPoseProof (igi_9a with "Htext") as "Hi9a".
    iPoseProof (igi_9c with "Htext") as "Hi9c".
    pose (TAILC := (wp_next b p (fun (CIDt : CpuId) =>
      ∀ (mt : regfile) (kk : nat) (q : Qp),
        ⌜ (kk < NINODE)%nat
          /\ mt !!! Regidx Rs3 = ientry kk
          /\ mt !!! Regidx csp_rs1 = spr
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mt !!! Regidx c = m !!! Regidx c) ⌝ -∗
        sie_cap_gpr (CID := CIDt) mt (K - 6)%nat b p -∗
        cpu_own (CID := CIDt) n eb p C b -∗
        pc_is (CID := CIDt) (mword_of_int (KernelSyms.iget + 0x8c) : mword 64) -∗
        IcacheRef.inode_ref kk q dev inum -∗
        WP (Loop : expr riscv_lang)))%I).
    iAssert TAILC
      with "[Hcont Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hcont2".
    { rewrite /TAILC. iIntros (CIDt Hst).
      iIntros (mt kk q) "%Hmt Hcg Hcnt Hpc Href".
      destruct Hmt as (Hkk & Hmts3 & Hmtsp & Hmtcs).
      (* +0x8c c.mv a0,s3 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iget + 0x8c)) Ra0 Rs3
                mt (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c [-]").
      iIntros (CIDt1 Hst1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (P1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mt !!! Regidx Rs3))]> mt).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
        by (rewrite /P1 upd_ne; [exact Hmtsp | nz]).
      assert (Hpp8e : add_vec_int (mword_of_int (KernelSyms.iget + 0x8c) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x8e)) by pcw.
      iEval (rewrite Hpp8e) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x8e)) (mword_of_int 5 : mword 6) Rra
                P1 (K - 6)%nat (R1 !!! Regidx Rra) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi8e [Hf1] [-]").
      { iEval (rewrite HP1sp). iExact "Hf1". }
      iIntros (CIDt2 Hst2) "Hcg Hpc Hf1".
      iEval (rewrite HP1sp) in "Hf1".
      set (P2 := <[Regidx Rra := regval_into_reg (R1 !!! Regidx Rra)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
        by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
      assert (Hpp90 : add_vec_int (mword_of_int (KernelSyms.iget + 0x8e) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x90)) by pcw.
      iEval (rewrite Hpp90) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x90)) (mword_of_int 4 : mword 6) Rs0
                P2 (K - 6)%nat (R1 !!! Regidx Rs0) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi90 [Hf2] [-]").
      { iEval (rewrite HP2sp). iExact "Hf2". }
      iIntros (CIDt3 Hst3) "Hcg Hpc Hf2".
      iEval (rewrite HP2sp) in "Hf2".
      set (P3 := <[Regidx Rs0 := regval_into_reg (R1 !!! Regidx Rs0)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
        by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
      assert (Hpp92 : add_vec_int (mword_of_int (KernelSyms.iget + 0x90) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x92)) by pcw.
      iEval (rewrite Hpp92) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x92)) (mword_of_int 3 : mword 6) Rs1
                P3 (K - 6)%nat (R1 !!! Regidx Rs1) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi92 [Hf3] [-]").
      { iEval (rewrite HP3sp). iExact "Hf3". }
      iIntros (CIDt4 Hst4) "Hcg Hpc Hf3".
      iEval (rewrite HP3sp) in "Hf3".
      set (P4 := <[Regidx Rs1 := regval_into_reg (R1 !!! Regidx Rs1)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
        by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
      assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.iget + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x94)) by pcw.
      iEval (rewrite Hpp94) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x94)) (mword_of_int 2 : mword 6) Rs2
                P4 (K - 6)%nat (R1 !!! Regidx Rs2) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi94 [Hf4] [-]").
      { iEval (rewrite HP4sp). iExact "Hf4". }
      iIntros (CIDt5 Hst5) "Hcg Hpc Hf4".
      iEval (rewrite HP4sp) in "Hf4".
      set (P5 := <[Regidx Rs2 := regval_into_reg (R1 !!! Regidx Rs2)]> P4).
      assert (HP5sp : P5 !!! Regidx csp_rs1 = spr)
        by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
      assert (Hpp96 : add_vec_int (mword_of_int (KernelSyms.iget + 0x94) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x96)) by pcw.
      iEval (rewrite Hpp96) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x96)) (mword_of_int 1 : mword 6) Rs3
                P5 (K - 6)%nat (R1 !!! Regidx Rs3) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi96 [Hf5] [-]").
      { iEval (rewrite HP5sp). iExact "Hf5". }
      iIntros (CIDt6 Hst6) "Hcg Hpc Hf5".
      iEval (rewrite HP5sp) in "Hf5".
      set (P6 := <[Regidx Rs3 := regval_into_reg (R1 !!! Regidx Rs3)]> P5).
      assert (HP6sp : P6 !!! Regidx csp_rs1 = spr)
        by (rewrite /P6 upd_ne; [exact HP5sp | nz]).
      assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.iget + 0x96) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x98)) by pcw.
      iEval (rewrite Hpp98) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.iget + 0x98)) (mword_of_int 0 : mword 6) Rs4
                P6 (K - 6)%nat (R1 !!! Regidx Rs4) b ltac:(nz) ltac:(rdok)
                with "Hcg Hpc Hi98 [Hf6] [-]").
      { iEval (rewrite HP6sp). iExact "Hf6". }
      iIntros (CIDt7 Hst7) "Hcg Hpc Hf6".
      iEval (rewrite HP6sp) in "Hf6".
      set (P7 := <[Regidx Rs4 := regval_into_reg (R1 !!! Regidx Rs4)]> P6).
      assert (HP7sp : P7 !!! Regidx csp_rs1 = spr)
        by (rewrite /P7 upd_ne; [exact HP6sp | nz]).
      assert (Hpp9a : add_vec_int (mword_of_int (KernelSyms.iget + 0x98) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x9a)) by pcw.
      iEval (rewrite Hpp9a) in "Hpc".
      (* +0x9a c.addi16sp sp,48 : the frame goes back *)
      assert (Hwv : add_vec (P7 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0).
      { rewrite HP7sp. unfold spr, sp0. apply frame_cancel_48. }
      assert (Hpop : P7 !!! Regidx csp_rs1
                     = pa_stk (add_vec (P7 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
      { rewrite Hwv HP7sp. unfold spr, sp0, pa_stk, add_vec_int.
        apply f_equal. pcw. }
      iAssert (stack_own sp0 6) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6]" as "Hframe6".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hf1"; [iEval (rewrite -Hb1 HspR1); iExists _; iExact "Hf1"|].
        iSplitL "Hf2"; [iEval (rewrite -Hb2 HspR1); iExists _; iExact "Hf2"|].
        iSplitL "Hf3"; [iEval (rewrite -Hb3 HspR1); iExists _; iExact "Hf3"|].
        iSplitL "Hf4"; [iEval (rewrite -Hb4 HspR1); iExists _; iExact "Hf4"|].
        iSplitL "Hf5"; [iEval (rewrite -Hb5 HspR1); iExists _; iExact "Hf5"|].
        iSplitL "Hf6"; [iEval (rewrite -Hb6 HspR1); iExists _; iExact "Hf6"|].
        done. }
      iEval (rewrite -Hwv) in "Hframe6".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.iget + 0x9a)) (mword_of_int 3 : mword 6)
                P7 (K - 6)%nat 6 b Hpop with "Hcg Hpc Hi9a Hframe6 [-]").
      iIntros (CIDt8 Hst8) "Hcg Hpc".
      assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      set (P8 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (P7 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P7).
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (P7 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P7) with P8.
      assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.iget + 0x9a) : mword 64) 2 = mword_of_int (KernelSyms.iget + 0x9c)) by pcw.
      iEval (rewrite Hpp9c) in "Hpc".
      assert (HP8ra : P8 !!! Regidx Rra = m !!! Regidx Rra).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_eq. rewrite /R1 upd_ne; [reflexivity | nz]. }
      assert (HP8a0 : P8 !!! Regidx Ra0 = ientry kk).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq.
        rewrite Hmts3. apply add_vec_zero_l. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.iget + 0x9c)) Rra P8 K b
                ltac:(nz) with "Hcg Hpc Hi9c [-]").
      iIntros (CIDt9 Hst9) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (P8 !!! Regidx Rra) = ret_tgt) by (rewrite HP8ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDt CIDt9 n eb p C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDt9 with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! P8 kk q with "Hcg Hcnt Hpc [%] Href").
      (* [callee_saved m P8], the slot bound, and [a0 = ientry kk] *)
      split; [| split; [exact Hkk | exact HP8a0]].
      assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                P8 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /P8 upd_ne; [| regne]. rewrite /P7 upd_ne; [| regne].
        rewrite /P6 upd_ne; [| regne]. rewrite /P5 upd_ne; [| regne].
        rewrite /P4 upd_ne; [| regne]. rewrite /P3 upd_ne; [| regne].
        rewrite /P2 upd_ne; [| regne]. rewrite /P1 upd_ne; [| regne].
        by apply Hmtcs. }
      unfold callee_saved.
      assert (Hc2 : P8 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
      { rewrite /P8 upd_eq. rewrite HP7sp. unfold regval_into_reg, spr, sp0.
        apply frame_cancel_48. }
      assert (Hc8 : P8 !!! Regidx Rs0 = m !!! Regidx Rs0).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | nz]. }
      assert (Hc9 : P8 !!! Regidx Rs1 = m !!! Regidx Rs1).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_eq. rewrite /R1 upd_ne; [reflexivity | nz]. }
      assert (Hc18 : P8 !!! Regidx Rs2 = m !!! Regidx Rs2).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | nz]. }
      assert (Hc19 : P8 !!! Regidx Rs3 = m !!! Regidx Rs3).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_ne; [| nz].
        rewrite /P6 upd_eq. rewrite /R1 upd_ne; [reflexivity | nz]. }
      assert (Hc20 : P8 !!! Regidx Rs4 = m !!! Regidx Rs4).
      { rewrite /P8 upd_ne; [| nz]. rewrite /P7 upd_eq.
        rewrite /R1 upd_ne; [reflexivity | nz]. }
      repeat split;
        first [ exact Hc2 | exact Hc8 | exact Hc9 | exact Hc18 | exact Hc19 | exact Hc20
              | apply Hthread; vm_compute; first [reflexivity | discriminate] ]. }
    (* ================================================================= *)
    (*  THE SCAN.  Fuel induction on [NINODE - cursor]; [M] and [ci] are   *)
    (*  FIXED (the scan writes nothing) so the lock's resource threads     *)
    (*  through unchanged, and [b = false] keeps the hart pinned, so       *)
    (*  neither a [CpuId] nor the six stack cells ride the universal.      *)
    (* ================================================================= *)
    iDestruct "HRres" as (M ci) "(Hhalf & %Hwf & %Hciwf & Hiauth & Hslots & Hpool)".
    iPoseProof (igi_34 with "Htext") as "Hi34".
    iPoseProof (igi_36 with "Htext") as "Hi36".
    iPoseProof (igi_3a with "Htext") as "Hi3a".
    iPoseProof (igi_3c with "Htext") as "Hi3c".
    iPoseProof (igi_40 with "Htext") as "Hi40".
    iPoseProof (igi_44 with "Htext") as "Hi44".
    iPoseProof (igi_46 with "Htext") as "Hi46".
    iPoseProof (igi_4a with "Htext") as "Hi4a".
    iPoseProof (igi_4c with "Htext") as "Hi4c".
    iPoseProof (igi_50 with "Htext") as "Hi50".
    iPoseProof (igi_52 with "Htext") as "Hi52".
    iAssert (∀ (fuel j : nat) (Mr : regfile),
      ⌜(NINODE - j <= fuel)%nat⌝ -∗
      ⌜(j < NINODE)%nat⌝ -∗
      ⌜ Mr !!! Regidx Rs1 = ientry j
        /\ Mr !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64)
        /\ Mr !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64)
        /\ Mr !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64)
        /\ Mr !!! Regidx csp_rs1 = spr
        /\ Mr !!! Regidx Rra = macq !!! Regidx Rra
        /\ (forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
              Mr !!! Regidx c = macq !!! Regidx c) ⌝ -∗
      ⌜ forall (i : nat) (qi : Qp) (ni : positive) (di ii : mword 32),
          (i < j)%nat -> M !! i = Some (qi, ni) -> ci !! i = Some (di, ii) ->
          ~ (di = dev /\ ii = inum) ⌝ -∗
      ⌜ Mr !!! Regidx Rs3 = (zero_reg : mword 64)
        \/ (exists e : nat, (e < NINODE)%nat /\ Mr !!! Regidx Rs3 = ientry e
                            /\ M !! e = None) ⌝ -∗
      sie_cap_gpr Mr (trap_res b + (K - 6))%nat false p -∗
      pc_is (mword_of_int (KernelSyms.iget + 0x44) : mword 64) -∗
      cpu_own (S n) eb p C false -∗
      arm_pay n eb p -∗
      locked γl cpu_id -∗
      itable_half M -∗
      iref_slots_auth -∗
      ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn M ci i0) -∗
      ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
      iref_slot -∗
      TAILC -∗
      WP (Loop : expr riscv_lang))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (j Mr) "%Hfuel %Hj %Hreg %Hscan %Hemp Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2".
        exfalso. unfold NINODE in Hj, Hfuel. lia. }
      iIntros (j Mr) "%Hfuel %Hj %Hreg %Hscan %Hemp Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2".
      destruct Hreg as (HMs1 & HMa3 & HMs2 & HMs4 & HMsp & HMra & HMcs).
      (* ---- THE LOOP STEP, +0x3c / +0x40, shared by the three MISS
         entries (+0x4c taken, +0x52 taken, +0x36 taken) and by the
         empty-slot arm (+0x3a). ---- *)
      iAssert (∀ (Ms : regfile),
        ⌜ Ms !!! Regidx Rs1 = ientry j
          /\ Ms !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64)
          /\ Ms !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64)
          /\ Ms !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64)
          /\ Ms !!! Regidx csp_rs1 = spr
          /\ Ms !!! Regidx Rra = macq !!! Regidx Rra
          /\ (forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                Ms !!! Regidx c = macq !!! Regidx c) ⌝ -∗
        ⌜ forall (i : nat) (qi : Qp) (ni : positive) (di ii : mword 32),
            (i < S j)%nat -> M !! i = Some (qi, ni) -> ci !! i = Some (di, ii) ->
            ~ (di = dev /\ ii = inum) ⌝ -∗
        ⌜ Ms !!! Regidx Rs3 = (zero_reg : mword 64)
          \/ (exists e : nat, (e < NINODE)%nat /\ Ms !!! Regidx Rs3 = ientry e
                              /\ M !! e = None) ⌝ -∗
        sie_cap_gpr Ms (trap_res b + (K - 6))%nat false p -∗
        pc_is (mword_of_int (KernelSyms.iget + 0x3c) : mword 64) -∗
        cpu_own (S n) eb p C false -∗
        arm_pay n eb p -∗
        locked γl cpu_id -∗
        itable_half M -∗
        iref_slots_auth -∗
        ([∗ list] i0 ∈ seq 0 NINODE, islot2 cn M ci i0) -∗
        ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci) -∗
        iref_slot -∗
        TAILC -∗
        WP (Loop : expr riscv_lang))%I with "[]" as "Hstep".
      { iIntros (Ms) "%Hsreg %Hscan' %Hemp' Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2".
        destruct Hsreg as (HSs1 & HSa3 & HSs2 & HSs4 & HSsp & HSra & HScs).
        (* +0x3c addi s1,s1,136 -- [IcacheRef.ientry_step] *)
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x3c)) Rs1 Rs1
                  (mword_of_int 136 : mword 12) Ms (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3c [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (N1 := <[Regidx Rs1 := regval_into_reg
                      (add_vec (Ms !!! Regidx Rs1)
                         (sign_extend' 64 (mword_of_int 136 : mword 12)))]> Ms).
        assert (HN1s1 : N1 !!! Regidx Rs1 = ientry (S j)).
        { rewrite /N1 upd_eq. rewrite HSs1. apply ig_cursor_step. }
        assert (HN1a3 : N1 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
          by (rewrite /N1 upd_ne; [exact HSa3 | nz]).
        assert (HN1s2 : N1 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
          by (rewrite /N1 upd_ne; [exact HSs2 | nz]).
        assert (HN1s4 : N1 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
          by (rewrite /N1 upd_ne; [exact HSs4 | nz]).
        assert (HN1sp : N1 !!! Regidx csp_rs1 = spr)
          by (rewrite /N1 upd_ne; [exact HSsp | nz]).
        assert (HN1ra : N1 !!! Regidx Rra = macq !!! Regidx Rra)
          by (rewrite /N1 upd_ne; [exact HSra | nz]).
        assert (HN1s3 : N1 !!! Regidx Rs3 = Ms !!! Regidx Rs3)
          by (rewrite /N1 upd_ne; [reflexivity | nz]).
        assert (HN1cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  N1 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19. rewrite /N1 upd_ne; [| regne]. by apply HScs. }
        assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.iget + 0x3c) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x40)) by pcw.
        iEval (rewrite Hpp40) in "Hpc".
        assert (Hcmp : eq_vec (N1 !!! Regidx Rs1) (N1 !!! Regidx Ra3) = Nat.eqb (S j) NINODE).
        { rewrite HN1s1 HN1a3. apply ig_sentinel_eq. unfold NINODE in Hj |- *. lia. }
        destruct (decide (S j = NINODE)) as [Hend | Hne].
        - (* ===== THE SENTINEL: the branch is TAKEN, to +0x6a ===== *)
          assert (Htaken : eq_vec (N1 !!! Regidx Rs1) (N1 !!! Regidx Ra3) = true).
          { rewrite Hcmp. by apply Nat.eqb_eq. }
          assert (Htgt6a : add_vec (mword_of_int (KernelSyms.iget + 0x40) : mword 64)
                             (sign_extend' 64 (mword_of_int 42 : mword 13))
                           = mword_of_int (KernelSyms.iget + 0x6a)) by pcw.
          iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x40))
                    (mword_of_int 42 : mword 13) Ra3 Rs1 N1 (trap_res b + (K - 6))%nat false
                    ltac:(nz) ltac:(nz) ltac:(rgne; rgne; exact Htaken)
                    ltac:(rewrite Htgt6a; vm_compute; reflexivity)
                    with "Hcg Hpc Hi40 [-]").
          iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt6a) in "Hpc".
          iPoseProof (igi_6a with "Htext") as "Hi6a".
          destruct Hemp' as [Hz | (e & He & Hes3 & HMe)].
          + (* ===== "iget: no inodes".  THE PANIC IS LIVE: a full table is
               a real state and no caller premise refutes it (SpecIget's
               header).  The branch is TAKEN, to +0x9e. ===== *)
            iPoseProof (igi_9e with "Htext") as "Hi9e".
            iPoseProof (igi_a2 with "Htext") as "Hia2".
            iPoseProof (igi_a6 with "Htext") as "Hia6".
            assert (Htgt9e : add_vec (mword_of_int (KernelSyms.iget + 0x6a) : mword 64)
                               (sign_extend' 64 (mword_of_int 52 : mword 13))
                             = mword_of_int (KernelSyms.iget + 0x9e)) by pcw.
            iApply (wp_beqz_x0_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x6a))
                      (mword_of_int 52 : mword 13) Rs3 N1 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rgne; rewrite HN1s3 Hz; exact ig_zero_eqz)
                      ltac:(rewrite Htgt9e; vm_compute; reflexivity)
                      with "Hcg Hpc Hi6a [-]").
            iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
            iEval (rewrite Htgt9e) in "Hpc".
            iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x9e)) Ra0
                      (mword_of_int 4 : mword 20) N1 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            set (PA1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (mword_of_int (KernelSyms.iget + 0x9e) : mword 64)
                              (auipc_off (mword_of_int 4 : mword 20)))]> N1).
            assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.iget + 0x9e) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0xa2)) by pcw.
            iEval (rewrite Hppa2) in "Hpc".
            iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0xa2)) Ra0 Ra0
                      (mword_of_int 1032 : mword 12) PA1 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            set (PA2 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (rget PA1 Ra0)
                              (sign_extend' 64 (mword_of_int 1032 : mword 12)))]> PA1).
            assert (Hppa6 : add_vec_int (mword_of_int (KernelSyms.iget + 0xa2) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0xa6)) by pcw.
            iEval (rewrite Hppa6) in "Hpc".
            iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iget + 0xa6)) Rra
                      (mword_of_int 2086934 : mword 21) PA2 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hia6 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Htgtpn : add_vec (mword_of_int (KernelSyms.iget + 0xa6) : mword 64)
                               (sign_extend' 64 (mword_of_int 2086934 : mword 21))
                             = mword_of_int KernelSyms.panic) by pcw.
            iEval (rewrite Htgtpn) in "Hpc".
            iPoseProof (panic_wp_any_at _ with "Hpanic") as "Hpan".
            iApply ("Hpan" with "Htext Hpc Hcg").
          + (* ===== THE RECYCLE, four stores wide ===== *)
            iPoseProof (igi_6e with "Htext") as "Hi6e".
            iPoseProof (igi_72 with "Htext") as "Hi72".
            iPoseProof (igi_76 with "Htext") as "Hi76".
            iPoseProof (igi_78 with "Htext") as "Hi78".
            iPoseProof (igi_7c with "Htext") as "Hi7c".
            iPoseProof (igi_80 with "Htext") as "Hi80".
            iPoseProof (igi_84 with "Htext") as "Hi84".
            iPoseProof (igi_88 with "Htext") as "Hi88".
            (* a slot the scan leaves as [empty] is NOT live, so §13.9's
               restored [dom ci = dom M] says [ci] does not name it either --
               which is what collapses the recycle to ONE variant. *)
            assert (Hcik : ci !! e = None).
            { destruct Hciwf as (Hdom & _ & _ & _).
              destruct (ci !! e) as [pe|] eqn:Ece; [| reflexivity].
              exfalso.
              assert (Hin : e ∈ dom ci) by (apply elem_of_dom; by eexists).
              rewrite Hdom in Hin. apply elem_of_dom in Hin.
              rewrite HMe in Hin. by destruct Hin. }
            (* THE POOL MEMBERSHIP.  The scan proves no live slot carries the
               PAIR; the table's single-device clause (§13.11) turns that into
               "no live slot carries this INUM", which is [ipool_acc]'s
               premise -- the pool being inum-keyed. *)
            assert (Hzin : bv_unsigned inum ∈ region_inums nib ∖ ci_inums ci).
            { apply elem_of_difference. split.
              - apply region_inums_spec.
                pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
                split; [exact Hlo | exact Hnib].
              - intros Hin. apply ci_inums_spec in Hin as (i & pi & Hci & Heq).
                destruct pi as [di ii]. cbn [snd] in Heq.
                destruct Hciwf as (Hdom & Hinj & Hrange & Hdv).
                assert (Hii : ii = inum) by (apply bv_eq; symmetry; exact Heq).
                assert (Hdi : di = dev) by exact (Hdv i (di, ii) Hci).
                assert (Hlive : is_Some (M !! i)).
                { assert (Hin2 : i ∈ dom ci) by (apply elem_of_dom; by eexists).
                  rewrite Hdom in Hin2. by apply elem_of_dom in Hin2. }
                destruct Hlive as [[qi ni] HMi].
                assert (Hilt : (i < NINODE)%nat) by (apply (proj1 Hwf); by eexists).
                apply (Hscan' i qi ni di ii ltac:(lia) HMi Hci).
                split; [exact Hdi | exact Hii]. }
            assert (Hnotin : bv_unsigned inum ∉ ci_inums ci).
            { apply elem_of_difference in Hzin. tauto. }
            iDestruct (big_sepL_lookup
                         (fun (_ : nat) (i0 : nat) => ic_escrow cn γfs γi cov logstart i0)
                         (seq 0 NINODE) e e
                         ltac:(apply lookup_seq; split; [lia | exact He])
                         with "Hescs") as "#Hesc".
            iDestruct (islots2_acc_upd cn M ci e He with "Hslots") as "[Hslot Hback]".
            iEval (rewrite /islot2 HMe Hcik) in "Hslot".
            iDestruct "Hslot" as (devT inumT) "[HinT Hgid]".
            (* +0x6a falls through: [empty] IS an entry *)
            iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x6a))
                      (mword_of_int 52 : mword 13) Rs3 N1 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rgne; rewrite HN1s3 Hes3; apply ig_entry_nonzero;
                                      unfold NINODE in He |- *; lia)
                      with "Hcg Hpc Hi6a [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Hpp6e : add_vec_int (mword_of_int (KernelSyms.iget + 0x6a) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x6e)) by pcw.
            iEval (rewrite Hpp6e) in "Hpc".
            assert (HN1s3e : N1 !!! Regidx Rs3 = ientry e) by (rewrite HN1s3; exact Hes3).
            (* ---- +0x6e sw s2,0(s3) : ip->dev = dev.  The empty arm owns the
               cell WHOLE, so the recycler keeps no fraction and the ghost
               re-tag (§13.10) is what carries the value to +0x72. ---- *)
            assert (Hpa6e : add_vec (rget N1 Rs3) (sign_extend' 64 (mword_of_int 0 : mword 12))
                            = i_dev (ientry e)).
            { rewrite (rget_ne N1 Rs3 ltac:(nz)) HN1s3e. reflexivity. }
            assert (Hsv6e : trunc32 (rget N1 Rs2) = dev).
            { rewrite (rget_ne N1 Rs2 ltac:(nz)) HN1s2. apply trunc32_sext. }
            iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.iget + 0x6e)) Rs2 Rs3
                      (mword_of_int 0 : mword 12) N1 (trap_res b + (K - 6))%nat
                      (ic_id cn e (1/2) false dev inumT)
                      (⊤ ∖ ↑minstretN ∖ ↑icEscN) false ltac:(solve_ndisj)
                      with "Hcg Hpc Hi6e [Hgid] [-]").
            { rewrite Hpa6e Hsv6e.
              iInv "Hesc" as ">Hbody" "Hclose2".
              iMod (ic_open_empty_dev cn γfs γi cov logstart e devT inumT dev
                      with "Hbody Hgid") as "(Hcell & Hgid & Hcb)".
              iModIntro. iExists devT. iFrame "Hcell". iIntros "Hcell".
              iMod ("Hclose2" with "[Hcb Hcell]") as "_";
                [ iNext; iApply ("Hcb" with "Hcell") |].
              iModIntro. iFrame "Hgid". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc Hgid".
            assert (Hpp72 : add_vec_int (mword_of_int (KernelSyms.iget + 0x6e) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x72)) by pcw.
            iEval (rewrite Hpp72) in "Hpc".
            (* ---- +0x72 sw s4,4(s3) : ip->inum = inum.  The table's inum
               half joins in, the pool's bundle comes out and is parked in the
               MID arm, and the identification ghost flips at the entry's NEW
               identity.  The recycler keeps a dev half and the table's ghost
               half -- the latter is what pins the arm's FULL inum cell at
               +0x7c. ---- *)
            iDestruct (ipool_acc γfs γi cov logstart
                         (region_inums nib ∖ ci_inums ci) (bv_unsigned inum) Hzin
                         with "Hpool") as "[Hbundle Hpool]".
            iEval (rewrite ig_moi_inum) in "Hbundle".
            assert (Hpa72 : add_vec (rget N1 Rs3) (sign_extend' 64 (mword_of_int 4 : mword 12))
                            = i_inum (ientry e)).
            { rewrite (rget_ne N1 Rs3 ltac:(nz)) HN1s3e. reflexivity. }
            assert (Hsv72 : trunc32 (rget N1 Rs4) = inum).
            { rewrite (rget_ne N1 Rs4 ltac:(nz)) HN1s4. apply trunc32_sext. }
            iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.iget + 0x72)) Rs4 Rs3
                      (mword_of_int 4 : mword 12) N1 (trap_res b + (K - 6))%nat
                      (i_dev (ientry e) ↦₄{DfracOwn (1/2)} dev ∗
                       ic_id cn e (1/2) true dev inum ∗ ic_mid cn e)%I
                      (⊤ ∖ ↑minstretN ∖ ↑icEscN) false ltac:(solve_ndisj)
                      with "Hcg Hpc Hi72 [Hgid HinT Hbundle] [-]").
            { rewrite Hpa72 Hsv72.
              iInv "Hesc" as ">Hbody" "Hclose2".
              iMod (ic_open_empty_free cn γfs γi cov logstart e dev inumT dev inum
                      with "Hbody Hgid HinT")
                as "(Hincell & Hdcell & Hvld & Hraw & Hmt & Hgid1 & Hgid2)".
              iModIntro. iExists inumT. iFrame "Hincell". iIntros "Hincell".
              iDestruct (word4_pointsto_half_split with "Hdcell") as "[Hd1 Hd2]".
              iDestruct "Hvld" as (wv) "Hvld".
              iMod ("Hclose2" with "[Hd1 Hincell Hvld Hraw Hbundle Hgid1]") as "_".
              { iNext. iApply ic_close_mid.
                iApply (ic_mk_mid_arm cn γfs γi cov logstart e dev inum wv
                          with "Hd1 Hincell Hvld [Hraw Hbundle] Hgid1").
                iApply (ic_mk_unloaded with "Hraw Hbundle"). }
              iModIntro. iFrame "Hd2 Hgid2 Hmt". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc (Hd2 & Hgid2 & Hmt)".
            assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.iget + 0x72) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x76)) by pcw.
            iEval (rewrite Hpp76) in "Hpc".
            (* +0x76 c.li a5,1 *)
            iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.iget + 0x76)) Ra5
                      (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                      N1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) ltac:(pcw)
                      with "Hcg Hpc Hi76 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            set (V1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> N1).
            assert (HV1s3 : V1 !!! Regidx Rs3 = ientry e)
              by (rewrite /V1 upd_ne; [exact HN1s3e | nz]).
            assert (HV1sp : V1 !!! Regidx csp_rs1 = spr)
              by (rewrite /V1 upd_ne; [exact HN1sp | nz]).
            assert (HV1ra : V1 !!! Regidx Rra = macq !!! Regidx Rra)
              by (rewrite /V1 upd_ne; [exact HN1ra | nz]).
            assert (HV1cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                      V1 !!! Regidx c = macq !!! Regidx c).
            { intros c Hcs N9 N19. rewrite /V1 upd_ne; [| regne]. by apply HN1cs. }
            assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.iget + 0x76) : mword 64) 2
                            = mword_of_int (KernelSyms.iget + 0x78)) by pcw.
            iEval (rewrite Hpp78) in "Hpc".
            (* ---- +0x78 sw a5,8(s3) : ip->ref = 1, with [iref_alloc_step] at
               q = 1/4 inside the SAME [itable_inv] opening. ---- *)
            assert (Hpa78 : add_vec (rget V1 Rs3) (sign_extend' 64 (mword_of_int 8 : mword 12))
                            = i_ref (ientry e)).
            { rewrite (rget_ne V1 Rs3 ltac:(nz)) HV1s3. reflexivity. }
            assert (Hsv78 : trunc32 (rget V1 Ra5) = (mword_of_int 1 : mword 32)).
            { rewrite (rget_ne V1 Ra5 ltac:(nz)) /V1 upd_eq.
              unfold regval_into_reg. pcw. }
            assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
            iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.iget + 0x78)) Ra5 Rs3
                      (mword_of_int 8 : mword 12) V1 (trap_res b + (K - 6))%nat
                      (itable_half (<[e := ((1/2/2)%Qp, 1%positive)]> M) ∗
                       iref_tok e (1/2/2)%Qp)%I
                      (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(solve_ndisj)
                      with "Hcg Hpc Hi78 [Hhalf] [-]").
            { rewrite Hpa78 Hsv78.
              iInv "Hinv" as ">Hbody" "Hclose2".
              iDestruct "Hbody" as (M') "(Ha & %Hwf' & Hcells & Hlpool)".
              iDestruct (itable_half_agree with "Ha Hhalf") as %->.
              iDestruct (iref_cells_acc_upd M e He with "Hcells") as "[Hcell Hcback]".
              (* the recycled slot's liveness unit splits here, exactly as its
                 identity halves do below: 1/4 to the first reference, the rest
                 to the invariant's arm (design 14.6). *)
              iDestruct (live_pool_acc_upd M e He with "Hlpool") as "[Hlslot Hlback]".
              iModIntro. iExists (iref_word M e). iFrame "Hcell". iIntros "Hcell".
              iDestruct (itable_half_join with "Ha Hhalf") as "Hauth".
              iMod (iref_alloc_step M e (1/2/2)%Qp HMe ig_quarter_le
                      with "Hauth Hlslot") as "(Hauth & Hlslot & Htok2)".
              iDestruct (itable_half_split with "Hauth") as "[Ha Hhalf]".
              iMod ("Hclose2" with "[Ha Hcell Hcback Hlslot Hlback]") as "_".
              { iNext. iExists (<[e := ((1/2/2)%Qp, 1%positive)]> M). iFrame "Ha".
                iSplitR.
                { iPureIntro. destruct Hwf' as [Hdom Hcnt']. split.
                  - intros i Hi. destruct (decide (i = e)) as [->|Hne]; [exact He|].
                    rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
                  - intros i qi ni Hi. destruct (decide (i = e)) as [->|Hne].
                    + rewrite lookup_insert in Hi. apply Some_inj in Hi.
                      injection Hi as _ Hn. subst ni. rewrite E31. lia.
                    + rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
                      by apply (Hcnt' i qi). }
                iSplitL "Hcell Hcback".
                { iApply ("Hcback" $! ((1/2/2)%Qp, 1%positive)).
                  rewrite /iref_word lookup_insert. iExact "Hcell". }
                iApply ("Hlback" $! (<[e := ((1/2/2)%Qp, 1%positive)]> M)
                          with "[%] Hlslot").
                intros i Hi. rewrite lookup_insert_ne;
                  [reflexivity | by apply not_eq_sym]. }
              iModIntro. iFrame. }
            iApply wp_next_off_intro. iIntros "Hcg Hpc [Hhalf Htok2]".
            assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.iget + 0x78) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x7c)) by pcw.
            iEval (rewrite Hpp7c) in "Hpc".
            (* ---- +0x7c sw zero,64(s3) : ip->valid = 0 -- the window closes
               at a normal parked arm, unloaded.  The ghost half the recycler
               kept is what names the arm's FULL inum cell. ---- *)
            assert (Hpa7c : add_vec (rget V1 Rs3) (sign_extend' 64 (mword_of_int 64 : mword 12))
                            = i_valid (ientry e)).
            { rewrite (rget_ne V1 Rs3 ltac:(nz)) HV1s3. reflexivity. }
            iDestruct (sie_cap_gpr_x0 V1 (trap_res b + (K - 6))%nat false p Rz
                         ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
            assert (Hsv7c : trunc32 (rget V1 Rz) = valid_word false).
            { rewrite (rget_ne V1 Rz ltac:(nz)) Hx0. exact ig_trunc32_zero. }
            iApply (wp_sw_au_s_sconf false (mword_of_int (KernelSyms.iget + 0x7c)) Rz Rs3
                      (mword_of_int 64 : mword 12) V1 (trap_res b + (K - 6))%nat
                      (i_dev (ientry e) ↦₄{DfracOwn (1/2)} dev ∗
                       i_inum (ientry e) ↦₄{DfracOwn (1/2)} inum ∗
                       ic_id cn e (1/2) true dev inum)%I
                      (⊤ ∖ ↑minstretN ∖ ↑icEscN) false ltac:(solve_ndisj)
                      with "Hcg Hpc Hi7c [Hmt Hgid2 Hd2] [-]").
            { rewrite Hpa7c Hsv7c.
              iInv "Hesc" as ">Hbody" "Hclose2".
              iDestruct (ic_open_mid cn γfs γi cov logstart e with "Hmt Hbody")
                as "[Hmt Harm]".
              iDestruct "Harm" as (dev' inum' wv) "(Hd1 & Hincell & Hvld & Hpay & Hgid1)".
              iDestruct (ic_id_agree with "Hgid2 Hgid1") as %(_ & <- & <-).
              iModIntro. iExists wv. iFrame "Hvld". iIntros "Hvld".
              iDestruct (ic_close_mid_to_parked cn γfs γi cov logstart e dev inum
                           with "Hmt Hgid1 Hd1 Hincell Hvld Hpay") as "[Hbody Hinhalf]".
              iMod ("Hclose2" with "[Hbody]") as "_"; [by iNext |].
              iModIntro. iFrame "Hd2 Hinhalf Hgid2". }
            iApply wp_next_off_intro. iIntros "Hcg Hpc (Hd2 & Hinhalf & Hgid2)".
            (* the identity budget: half of each cell is the table's, and the
               minted reference takes 1/4 of it (§13.1b/§13.1e). *)
            iDestruct (inode_ident_split e (1/2/2) (1/2/2) dev inum) as "[Hsplit _]".
            iEval (rewrite Qp.div_2) in "Hsplit".
            iDestruct ("Hsplit" with "[Hd2 Hinhalf]") as "[Hid1 Hid2]";
              [ rewrite /inode_ident; iFrame | ].
            assert (Hp1 : Pos.to_nat 1 = 1%nat) by reflexivity.
            iDestruct ("Hback" $! (<[e := ((1/2/2)%Qp, 1%positive)]> M)
                         (<[e := (dev, inum)]> ci)
                         with "[%] [%] [Hid1 Hislot Hgid2]") as "Hslots".
            { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
            { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
            { rewrite /islot2 !lookup_insert Hp1.
              rewrite /islot_rest_at ig_quarter_rest /inode_ident.
              iDestruct "Hid1" as "[Hidd Hidn]".
              iFrame "Hidd Hidn Hgid2". iExact "Hislot". }
            iAssert (itable_res2 cn γfs γi cov logstart nib dev)
              with "[Hhalf Hiauth Hslots Hpool]" as "HRres".
            { iExists (<[e := ((1/2/2)%Qp, 1%positive)]> M), (<[e := (dev, inum)]> ci).
              iFrame "Hhalf Hiauth".
              iSplitR; [| iSplitR].
              - iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
                + intros i Hi. destruct (decide (i = e)) as [->|Hne]; [exact He|].
                  rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
                + intros i qi ni Hi. destruct (decide (i = e)) as [->|Hne].
                  * rewrite lookup_insert in Hi. apply Some_inj in Hi.
                    injection Hi as _ Hn. subst ni. rewrite E31. lia.
                  * rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
                    by apply (Hcnt' i qi).
              - iPureIntro. destruct Hciwf as (Hdom & Hinj & Hrange & Hdv).
                split_and!.
                + rewrite !dom_insert_L Hdom. reflexivity.
                + (* injectivity: the scan is what proves it *)
                  intros k1 k2 p1 p2 Hp1' Hp2' Heq.
                  destruct (decide (k1 = e)) as [->|Hn1];
                    destruct (decide (k2 = e)) as [->|Hn2]; try reflexivity.
                  * rewrite lookup_insert in Hp1'. injection Hp1' as <-.
                    rewrite lookup_insert_ne in Hp2'; [| by apply not_eq_sym].
                    exfalso. apply Hnotin.
                    apply ci_inums_spec. exists k2, p2. split; [exact Hp2'|].
                    cbn [snd] in Heq. exact Heq.
                  * rewrite lookup_insert in Hp2'. injection Hp2' as <-.
                    rewrite lookup_insert_ne in Hp1'; [| by apply not_eq_sym].
                    exfalso. apply Hnotin.
                    apply ci_inums_spec. exists k1, p1. split; [exact Hp1'|].
                    cbn [snd] in Heq. symmetry. exact Heq.
                  * rewrite lookup_insert_ne in Hp1'; [| by apply not_eq_sym].
                    rewrite lookup_insert_ne in Hp2'; [| by apply not_eq_sym].
                    exact (Hinj k1 k2 p1 p2 Hp1' Hp2' Heq).
                + intros k1 p1 Hp1'. destruct (decide (k1 = e)) as [->|Hn1].
                  * rewrite lookup_insert in Hp1'. injection Hp1' as <-.
                    simpl. exact Hnib.
                  * rewrite lookup_insert_ne in Hp1'; [| by apply not_eq_sym].
                    exact (Hrange k1 p1 Hp1').
                + intros k1 p1 Hp1'. destruct (decide (k1 = e)) as [->|Hn1].
                  * rewrite lookup_insert in Hp1'. injection Hp1' as <-. reflexivity.
                  * rewrite lookup_insert_ne in Hp1'; [| by apply not_eq_sym].
                    exact (Hdv k1 p1 Hp1').
              - iFrame "Hslots".
                rewrite (ig_ci_inums_insert ci e dev inum Hcik) ig_pool_set.
                iExact "Hpool". }
            assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.iget + 0x7c) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x80)) by pcw.
            iEval (rewrite Hpp80) in "Hpc".
            (* +0x80/+0x84 a0 := &itable ; +0x88 jal release ; then the tail *)
            iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x80)) Ra0
                      (mword_of_int 30 : mword 20) V1 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi80 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            set (V2 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (mword_of_int (KernelSyms.iget + 0x80) : mword 64)
                             (auipc_off (mword_of_int 30 : mword 20)))]> V1).
            assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.iget + 0x80) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x84)) by pcw.
            iEval (rewrite Hpp84) in "Hpc".
            iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x84)) Ra0 Ra0
                      (mword_of_int 2182 : mword 12) V2 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            iEval (rgne) in "Hcg".
            set (V3 := <[Regidx Ra0 := regval_into_reg
                          (add_vec (V2 !!! Regidx Ra0)
                             (sign_extend' 64 (mword_of_int 2182 : mword 12)))]> V2).
            assert (HV3a0 : V3 !!! Regidx Ra0 = itable_lock).
            { rewrite /V3 upd_eq /V2 upd_eq. rewrite /itable_lock. pcw. }
            assert (HV3thr : forall c : mword 5, is_cs_idx c = true ->
                      V3 !!! Regidx c = V1 !!! Regidx c).
            { intros c Hcs.
              rewrite /V3 upd_ne; [| regne]. rewrite /V2 upd_ne; [reflexivity | regne]. }
            assert (HV3sp : V3 !!! Regidx csp_rs1 = spr)
              by (rewrite (HV3thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HV1sp).
            assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.iget + 0x84) : mword 64) 4
                            = mword_of_int (KernelSyms.iget + 0x88)) by pcw.
            iEval (rewrite Hpp88) in "Hpc".
            iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iget + 0x88)) Rra
                      (mword_of_int 2088094 : mword 21) V3 (trap_res b + (K - 6))%nat false
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hi88 [-]").
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            set (V4 := <[Regidx Rra := regval_into_reg
                          (add_vec_int (mword_of_int (KernelSyms.iget + 0x88) : mword 64) 4)]> V3).
            assert (Htgtrel2 : add_vec (mword_of_int (KernelSyms.iget + 0x88) : mword 64)
                                 (sign_extend' 64 (mword_of_int 2088094 : mword 21))
                               = mword_of_int KernelSyms.release) by pcw.
            iEval (rewrite Htgtrel2) in "Hpc".
            assert (HV4a0 : V4 !!! Regidx Ra0 = itable_lock)
              by (rewrite /V4 upd_ne; [exact HV3a0 | nz]).
            assert (HV4ra : V4 !!! Regidx Rra
                            = add_vec_int (mword_of_int (KernelSyms.iget + 0x88) : mword 64) 4)
              by (rewrite /V4; apply upd_eq).
            assert (HV4thr : forall c : mword 5, is_cs_idx c = true ->
                      V4 !!! Regidx c = V1 !!! Regidx c).
            { intros c Hcs. rewrite /V4 upd_ne; [| regne]. by apply HV3thr. }
            assert (HV4sp : V4 !!! Regidx csp_rs1 = spr)
              by (rewrite (HV4thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HV1sp).
            (* the acquire handed the window index out as [trap_res b + N];
               release wants it as [trap_res outb + N], and [Houtb] says those
               are the same bool.  Pure re-spelling; it is what makes the
               acquire/release pair compose back to [N]. *)
            iEval (rewrite Houtb) in "Hcg".
            iApply (Release.wp_release_sconf γl itable_lock "itable"%string
                      (itable_res2 cn γfs γi cov logstart nib dev) V4
                      n eb p C (K - 6)%nat ltac:(rewrite HV4a0; reflexivity) ltac:(lia)
                      with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay [-]").
            { iExact "Hlock". }
            iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
            iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
            rewrite <- Houtb in Hsr.
            pose proof Hrelpins as Hrelpins_cs.
            assert (Hpc8c : ret_pc (V4 !!! Regidx Rra) = mword_of_int (KernelSyms.iget + 0x8c)).
            { rewrite HV4ra. pcw. }
            iEval (rewrite Hpc8c) in "Hpc".
            assert (Hmrs3 : mr !!! Regidx Rs3 = ientry e).
            { rewrite (callee_saved_lookup Hrelpins_cs (mword_of_int 19)
                         ltac:(vm_compute; reflexivity)).
              rewrite (HV4thr (mword_of_int 19) ltac:(vm_compute; reflexivity)).
              exact HV1s3. }
            assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
              by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HV4sp).
            assert (Hmrcs : forall c : mword 5, is_cs_idx c = true ->
                      c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                      c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                      mr !!! Regidx c = m !!! Regidx c).
            { intros c Hcs N2 N8 N9 N18 N19 N20.
              rewrite (callee_saved_lookup Hrelpins_cs c Hcs) (HV4thr c Hcs)
                      (HV1cs c Hcs N9 N19). by apply Hmcs. }
            iEval (rewrite /TAILC) in "Hcont2".
            iSpecialize ("Hcont2" $! CIDr with "[]"); [ iPureIntro; wp_next_chain | ].
            iApply ("Hcont2" $! mr e (1/2/2)%Qp with "[%] Hcg Hcnt Hpc [Htok2 Hid2]").
            * split; [exact He|]. split; [exact Hmrs3|].
              split; [exact Hmrsp | exact Hmrcs].
            * rewrite /IcacheRef.inode_ref. iFrame "Htok2 Hid2".
        - (* ===== the back edge to +0x44, at cursor [S j] ===== *)
          assert (Hfall : eq_vec (N1 !!! Regidx Rs1) (N1 !!! Regidx Ra3) = false).
          { rewrite Hcmp. by apply Nat.eqb_neq. }
          iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x40))
                    (mword_of_int 42 : mword 13) Ra3 Rs1 N1 (trap_res b + (K - 6))%nat false
                    ltac:(nz) ltac:(nz) ltac:(rgne; rgne; exact Hfall)
                    with "Hcg Hpc Hi40 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.iget + 0x40) : mword 64) 4
                          = mword_of_int (KernelSyms.iget + 0x44)) by pcw.
          iEval (rewrite Hpp44) in "Hpc".
          iApply ("IHf" $! (S j) N1 with "[%] [%] [%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
          + unfold NINODE in Hfuel, Hj, Hne |- *. lia.
          + unfold NINODE in Hj, Hne |- *. lia.
          + split; [exact HN1s1|]. split; [exact HN1a3|]. split; [exact HN1s2|].
            split; [exact HN1s4|]. split; [exact HN1sp|]. split; [exact HN1ra|].
            exact HN1cs.
          + exact Hscan'.
          + rewrite HN1s3. exact Hemp'. }
      (* ---- +0x44 c.lw a5,8(s1) : the ref word, through [itable_inv] ---- *)
      assert (Hk : (j < NINODE)%nat) by exact Hj.
      assert (Hpa44 : add_vec (rget Mr Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                      = i_ref (ientry j)).
      { rewrite (rget_ne Mr Rs1 ltac:(nz)) HMs1. reflexivity. }
      iApply (wp_lw_au_s_sconf true (mword_of_int (KernelSyms.iget + 0x44)) Ra5 Rs1
                (mword_of_int 8 : mword 12) Mr (trap_res b + (K - 6))%nat
                (fun v => (⌜v = iref_word M j⌝ ∗ itable_half M)%I)
                (⊤ ∖ ↑minstretN ∖ ↑icacheN) false
                ltac:(nz) ltac:(rdok) ltac:(solve_ndisj)
                with "Hcg Hpc Hi44 [Hhalf] [-]").
      { rewrite Hpa44.
        iMod (iref_load_locked_au (⊤ ∖ ↑minstretN) M j
                ltac:(solve_ndisj) Hk with "Hinv Hhalf") as "[Hcell Hback]".
        iModIntro. iExists (iref_word M j). iFrame "Hcell". iIntros "Hcell".
        iMod ("Hback" with "Hcell") as "Hhalf". iModIntro. by iFrame. }
      iIntros (vld). iApply wp_next_off_intro. iIntros "Hcg Hpc [%Hvld Hhalf]".
      subst vld.
      destruct (M !! j) as [[qj nj]|] eqn:HMj.
      - (* ===== A LIVE SLOT: [bge x0,a5] falls through ===== *)
        assert (Hiw : iref_word M j = (mword_of_int (Z.pos nj) : mword 32))
          by (rewrite /iref_word HMj; reflexivity).
        iEval (rewrite Hiw) in "Hcg".
        set (L1 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (mword_of_int (Z.pos nj) : mword 32))]> Mr).
        assert (HL1a5 : L1 !!! Regidx Ra5
                        = sign_extend' 64 (mword_of_int (Z.pos nj) : mword 32))
          by (rewrite /L1; apply upd_eq).
        assert (HL1s1 : L1 !!! Regidx Rs1 = ientry j)
          by (rewrite /L1 upd_ne; [exact HMs1 | nz]).
        assert (HL1s2 : L1 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
          by (rewrite /L1 upd_ne; [exact HMs2 | nz]).
        assert (HL1s4 : L1 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
          by (rewrite /L1 upd_ne; [exact HMs4 | nz]).
        assert (HL1a3 : L1 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
          by (rewrite /L1 upd_ne; [exact HMa3 | nz]).
        assert (HL1sp : L1 !!! Regidx csp_rs1 = spr)
          by (rewrite /L1 upd_ne; [exact HMsp | nz]).
        assert (HL1ra : L1 !!! Regidx Rra = macq !!! Regidx Rra)
          by (rewrite /L1 upd_ne; [exact HMra | nz]).
        assert (HL1s3 : L1 !!! Regidx Rs3 = Mr !!! Regidx Rs3)
          by (rewrite /L1 upd_ne; [reflexivity | nz]).
        assert (HL1cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  L1 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19. rewrite /L1 upd_ne; [| regne]. by apply HMcs. }
        assert (Hnjb : (Z.pos nj < 2 ^ 31)%Z) by exact (icM_wf_count M j qj nj Hwf HMj).
        iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x46))
                  (mword_of_int 8174 : mword 13) Ra5 L1 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rgne; rewrite HL1a5; exact (ig_ref_spos nj Hnjb))
                  with "Hcg Hpc Hi46 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.iget + 0x46) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x4a)) by pcw.
        iEval (rewrite Hpp4a) in "Hpc".
        (* the slot's identity is readable off [ci] -- §13.9's [dom ci = dom M] *)
        assert (Hcij : exists di : mword 32 * mword 32, ci !! j = Some di).
        { destruct Hciwf as [Hdom _].
          assert (Hin : j ∈ dom ci) by (rewrite Hdom; apply elem_of_dom; by eexists).
          apply elem_of_dom in Hin. exact Hin. }
        destruct Hcij as [[dj ij] Hcij].
        iDestruct (islots2_acc_upd cn M ci j Hk with "Hslots") as "[Hslot Hback]".
        iEval (rewrite /islot2 HMj Hcij) in "Hslot".
        iDestruct "Hslot" as "(Hrest & Hiu & Hgid)".
        destruct (1/2 - qj)%Qp as [qj'|] eqn:Eqj; last first.
        { iEval (rewrite /islot_rest_at Eqj) in "Hrest". iDestruct "Hrest" as "[]". }
        iEval (rewrite /islot_rest_at /inode_ident Eqj) in "Hrest".
        iDestruct "Hrest" as "[Hdcell Hncell]".
        (* +0x4a c.lw a4,0(s1) : ip->dev *)
        assert (Hpa4a : add_vec (rget L1 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                        = i_dev (ientry j)).
        { rewrite (rget_ne L1 Rs1 ltac:(nz)) HL1s1. reflexivity. }
        iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.iget + 0x4a)) Ra4 Rs1
                  (mword_of_int 0 : mword 12) L1 (trap_res b + (K - 6))%nat dj false
                  (dqm := DfracOwn qj') ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi4a [Hdcell] [-]").
        { rewrite Hpa4a. iExact "Hdcell". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hdcell".
        iEval (rewrite Hpa4a) in "Hdcell".
        set (L2 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 dj)]> L1).
        assert (HL2a4 : L2 !!! Regidx Ra4 = (sign_extend' 64 dj : mword 64))
          by (rewrite /L2; apply upd_eq).
        assert (HL2s1 : L2 !!! Regidx Rs1 = ientry j)
          by (rewrite /L2 upd_ne; [exact HL1s1 | nz]).
        assert (HL2s2 : L2 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
          by (rewrite /L2 upd_ne; [exact HL1s2 | nz]).
        assert (HL2s4 : L2 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
          by (rewrite /L2 upd_ne; [exact HL1s4 | nz]).
        assert (HL2a3 : L2 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
          by (rewrite /L2 upd_ne; [exact HL1a3 | nz]).
        assert (HL2sp : L2 !!! Regidx csp_rs1 = spr)
          by (rewrite /L2 upd_ne; [exact HL1sp | nz]).
        assert (HL2ra : L2 !!! Regidx Rra = macq !!! Regidx Rra)
          by (rewrite /L2 upd_ne; [exact HL1ra | nz]).
        assert (HL2s3 : L2 !!! Regidx Rs3 = Mr !!! Regidx Rs3)
          by (rewrite /L2 upd_ne; [exact HL1s3 | nz]).
        assert (HL2cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  L2 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19. rewrite /L2 upd_ne; [| regne]. by apply HL1cs. }
        assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.iget + 0x4a) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x4c)) by pcw.
        iEval (rewrite Hpp4c) in "Hpc".
        assert (Htgt3c : add_vec (mword_of_int (KernelSyms.iget + 0x4c) : mword 64)
                           (sign_extend' 64 (mword_of_int 8176 : mword 13))
                         = mword_of_int (KernelSyms.iget + 0x3c)) by pcw.
        destruct (decide (dj = dev)) as [Hdeq | Hdne]; last first.
        { (* the device differs: MISS, and [ip->inum] is never read *)
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x4c))
                    (mword_of_int 8176 : mword 13) Rs2 Ra4 L2 (trap_res b + (K - 6))%nat false
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HL2a4 HL2s2; by apply ig_neqv_ne)
                    ltac:(rewrite Htgt3c; vm_compute; reflexivity)
                    with "Hcg Hpc Hi4c [-]").
          iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt3c) in "Hpc".
          iDestruct ("Hback" $! M ci with "[%] [%] [Hdcell Hncell Hiu Hgid]") as "Hslots";
            [ done | done | | ].
          { rewrite /islot2 HMj Hcij. iFrame "Hiu Hgid".
            rewrite /islot_rest_at /inode_ident Eqj. iFrame. }
          iApply ("Hstep" $! L2 with "[%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
          - split; [exact HL2s1|]. split; [exact HL2a3|]. split; [exact HL2s2|].
            split; [exact HL2s4|]. split; [exact HL2sp|]. split; [exact HL2ra|].
            exact HL2cs.
          - intros i qi ni di ii Hi HMi Hcii.
            destruct (decide (i = j)) as [->|Hij].
            + rewrite HMj in HMi. rewrite Hcij in Hcii.
              injection Hcii as <- <-. intros [Hd _]. exact (Hdne Hd).
            + apply (Hscan i qi ni di ii ltac:(lia) HMi Hcii).
          - rewrite HL2s3. exact Hemp. }
        (* +0x4c falls through: the device matched *)
        subst dj.
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x4c))
                  (mword_of_int 8176 : mword 13) Rs2 Ra4 L2 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL2a4 HL2s2; exact (ig_neqv_refl dev))
                  with "Hcg Hpc Hi4c [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.iget + 0x4c) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x50)) by pcw.
        iEval (rewrite Hpp50) in "Hpc".
        (* +0x50 c.lw a4,4(s1) : ip->inum, read only when the device matched *)
        assert (Hpa50 : add_vec (rget L2 Rs1) (sign_extend' 64 (mword_of_int 4 : mword 12))
                        = i_inum (ientry j)).
        { rewrite (rget_ne L2 Rs1 ltac:(nz)) HL2s1. reflexivity. }
        iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.iget + 0x50)) Ra4 Rs1
                  (mword_of_int 4 : mword 12) L2 (trap_res b + (K - 6))%nat ij false
                  (dqm := DfracOwn qj') ltac:(nz) ltac:(rdok)
                  with "Hcg Hpc Hi50 [Hncell] [-]").
        { rewrite Hpa50. iExact "Hncell". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hncell".
        iEval (rewrite Hpa50) in "Hncell".
        set (L3 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 ij)]> L2).
        assert (HL3a4 : L3 !!! Regidx Ra4 = (sign_extend' 64 ij : mword 64))
          by (rewrite /L3; apply upd_eq).
        assert (HL3a5 : L3 !!! Regidx Ra5
                        = sign_extend' 64 (mword_of_int (Z.pos nj) : mword 32)).
        { rewrite /L3 upd_ne; [| nz]. rewrite /L2 upd_ne; [| nz]. exact HL1a5. }
        assert (HL3s1 : L3 !!! Regidx Rs1 = ientry j)
          by (rewrite /L3 upd_ne; [exact HL2s1 | nz]).
        assert (HL3s2 : L3 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
          by (rewrite /L3 upd_ne; [exact HL2s2 | nz]).
        assert (HL3s4 : L3 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
          by (rewrite /L3 upd_ne; [exact HL2s4 | nz]).
        assert (HL3a3 : L3 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
          by (rewrite /L3 upd_ne; [exact HL2a3 | nz]).
        assert (HL3sp : L3 !!! Regidx csp_rs1 = spr)
          by (rewrite /L3 upd_ne; [exact HL2sp | nz]).
        assert (HL3ra : L3 !!! Regidx Rra = macq !!! Regidx Rra)
          by (rewrite /L3 upd_ne; [exact HL2ra | nz]).
        assert (HL3s3 : L3 !!! Regidx Rs3 = Mr !!! Regidx Rs3)
          by (rewrite /L3 upd_ne; [exact HL2s3 | nz]).
        assert (HL3cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  L3 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19. rewrite /L3 upd_ne; [| regne]. by apply HL2cs. }
        assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.iget + 0x50) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x52)) by pcw.
        iEval (rewrite Hpp52) in "Hpc".
        assert (Htgt3c2 : add_vec (mword_of_int (KernelSyms.iget + 0x52) : mword 64)
                            (sign_extend' 64 (mword_of_int 8170 : mword 13))
                          = mword_of_int (KernelSyms.iget + 0x3c)) by pcw.
        destruct (decide (ij = inum)) as [Hieq | Hine]; last first.
        { (* the inum differs: MISS *)
          iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x52))
                    (mword_of_int 8170 : mword 13) Rs4 Ra4 L3 (trap_res b + (K - 6))%nat false
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite HL3a4 HL3s4; by apply ig_neqv_ne)
                    ltac:(rewrite Htgt3c2; vm_compute; reflexivity)
                    with "Hcg Hpc Hi52 [-]").
          iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt3c2) in "Hpc".
          iDestruct ("Hback" $! M ci with "[%] [%] [Hdcell Hncell Hiu Hgid]") as "Hslots";
            [ done | done | | ].
          { rewrite /islot2 HMj Hcij. iFrame "Hiu Hgid".
            rewrite /islot_rest_at /inode_ident Eqj. iFrame. }
          iApply ("Hstep" $! L3 with "[%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
          - split; [exact HL3s1|]. split; [exact HL3a3|]. split; [exact HL3s2|].
            split; [exact HL3s4|]. split; [exact HL3sp|]. split; [exact HL3ra|].
            exact HL3cs.
          - intros i qi ni di ii Hi HMi Hcii.
            destruct (decide (i = j)) as [->|Hij].
            + rewrite Hcij in Hcii. injection Hcii as <- <-.
              intros [_ Hn]. exact (Hine Hn).
            + apply (Hscan i qi ni di ii ltac:(lia) HMi Hcii).
          - rewrite HL3s3. exact Hemp. }
        (* ===== THE CACHE HIT (+0x56 .. +0x68) ===== *)
        subst ij.
        iPoseProof (igi_56 with "Htext") as "Hi56".
        iPoseProof (igi_58 with "Htext") as "Hi58".
        iPoseProof (igi_5a with "Htext") as "Hi5a".
        iPoseProof (igi_5e with "Htext") as "Hi5e".
        iPoseProof (igi_62 with "Htext") as "Hi62".
        iPoseProof (igi_66 with "Htext") as "Hi66".
        iPoseProof (igi_68 with "Htext") as "Hi68".
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x52))
                  (mword_of_int 8170 : mword 13) Rs4 Ra4 L3 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(nz)
                  ltac:(rgne; rgne; rewrite HL3a4 HL3s4; exact (ig_neqv_refl inum))
                  with "Hcg Hpc Hi52 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.iget + 0x52) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x56)) by pcw.
        iEval (rewrite Hpp56) in "Hpc".
        (* the iref-slot conservation law: caller's unit + the table's *)
        iDestruct (iref_slots_combine with "Hiu Hislot") as "Hiu".
        assert (Hsucc : (Pos.to_nat nj + 1)%nat = Pos.to_nat (Pos.succ nj))
          by (rewrite Pos2Nat.inj_succ; lia).
        iEval (rewrite Hsucc) in "Hiu".
        iDestruct (iref_slots_no_overflow with "Hiauth Hiu") as %[Hno1 Hno2].
        (* +0x56 c.addiw a5,a5,1 *)
        iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.iget + 0x56)) Ra5
                  (mword_of_int 1 : mword 6) L3 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi56 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (L4 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (subrange_vec_dec
                         (add_vec (L3 !!! Regidx Ra5)
                            (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> L3).
        assert (HL4s1 : L4 !!! Regidx Rs1 = ientry j)
          by (rewrite /L4 upd_ne; [exact HL3s1 | nz]).
        assert (Hstv : trunc32 (rget L4 Ra5) = (mword_of_int (Z.pos (Pos.succ nj)) : mword 32)).
        { rewrite (rget_ne L4 Ra5 ltac:(nz)).
          rewrite /L4 upd_eq. unfold regval_into_reg. rewrite HL3a5.
          rewrite (moi32_storeval_succ (Z.pos nj) ltac:(lia)
                     ltac:(pose proof Hno1 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
          f_equal. rewrite Pos2Z.inj_succ. lia. }
        assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.iget + 0x56) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x58)) by pcw.
        iEval (rewrite Hpp58) in "Hpc".
        (* +0x58 c.sw a5,8(s1) : the ref word and the authority move together *)
        assert (Hpa58 : add_vec (rget L4 Rs1) (sign_extend' 64 (mword_of_int 8 : mword 12))
                        = i_ref (ientry j)).
        { rewrite (rget_ne L4 Rs1 ltac:(nz)) HL4s1. reflexivity. }
        assert (Hqv : (qj + qj'/2 < 1)%Qp) by (apply ig_frac_lt1; by apply Qp.sub_Some).
        iApply (wp_sw_au_s_sconf true (mword_of_int (KernelSyms.iget + 0x58)) Ra5 Rs1
                  (mword_of_int 8 : mword 12) L4 (trap_res b + (K - 6))%nat
                  (itable_half (<[j := ((qj + qj'/2)%Qp, Pos.succ nj)]> M) ∗
                   iref_tok j (qj'/2)%Qp)%I
                  (⊤ ∖ ↑minstretN ∖ ↑icacheN) false ltac:(solve_ndisj)
                  with "Hcg Hpc Hi58 [Hhalf] [-]").
        { rewrite Hpa58 Hstv.
          iMod (iref_incr_store_au (⊤ ∖ ↑minstretN) M j qj (qj'/2)%Qp nj
                  ltac:(solve_ndisj) HMj Hqv Hno1 with "Hinv Hhalf") as "[Hcell Hback2]".
          iModIntro. iExists (iref_word M j). iFrame "Hcell". iIntros "Hcell".
          iMod ("Hback2" with "Hcell") as "[Hhalf Htok2]". iModIntro. iFrame. }
        iApply wp_next_off_intro. iIntros "Hcg Hpc [Hhalf Htok2]".
        (* the minted identity fraction comes out of the table's retained share *)
        iDestruct (inode_ident_split j (qj'/2) (qj'/2) dev inum) as "[Hsplit _]".
        iEval (rewrite Qp.div_2) in "Hsplit".
        iDestruct ("Hsplit" with "[Hdcell Hncell]") as "[Hid1 Hid2]";
          [ rewrite /inode_ident; iFrame | ].
        iDestruct ("Hback" $! (<[j := ((qj + qj'/2)%Qp, Pos.succ nj)]> M) ci
                     with "[%] [%] [Hid1 Hiu Hgid]") as "Hslots".
        { intros i Hi. rewrite lookup_insert_ne; [reflexivity | by apply not_eq_sym]. }
        { intros i Hi. reflexivity. }
        { rewrite /islot2 lookup_insert Hcij. iFrame "Hiu Hgid".
          rewrite /islot_rest_at (ig_frac_rest qj qj' ltac:(by apply Qp.sub_Some)).
          rewrite /inode_ident. iFrame. }
        iAssert (itable_res2 cn γfs γi cov logstart nib dev)
          with "[Hhalf Hiauth Hslots Hpool]" as "HRres".
        { iExists (<[j := ((qj + qj'/2)%Qp, Pos.succ nj)]> M), ci.
          iFrame "Hhalf Hiauth Hpool".
          iSplitR; [| iSplitR; [| iExact "Hslots"]].
          2:{ iPureIntro. destruct Hciwf as (Hdom & Hinj & Hrange & Hdv).
              split_and!; [| exact Hinj | exact Hrange | exact Hdv].
              (* NOT [set_solver]: from inside a whole-function proof it
                 rescans the entire Iris context -- 145 s for this one domain
                 identity (optimization.md).  [j] is already in [dom M], so
                 the re-insert does not move the domain at all. *)
              rewrite (dom_insert_lookup_L M j _ (mk_is_Some _ _ HMj)).
              exact Hdom. }
          iPureIntro. destruct Hwf as [Hdom Hcnt']. split.
          - intros i Hi. destruct (decide (i = j)) as [->|Hne]; [exact Hk|].
            rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym]. by apply Hdom.
          - intros i qi ni Hi. destruct (decide (i = j)) as [->|Hne].
            + rewrite lookup_insert in Hi. apply Some_inj in Hi.
              injection Hi as _ Hn. subst ni. exact Hno1.
            + rewrite lookup_insert_ne in Hi; [|by apply not_eq_sym].
              by apply (Hcnt' i qi). }
        assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.iget + 0x58) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x5a)) by pcw.
        iEval (rewrite Hpp5a) in "Hpc".
        (* +0x5a/+0x5e a0 := &itable ; +0x62 jal release *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.iget + 0x5a)) Ra0
                  (mword_of_int 30 : mword 20) L4 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (L5 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.iget + 0x5a) : mword 64)
                         (auipc_off (mword_of_int 30 : mword 20)))]> L4).
        assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.iget + 0x5a) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x5e)) by pcw.
        iEval (rewrite Hpp5e) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.iget + 0x5e)) Ra0 Ra0
                  (mword_of_int 2220 : mword 12) L5 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5e [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (L6 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (L5 !!! Regidx Ra0)
                         (sign_extend' 64 (mword_of_int 2220 : mword 12)))]> L5).
        assert (HL6a0 : L6 !!! Regidx Ra0 = itable_lock).
        { rewrite /L6 upd_eq /L5 upd_eq. rewrite /itable_lock. pcw. }
        assert (HL6s1 : L6 !!! Regidx Rs1 = ientry j).
        { rewrite /L6 upd_ne; [| nz]. rewrite /L5 upd_ne; [| nz]. exact HL4s1. }
        assert (HL6thr : forall c : mword 5, is_cs_idx c = true ->
                  L6 !!! Regidx c = L3 !!! Regidx c).
        { intros c Hcs.
          rewrite /L6 upd_ne; [| regne]. rewrite /L5 upd_ne; [| regne].
          rewrite /L4 upd_ne; [reflexivity | regne]. }
        assert (HL6sp : L6 !!! Regidx csp_rs1 = spr)
          by (rewrite (HL6thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HL3sp).
        assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.iget + 0x5e) : mword 64) 4
                        = mword_of_int (KernelSyms.iget + 0x62)) by pcw.
        iEval (rewrite Hpp62) in "Hpc".
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.iget + 0x62)) Rra
                  (mword_of_int 2088132 : mword 21) L6 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi62 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (L7 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KernelSyms.iget + 0x62) : mword 64) 4)]> L6).
        assert (Htgtrel : add_vec (mword_of_int (KernelSyms.iget + 0x62) : mword 64)
                            (sign_extend' 64 (mword_of_int 2088132 : mword 21))
                          = mword_of_int KernelSyms.release) by pcw.
        iEval (rewrite Htgtrel) in "Hpc".
        assert (HL7a0 : L7 !!! Regidx Ra0 = itable_lock)
          by (rewrite /L7 upd_ne; [exact HL6a0 | nz]).
        assert (HL7s1 : L7 !!! Regidx Rs1 = ientry j)
          by (rewrite /L7 upd_ne; [exact HL6s1 | nz]).
        assert (HL7ra : L7 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KernelSyms.iget + 0x62) : mword 64) 4)
          by (rewrite /L7; apply upd_eq).
        assert (HL7thr : forall c : mword 5, is_cs_idx c = true ->
                  L7 !!! Regidx c = L3 !!! Regidx c).
        { intros c Hcs. rewrite /L7 upd_ne; [| regne]. by apply HL6thr. }
        assert (HL7sp : L7 !!! Regidx csp_rs1 = spr)
          by (rewrite (HL7thr csp_rs1 ltac:(vm_compute; reflexivity)); exact HL3sp).
        (* same re-spelling as the HIT arm above. *)
        iEval (rewrite Houtb) in "Hcg".
        iApply (Release.wp_release_sconf γl itable_lock "itable"%string
                  (itable_res2 cn γfs γi cov logstart nib dev) L7
                  n eb p C (K - 6)%nat ltac:(rewrite HL7a0; reflexivity) ltac:(lia)
                  with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay [-]").
        { iExact "Hlock". }
        iIntros (CIDr Hsr mr) "Hcg Hpc %Hrelpins Hcnt".
        iEval (rewrite <- Houtb) in "Hcg". iEval (rewrite <- Houtb) in "Hcnt".
        rewrite <- Houtb in Hsr.
        pose proof Hrelpins as Hrelpins_cs.
        assert (Hpc66 : ret_pc (L7 !!! Regidx Rra) = mword_of_int (KernelSyms.iget + 0x66)).
        { rewrite HL7ra. pcw. }
        iEval (rewrite Hpc66) in "Hpc".
        assert (Hmrs1 : mr !!! Regidx Rs1 = ientry j)
          by (rewrite (callee_saved_lookup Hrelpins_cs (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact HL7s1).
        assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
          by (rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)); exact HL7sp).
        assert (Hmrcs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  mr !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19.
          rewrite (callee_saved_lookup Hrelpins_cs c Hcs) (HL7thr c Hcs). by apply HL3cs. }
        (* +0x66 c.mv s3,s1 : the hit funnels into the common exit *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iget + 0x66)) Rs3 Rs1
                  mr (K - 6)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi66 [-]").
        iIntros (CIDh1 Hsh1) "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (Z1 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Rs1))]> mr).
        assert (HZ1s3 : Z1 !!! Regidx Rs3 = ientry j).
        { rewrite /Z1 upd_eq. rewrite Hmrs1. apply add_vec_zero_l. }
        assert (HZ1sp : Z1 !!! Regidx csp_rs1 = spr)
          by (rewrite /Z1 upd_ne; [exact Hmrsp | nz]).
        assert (HZ1cs : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                  c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                  Z1 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N18 N19 N20.
          rewrite /Z1 upd_ne; [| regne].
          rewrite (Hmrcs c Hcs N9 N19). by apply Hmcs. }
        assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.iget + 0x66) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x68)) by pcw.
        iEval (rewrite Hpp68) in "Hpc".
        (* +0x68 c.j : to the common tail at +0x8c *)
        assert (Htgt8c : add_vec (mword_of_int (KernelSyms.iget + 0x68) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0"))))
                         = mword_of_int (KernelSyms.iget + 0x8c)) by pcw.
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.iget + 0x68))
                  (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")))
                  Z1 (K - 6)%nat b ltac:(rewrite Htgt8c; vm_compute; reflexivity)
                  with "Hcg Hpc Hi68 [-]").
        iIntros (CIDh2 Hsh2). iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt8c) in "Hpc".
        iDestruct (cpu_own_transport CIDr CIDh2 n eb p C b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iEval (rewrite /TAILC) in "Hcont2".
        iSpecialize ("Hcont2" $! CIDh2 with "[]"); [ iPureIntro; wp_next_chain | ].
        iApply ("Hcont2" $! Z1 j (qj'/2)%Qp with "[%] Hcg Hcnt Hpc [Htok2 Hid2]").
        + split; [exact Hk|]. split; [exact HZ1s3|]. split; [exact HZ1sp | exact HZ1cs].
        + rewrite /IcacheRef.inode_ref. iFrame "Htok2 Hid2".
      - (* ===== A FREE SLOT: [bge x0,a5] is TAKEN, to +0x34 ===== *)
        assert (Hiw : iref_word M j = (mword_of_int 0 : mword 32))
          by (rewrite /iref_word HMj; reflexivity).
        iEval (rewrite Hiw) in "Hcg".
        set (L1 := <[Regidx Ra5 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 32))]> Mr).
        assert (HL1a5 : L1 !!! Regidx Ra5
                        = sign_extend' 64 (mword_of_int 0 : mword 32))
          by (rewrite /L1; apply upd_eq).
        assert (HL1s1 : L1 !!! Regidx Rs1 = ientry j)
          by (rewrite /L1 upd_ne; [exact HMs1 | nz]).
        assert (HL1s2 : L1 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
          by (rewrite /L1 upd_ne; [exact HMs2 | nz]).
        assert (HL1s4 : L1 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
          by (rewrite /L1 upd_ne; [exact HMs4 | nz]).
        assert (HL1a3 : L1 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
          by (rewrite /L1 upd_ne; [exact HMa3 | nz]).
        assert (HL1sp : L1 !!! Regidx csp_rs1 = spr)
          by (rewrite /L1 upd_ne; [exact HMsp | nz]).
        assert (HL1ra : L1 !!! Regidx Rra = macq !!! Regidx Rra)
          by (rewrite /L1 upd_ne; [exact HMra | nz]).
        assert (HL1s3 : L1 !!! Regidx Rs3 = Mr !!! Regidx Rs3)
          by (rewrite /L1 upd_ne; [reflexivity | nz]).
        assert (HL1cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                  L1 !!! Regidx c = macq !!! Regidx c).
        { intros c Hcs N9 N19. rewrite /L1 upd_ne; [| regne]. by apply HMcs. }
        assert (Htgt34 : add_vec (mword_of_int (KernelSyms.iget + 0x46) : mword 64)
                           (sign_extend' 64 (mword_of_int 8174 : mword 13))
                         = mword_of_int (KernelSyms.iget + 0x34)) by pcw.
        iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x46))
                  (mword_of_int 8174 : mword 13) Ra5 L1 (trap_res b + (K - 6))%nat false
                  ltac:(nz) ltac:(rgne; rewrite HL1a5; exact ig_ref_bge_zero)
                  ltac:(rewrite Htgt34; vm_compute; reflexivity)
                  with "Hcg Hpc Hi46 [-]").
        iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
        iEval (rewrite Htgt34) in "Hpc".
        (* +0x34 c.bnez a5 : the ref word is zero, so it falls through *)
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x34))
                  (mword_of_int 4 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  L1 (trap_res b + (K - 6))%nat false ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HL1a5; exact ig_ref_neqz_zero)
                  with "Hcg Hpc Hi34 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.iget + 0x34) : mword 64) 2
                        = mword_of_int (KernelSyms.iget + 0x36)) by pcw.
        iEval (rewrite Hpp36) in "Hpc".
        assert (Htgt3c3 : add_vec (mword_of_int (KernelSyms.iget + 0x36) : mword 64)
                            (sign_extend' 64 (mword_of_int 6 : mword 13))
                          = mword_of_int (KernelSyms.iget + 0x3c)) by pcw.
        destruct Hemp as [Hz | (e & He & Hes3 & HMe)].
        + (* [empty] is still 0: the branch falls through and +0x3a takes it *)
          iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.iget + 0x36))
                    (mword_of_int 6 : mword 13) Rs3 L1 (trap_res b + (K - 6))%nat false
                    ltac:(nz) ltac:(rgne; rewrite HL1s3 Hz; exact ig_zero_neqz)
                    with "Hcg Hpc Hi36 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.iget + 0x36) : mword 64) 4
                          = mword_of_int (KernelSyms.iget + 0x3a)) by pcw.
          iEval (rewrite Hpp3a) in "Hpc".
          (* +0x3a c.mv s3,s1 : this slot becomes the recycle candidate *)
          iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.iget + 0x3a)) Rs3 Rs1
                    L1 (trap_res b + (K - 6))%nat false ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3a [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          iEval (rgne) in "Hcg".
          set (L2 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs1))]> L1).
          assert (HL2s3 : L2 !!! Regidx Rs3 = ientry j).
          { rewrite /L2 upd_eq. rewrite HL1s1. apply add_vec_zero_l. }
          assert (HL2s1 : L2 !!! Regidx Rs1 = ientry j)
            by (rewrite /L2 upd_ne; [exact HL1s1 | nz]).
          assert (HL2s2 : L2 !!! Regidx Rs2 = (sign_extend' 64 dev : mword 64))
            by (rewrite /L2 upd_ne; [exact HL1s2 | nz]).
          assert (HL2s4 : L2 !!! Regidx Rs4 = (sign_extend' 64 inum : mword 64))
            by (rewrite /L2 upd_ne; [exact HL1s4 | nz]).
          assert (HL2a3 : L2 !!! Regidx Ra3 = (mword_of_int KernelSyms.log : mword 64))
            by (rewrite /L2 upd_ne; [exact HL1a3 | nz]).
          assert (HL2sp : L2 !!! Regidx csp_rs1 = spr)
            by (rewrite /L2 upd_ne; [exact HL1sp | nz]).
          assert (HL2ra : L2 !!! Regidx Rra = macq !!! Regidx Rra)
            by (rewrite /L2 upd_ne; [exact HL1ra | nz]).
          assert (HL2cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 -> c <> Rs3 ->
                    L2 !!! Regidx c = macq !!! Regidx c).
          { intros c Hcs N9 N19. rewrite /L2 upd_ne; [| regne]. by apply HL1cs. }
          assert (Hpp3c2 : add_vec_int (mword_of_int (KernelSyms.iget + 0x3a) : mword 64) 2
                           = mword_of_int (KernelSyms.iget + 0x3c)) by pcw.
          iEval (rewrite Hpp3c2) in "Hpc".
          iApply ("Hstep" $! L2 with "[%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
          * split; [exact HL2s1|]. split; [exact HL2a3|]. split; [exact HL2s2|].
            split; [exact HL2s4|]. split; [exact HL2sp|]. split; [exact HL2ra|].
            exact HL2cs.
          * intros i qi ni di ii Hi HMi Hcii.
            destruct (decide (i = j)) as [->|Hij].
            -- rewrite HMj in HMi. discriminate.
            -- apply (Hscan i qi ni di ii ltac:(lia) HMi Hcii).
          * right. exists j. split; [exact Hk|]. split; [exact HL2s3 | exact HMj].
        + (* a candidate is already held: the branch is TAKEN, straight to +0x3c *)
          iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.iget + 0x36))
                    (mword_of_int 6 : mword 13) Rs3 L1 (trap_res b + (K - 6))%nat false
                    ltac:(nz)
                    ltac:(rgne; rewrite HL1s3 Hes3; apply ig_entry_neqz;
                          unfold NINODE in He |- *; lia)
                    ltac:(rewrite Htgt3c3; vm_compute; reflexivity)
                    with "Hcg Hpc Hi36 [-]").
          iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
          iEval (rewrite Htgt3c3) in "Hpc".
          iApply ("Hstep" $! L1 with "[%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
          * split; [exact HL1s1|]. split; [exact HL1a3|]. split; [exact HL1s2|].
            split; [exact HL1s4|]. split; [exact HL1sp|]. split; [exact HL1ra|].
            exact HL1cs.
          * intros i qi ni di ii Hi HMi Hcii.
            destruct (decide (i = j)) as [->|Hij].
            -- rewrite HMj in HMi. discriminate.
            -- apply (Hscan i qi ni di ii ltac:(lia) HMi Hcii).
          * right. exists e. split; [exact He|]. split; [| exact HMe].
            rewrite HL1s3. exact Hes3. }
    (* enter the scan at slot 0 with NINODE units of fuel *)
    iApply ("Hloop" $! NINODE 0%nat D5
              with "[%] [%] [%] [%] [%] Hcg Hpc Hcnt Hpay Htok Hhalf Hiauth Hslots Hpool Hislot Hcont2").
    - lia.
    - unfold NINODE; lia.
    - split; [exact HD5s1|]. split; [exact HD5a3|].
      split; [rewrite (HD5thr Rs2 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)); exact Hms2|].
      split; [rewrite (HD5thr Rs4 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)); exact Hms4|].
      split; [rewrite (HD5thr csp_rs1 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz)); exact Hmsp|].
      split; [ rewrite /D5 upd_ne; [| nz]; rewrite /D4 upd_ne; [| nz];
               rewrite /D3 upd_ne; [| nz]; rewrite /D2 upd_ne; [| nz];
               rewrite /D1 upd_ne; [reflexivity | nz] |].
      exact HD5thr.
    - intros i qi ni di ii Hi. exfalso. lia.
    - left. exact HD5s3.
  Qed.

End ProofIget.

End IgetProof.
