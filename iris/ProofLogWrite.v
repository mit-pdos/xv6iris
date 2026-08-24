(* ProofLogWrite.v -- log_write over the SIE-agnostic sconf world.

     void log_write(struct buf *b) {
       int i;
       acquire(&log.lock);
       if (log.lh.n >= LOGBLOCKS)      panic("too big a transaction");
       if (log.outstanding < 1)        panic("log_write outside of trans");
       for (i = 0; i < log.lh.n; i++)
         if (log.lh.block[i] == b->blockno) break;   // log absorption
       log.lh.block[i] = b->blockno;
       if (i == log.lh.n) { bpin(b); log.lh.n++; }
       release(&log.lock);
     }

   THE SHAPE OF THE PROOF.  Everything happens inside one spinlock critical
   section, and the whole ghost choreography (LogInv/FsBlocks) is packaged
   into TWO CLOSING WANDS built ONCE, right after [acquire], and carried
   through the scan as a single [∧]:

     [lw_closeA]  the ABSORB closer -- premise ⌜uint bno ∈ map uint W⌝;
     [lw_closeB]  the APPEND closer -- premise ⌜uint bno ∉ map uint W⌝.

   The two premises are what makes the [∧] provable with no case split on
   the payload polarity [d]: the handle's dirty half agrees with
   [log_state]'s cov big-op entry, which reads
   [bool_decide (uint bno ∈ map uint W)], so ⌜∈⌝ forces d = true (the
   earlier bpin's reference is already parked in the payload) and ⌜∉⌝
   forces d = false (so the false->true flip is available).  Whichever
   branch the code takes, the scan hands over exactly the matching pure
   fact, and the OTHER closer is discharged vacuously.

   THE DUPLICATED SLOT STORE.  gcc emitted [lh.block[i] = b->blockno]
   twice (CodeLogWrite.v's header): the APPEND copy at +0x52 (addressed off
   4*lh.n) and the ABSORB copy at +0x94 (addressed off 4*i), the latter
   rejoining the bpin block at +0x66 through the [beq a2,a5] at +0xaa when
   i == n.  That branch is NOT dead: it is how the n == 0 entry from the
   +0x34 guard reaches bpin.  So +0x94 is proved ONCE, as [lw_blk94],
   keyed on ⌜i = nl⌝, and both store copies converge on [lw_pin] (+0x66).

   THE REFUND.  The caller's [bslot] goes in and comes back out
   unconditionally.  On the absorb path it is simply never spent; on the
   append path bpin absorbs it and the [lh.n++] store is where the batch's
   POOL gives one back -- [bslots ((LOGBLOCKS - nl) + 2)] splits as
   [bslot ∗ bslots ((LOGBLOCKS - S nl) + 2)], which is exactly the
   pool's invariant re-established at nl+1.  That split needs nl <= 29,
   which is the same fact that kills the "too big a transaction" panic.

   BOTH PANICS ARE DEAD.  [log_op γ (S u)] against the ledger authority
   gives out >= 1 (kills "outside of trans" at +0x2e) and op_sum om >= 1,
   which with log_res's sum tie [nl + op_sum om <= LOGBLOCKS] gives
   nl <= 29 (kills "too big a transaction" at +0x22). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import PrintintArith.
Require Import BufOwn BcacheInv BioInv.
Require Import BreadLru.
Require Import FsBlocks LogInv.
Require Import CodeLogWrite.
Require Import SpecAcquire SpecRelease SpecBpin.
Require Import SpecLogWrite.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure arithmetic, all over plain [Z]/[nat] so no solver ever runs      *)
(*  inside the WP context.                                               *)
(* ===================================================================== *)

(* the signed 64-bit compares the three branch tests reduce to, at the
   small nonnegative literals log_write actually holds *)
Local Lemma lw_ltb_s (a b : Z) :
  0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 ->
  zopz0zI_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.ltb a b.
Proof.
  intros Ha Hb. unfold zopz0zI_s.
  rewrite (sint_moi_small a ltac:(change (2^63) with 9223372036854775808; lia)).
  rewrite (sint_moi_small b ltac:(change (2^63) with 9223372036854775808; lia)).
  reflexivity.
Qed.

Local Lemma lw_geb_s0 (b : Z) :
  0 <= b < 2 ^ 31 ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz.
  rewrite (sint_moi_small b ltac:(change (2^63) with 9223372036854775808; lia)).
  reflexivity.
Qed.

Local Lemma lw_eqv_moi (a b : Z) :
  0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 ->
  eq_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.eqb a b.
Proof.
  intros Ha Hb.
  destruct (Z.eqb a b) eqn:Hab.
  - apply Z.eqb_eq in Hab. subst b. apply eq_vec_true_iff. reflexivity.
  - apply Z.eqb_neq in Hab. apply eq_vec_false_iff.
    intro Hc. apply Hab. apply (f_equal bv_unsigned) in Hc.
    rewrite !moi64_unsigned in Hc. unfold bv_wrap in Hc.
    assert (Hm : bv_modulus 64 = 2 ^ 64) by (vm_compute; reflexivity).
    rewrite Hm !Z.mod_small in Hc; [exact Hc | | ];
      change (2^64) with 18446744073709551616; change (2^31) with 2147483648 in *; lia.
Qed.

(* [c.li rd,k] / [c.addiw rd,rd,1] on a small nonnegative counter *)
Local Lemma lw_li (k : Z) :
  0 <= k < 2 ^ 31 ->
  add_vec (zero_reg : mword 64) (mword_of_int k : mword 64) = mword_of_int k.
Proof. intro Hk. apply add_vec_zero_l. Qed.

(* the two shifts: [slli rd,rs,2] at a small index *)
Local Lemma lw_slli2 (i : nat) : (i <= 30)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat i) : mword 64)
    (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (4 * Z.of_nat i).
Proof.
  intro H. do 31 (destruct i as [|i]; [apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

(* the sign-extended immediates log_write forms *)
Local Lemma lw_s0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s12 : sign_extend' 64 (mword_of_int 12 : mword 12) = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s16 : sign_extend' 64 (mword_of_int 16 : mword 12) = (mword_of_int 16 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s44 : sign_extend' 64 (mword_of_int 44 : mword 12) = (mword_of_int 44 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s4c : sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
                     = (mword_of_int 4 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s0c : sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))
                     = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s29c : sign_extend' 64 (sign_extend' 12 (mword_of_int 29 : mword 6))
                      = (mword_of_int 29 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Local Lemma lw_s1c : sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                     = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the log's own address, and the two cell addresses the code forms out of
   [&log] plus a computed byte displacement *)
Local Lemma lw_log_pa : log_pa = (mword_of_int KernelSyms.log : mword 64).
Proof. reflexivity. Qed.

(* &log + (4*i + 32), then the [16(reg)] displacement: the slot cell *)
Local Lemma lw_slot_addr (i : nat) : (i <= 30)%nat ->
  add_vec (add_vec (mword_of_int KernelSyms.log : mword 64)
                   (mword_of_int (4 * Z.of_nat i + 32)))
          (mword_of_int 16 : mword 64)
  = lh_block i.
Proof.
  intro Hi.
  assert (H1 : (mword_of_int (4 * Z.of_nat i + 32) : mword 64)
               = mword_of_int (Z.of_nat (32 + 4 * i))).
  { f_equal. lia. }
  rewrite H1.
  change (add_vec (mword_of_int KernelSyms.log : mword 64)
            (mword_of_int (Z.of_nat (32 + 4 * i))))
    with (pa_add (log_pa : mword 64) (32 + 4 * i)%nat).
  assert (H2 : (mword_of_int 16 : mword 64) = mword_of_int (Z.of_nat 16%nat))
    by (f_equal; lia).
  rewrite H2 pa_add_bump. rewrite /lh_block. f_equal. lia.
Qed.

(* [Z.of_nat i + 1] as the successor index -- a NAMED equation, because
   [lia] cannot be run on it inside the WP context (the zify hook) *)
Local Lemma lw_succ_moi (i : nat) :
  (mword_of_int (Z.of_nat i + 1) : mword 64) = mword_of_int (Z.of_nat (S i)).
Proof. f_equal. lia. Qed.

(* the loop's own access, [0(a4)], is the cursor itself *)
Local Lemma lw_cursor_at (i : nat) :
  add_vec (lh_block i) (mword_of_int 0 : mword 64) = lh_block i.
Proof.
  assert (H0 : (mword_of_int 0 : mword 64) = mword_of_int (Z.of_nat 0%nat))
    by reflexivity.
  rewrite /lh_block H0 pa_add_bump. f_equal. lia.
Qed.

(* the loop cursor's bump: &lh.block[i] + 4 = &lh.block[i+1] *)
Local Lemma lw_cursor_step (i : nat) :
  add_vec (lh_block i) (mword_of_int 4 : mword 64) = lh_block (S i).
Proof.
  assert (H2 : (mword_of_int 4 : mword 64) = mword_of_int (Z.of_nat 4%nat))
    by (f_equal; lia).
  rewrite /lh_block H2 pa_add_bump. f_equal. lia.
Qed.

(* ---- the write set after an APPEND, at the [uint] image the batch's
   pure facts and its cov big-op are stated over ---- *)

Local Lemma lw_mem_snoc (W : list (mword 32)) (w : mword 32) :
  uint w ∈ map uint (W ++ [w]).
Proof.
  apply elem_of_list_fmap. exists w. split; [reflexivity|].
  apply elem_of_app. right. apply elem_of_list_singleton. reflexivity.
Qed.

Local Lemma lw_bd_snoc (W : list (mword 32)) (w : mword 32) (x : Z) :
  x <> uint w ->
  bool_decide (x ∈ map uint (W ++ [w])) = bool_decide (x ∈ map uint W).
Proof.
  intro Hne. apply bool_decide_ext. split.
  - intro Hin. apply elem_of_list_fmap in Hin as (w2 & -> & Hw).
    apply elem_of_app in Hw as [Hw | Hw].
    + apply elem_of_list_fmap. exists w2. split; [reflexivity | exact Hw].
    + apply elem_of_list_singleton in Hw. subst w2. congruence.
  - intro Hin. apply elem_of_list_fmap in Hin as (w2 & -> & Hw).
    apply elem_of_list_fmap. exists w2. split; [reflexivity|].
    apply elem_of_app. left. exact Hw.
Qed.

Local Lemma lw_nodup_snoc (W : list (mword 32)) (w : mword 32) :
  NoDup (map uint W) -> ~ (uint w ∈ map uint W) ->
  NoDup (map uint (W ++ [w])).
Proof.
  intros Hnd Hni.
  assert (Heq : map uint (W ++ [w]) = map uint W ++ [uint w]) by apply map_app.
  rewrite Heq. apply NoDup_app.
  - exact Hnd.
  - constructor; [ intros [] | constructor ].
  - intros x Hx Hy. destruct Hy as [Heqx | []]. subst x.
    apply Hni. apply elem_of_list_In. exact Hx.
Qed.

Local Lemma lw_wok_snoc (W : list (mword 32)) (w : mword 32)
    (cov : gset Z) (logstart : Z) :
  (forall v, v ∈ W -> uint v ∈ cov /\ ~ (uint v ∈ log_region_set logstart)) ->
  uint w ∈ cov -> ~ (uint w ∈ log_region_set logstart) ->
  forall v, v ∈ W ++ [w] -> uint v ∈ cov /\ ~ (uint v ∈ log_region_set logstart).
Proof.
  intros Hall Hc Hl v Hv. apply elem_of_app in Hv as [Hv | Hv].
  - exact (Hall v Hv).
  - apply elem_of_list_singleton in Hv. subst v. split; assumption.
Qed.

(* uint is injective on [mword 32] -- the scan compares words, the batch's
   pure facts speak of [uint] *)
Local Lemma lw_uint32 (a : mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Local Lemma lw_uint_inj (a b : mword 32) : uint a = uint b -> a = b.
Proof. rewrite !lw_uint32. intro H. by apply bv_eq. Qed.

(* ===================================================================== *)

Module LogWriteProof (Acquire : ACQUIRE) (Release : RELEASE) (Bpin : BPIN) : LOG_WRITE.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

(* ===================================================================== *)
(*  The named bundles: the function's own continuation, its frame, the    *)
(*  register invariant, the output resources and the two closing wands.   *)
(* ===================================================================== *)
Section LogWriteDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* [Fb] is THE CALLER'S RECEIPT for the logged view -- opaque here, and
     threaded through every block exactly like [Bud].  The whole-function
     proof instantiates it with the atomic update's [Φfsb]; the derived
     [wp_log_write_gen] takes [Φfsb := fsblock (fs_bytes γfs) (uint bno) bs],
     the shape this used to be spelled with. *)
  Definition lw_cont `{GEN : GenId} `{CID0 : CpuId}
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (dev : mword 32) (k : nat) (pidv bno : mword 32)
      (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (m : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) : iProp Σ :=
    wp_next b p (fun (CID : CpuId) =>
      ∀ mr,
      sie_cap_gpr KT1 mr K b p -∗
      cpu_own n eb p b lks -∗
      pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
      ⌜ callee_saved m mr ⌝ -∗
      Bud -∗
      Fb -∗
      bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true -∗
      bslot -∗
      WP (Loop : expr riscv_lang))%I.

  (* re-anchor the continuation from the hart a block was entered at to the
     hart it hands it on at (ProofBread.bd_cont_shift's twin) *)
  Lemma lw_cont_shift `{GEN : GenId} `{CIDa : CpuId} `{CIDb : CpuId}
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (dev : mword 32) (k : nat) (pidv bno : mword 32)
      (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (m : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    (b = false \/ p = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    lw_cont (CID0 := CIDa) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    lw_cont (CID0 := CIDb) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks.
  Proof.
    intros Hs. rewrite /lw_cont /wp_next.
    iIntros "H" (CID2 Hs2). iApply "H". iPureIntro.
    intro Hb. specialize (Hs2 Hb). specialize (Hs Hb). congruence.
  Qed.

  (* the four frame slots (slot 4 -- offset 0 -- is pushed but never written) *)
  Definition lw_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     ∃ w : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈[KT1] w)%I.

  (* the register facts every block carries about its arrival map *)
  Definition lw_regs (m M : regfile) : Prop :=
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1 : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
    /\ M !!! Regidx Rs1 = (m !!! Regidx Ra0 : mword 64)
    /\ (forall c : mword 5, is_cs_idx c = true ->
          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
          M !!! Regidx c = (m !!! Regidx c : mword 64)).

  (* what the caller gets back *)
  Definition lw_res (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (γd : disk_names) (cov : gset Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ) : iProp Σ :=
    (Bud ∗ Fb ∗
     bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno bs bsd true ∗
     bslot)%I.

  (* ---- the two closing wands, and the two post-store remainders ---- *)

  (* ABSORB: the slot array comes back UNCHANGED (the store rewrote W[i]
     with the same word), the junk head and lh.n untouched, and the
     caller's own slot unit passes straight through. *)
  Definition lw_closeA (Psi : gmap Z (list (bv 8)) -> iProp Σ) (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (γd : disk_names) (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (nl : nat) (W : list (mword 32)) : iProp Σ :=
    (⌜uint bno ∈ map uint W⌝ -∗
     (∃ jk : mword 32, lh_block nl ↦₄ jk) -∗
     ([∗ list] j ↦ w ∈ W, lh_block j ↦₄ w) -∗
     b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
     lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
     bslot ==∗
     log_res Psi γ bn γfs cov logstart ∗
     lw_res bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud)%I.

  (* APPEND: the junk cell at index nl now holds bno, bpin's reference has
     been minted, and lh.n has been bumped. *)
  Definition lw_closeB (Psi : gmap Z (list (bv 8)) -> iProp Σ) (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (γd : disk_names) (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (nl : nat) (W : list (mword 32)) : iProp Σ :=
    (⌜~ (uint bno ∈ map uint W)⌝ -∗
     ([∗ list] j ↦ w ∈ W, lh_block j ↦₄ w) -∗
     lh_block nl ↦₄ bno -∗
     b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
     (∃ (q : Qp) (dv bv : mword 32), bref bn k q dv bv) -∗
     lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl + 1) : mword 32) ==∗
     log_res Psi γ bn γfs cov logstart ∗
     lw_res bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud)%I.

  (* what [lw_pin] (+0x66) still owes: the bpin reference and the bumped
     lh.n cell *)
  Definition lw_closeP (Psi : gmap Z (list (bv 8)) -> iProp Σ) (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (γd : disk_names) (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (nl : nat) : iProp Σ :=
    (b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
     (∃ (q : Qp) (dv bv : mword 32), bref bn k q dv bv) -∗
     lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl + 1) : mword 32) ==∗
     log_res Psi γ bn γfs cov logstart ∗
     lw_res bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud)%I.

  (* ... and what the absorb path still owes at the +0xaa fall-through *)
  Definition lw_closeR (Psi : gmap Z (list (bv 8)) -> iProp Σ) (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (γd : disk_names) (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (nl : nat) : iProp Σ :=
    (b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
     lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
     bslot ==∗
     log_res Psi γ bn γfs cov logstart ∗
     lw_res bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud)%I.

  (* ---- the payload's two halves, extracted / re-assembled without a
     case split leaking into the whole-function proof ---- *)

  Lemma lw_pay_split (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd : list (bv 8)) (d : bool) :
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗
    (uint bno ↪[fs_cache γfs]{#(1/2)} bsl ∗
     uint bno ↪[fs_dirty γfs]{#(1/2)} d ∗
     (if d then ∃ q : Qp, bref bn k q dv bno else ⌜bsd = bsl⌝)).
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "[[$ $] $]".
    - rewrite /fs_mclean. iIntros "[[$ $] $]".
  Qed.

  Lemma lw_pay_mk (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bs bsd : list (bv 8)) :
    uint bno ↪[fs_cache γfs]{#(1/2)} bs -∗
    uint bno ↪[fs_dirty γfs]{#(1/2)} true -∗
    (∃ q : Qp, bref bn k q dv bno) -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bs bsd true.
  Proof.
    rewrite /bio_pay /fs_view /= /fs_mdirty.
    iIntros "H1 H2 H3". iFrame.
  Qed.

End LogWriteDefs.

(* ===================================================================== *)
(*  THE BLOCKS.  Each is a [Local Lemma] with its OWN [CID0] binder, so a *)
(*  block whose predecessor returned on a different hart is applied at    *)
(*  the hart it actually starts on.                                      *)
(* ===================================================================== *)
Section LogWriteBlocks.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* ================================================================== *)
  (*  +0xae .. +0xc2 : release(&log.lock), the epilogue and the return.  *)
  (*  Both paths converge here with [log_res] already reassembled.       *)
  (* ================================================================== *)
  Local Lemma lw_rel `{GEN : GenId} `{CID0 : CpuId}
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ)
      (m M : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    (K_log_write <= K)%nat ->
    match n with O => eb | S _ => false end = b ->
    lw_regs m M ->
    (* [lks] IS THE CALLER'S OWN HELD SET -- the one [lw_cont] exits at.  The
       critical section runs one rank higher, at [{[rank "log"]} ∪ lks], which
       is exactly what acquire minted; [locks_below_not_elem] turns this bound
       into the non-membership that makes the release's set difference collapse
       back onto [lks]. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (trap_res b + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.log_write + 0xae) : mword 64) -∗
    log_ctx_at Psi γ bn γfs cov logstart dev -∗
    cpu_own (S n) eb p false ({["log"]} ∪ lks) -∗
    arm_pay KT1 n eb p -∗
    locked (ln_lk γ) cpu_id -∗
    log_res Psi γ bn γfs cov logstart -∗
    lw_frame m -∗
    lw_res bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud -∗
    lw_cont (CID0 := CID0) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbeq (Hsp & Hs1v & Hthr) Hno.
    iIntros "Hcg #Htext Hpc #Hlctx Hcnt Hpay Htok HRres Hframe Hout Hcont".
    iDestruct "Hlctx" as "(#Hlock & #Hdevc & #Hstc & _)".
    (* the frame geometry *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    rewrite /lw_frame.
    iDestruct "Hframe" as "(Hr24 & Hr16 & Hr8 & Hg4)".
    iDestruct "Hg4" as (vg4) "Hg4".
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    (* ===== +0xae / +0xb2 : a0 := &log ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0xae)) Ra0 (mword_of_int 30 : mword 20)
              M (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_ae with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0xae) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> M).
    assert (Hppb2 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xae) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0xb2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb2) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0xb2)) Ra0 Ra0 (mword_of_int 1212 : mword 12)
              E1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_b2 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (E1 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 1212 : mword 12)))]> E1).
    assert (HE2a0 : E2 !!! Regidx Ra0 = log_addr).
    { rewrite /E2 upd_eq /E1 upd_eq. rewrite /log_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xb2) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0xb6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb6) in "Hpc".
    (* ===== +0xb6 jal ra,release ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.log_write + 0xb6)) Rra (mword_of_int 2084206 : mword 21)
              E2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (lwi_b6 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.log_write + 0xb6) : mword 64) 4)]> E2).
    assert (Htgtrel : add_vec (mword_of_int (KernelSyms.log_write + 0xb6) : mword 64)
                        (sign_extend' 64 (mword_of_int 2084206 : mword 21))
                      = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    assert (HE3a0 : E3 !!! Regidx Ra0 = log_addr)
      by (rewrite /E3 upd_ne; [exact HE2a0 | vm_compute; discriminate]).
    assert (HE3ra : E3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.log_write + 0xb6) : mword 64) 4)
      by (rewrite /E3; apply upd_eq).
    assert (HE3thr : forall c : mword 5, is_cs_idx c = true ->
                       E3 !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c Hcs.
      rewrite /E3 upd_ne; [| regne].
      rewrite /E2 upd_ne; [| regne].
      rewrite /E1 upd_ne; [reflexivity | regne]. }
    assert (HE3sp : E3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (exact (HE3thr csp_rs1 ltac:(vm_compute; reflexivity))).
    (* the acquire handed this window out at [trap_res b + N]; release wants
       [trap_res outb + N], and [outb] IS [b] ([cpu_own] forces it, which is
       what [Hbeq]/[Houtb] records).  Pure re-spelling -- it is what makes
       the acquire/release pair compose back to [N]. *)
    iEval (rewrite -Hbeq) in "Hcg".
    iApply (Release.wp_release_sconf KT1 (ln_lk γ) log_addr "log"%string
              (log_res Psi γ bn γfs cov logstart) E3 n eb p (K - 4)%nat
              ({["log"]} ∪ lks)
              ltac:(rewrite HE3a0; rewrite /log_addr; apply bv_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CID1 Hs1 mr) "Hcg Hpc %Hrelpins Hcnt".
    rewrite Hbeq in Hs1.
    iEval (rewrite Hbeq) in "Hcg". iEval (rewrite Hbeq) in "Hcnt".
    (* release hands back [({[rank "log"]} ∪ lks) ∖ {[rank "log"]}]; the bound
       says the insert was fresh, so that is the caller's [lks] again -- which
       is the whole of "log_write is BALANCED". *)
    assert (Hnotin : "log" ∉ lks)
      by (exact (locks_below_not_elem lks "log" Hno)).
    assert (Heqlks : ({["log"]} ∪ lks) ∖ {["log"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Heqlks) in "Hcnt".
    assert (Hpcba : ret_pc (E3 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.log_write + 0xba)).
    { rewrite HE3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcba) in "Hpc".
    pose proof Hrelpins as Hrelpins_cs.
    assert (Hmrsp : mr !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hrelpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE3sp. }
    (* ===== EPILOGUE ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.log_write + 0xba)) (mword_of_int 3 : mword 6) Rra
              mr (K - 4)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr24]").
    { iApply (lwi_ba with "Htext"). }
    { iEval (rewrite Hmrsp). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rewrite Hmrsp) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mr).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P1 upd_ne; [exact Hmrsp | vm_compute; discriminate]).
    assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.log_write + 0xba) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xbc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbc) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.log_write + 0xbc)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr16]").
    { iApply (lwi_bc with "Htext"). }
    { iEval (rewrite HP1sp). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.log_write + 0xbc) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xbe))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbe) in "Hpc".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.log_write + 0xbe)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr8]").
    { iApply (lwi_be with "Htext"). }
    { iEval (rewrite HP2sp). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xbe) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xc0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc0) in "Hpc".
    set (P4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3).
    assert (Hwv : add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP3sp Hsp. apply frame_cancel_32. }
    assert (Hpop : P3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP3sp Hsp Hpush. reflexivity. }
    iAssert (stack_own (KTR := KT1) (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iEval (rewrite -Hb4); iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.log_write + 0xc0)) (mword_of_int 2 : mword 6)
              P3 (K - 4)%nat 4 b Hpop with "Hcg Hpc [] Hframe4").
    { iApply (lwi_c0 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by (lia).
    iEval (rewrite Hnk) in "Hcg".
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P3 !!! Regidx csp_rs1 : mword 64)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P3) with P4.
    assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xc0) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xc2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc2) in "Hpc".
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.log_write + 0xc2)) Rra P4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (lwi_c2 with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hretf : ret_pc (P4 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64)) by (rewrite HP4ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              P4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9.
      rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hrelpins_cs c Hcs).
      rewrite (HE3thr c Hcs).
      exact (Hthr c Hcs N2 N8 N9). }
    rewrite /lw_res.
    iDestruct "Hout" as "(Hop & Hfsb & Hlk & Hslot)".
    iDestruct (cpu_own_transport CID1 CID6 n eb p b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (lw_cont_shift (CIDa := CID0) (CIDb := CID6) bn γ γfs γd cov dev k pidv bno
                 bs bsd Fb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    rewrite /lw_cont.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P4 with "Hcg Hcnt Hpc [%] Hop Hfsb Hlk Hslot").
    unfold callee_saved.
    assert (Hc2 : P4 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_eq; exact Hwv).
    assert (Hc8 : P4 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Hc9 : P4 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq. reflexivity. }
    repeat split;
      first [ exact Hc2 | exact Hc8 | exact Hc9
            | apply Hthread; vm_compute; first [reflexivity | discriminate] ].
  Qed.

  (* ================================================================== *)
  (*  +0x66 .. +0x7a : bpin(b); log.lh.n++; goto release.                *)
  (*  BOTH copies of the slot store converge here -- the append copy by  *)
  (*  falling through from +0x64, the absorb copy by the [beq a2,a5] at  *)
  (*  +0xaa when i == n (the n == 0 entry from the +0x34 guard).         *)
  (* ================================================================== *)
  Local Lemma lw_pin `{GEN : GenId} `{CID0 : CpuId}
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ) (nl : nat)
      (m M : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    (K_log_write <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    match n with O => eb | S _ => false end = b ->
    (k < NBUF)%nat ->
    (nl <= 29)%nat ->
    (m !!! Regidx Ra0 : mword 64) = bnode k ->
    lw_regs m M ->
    (* the caller's own held set is [lks]; the block runs at
       [{[rank "log"]} ∪ lks] and calls bpin, which acquires "bcache" on top
       of that.  ONE bound covers both: see the derivation in the proof. *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (trap_res b + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.log_write + 0x66) : mword 64) -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx_at Psi γ bn γfs cov logstart dev -∗
    cpu_own (S n) eb p false ({["log"]} ∪ lks) -∗
    arm_pay KT1 n eb p -∗
    locked (ln_lk γ) cpu_id -∗
    lw_frame m -∗
    bslot -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
    lw_closeP Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl -∗
    lw_cont (CID0 := CID0) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnoff Hbeq Hk Hnl Ha0 Hregs Hno.
    pose proof Hregs as (Hsp & Hs1v & Hthr).
    (* BPIN'S OWN BOUND, DERIVED -- the composition [SpecAcquire.v]'s header
       promises, spelled out once.  The rank order "log"(3) < "bcache"(4) is a
       [vm_compute]; [locks_below_mono] lifts the caller's bound to "bcache",
       and [locks_below_union_singleton] carries it across log_write's own
       acquire, giving exactly the set bpin is entered at. *)
    assert (Hlt : (lock_rank "log" < lock_rank "bcache")%nat) by (vm_compute; lia).
    assert (Hble : locks_below lks "bcache")
      by lkbelow.
    assert (Hnobc2 : locks_below ({["log"]} ∪ lks) "bcache")
      by (exact (locks_below_union_singleton lks "log" "bcache"
                   Hlt Hble)).
    iIntros "Hcg #Htext Hpc #Hbio #Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc Hncell Hclose Hcont".
    assert (HMs1 : M !!! Regidx Rs1 = bnode k) by (rewrite Hs1v; exact Ha0).
    (* ===== +0x66 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.log_write + 0x66)) Ra0 Rs1
              M (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_66 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HA1a0 : A1 !!! Regidx Ra0 = bnode k).
    { rewrite /A1 upd_eq. rgne. rewrite add_vec_zero_l. exact HMs1. }
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x66) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x68 jal ra,bpin ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.log_write + 0x68)) Rra (mword_of_int 2092660 : mword 21)
              A1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (lwi_68 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.log_write + 0x68) : mword 64) 4)]> A1).
    assert (Htgtbp : add_vec (mword_of_int (KernelSyms.log_write + 0x68) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092660 : mword 21))
                     = mword_of_int KernelSyms.bpin)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbp) in "Hpc".
    assert (HA2a0 : A2 !!! Regidx Ra0 = bnode k)
      by (rewrite /A2 upd_ne; [exact HA1a0 | vm_compute; discriminate]).
    assert (HA2ra : A2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.log_write + 0x68) : mword 64) 4)
      by (rewrite /A2; apply upd_eq).
    assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
                       A2 !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c Hcs.
      rewrite /A2 upd_ne; [| regne].
      rewrite /A1 upd_ne; [reflexivity | regne]. }
    iApply (Bpin.wp_bpin_sconf bn (fs_view γfs γd dev cov) k A2 (S n) eb p
              (trap_res b + (K - 4))%nat false ({["log"]} ∪ lks)
              ltac:(lia)
              ltac:(rewrite Nat2Z.inj_succ; lia) Hk HA2a0 Hnobc2
              with "Hcg Hcnt Htext Hpc Hbio Hslot").
    all: try lkbelow.
    iApply wp_next_off_intro.
    iIntros (mb) "Hcg Hcnt Hpc %Hbppins Href".
    assert (Hpc6c : ret_pc (A2 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.log_write + 0x6c)).
    { rewrite HA2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc6c) in "Hpc".
    pose proof Hbppins as Hbppins_cs.
    assert (Hmbthr : forall c : mword 5, is_cs_idx c = true ->
                       mb !!! Regidx c = (M !!! Regidx c : mword 64)).
    { intros c Hcs. rewrite (callee_saved_lookup Hbppins_cs c Hcs). exact (HA2thr c Hcs). }
    (* ===== +0x6c / +0x70 : a4 := &log ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x6c)) Ra4 (mword_of_int 30 : mword 20)
              mb (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_6c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x6c) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> mb).
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x6c) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x70)) Ra4 Ra4 (mword_of_int 1278 : mword 12)
              A3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_70 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A4 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (A3 !!! Regidx Ra4 : mword 64)
                     (sign_extend' 64 (mword_of_int 1278 : mword 12)))]> A3).
    assert (HA4a4 : A4 !!! Regidx Ra4 = (mword_of_int KernelSyms.log : mword 64)).
    { rewrite /A4 upd_eq /A3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x74 c.lw a5,44(a4) : log.lh.n ===== *)
    assert (Hnaddr : add_vec (rget A4 Ra4) (sign_extend' 64 (mword_of_int 44 : mword 12))
                     = lh_n_pa).
    { rgne. rewrite HA4a4 lw_s44. reflexivity. }
    iEval (rewrite -Hnaddr) in "Hncell".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.log_write + 0x74)) Ra5 Ra4 (mword_of_int 44 : mword 12)
              A4 (trap_res b + (K - 4))%nat (mword_of_int (Z.of_nat nl) : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hncell").
    { iApply (lwi_74 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hncell".
    iEval (rewrite Hnaddr) in "Hncell".
    set (A5 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat nl) : mword 32))]> A4).
    assert (HA5a5 : A5 !!! Regidx Ra5 = (mword_of_int (Z.of_nat nl) : mword 64)).
    { rewrite /A5 upd_eq. apply sext32_64_small.
      change (2^31) with 2147483648; lia. }
    assert (HA5a4 : A5 !!! Regidx Ra4 = (mword_of_int KernelSyms.log : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4a4 | vm_compute; discriminate]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* ===== +0x76 c.addiw a5,a5,1 ===== *)
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.log_write + 0x76)) Ra5 (mword_of_int 1 : mword 6)
              A5 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_76 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A6 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget A5 Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> A5).
    assert (HA6a5 : A6 !!! Regidx Ra5 = (mword_of_int (Z.of_nat nl + 1) : mword 64)).
    { rewrite /A6 upd_eq. rgne. rewrite HA5a5.
      apply (addiw_lit (Z.of_nat nl) 1 _ lw_s1c).
      change (2^31) with 2147483648; lia. }
    assert (HA6a4 : A6 !!! Regidx Ra4 = (mword_of_int KernelSyms.log : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5a4 | vm_compute; discriminate]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x76) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* ===== +0x78 c.sw a5,44(a4) : log.lh.n = n+1 ===== *)
    assert (Hnaddr2 : add_vec (rget A6 Ra4) (sign_extend' 64 (mword_of_int 44 : mword 12))
                      = lh_n_pa).
    { rgne. rewrite HA6a4 lw_s44. reflexivity. }
    iEval (rewrite -Hnaddr2) in "Hncell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.log_write + 0x78)) Ra5 Ra4 (mword_of_int 44 : mword 12)
              A6 (trap_res b + (K - 4))%nat (mword_of_int (Z.of_nat nl) : mword 32) false
              with "Hcg Hpc [] Hncell").
    { iApply (lwi_78 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hncell".
    iEval (rewrite Hnaddr2) in "Hncell".
    assert (Hstv : trunc32 (rget A6 Ra5) = (mword_of_int (Z.of_nat nl + 1) : mword 32)).
    { rgne. rewrite HA6a5. apply trunc32_mword_of_int. }
    iEval (rewrite Hstv) in "Hncell".
    iMod ("Hclose" with "Hbnoc Href Hncell") as "[HRres Hout]".
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.log_write + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7a c.j +0xae ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.log_write + 0x7a))
              (sign_extend' 21 (concat_vec (mword_of_int 26 : mword 11) ('b"0")))
              A6 (trap_res b + (K - 4))%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (lwi_7a with "Htext"). }
    iApply wp_next_off_intro.
    iNext. iIntros "Hcg Hpc".
    assert (Htgtae : add_vec (mword_of_int (KernelSyms.log_write + 0x7a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 26 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.log_write + 0xae))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtae) in "Hpc".
    assert (HA6regs : lw_regs m A6).
    { rewrite /lw_regs. split_and!.
      - rewrite /A6 upd_ne; [| vm_compute; discriminate].
        rewrite /A5 upd_ne; [| vm_compute; discriminate].
        rewrite /A4 upd_ne; [| vm_compute; discriminate].
        rewrite /A3 upd_ne; [| vm_compute; discriminate].
        rewrite (Hmbthr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      - rewrite /A6 upd_ne; [| vm_compute; discriminate].
        rewrite /A5 upd_ne; [| vm_compute; discriminate].
        rewrite /A4 upd_ne; [| vm_compute; discriminate].
        rewrite /A3 upd_ne; [| vm_compute; discriminate].
        rewrite (Hmbthr Rs1 ltac:(vm_compute; reflexivity)). exact Hs1v.
      - intros c Hcs N2 N8 N9.
        rewrite /A6 upd_ne; [| regne].
        rewrite /A5 upd_ne; [| regne].
        rewrite /A4 upd_ne; [| regne].
        rewrite /A3 upd_ne; [| regne].
        rewrite (Hmbthr c Hcs). exact (Hthr c Hcs N2 N8 N9). }
    iDestruct (lw_cont_shift (CIDa := CID0) (CIDb := cpu_id) bn γ γfs γd cov dev k pidv bno
                 bs bsd Fb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (lw_rel (CID0 := cpu_id) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud
              m A6 K n eb p b lks HK Hbeq HA6regs Hno
              with "Hcg Htext Hpc Hlctx Hcnt Hpay Htok HRres Hframe Hout Hcont").
  Qed.

  (* ================================================================== *)
  (*  +0x94 .. +0xaa : the ABSORB copy of [log.lh.block[i] = b->blockno], *)
  (*  addressed off 4*i, followed by [beq a2,a5] -- which REJOINS the     *)
  (*  bpin block when i == n (the n == 0 entry from the +0x34 guard) and  *)
  (*  otherwise falls through to the release.                            *)
  (* ================================================================== *)
  Local Lemma lw_blk94 `{GEN : GenId} `{CID0 : CpuId}
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ) (nl i : nat)
      (wold : mword 32)
      (m M : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    (K_log_write <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    match n with O => eb | S _ => false end = b ->
    (k < NBUF)%nat ->
    (nl <= 29)%nat ->
    (i <= nl)%nat ->
    (m !!! Regidx Ra0 : mword 64) = bnode k ->
    lw_regs m M ->
    M !!! Regidx Ra5 = (mword_of_int (Z.of_nat i) : mword 64) ->
    M !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64) ->
    (* both exits need it: [lw_pin] calls bpin, [lw_rel] releases "log" *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (trap_res b + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.log_write + 0x94) : mword 64) -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx_at Psi γ bn γfs cov logstart dev -∗
    cpu_own (S n) eb p false ({["log"]} ∪ lks) -∗
    arm_pay KT1 n eb p -∗
    locked (ln_lk γ) cpu_id -∗
    lw_frame m -∗
    bslot -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
    lh_block i ↦₄ wold -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
    ((⌜i = nl⌝ -∗ lh_block i ↦₄ bno -∗
        lw_closeP Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl)
     ∧ (⌜i <> nl⌝ -∗ lh_block i ↦₄ bno -∗
        lw_closeR Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl)) -∗
    lw_cont (CID0 := CID0) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnoff Hbeq Hk Hnl Hinl Ha0 Hregs Ha5v Ha2v Hno.
    pose proof Hregs as (Hsp & Hs1v & Hthr).
    iIntros "Hcg #Htext Hpc #Hbio #Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc Hcell Hncell Hcl Hcont".
    assert (HMs1 : M !!! Regidx Rs1 = bnode k) by (rewrite Hs1v; exact Ha0).
    (* ===== +0x94 slli a3,a5,2 ===== *)
    iApply (wp_slli_s_sconf (mword_of_int (KernelSyms.log_write + 0x94)) Ra3 Ra5 (mword_of_int 2 : mword 6)
              (mword_of_int (4 * Z.of_nat i) : mword 64) M (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite Ha5v; apply lw_slli2; lia)
              with "Hcg Hpc []").
    { iApply (lwi_94 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B1 := <[Regidx Ra3 := regval_into_reg
                  (mword_of_int (4 * Z.of_nat i) : mword 64)]> M).
    assert (HB1a3 : B1 !!! Regidx Ra3 = (mword_of_int (4 * Z.of_nat i) : mword 64))
      by (rewrite /B1; apply upd_eq).
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x94) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x98))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x98 addi a3,a3,32 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x98)) Ra3 Ra3 (mword_of_int 32 : mword 12)
              B1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_98 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx Ra3 := regval_into_reg
                  (add_vec (B1 !!! Regidx Ra3 : mword 64)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> B1).
    assert (HB2a3 : B2 !!! Regidx Ra3
                    = (mword_of_int (4 * Z.of_nat i + 32) : mword 64)).
    { rewrite /B2 upd_eq HB1a3.
      assert (Hs32 : sign_extend' 64 (mword_of_int 32 : mword 12)
                     = (mword_of_int 32 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hs32 moi_add. reflexivity. }
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.log_write + 0x98) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x9c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9c) in "Hpc".
    (* ===== +0x9c / +0xa0 : a4 := &log ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x9c)) Ra4 (mword_of_int 30 : mword 20)
              B2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_9c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B3 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x9c) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> B2).
    assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x9c) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0xa0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa0) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0xa0)) Ra4 Ra4 (mword_of_int 1230 : mword 12)
              B3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_a0 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B4 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (B3 !!! Regidx Ra4 : mword 64)
                     (sign_extend' 64 (mword_of_int 1230 : mword 12)))]> B3).
    assert (HB4a4 : B4 !!! Regidx Ra4 = (mword_of_int KernelSyms.log : mword 64)).
    { rewrite /B4 upd_eq /B3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HB4a3 : B4 !!! Regidx Ra3
                    = (mword_of_int (4 * Z.of_nat i + 32) : mword 64))
      by (rewrite /B4 upd_ne; [| vm_compute; discriminate];
          rewrite /B3 upd_ne; [exact HB2a3 | vm_compute; discriminate]).
    assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xa0) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0xa4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa4) in "Hpc".
    (* ===== +0xa4 c.add a4,a4,a3 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.log_write + 0xa4)) Ra4 Ra3
              B4 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_a4 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B5 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (rget B4 Ra4) (rget B4 Ra3))]> B4).
    assert (HB5a4 : B5 !!! Regidx Ra4
                    = add_vec (mword_of_int KernelSyms.log : mword 64)
                              (mword_of_int (4 * Z.of_nat i + 32))).
    { rewrite /B5 upd_eq. rgne. rgne. rewrite HB4a4 HB4a3. reflexivity. }
    assert (HB5s1 : B5 !!! Regidx Rs1 = bnode k).
    { rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [exact HMs1 | vm_compute; discriminate]. }
    assert (Hppa6 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xa4) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xa6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa6) in "Hpc".
    (* ===== +0xa6 c.lw a3,12(s1) : b->blockno ===== *)
    assert (Hbaddr : add_vec (rget B5 Rs1) (sign_extend' 64 (mword_of_int 12 : mword 12))
                     = b_blockno (bpa k)).
    { rgne. rewrite HB5s1 lw_s12.
      rewrite /b_blockno /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hbaddr) in "Hbnoc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (dqm := DfracOwn (1/2)) (mword_of_int (KernelSyms.log_write + 0xa6)) Ra3 Rs1
              (mword_of_int 12 : mword 12) B5 (trap_res b + (K - 4))%nat bno false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbnoc").
    { iApply (lwi_a6 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbnoc".
    iEval (rewrite Hbaddr) in "Hbnoc".
    set (B6 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 bno)]> B5).
    assert (HB6a4 : B6 !!! Regidx Ra4
                    = add_vec (mword_of_int KernelSyms.log : mword 64)
                              (mword_of_int (4 * Z.of_nat i + 32)))
      by (rewrite /B6 upd_ne; [exact HB5a4 | vm_compute; discriminate]).
    assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.log_write + 0xa6) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xa8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa8) in "Hpc".
    (* ===== +0xa8 c.sw a3,16(a4) : the slot store ===== *)
    assert (Hsaddr : add_vec (rget B6 Ra4) (sign_extend' 64 (mword_of_int 16 : mword 12))
                     = lh_block i).
    { rgne. rewrite HB6a4 lw_s16. apply lw_slot_addr. lia. }
    iEval (rewrite -Hsaddr) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.log_write + 0xa8)) Ra3 Ra4 (mword_of_int 16 : mword 12)
              B6 (trap_res b + (K - 4))%nat wold false
              with "Hcg Hpc [] Hcell").
    { iApply (lwi_a8 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hsaddr) in "Hcell".
    assert (Hstv : trunc32 (rget B6 Ra3) = bno).
    { rgne. rewrite /B6 upd_eq. apply trunc32_sext. }
    iEval (rewrite Hstv) in "Hcell".
    assert (HB6a5 : B6 !!! Regidx Ra5 = (mword_of_int (Z.of_nat i) : mword 64)).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [exact Ha5v | vm_compute; discriminate]. }
    assert (HB6a2 : B6 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64)).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [exact Ha2v | vm_compute; discriminate]. }
    assert (HB6regs : lw_regs m B6).
    { rewrite /lw_regs. split_and!.
      - rewrite /B6 upd_ne; [| vm_compute; discriminate].
        rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - rewrite /B6 upd_ne; [| vm_compute; discriminate].
        rewrite /B5 upd_ne; [| vm_compute; discriminate].
        rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact Hs1v | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9.
        rewrite /B6 upd_ne; [| regne].
        rewrite /B5 upd_ne; [| regne].
        rewrite /B4 upd_ne; [| regne].
        rewrite /B3 upd_ne; [| regne].
        rewrite /B2 upd_ne; [| regne].
        rewrite /B1 upd_ne; [| regne].
        exact (Hthr c Hcs N2 N8 N9). }
    assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.log_write + 0xa8) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0xaa))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa beq a2,a5 ===== *)
    destruct (decide (i = nl)) as [Hin | Hin].
    - (* i == n: rejoin the bpin block at +0x66 *)
      iDestruct "Hcl" as "[Hcl _]".
      iDestruct ("Hcl" with "[%] Hcell") as "Hclose"; [exact Hin|].
      assert (Hcmp : eq_vec (rget B6 Ra2) (rget B6 Ra5) = true).
      { rgne. rgne. rewrite HB6a2 HB6a5.
        rewrite lw_eqv_moi; [| change (2^31) with 2147483648; lia
                             | change (2^31) with 2147483648; lia].
        apply Z.eqb_eq. lia. }
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.log_write + 0xaa))
                (mword_of_int 8124 : mword 13) Ra5 Ra2 B6 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (lwi_aa with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt66 : add_vec (mword_of_int (KernelSyms.log_write + 0xaa) : mword 64)
                         (sign_extend' 64 (mword_of_int 8124 : mword 13))
                       = mword_of_int (KernelSyms.log_write + 0x66))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt66) in "Hpc".
      iDestruct (lw_cont_shift (CIDa := CID0) (CIDb := cpu_id) bn γ γfs γd cov dev k pidv bno
                   bs bsd Fb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (lw_pin (CID0 := cpu_id) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl
                m B6 K n eb p b lks HK Hnoff Hbeq Hk Hnl Ha0 HB6regs Hno
                with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc
                      Hncell Hclose Hcont").
    - (* i < n: fall through to the release *)
      iDestruct "Hcl" as "[_ Hcl]".
      iDestruct ("Hcl" with "[%] Hcell") as "Hclose"; [exact Hin|].
      iMod ("Hclose" with "Hbnoc Hncell Hslot") as "[HRres Hout]".
      assert (Hcmp : eq_vec (rget B6 Ra2) (rget B6 Ra5) = false).
      { rgne. rgne. rewrite HB6a2 HB6a5.
        rewrite lw_eqv_moi; [| change (2^31) with 2147483648; lia
                             | change (2^31) with 2147483648; lia].
        apply Z.eqb_neq. lia. }
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0xaa))
                (mword_of_int 8124 : mword 13) Ra5 Ra2 B6 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc []").
      { iApply (lwi_aa with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hppae : add_vec_int (mword_of_int (KernelSyms.log_write + 0xaa) : mword 64) 4
                      = mword_of_int (KernelSyms.log_write + 0xae))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppae) in "Hpc".
      iDestruct (lw_cont_shift (CIDa := CID0) (CIDb := cpu_id) bn γ γfs γd cov dev k pidv bno
                   bs bsd Fb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (lw_rel (CID0 := cpu_id) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud
                m B6 K n eb p b lks HK Hbeq HB6regs Hno
                with "Hcg Htext Hpc Hlctx Hcnt Hpay Htok HRres Hframe Hout Hcont").
  Qed.

  (* ================================================================== *)
  (*  +0x52 .. +0x64 : the APPEND copy of the slot store, addressed off   *)
  (*  4*lh.n.  Reached by falling out of the scan with i == n >= 1, and   *)
  (*  falling straight into the bpin block at +0x66.                     *)
  (* ================================================================== *)
  Local Lemma lw_app52 `{GEN : GenId} `{CID0 : CpuId}
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ) (nl : nat)
      (jk : mword 32)
      (m M : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    (K_log_write <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    match n with O => eb | S _ => false end = b ->
    (k < NBUF)%nat ->
    (nl <= 29)%nat ->
    (m !!! Regidx Ra0 : mword 64) = bnode k ->
    lw_regs m M ->
    M !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64) ->
    (* this block falls into [lw_pin], which needs the bound for bpin too *)
    locks_below lks "log" ->
    sie_cap_gpr KT1 M (trap_res b + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.log_write + 0x52) : mword 64) -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx_at Psi γ bn γfs cov logstart dev -∗
    cpu_own (S n) eb p false ({["log"]} ∪ lks) -∗
    arm_pay KT1 n eb p -∗
    locked (ln_lk γ) cpu_id -∗
    lw_frame m -∗
    bslot -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
    lh_block nl ↦₄ jk -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
    (lh_block nl ↦₄ bno -∗
       lw_closeP Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl) -∗
    lw_cont (CID0 := CID0) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnoff Hbeq Hk Hnl Ha0 Hregs Ha2v Hno.
    pose proof Hregs as (Hsp & Hs1v & Hthr).
    iIntros "Hcg #Htext Hpc #Hbio #Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc Hcell Hncell Hcl Hcont".
    assert (HMs1 : M !!! Regidx Rs1 = bnode k) by (rewrite Hs1v; exact Ha0).
    (* ===== +0x52 c.slli a2,a2,2 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.log_write + 0x52)) (Regidx Ra2) Ra2
              (mword_of_int 2 : mword 6) M (trap_res b + (K - 4))%nat false
              eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_52 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (G1 := <[Regidx Ra2 := regval_into_reg
                  (shift_bits_left (rget M Ra2)
                     (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0))]> M).
    assert (HG1a2 : G1 !!! Regidx Ra2 = (mword_of_int (4 * Z.of_nat nl) : mword 64)).
    { rewrite /G1 upd_eq. rgne. rewrite Ha2v. apply lw_slli2. lia. }
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x52) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x54 addi a2,a2,32 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x54)) Ra2 Ra2 (mword_of_int 32 : mword 12)
              G1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_54 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (G2 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (G1 !!! Regidx Ra2 : mword 64)
                     (sign_extend' 64 (mword_of_int 32 : mword 12)))]> G1).
    assert (HG2a2 : G2 !!! Regidx Ra2
                    = (mword_of_int (4 * Z.of_nat nl + 32) : mword 64)).
    { rewrite /G2 upd_eq HG1a2.
      assert (Hs32 : sign_extend' 64 (mword_of_int 32 : mword 12)
                     = (mword_of_int 32 : mword 64))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hs32 moi_add. reflexivity. }
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x54) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* ===== +0x58 / +0x5c : a5 := &log ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x58)) Ra5 (mword_of_int 30 : mword 20)
              G2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_58 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (G3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x58) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> G2).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.log_write + 0x58) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x5c)) Ra5 Ra5 (mword_of_int 1298 : mword 12)
              G3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_5c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (G4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (G3 !!! Regidx Ra5 : mword 64)
                     (sign_extend' 64 (mword_of_int 1298 : mword 12)))]> G3).
    assert (HG4a5 : G4 !!! Regidx Ra5 = (mword_of_int KernelSyms.log : mword 64)).
    { rewrite /G4 upd_eq /G3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HG4a2 : G4 !!! Regidx Ra2
                    = (mword_of_int (4 * Z.of_nat nl + 32) : mword 64))
      by (rewrite /G4 upd_ne; [| vm_compute; discriminate];
          rewrite /G3 upd_ne; [exact HG2a2 | vm_compute; discriminate]).
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x5c) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* ===== +0x60 c.add a5,a5,a2 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.log_write + 0x60)) Ra5 Ra2
              G4 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_60 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (G5 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget G4 Ra5) (rget G4 Ra2))]> G4).
    assert (HG5a5 : G5 !!! Regidx Ra5
                    = add_vec (mword_of_int KernelSyms.log : mword 64)
                              (mword_of_int (4 * Z.of_nat nl + 32))).
    { rewrite /G5 upd_eq. rgne. rgne. rewrite HG4a5 HG4a2. reflexivity. }
    assert (HG5s1 : G5 !!! Regidx Rs1 = bnode k).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMs1 | vm_compute; discriminate]. }
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* ===== +0x62 c.lw a4,12(s1) : b->blockno ===== *)
    assert (Hbaddr : add_vec (rget G5 Rs1) (sign_extend' 64 (mword_of_int 12 : mword 12))
                     = b_blockno (bpa k)).
    { rgne. rewrite HG5s1 lw_s12.
      rewrite /b_blockno /bpa /pa_add /add_vec_int. reflexivity. }
    iEval (rewrite -Hbaddr) in "Hbnoc".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (dqm := DfracOwn (1/2)) (mword_of_int (KernelSyms.log_write + 0x62)) Ra4 Rs1
              (mword_of_int 12 : mword 12) G5 (trap_res b + (K - 4))%nat bno false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hbnoc").
    { iApply (lwi_62 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hbnoc".
    iEval (rewrite Hbaddr) in "Hbnoc".
    set (G6 := <[Regidx Ra4 := regval_into_reg (sign_extend' 64 bno)]> G5).
    assert (HG6a5 : G6 !!! Regidx Ra5
                    = add_vec (mword_of_int KernelSyms.log : mword 64)
                              (mword_of_int (4 * Z.of_nat nl + 32)))
      by (rewrite /G6 upd_ne; [exact HG5a5 | vm_compute; discriminate]).
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x64 c.sw a4,16(a5) : the slot store ===== *)
    assert (Hsaddr : add_vec (rget G6 Ra5) (sign_extend' 64 (mword_of_int 16 : mword 12))
                     = lh_block nl).
    { rgne. rewrite HG6a5 lw_s16. apply lw_slot_addr. lia. }
    iEval (rewrite -Hsaddr) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.log_write + 0x64)) Ra4 Ra5 (mword_of_int 16 : mword 12)
              G6 (trap_res b + (K - 4))%nat jk false
              with "Hcg Hpc [] Hcell").
    { iApply (lwi_64 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hsaddr) in "Hcell".
    assert (Hstv : trunc32 (rget G6 Ra4) = bno).
    { rgne. rewrite /G6 upd_eq. apply trunc32_sext. }
    iEval (rewrite Hstv) in "Hcell".
    iDestruct ("Hcl" with "Hcell") as "Hclose".
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x64) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    assert (HG6regs : lw_regs m G6).
    { rewrite /lw_regs. split_and!.
      - rewrite /G6 upd_ne; [| vm_compute; discriminate].
        rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [| vm_compute; discriminate].
        rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - rewrite /G6 upd_ne; [| vm_compute; discriminate].
        rewrite /G5 upd_ne; [| vm_compute; discriminate].
        rewrite /G4 upd_ne; [| vm_compute; discriminate].
        rewrite /G3 upd_ne; [| vm_compute; discriminate].
        rewrite /G2 upd_ne; [| vm_compute; discriminate].
        rewrite /G1 upd_ne; [exact Hs1v | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9.
        rewrite /G6 upd_ne; [| regne].
        rewrite /G5 upd_ne; [| regne].
        rewrite /G4 upd_ne; [| regne].
        rewrite /G3 upd_ne; [| regne].
        rewrite /G2 upd_ne; [| regne].
        rewrite /G1 upd_ne; [| regne].
        exact (Hthr c Hcs N2 N8 N9). }
    iApply (lw_pin (CID0 := CID0) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl
              m G6 K n eb p b lks HK Hnoff Hbeq Hk Hnl Ha0 HG6regs Hno
              with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc
                    Hncell Hclose Hcont").
  Qed.

  (* ================================================================== *)
  (*  +0x44 .. +0x4e : the absorption scan.                              *)
  (*    top    +0x44  lw a3,0(a4)                                        *)
  (*    break  +0x46  beq a3,a1 -> +0x94  (hit at THIS i)                *)
  (*    bump   +0x4a/+0x4c                                               *)
  (*    back   +0x4e  bne a2,a5 -> +0x44                                 *)
  (*    exit   +0x52  (i == n: the append path)                          *)
  (*  A fuel induction over the entries still to test, ACCUMULATING the   *)
  (*  negative fact [forall j < i, W !! j <> Some bno] -- which is what   *)
  (*  turns the fall-out into the append closer's ⌜bno ∉ W⌝ premise.     *)
  (* ================================================================== *)
  Local Lemma lw_scan `{GEN : GenId} `{CID0 : CpuId}
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (bn : bio_names) (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (k : nat)
      (pidv bno : mword 32) (bs bsd : list (bv 8)) (Fb Bud : iProp Σ) (nl : nat)
      (W : list (mword 32))
      (m : regfile) (K : nat) (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) (fuel : nat) :
    (K_log_write <= K)%nat ->
    (Z.of_nat n + 2 < 2 ^ 31)%Z ->
    match n with O => eb | S _ => false end = b ->
    (k < NBUF)%nat ->
    (nl <= 29)%nat ->
    nl = length W ->
    (m !!! Regidx Ra0 : mword 64) = bnode k ->
    (* loop-INVARIANT freshness: the set is not touched by the scan (no
       acquire/release inside it), so the bound is stated once, ahead of the
       [forall i M], and carried unchanged into every iteration and both exits
       ([lw_blk94] on a hit, [lw_app52] on the fall-out). *)
    locks_below lks "log" ->
    forall (i : nat) (M : regfile),
    (i < nl)%nat ->
    (nl - i <= fuel)%nat ->
    (forall j, (j < i)%nat -> W !! j <> Some bno) ->
    lw_regs m M ->
    M !!! Regidx Ra5 = (mword_of_int (Z.of_nat i) : mword 64) ->
    M !!! Regidx Ra4 = lh_block i ->
    M !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64) ->
    M !!! Regidx Ra1 = sign_extend' 64 bno ->
    sie_cap_gpr KT1 M (trap_res b + (K - 4))%nat false p -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.log_write + 0x44) : mword 64) -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx_at Psi γ bn γfs cov logstart dev -∗
    cpu_own (S n) eb p false ({["log"]} ∪ lks) -∗
    arm_pay KT1 n eb p -∗
    locked (ln_lk γ) cpu_id -∗
    lw_frame m -∗
    bslot -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bno -∗
    ([∗ list] j ↦ w ∈ W, lh_block j ↦₄ w) -∗
    (∃ jk : mword 32, lh_block nl ↦₄ jk) -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat nl) : mword 32) -∗
    (lw_closeA Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl W
     ∧ lw_closeB Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl W) -∗
    lw_cont (CID0 := CID0) bn γ γfs γd cov dev k pidv bno bs bsd Fb Bud m K n eb p b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hnoff Hbeq Hk Hnl HnW Ha0 Hno.
    iInduction fuel as [|fuel] "IH";
      iIntros (i M Hi Hfuel Hprev Hregs Ha5v Ha4v Ha2v Ha1v);
      [ exfalso; lia |].
    pose proof Hregs as (Hsp & Hs1v & Hthr).
    iIntros "Hcg #Htext Hpc #Hbio #Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc HW Hjunk Hncell Hcl Hcont".
    assert (HMs1 : M !!! Regidx Rs1 = bnode k) by (rewrite Hs1v; exact Ha0).
    (* the entry under test *)
    destruct (lookup_lt_is_Some_2 W i ltac:(lia)) as [w Hw].
    iDestruct (big_sepL_lookup_acc _ _ i w Hw with "HW") as "[Hcell Hback]".
    (* ===== +0x44 c.lw a3,0(a4) ===== *)
    assert (Haddr : add_vec (rget M Ra4) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = lh_block i).
    { rgne. rewrite Ha4v lw_s0. apply lw_cursor_at. }
    iEval (rewrite -Haddr) in "Hcell".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.log_write + 0x44)) Ra3 Ra4
              (mword_of_int 0 : mword 12) M (trap_res b + (K - 4))%nat w false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcell").
    { iApply (lwi_44 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Haddr) in "Hcell".
    set (S1 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 w)]> M).
    assert (HS1a3 : S1 !!! Regidx Ra3 = sign_extend' 64 w)
      by (rewrite /S1; apply upd_eq).
    assert (HS1a1 : S1 !!! Regidx Ra1 = sign_extend' 64 bno)
      by (rewrite /S1 upd_ne; [exact Ha1v | vm_compute; discriminate]).
    assert (HS1a5 : S1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite /S1 upd_ne; [exact Ha5v | vm_compute; discriminate]).
    assert (HS1a4 : S1 !!! Regidx Ra4 = lh_block i)
      by (rewrite /S1 upd_ne; [exact Ha4v | vm_compute; discriminate]).
    assert (HS1a2 : S1 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64))
      by (rewrite /S1 upd_ne; [exact Ha2v | vm_compute; discriminate]).
    assert (HS1regs : lw_regs m S1).
    { rewrite /lw_regs. split_and!.
      - rewrite /S1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - rewrite /S1 upd_ne; [exact Hs1v | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9.
        rewrite /S1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9). }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x46 beq a3,a1 ===== *)
    destruct (decide (w = bno)) as [Hhit | Hmiss].
    - (* ---- ABSORPTION HIT at index i ---- *)
      assert (Hcmp : eq_vec (rget S1 Ra3) (rget S1 Ra1) = true).
      { rgne. rgne. rewrite HS1a3 HS1a1 bd_sext_eqv.
        apply eq_vec_true_iff. exact Hhit. }
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.log_write + 0x46))
                (mword_of_int 78 : mword 13) Ra1 Ra3 S1 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (lwi_46 with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt94 : add_vec (mword_of_int (KernelSyms.log_write + 0x46) : mword 64)
                         (sign_extend' 64 (mword_of_int 78 : mword 13))
                       = mword_of_int (KernelSyms.log_write + 0x94))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt94) in "Hpc".
      assert (Hmem : uint bno ∈ map uint W).
      { apply elem_of_list_fmap. exists bno. split; [reflexivity|].
        apply elem_of_list_lookup. exists i. rewrite Hw Hhit. reflexivity. }
      subst w.
      iDestruct "Hcl" as "[HA _]".
      iAssert ((⌜i = nl⌝ -∗ lh_block i ↦₄ bno -∗
                  lw_closeP Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl)
               ∧ (⌜i <> nl⌝ -∗ lh_block i ↦₄ bno -∗
                  lw_closeR Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Fb Bud nl))%I
        with "[HA Hback Hjunk]" as "Hcl94".
      { iSplit.
        - iIntros (Hbad). exfalso. lia.
        - iIntros (_) "Hcell".
          iDestruct ("Hback" with "Hcell") as "HW".
          rewrite /lw_closeA.
          iApply ("HA" with "[%] Hjunk HW"). exact Hmem. }
      iDestruct (lw_cont_shift (CIDa := CID0) (CIDb := cpu_id) bn γ γfs γd cov dev k pidv bno
                   bs bsd Fb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (lw_blk94 (CID0 := cpu_id) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud
                nl i bno m S1 K n eb p b lks HK Hnoff Hbeq Hk Hnl ltac:(lia) Ha0
                HS1regs HS1a5 HS1a2 Hno
                with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc
                      Hcell Hncell Hcl94 Hcont").
    - (* ---- no hit here: bump and loop ---- *)
      assert (Hcmp : eq_vec (rget S1 Ra3) (rget S1 Ra1) = false).
      { rgne. rgne. rewrite HS1a3 HS1a1 bd_sext_eqv.
        apply eq_vec_false_iff. exact Hmiss. }
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0x46))
                (mword_of_int 78 : mword 13) Ra1 Ra3 S1 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc []").
      { iApply (lwi_46 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iDestruct ("Hback" with "Hcell") as "HW".
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.log_write + 0x46) : mword 64) 4
                      = mword_of_int (KernelSyms.log_write + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* ===== +0x4a c.addiw a5,a5,1 ===== *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.log_write + 0x4a)) Ra5 (mword_of_int 1 : mword 6)
                S1 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (lwi_4a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (S2 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (subrange_vec_dec
                       (add_vec (rget S1 Ra5)
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> S1).
      assert (HS2a5 : S2 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (S i)) : mword 64)).
      { rewrite /S2 upd_eq. rgne. rewrite HS1a5.
        rewrite (addiw_lit (Z.of_nat i) 1 _ lw_s1c
                   ltac:(change (2^31) with 2147483648; lia)).
        apply lw_succ_moi. }
      assert (HS2a4 : S2 !!! Regidx Ra4 = lh_block i)
        by (rewrite /S2 upd_ne; [exact HS1a4 | vm_compute; discriminate]).
      assert (HS2a2 : S2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64))
        by (rewrite /S2 upd_ne; [exact HS1a2 | vm_compute; discriminate]).
      assert (HS2a1 : S2 !!! Regidx Ra1 = sign_extend' 64 bno)
        by (rewrite /S2 upd_ne; [exact HS1a1 | vm_compute; discriminate]).
      assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.log_write + 0x4a) : mword 64) 2
                      = mword_of_int (KernelSyms.log_write + 0x4c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4c) in "Hpc".
      (* ===== +0x4c c.addi a4,a4,4 ===== *)
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.log_write + 0x4c)) Ra4 (mword_of_int 4 : mword 6)
                S2 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (lwi_4c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (S3 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (rget S2 Ra4)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> S2).
      assert (HS3a4 : S3 !!! Regidx Ra4 = lh_block (S i)).
      { rewrite /S3 upd_eq. rgne. rewrite HS2a4 lw_s4c. apply lw_cursor_step. }
      assert (HS3a5 : S3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (S i)) : mword 64))
        by (rewrite /S3 upd_ne; [exact HS2a5 | vm_compute; discriminate]).
      assert (HS3a2 : S3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64))
        by (rewrite /S3 upd_ne; [exact HS2a2 | vm_compute; discriminate]).
      assert (HS3a1 : S3 !!! Regidx Ra1 = sign_extend' 64 bno)
        by (rewrite /S3 upd_ne; [exact HS2a1 | vm_compute; discriminate]).
      assert (HS3regs : lw_regs m S3).
      { rewrite /lw_regs. split_and!.
        - rewrite /S3 upd_ne; [| vm_compute; discriminate].
          rewrite /S2 upd_ne; [| vm_compute; discriminate].
          rewrite /S1 upd_ne; [exact Hsp | vm_compute; discriminate].
        - rewrite /S3 upd_ne; [| vm_compute; discriminate].
          rewrite /S2 upd_ne; [| vm_compute; discriminate].
          rewrite /S1 upd_ne; [exact Hs1v | vm_compute; discriminate].
        - intros c Hcs N2 N8 N9.
          rewrite /S3 upd_ne; [| regne].
          rewrite /S2 upd_ne; [| regne].
          rewrite /S1 upd_ne; [| regne].
          exact (Hthr c Hcs N2 N8 N9). }
      assert (Hprev' : forall j, (j < S i)%nat -> W !! j <> Some bno).
      { intros j Hj. destruct (decide (j = i)) as [->|Hne].
        - rewrite Hw. intro Hc. apply Hmiss. congruence.
        - apply Hprev. lia. }
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.log_write + 0x4c) : mword 64) 2
                      = mword_of_int (KernelSyms.log_write + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* ===== +0x4e bne a2,a5 ===== *)
      destruct (decide (S i = nl)) as [Hdone | Hmore].
      + (* the scan ran off the end: i == n, the APPEND path *)
        assert (Hcmp2 : neq_vec (rget S3 Ra2) (rget S3 Ra5) = false).
        { rgne. rgne. rewrite HS3a2 HS3a5. unfold neq_vec.
          rewrite lw_eqv_moi; [| change (2^31) with 2147483648; lia
                               | change (2^31) with 2147483648; lia].
          replace (Z.eqb (Z.of_nat nl) (Z.of_nat (S i))) with true
            by (symmetry; apply Z.eqb_eq; lia).
          reflexivity. }
        iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0x4e))
                  (mword_of_int 8182 : mword 13) Ra5 Ra2 S3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp2 with "Hcg Hpc []").
        { iApply (lwi_4e with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x4e) : mword 64) 4
                        = mword_of_int (KernelSyms.log_write + 0x52))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp52) in "Hpc".
        assert (Hnotmem : ~ (uint bno ∈ map uint W)).
        { intro Hc. apply elem_of_list_fmap in Hc as (w2 & Heq & Hin).
          apply elem_of_list_lookup in Hin as [j Hj].
          apply (Hprev' j); [| rewrite Hj; f_equal; symmetry; apply lw_uint_inj; exact Heq].
          assert (Hjl : (j < length W)%nat) by (apply lookup_lt_is_Some_1; eauto).
          lia. }
        iDestruct "Hcl" as "[_ HB]".
        rewrite /lw_closeB.
        iDestruct ("HB" with "[%] HW") as "Hcl52"; [exact Hnotmem|].
        iDestruct "Hjunk" as (jk) "Hjunk".
        iApply (lw_app52 (CID0 := CID0) Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Fb Bud
                  nl jk m S3 K n eb p b lks HK Hnoff Hbeq Hk Hnl Ha0 HS3regs HS3a2
                  Hno
                  with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc
                        Hjunk Hncell Hcl52 Hcont").
      + (* another entry to test: back to +0x44 *)
        assert (Hcmp2 : neq_vec (rget S3 Ra2) (rget S3 Ra5) = true).
        { rgne. rgne. rewrite HS3a2 HS3a5. unfold neq_vec.
          rewrite lw_eqv_moi; [| change (2^31) with 2147483648; lia
                               | change (2^31) with 2147483648; lia].
          replace (Z.eqb (Z.of_nat nl) (Z.of_nat (S i))) with false
            by (symmetry; apply Z.eqb_neq; lia).
          reflexivity. }
        iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.log_write + 0x4e))
                  (mword_of_int 8182 : mword 13) Ra5 Ra2 S3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp2 ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (lwi_4e with "Htext"). }
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt44 : add_vec (mword_of_int (KernelSyms.log_write + 0x4e) : mword 64)
                           (sign_extend' 64 (mword_of_int 8182 : mword 13))
                         = mword_of_int (KernelSyms.log_write + 0x44))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt44) in "Hpc".
        assert (Hi' : (S i < nl)%nat) by (clear - Hi Hmore; lia).
        assert (Hf' : (nl - S i <= fuel)%nat) by (clear - Hi Hfuel Hmore; lia).
        iApply ("IH" $! (S i) S3 Hi' Hf' Hprev' HS3regs HS3a5 HS3a4 HS3a2 HS3a1
                  with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hslot Hbnoc
                        HW Hjunk Hncell Hcl Hcont").
  Qed.

End LogWriteBlocks.

(* ===================================================================== *)

Section ProofLogWrite.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE WHOLE-FUNCTION PROOF, at the most general (byte-range atomic-update)
     contract.  [wp_log_write_au] below is its whole-block instance,
     [wp_log_write_gen] that one's degenerate instance at a held [fsblock],
     and [wp_log_write_sconf] the set-forgetting instance of that. *)
  Lemma wp_log_write_au_range
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (off len : nat) (sub_new : list (bv 8))
      (cr : bool) (Sb : gset Z) (e0 : nat) (vlb : nat)
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (Efs : coPset) (Φfsb : iProp Σ)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string)
    : wp_log_write_au_range_body bn γ γfs γd cov logstart dev k pidv bno
                                 bs bsl bsd d u off len sub_new
                                 cr Sb e0 vlb Psi Efs Φfsb m n eb p K b lks.
  Proof.
    cbv beta delta [wp_log_write_au_range_body].
    intros pcE ret_tgt HK Hnoff Hk Ha0 Hcovbno Hnotlog HlogE
           Hwin Hlenpos Hshape Hno.
    (* the budget resource this run delivers, threaded opaquely through the
       lw_* helpers -- none of them inspects it *)
    pose (Bud := (log_opSwe γ (if cr then S u else u) (Sb ∪ {[uint bno]})
                    (uint bno) vlb e0)%I).
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hlctx Hbslot #Hvlb #Hcredit Hop Hau Hheld Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbeq.
    iDestruct "Hlctx" as "#Hlctx2".
    iAssert (log_ctx_at Psi γ bn γfs cov logstart dev) as "#Hlctx";
      [iExact "Hlctx2"|].
    iDestruct "Hlctx2" as "(#Hlock & #Hdevc & #Hstc & _)".
    (* the byte view's invariant, off the context log_write already threads
       (durable-disk 1c-flip step 4) *)
    iPoseProof (log_ctx_at_bytes with "Hlctx") as "#Hbinv".
    iAssert (lw_cont (CID0 := CID) bn γ γfs γd cov dev k pidv bno bs bsd Φfsb Bud
                     m K n eb p b lks)%I with "[Hcont]" as "Hcont";
      [rewrite /lw_cont; iExact "Hcont"|].
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : (m !!! Regidx csp_rs1 : mword 64) = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc []").
    { iApply (lwi_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hg4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.log_write + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.log_write + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc [] Hr24").
    { iApply (lwi_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.log_write + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc [] Hr16").
    { iApply (lwi_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.log_write + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc [] Hr8").
    { iApply (lwi_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.log_write + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.log_write + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.log_write + 0x0a)) Rs1 Ra0
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = (m !!! Regidx Ra0 : mword 64)).
    { rewrite /R3 upd_eq. rgne.
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [| vm_compute; discriminate].
      apply add_vec_zero_l. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.log_write + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x0c)) Ra0 (mword_of_int 30 : mword 20)
              R3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R3).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x0c) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x10)) Ra0 Ra0 (mword_of_int 1374 : mword 12)
              R4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 1374 : mword 12)))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = log_addr).
    { rewrite /R5 upd_eq /R4 upd_eq /log_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 jal ra,acquire ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.log_write + 0x14)) Rra (mword_of_int 2084232 : mword 21)
              R5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (lwi_14 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.log_write + 0x14) : mword 64) 4)]> R5).
    assert (Htgtacq : add_vec (mword_of_int (KernelSyms.log_write + 0x14) : mword 64)
                        (sign_extend' 64 (mword_of_int 2084232 : mword 21))
                      = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    assert (HmAsp : mA !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAa0 : mA !!! Regidx Ra0 = log_addr)
      by (rewrite /mA upd_ne; [exact HR5a0 | vm_compute; discriminate]).
    assert (HmAs1 : mA !!! Regidx Rs1 = (m !!! Regidx Ra0 : mword 64)).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [exact HR3s1 | vm_compute; discriminate]. }
    assert (HmAra : mA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.log_write + 0x14) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              mA !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9.
      rewrite /mA upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CID CID9 n eb p b ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (lw_cont_shift (CIDa := CID) (CIDb := CID9) bn γ γfs γd cov dev k pidv bno
                 bs bsd Φfsb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (Acquire.wp_acquire_sconf KT1 (ln_lk γ) "log"%string
              (log_res Psi γ bn γfs cov logstart) mA n eb p (K - 4)%nat b lks
              ltac:(lia) ltac:(lia) Hno
              with "Hcg Hcnt Htext Hpc [Hlock]").
    all: try lkbelow.
    { iEval (rewrite HmAa0). iExact "Hlock". }
    iIntros (CID10 Hs10 ms macq) "%Hmsfacts Hcg Hpc %Hacqpins Htok HRres Hcnt Hpay".
    assert (Hpc18 : ret_pc (mA !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.log_write + 0x18)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc18) in "Hpc".
    iDestruct (lw_cont_shift (CIDa := CID9) (CIDb := CID10) bn γ γfs γd cov dev k pidv bno
                 bs bsd Φfsb Bud m K n eb p b lks ltac:(wp_next_chain) with "Hcont") as "Hcont".
    pose proof Hacqpins as Hacqpins_cs.
    assert (Hregs : lw_regs m macq).
    { rewrite /lw_regs. split_and!.
      - rewrite (callee_saved_lookup Hacqpins_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HmAsp.
      - rewrite (callee_saved_lookup Hacqpins_cs Rs1 ltac:(vm_compute; reflexivity)).
        exact HmAs1.
      - intros c Hcs N2 N8 N9.
        rewrite (callee_saved_lookup Hacqpins_cs c Hcs). exact (HmAthr c Hcs N2 N8 N9). }
    pose proof Hregs as (Hsp & Hs1v & Hthr).
    assert (HmqS1 : macq !!! Regidx Rs1 = bnode k) by (rewrite Hs1v; exact Ha0).
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iAssert (lw_frame m) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe".
    { rewrite /lw_frame.
      iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hr24".
      iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hr16".
      iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hr8".
      iEval (rewrite Hb4) in "Hg4".
      iSplitL "Hr24"; [iExact "Hr24"|]. iSplitL "Hr16"; [iExact "Hr16"|].
      iSplitL "Hr8"; [iExact "Hr8"|]. iExists vg4. iExact "Hg4". }
    (* ================= THE CRITICAL SECTION ================= *)
    rewrite /log_res.
    iDestruct "HRres" as (out cmt nc om Ep Xr)
      "(Houtc & Hcmtc & Hncc & Hoauth & %Hsz & %Hbnd & %Hout3 & %Hcmt0 & Hepa & %Hepos & Hxa & %Hlive & %Hcap & Hbatch)".
    (* THIS OP'S BIRTH EPOCH ARRIVES NAMED (fs-log.md §G.19): the credit's
       group form is stated against it, so the contract takes [log_opSe] and
       [e0] is a parameter.  The auth's own soundness clause is about to pin
       it to [Ep]. *)
    iDestruct (log_opSe_positive with "Hoauth Hop") as %Hpos.
    destruct cmt.
    { exfalso. specialize (Hcmt0 eq_refl). lia. }
    iDestruct "Hbatch" as (nl LB) "(%Hsum & %Hsub & %Hreg & Hbatch)".
    rewrite /log_state.
    iDestruct "Hbatch" as (W L D M)
      "(%Hlen & %HLB & %Hnodup & %Hwok & Hncell & HW & Hjunk & HLauth & HDauth & Hcov & Hhdr & Hlogr & Hpool & Hmirh & %Hmhdr & %Hmtie & Hpsi)".
    destruct Hlen as [HlenW HnlB].
    (* ---- THE LEDGER STEP, both arms into ONE post-state.

       UNCREDITED (cr = false): a unit burns and [bno] joins this op's
       already-logged set, paying in advance for the lh.n the append will
       grow.
       CREDITED (cr = true): [bno] is already in the set, so
       [Sb ∪ {[bno]} = Sb] AND the entry is already [(u, Sb)] -- the insert
       is the identity and the ledger does not move at all.  The two arms
       therefore agree on [om'], and everything downstream is shared.

       What does NOT agree is the sum: the uncredited arm drops it by one,
       the credited arm leaves it alone.  So [HsumA] (the ABSORB exit, where
       lh.n is unchanged) holds on both arms, while [HsumB] (the APPEND
       exit, lh.n+1) is available only when a unit was actually spent --
       which is exactly right, because a credit makes the append branch
       unreachable ([Hcrmem] below refutes it). ---- *)
    (* MY ENTRY IS LIVE, SO IT WAS BORN IN THE CURRENT EPOCH.  This is the
       one place the group extension's soundness core is cashed, and it is
       cashed BEFORE the case split because both arms need it: the ledger
       step must hand the entry back at an epoch the caller can name, and
       the mint below has to agree with it. *)
    iDestruct (log_absorb_step γ om (S u) Sb e0 with "Hoauth Hop") as (i1) "%Hi1".
    assert (He0 : e0 = Ep) by exact (Hlive i1 (S u, Sb, e0) Hi1).
    subst e0. clear Hi1 i1.
    (* ---- THE CREDIT, CASHED (fs-log.md §G.19).  A credit says the block is
       in lh.block[] ALREADY, by whichever of the two routes the caller took
       -- its own earlier append ([uint bno ∈ Sb], through [Hsub]) or the
       group's ([logged_at] no older than [Ep], through [log_use_group]).
       Both land here, on the one pure fact the rest of this proof spends:
       it is what refutes the append branch below, and it is what lets the
       ledger record the block without spending a unit.  Nothing is
       consumed -- the conclusion is pure. ---- *)
    iDestruct (log_credit_use γ om Ep Xr LB (S u) Sb Ep (uint bno) cr
                 Hlive Hcap Hreg Hsub with "Hoauth Hxa Hop Hcredit") as %HcrLB.
    iAssert (|==> ∃ (om' : gmap nat op_entry),
               ghost_map_auth (ln_ops γ) 1 om' ∗
               log_opSe γ (if cr then S u else u) (Sb ∪ {[uint bno]}) Ep ∗
               ⌜size om' = out⌝ ∗
               ⌜forall j e, om' !! j = Some e -> (e.1.1 <= MAXOPBLOCKS)%nat⌝ ∗
               ⌜uint bno ∈ LB -> forall j e, om' !! j = Some e -> e.1.2 ⊆ LB⌝ ∗
               ⌜forall j e, om' !! j = Some e -> e.1.2 ⊆ LB ∪ {[uint bno]}⌝ ∗
               (* neither arm re-dates an entry: an absorb touches nothing
                  and a spend rewrites the budget and the set only *)
               ⌜forall j e, om' !! j = Some e -> e.2 = Ep⌝ ∗
               ⌜(nl + op_sum om' <= LOGBLOCKS)%nat⌝ ∗
               ⌜cr = false -> (S nl + op_sum om' <= LOGBLOCKS)%nat⌝ ∗
               ⌜(1 <= op_sum om)%nat⌝ ∗
               (* THE PENDING SET GROWS (durable-disk stage G1).  Both arms
                  record the written block in THIS op's already-logged set,
                  so [op_pending] only gets bigger -- which is exactly why
                  [log_state]'s rows are free at a [log_write]: the block
                  leaves the row's domain in the same critical section that
                  moves [L] at it. *)
               ⌜op_pending om ⊆ op_pending om'⌝)%I
      with "[Hoauth Hop]" as ">Hled".
    { destruct cr.
      - (* CREDITED: no unit burns and lh.n does not move, but the block
           still joins this op's set -- [log_record_step], whose sum is
           untouched ([op_sum_absorb]).  The old proof got away with "the
           ledger does not move at all" because the pure premise made
           [Sb ∪ {[bno]} = Sb]; under GROUP absorption the block need not be
           in [Sb] at all, so the insert is a real one.  Everything it owes
           is discharged by [HcrLB]: the block is in the header, so the
           grown set is still a subset of it. *)
        specialize (HcrLB eq_refl).
        iMod (log_record_step γ om (S u) Sb Ep (uint bno) with "Hoauth Hop")
          as (i0) "(%Hi0 & Hoauth & Hop)".
        set (om' := <[i0 := (S u, Sb ∪ {[uint bno]}, Ep)]> om).
        assert (Habs : op_sum om' = op_sum om)
          by (unfold om';
              apply (op_sum_absorb om i0 (S u) Sb (Sb ∪ {[uint bno]}) Ep);
              exact Hi0).
        iModIntro. iExists om'. iFrame "Hoauth Hop".
        iSplitR.
        { iPureIntro. unfold om'. rewrite map_size_insert_Some; [exact Hsz | eauto]. }
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hbnd i0 (S u, Sb, Ep) Hi0) as Hb. cbn in Hb. lia.
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hbnd j e Hj). }
        iSplitR.
        { iPureIntro. intros _ j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hsub i0 (S u, Sb, Ep) Hi0) as Hs. cbn in Hs.
            apply union_least; [exact Hs | apply elem_of_subseteq_singleton, HcrLB].
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hsub j e Hj). }
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hsub i0 (S u, Sb, Ep) Hi0) as Hs. cbn in Hs.
            exact (union_mono_r _ _ _ Hs).
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (union_subseteq_l' _ _ _ (Hsub j e Hj)). }
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. reflexivity.
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hlive j e Hj). }
        iSplitR; [iPureIntro; rewrite Habs; exact Hsum|].
        iSplitR; [iPureIntro; discriminate|].
        (* the unit in hand bounds the sum below, hence lh.n above *)
        iSplitR.
        { iPureIntro. pose proof (op_sum_delete om i0 (S u, Sb, Ep) Hi0) as He.
          cbn in He. lia. }
        iPureIntro. unfold om'. apply op_pending_insert_mono.
        intros e He. rewrite Hi0 in He. injection He as <-. cbn.
        apply union_subseteq_l.
      - (* UNCREDITED: spend one, and record the block *)
        iMod (log_spend_step γ om u Sb Ep (uint bno) with "Hoauth Hop")
          as (i0) "(%Hi0 & Hoauth & Hop)".
        set (om' := <[i0 := (u, Sb ∪ {[uint bno]}, Ep)]> om).
        assert (Hsum1 : (1 <= op_sum om)%nat).
        { pose proof (op_sum_delete om i0 (S u, Sb, Ep) Hi0) as He.
          cbn in He. lia. }
        assert (Hspend : op_sum om' = (op_sum om - 1)%nat)
          by (unfold om';
              apply (op_sum_spend om i0 u Sb (Sb ∪ {[uint bno]}) Ep);
              exact Hi0).
        iModIntro. iExists om'. iFrame "Hoauth Hop".
        iSplitR.
        { iPureIntro. unfold om'. rewrite map_size_insert_Some; [exact Hsz | eauto]. }
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hbnd i0 (S u, Sb, Ep) Hi0) as Hb. cbn in Hb. lia.
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hbnd j e Hj). }
        iSplitR.
        { iPureIntro. intros HinLB j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hsub i0 (S u, Sb, Ep) Hi0) as Hs. cbn in Hs.
            apply union_least; [exact Hs | apply elem_of_subseteq_singleton, HinLB].
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hsub j e Hj). }
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. cbn.
            pose proof (Hsub i0 (S u, Sb, Ep) Hi0) as Hs. cbn in Hs.
            exact (union_mono_r _ _ _ Hs).
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (union_subseteq_l' _ _ _ (Hsub j e Hj)). }
        (* the SPEND rewrites budget and set; the birth epoch rides along
           unchanged, which is what keeps the entry live at [Ep] *)
        iSplitR.
        { iPureIntro. intros j e Hj. unfold om' in Hj.
          destruct (decide (j = i0)) as [->|Hne].
          - rewrite lookup_insert in Hj. injection Hj as <-. reflexivity.
          - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
            exact (Hlive j e Hj). }
        iSplitR; [iPureIntro; rewrite Hspend; unfold LOGBLOCKS in *; lia|].
        iSplitR;
          [iPureIntro; intros _; rewrite Hspend; unfold LOGBLOCKS in *; lia|].
        iSplitR; [iPureIntro; exact Hsum1|].
        iPureIntro. unfold om'. apply op_pending_insert_mono.
        intros e He. rewrite Hi0 in He. injection He as <-. cbn.
        apply union_subseteq_l. }
    iDestruct "Hled" as (om')
      "(Hoauth & Hop & %HszL & %HbndL & %HsubA & %HsubB & %HliveL & %HsumA & %HsumBcr
        & %Hsum1 & %Hpend)".
    (* ---- THE MINT (fs-log.md §G.2).  One registry row, [(Ep, bno)], at
       the epoch this op was born in -- which by [HliveL] is the epoch the
       batch is running under.  It is minted HERE, before the arm split,
       because BOTH exits earn it: the append arm is about to write the
       block into lh.block[], and the absorb arm's scan has just reported it
       ALREADY there ([Hmem]/[HLB] below).  §G.10 reserved the absorbed-arm
       row on the grounds that its [(E,b) ∈ X -> b ∈ LB] obligation would
       have to come "from the credit"; at the site it comes from the scan,
       for free, and hoisting the mint keeps [Bud] free of the arm. ---- *)
    iMod (log_mint_logged γ Xr Ep (uint bno) with "Hxa") as "[Hxa #Hwit]".
    (* ---- AND THE ANCHOR CASHED (fs-log.md §G.17, blocker 4).  [Hepa] is
       the [ln_ep] auth, open only here; [HliveL]'s [e0 = Ep] above is the
       other half.  This one line is why the region's depositor can order
       its witness against the observation counter at all -- outside this
       ghost step the caller holds two lower bounds and can do nothing with
       them. ---- *)
    iDestruct (log_epoch_lb_le γ Ep vlb with "Hepa Hvlb") as %Hvle.
    iAssert Bud with "[Hop]" as "Hop".
    { rewrite /Bud.
      iApply (log_opSwe_intro γ _ _ Ep (uint bno) vlb Hvle with "Hop").
      iExact "Hwit". }
    assert (Hnl : (nl <= 29)%nat) by (unfold LOGBLOCKS in Hsum; lia).
    (* ...and in the header's terms: this is what refutes the append
       branch, since the scan can only fail to find a block that is not
       there. *)
    assert (Hcrmem : cr = true -> uint bno ∈ map uint W).
    { intros Hc. specialize (HcrLB Hc). rewrite HLB in HcrLB.
      by apply elem_of_list_to_set in HcrLB. }
    (* ---- the handle, opened ---- *)
    rewrite /bio_held.
    iDestruct "Hheld" as
      "(%Hk2 & %Hcov2 & %Hdev2 & Hslk & Hvalid & Hdevh & Hbufown & Hdisk & Hbpay)".
    rewrite /buf_own.
    iDestruct "Hbufown" as "(Hbnoc & Hbdisk & %Hlenbs & Hbytes)".
    iDestruct (lw_pay_split with "Hbpay") as "(HpL & HpD & Hextra)".
    (* ---- the logged view moves to the caller's bytes.  THE ATOMIC UPDATE
       IS FIRED HERE, and nowhere else: this is the one ghost moment between
       two instruction dispatches at which the caller's byte run has to
       exist, so the invariant it lives in is opened across exactly this step
       and shut again before the next dispatch.  [fsblock_update]'s own
       agreement against the handle's payload half is what pins the parked
       content [bsl'] to the [bsl] the handle is indexed at -- the caller
       never has to know it in advance. ---- *)
    iApply fupd_wp.
    (* THE WRITER'S ANCHOR, CASHED IN THE SAME BREATH (fs-log.md §G.17,
       blocker 4).  The fupd hands out its own lower bound [v'] -- the one
       resource the caller could not name outside its own invariant -- and
       [Hepa], still open here, is what orders it against this batch's
       epoch.  [Hwit] (minted above, both arms) and this comparison are the
       two inputs the closing wand takes; together they are exactly
       [InodeRegion.izrcpt]'s witness disjunct. *)
    iMod "Hau" as (sub_old v') "(%Hlsub & Hfsb & #Hvlb' & HauClose)".
    (* [e0] is already [Ep] here -- a live entry is born at the current
       epoch, [subst] above -- so this IS the comparison the wand wants. *)
    iDestruct (log_epoch_lb_le γ Ep v' with "Hepa Hvlb'") as %Hvle'.
    (* THE CROSSING, AT THE WRITER'S OWN WINDOW (durable-disk 2b-0).  The
       caller surrendered only [sub_old]; the other bytes of the block are
       LEARNED here, from the log's tie between the cache entry and the
       byte view, and the new cache content is the SPLICE -- which the
       shape premise then identifies with the buffer's own [bs]. *)
    iMod (byte_range_log_update Efs (fs_bytes γfs) (fs_cache γfs)
            (fs_home_set cov logstart) L (uint bno) off sub_old sub_new bsl
            HlogE ltac:(lia) ltac:(lia)
            ltac:(intros Hlb; destruct (Hshape Hlenbs Hlb) as [Hsn _]; lia)
            with "Hbinv HLauth Hfsb HpL")
      as "((%Hllk & %Hlenbsl & %Hslice) & HLauth & Hfsb & HpL)".
    (* the block's width is nameable only HERE, so the writer's shape
       obligation is discharged here too -- and the cache's new content is
       then literally the buffer's bytes, which is what everything
       downstream (the payload, the arms' rows, the post) is stated at. *)
    destruct (Hshape Hlenbs Hlenbsl) as [Hlsn Hbsplice].
    iEval (rewrite -Hbsplice) in "HLauth".
    iEval (rewrite -Hbsplice) in "HpL".
    (* THE PARKED PAYLOAD CROSSES THE CLIENT'S UPDATE (durable-disk 1d',
       item 3).  A [log_write] writes no disk block, so the committed view
       -- and with it the payload's index -- does not move: the payload goes
       in at [lm_committed M cov logstart] and comes back at the same index,
       whatever the client did inside it. *)
    assert (Hauin : length bsl = BSIZE /\ length sub_new = len /\
                    sub_old = take len (drop off bsl)).
    { split_and!; [exact Hlenbsl | exact Hlsn | rewrite -Hlsub; exact Hslice]. }
    iDestruct ("HauClose" with "[//] Hwit [//] Hfsb") as "HauClose".
    iMod ("HauClose" $! (lm_committed M cov logstart) with "Hpsi")
      as "[Hpsi HPhifsb]".
    iModIntro.
    (* ---- THE d-TIE: the handle's dirty half against the batch's ---- *)
    rewrite (big_sepS_delete _ cov (uint bno) Hcovbno).
    iDestruct "Hcov" as "[Hcovb Hcovrest]".
    iDestruct (ghost_map_elem_agree with "HpD Hcovb") as %Hdtie.
    (* ---- the junk slot at index nl, peeled off the free run ---- *)
    assert (Hsq2 : seq nl (LOGBLOCKS - nl)
                   = nl :: seq (S nl) (LOGBLOCKS - S nl)).
    { assert (Hsq : (LOGBLOCKS - nl)%nat = S (LOGBLOCKS - S nl))
        by (unfold LOGBLOCKS; lia).
      rewrite Hsq. reflexivity. }
    iEval (rewrite Hsq2) in "Hjunk".
    iDestruct "Hjunk" as "[Hjhead Hjtail]".
    (* ===== +0x18 / +0x1c : a2 := log.lh.n ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x18)) Ra2 (mword_of_int 30 : mword 20)
              macq (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_18 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T1 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x18) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> macq).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.log_write + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    assert (Hna : add_vec (rget T1 Ra2) (sign_extend' 64 (mword_of_int 1406 : mword 12))
                  = lh_n_pa).
    { rgne. rewrite /T1 upd_eq /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hna) in "Hncell".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.log_write + 0x1c)) Ra2 Ra2
              (mword_of_int 1406 : mword 12) T1 (trap_res b + (K - 4))%nat
              (mword_of_int (Z.of_nat nl) : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hncell").
    { iApply (lwi_1c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hncell".
    iEval (rewrite Hna) in "Hncell".
    set (T2 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat nl) : mword 32))]> T1).
    assert (HT2a2 : T2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64)).
    { rewrite /T2 upd_eq. apply sext32_64_small.
      change (2^31) with 2147483648; lia. }
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x1c) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ===== +0x20 c.li a5,29 ; +0x22 blt a5,a2 -- the DEAD "too big" panic ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.log_write + 0x20)) Ra5 (mword_of_int 29 : mword 6)
              (mword_of_int 29 : mword 64) T2 (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite lw_s29c; apply add_vec_zero_l)
              with "Hcg Hpc []").
    { iApply (lwi_20 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 29 : mword 64)]> T2).
    assert (HT3a5 : T3 !!! Regidx Ra5 = (mword_of_int 29 : mword 64))
      by (rewrite /T3; apply upd_eq).
    assert (HT3a2 : T3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2a2 | vm_compute; discriminate]).
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    assert (Hbltf : zopz0zI_s (rget T3 Ra5) (rget T3 Ra2) = false).
    { rgne. rgne. rewrite HT3a5 HT3a2.
      rewrite lw_ltb_s; [| change (2^31) with 2147483648; lia
                         | change (2^31) with 2147483648; lia].
      apply Z.ltb_ge. lia. }
    iApply (wp_blt_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0x22)) (mword_of_int 90 : mword 13)
              Ra2 Ra5 T3 (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hbltf with "Hcg Hpc []").
    { iApply (lwi_22 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x22) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 / +0x2a : a5 := log.outstanding ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x26)) Ra5 (mword_of_int 30 : mword 20)
              T3 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (lwi_26 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.log_write + 0x26) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> T3).
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.log_write + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    assert (Hoa : add_vec (rget T4 Ra5) (sign_extend' 64 (mword_of_int 1376 : mword 12))
                  = l_out).
    { rgne. rewrite /T4 upd_eq /l_out /log_pa /log_addr /pa_add /add_vec_int.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hoa) in "Houtc".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.log_write + 0x2a)) Ra5 Ra5
              (mword_of_int 1376 : mword 12) T4 (trap_res b + (K - 4))%nat
              (mword_of_int (Z.of_nat out) : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Houtc").
    { iApply (lwi_2a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Houtc".
    iEval (rewrite Hoa) in "Houtc".
    set (T5 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> T4).
    assert (HT5a5 : T5 !!! Regidx Ra5 = (mword_of_int (Z.of_nat out) : mword 64)).
    { rewrite /T5 upd_eq. apply sext32_64_small.
      change (2^31) with 2147483648; lia. }
    assert (HT5a2 : T5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64)).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [exact HT3a2 | vm_compute; discriminate]. }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.log_write + 0x2a) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e blez a5 -- the DEAD "outside of trans" panic ===== *)
    assert (Hblezf : zopz0zKzJ_s (zero_reg : mword 64) (rget T5 Ra5) = false).
    { rgne. rewrite HT5a5.
      rewrite lw_geb_s0; [| change (2^31) with 2147483648; lia].
      rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0x2e)) (mword_of_int 90 : mword 13)
              Ra5 T5 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate)
              Hblezf with "Hcg Hpc []").
    { iApply (lwi_2e with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x2e) : mword 64) 4
                    = mword_of_int (KernelSyms.log_write + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x32 c.li a5,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.log_write + 0x32)) Ra5 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) T5 (trap_res b + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rewrite lw_s0c; apply add_vec_zero_l)
              with "Hcg Hpc []").
    { iApply (lwi_32 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T6 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> T5).
    assert (HT6a5 : T6 !!! Regidx Ra5 = (mword_of_int (Z.of_nat 0%nat) : mword 64))
      by (rewrite /T6; apply upd_eq).
    assert (HT6a2 : T6 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nl) : mword 64))
      by (rewrite /T6 upd_ne; [exact HT5a2 | vm_compute; discriminate]).
    assert (HT6s1 : T6 !!! Regidx Rs1 = bnode k).
    { rewrite /T6 upd_ne; [| vm_compute; discriminate].
      rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact HmqS1 | vm_compute; discriminate]. }
    assert (HT6regs : lw_regs m T6).
    { rewrite /lw_regs. split_and!.
      - rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - rewrite /T6 upd_ne; [| vm_compute; discriminate].
        rewrite /T5 upd_ne; [| vm_compute; discriminate].
        rewrite /T4 upd_ne; [| vm_compute; discriminate].
        rewrite /T3 upd_ne; [| vm_compute; discriminate].
        rewrite /T2 upd_ne; [| vm_compute; discriminate].
        rewrite /T1 upd_ne; [exact Hs1v | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9.
        rewrite /T6 upd_ne; [| regne].
        rewrite /T5 upd_ne; [| regne].
        rewrite /T4 upd_ne; [| regne].
        rewrite /T3 upd_ne; [| regne].
        rewrite /T2 upd_ne; [| regne].
        rewrite /T1 upd_ne; [| regne].
        exact (Hthr c Hcs N2 N8 N9). }
    (* ================= THE TWO CLOSING WANDS ================= *)
    iAssert (lw_closeA Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud nl W
             ∧ lw_closeB Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud nl W)%I
      with "[Houtc Hcmtc Hncc Hoauth Hepa Hxa HLauth HDauth Hcovrest Hcovb Hhdr Hlogr Hpool
             Hmirh Hpsi Hjtail HpL HpD Hextra Hslk Hvalid Hdevh Hbdisk Hbytes Hdisk
             HPhifsb Hop]"
      as "Hcl".
    { iSplit.
      - (* ---------------- ABSORB ---------------- *)
        rewrite /lw_closeA.
        iIntros (Hmem) "Hjh HW Hbnoc Hncell Hslot".
        assert (Hdt : d = true)
          by (rewrite Hdtie; apply bool_decide_eq_true_2; exact Hmem).
        clear Hdtie. subst d.
        iDestruct "Hextra" as (q) "Href".
        iModIntro.
        iSplitR "HpL HpD Href Hslk Hvalid Hdevh Hbnoc Hbdisk Hbytes Hdisk HPhifsb Hop Hslot".
        + rewrite /log_res.
          iExists out, false, nc, om', Ep, (Xr ∪ {[(Ep, uint bno)]}).
          iFrame "Houtc Hcmtc Hncc Hoauth".
          iSplitR; [iPureIntro; exact HszL|].
          iSplitR; [iPureIntro; exact HbndL|].
          iSplitR; [iPureIntro; exact Hout3|].
          iSplitR; [iPureIntro; intros Hc; discriminate|].
          iFrame "Hepa".
          iSplitR; [iPureIntro; exact Hepos|].
          iFrame "Hxa".
          iSplitR; [iPureIntro; exact HliveL|].
          (* the new row carries the CURRENT epoch, so the cap still holds *)
          iSplitR.
          { iPureIntro. intros e' b' Hin.
            apply elem_of_union in Hin as [Hin|Hin].
            - exact (Hcap e' b' Hin).
            - apply elem_of_singleton in Hin. injection Hin as -> ->. lia. }
          iExists nl, LB. iSplitR; [iPureIntro; exact HsumA|].
          (* ABSORB: W is unchanged, so LB is too, and the block is already
             in it -- which is exactly what [Hmem] says. *)
          assert (HbnoLB : uint bno ∈ LB).
          { rewrite HLB. by apply elem_of_list_to_set. }
          iSplitR.
          { iPureIntro. apply HsubA. exact HbnoLB. }
          (* ...AND THAT IS THE ABSORBED-ARM MINT'S WHOLE COST: the block the
             row names is in the header because the SCAN found it there. *)
          iSplitR.
          { iPureIntro. intros b' Hin.
            apply elem_of_union in Hin as [Hin|Hin].
            - exact (Hreg b' Hin).
            - apply elem_of_singleton in Hin. injection Hin as ->. exact HbnoLB. }
          iApply (log_state_pend_mono _ _ _ _ _ _ _ _ _ Hpend).
          rewrite /log_state. iExists W, (<[uint bno := bs]> L), D, M.
          iSplitR; [iPureIntro; split; [exact HlenW | exact HnlB]|].
          iSplitR; [iPureIntro; exact HLB|].
          iSplitR; [iPureIntro; exact Hnodup|].
          iSplitR; [iPureIntro; exact Hwok|].
          iFrame "Hncell HW".
          iSplitL "Hjh Hjtail".
          { iEval (rewrite Hsq2). iSplitL "Hjh"; [iExact "Hjh" | iExact "Hjtail"]. }
          iFrame "HLauth HDauth".
          iSplitL "Hcovb Hcovrest".
          { rewrite (big_sepS_delete _ cov (uint bno) Hcovbno).
            iSplitL "Hcovb"; [iExact "Hcovb" | iExact "Hcovrest"]. }
          iFrame "Hhdr Hlogr Hpool Hmirh".
          iSplitR; [iPureIntro; exact Hmhdr|].
          (* ROW (b), the ABSORB arm.  FREE: [LB] does not move and the scan
             found [bno] in it ([HbnoLB]), so the only key [L] moves at is
             already outside the row's domain. *)
          iSplitR.
          { iPureIntro. intros b' Hb' HbLB.
            assert (Hne : uint bno <> b')
              by (intros Heq; apply HbLB; rewrite -Heq; exact HbnoLB).
            rewrite (lookup_insert_ne L (uint bno) b' bs Hne).
            exact (Hmtie b' Hb' HbLB). }
          (* THE PARKED PAYLOAD GOES BACK AT THE SAME INDEX: the picture [M]
             does not move at a [log_write], so neither does the committed
             view it is indexed by (durable-disk 1d'). *)
          iExact "Hpsi".
        + rewrite /lw_res. iFrame "Hop HPhifsb Hslot".
          rewrite /bio_locked /bio_held.
          iSplitR; [iPureIntro; exact Hk2|].
          iSplitR; [iPureIntro; exact Hcov2|].
          iSplitR; [iPureIntro; exact Hdev2|].
          iFrame "Hslk Hvalid Hdevh".
          iSplitL "Hbnoc Hbdisk Hbytes".
          { rewrite /buf_own.
            iSplitL "Hbnoc"; [iExact "Hbnoc"|].
            iSplitL "Hbdisk"; [iExact "Hbdisk"|].
            iSplitR; [iPureIntro; exact Hlenbs|]. iExact "Hbytes". }
          iSplitL "Hdisk"; [iExact "Hdisk"|].
          iApply (lw_pay_mk with "HpL HpD [Href]"). iExists q. iExact "Href".
      - (* ---------------- APPEND ---------------- *)
        rewrite /lw_closeB.
        iIntros (Hnotmem) "HW Hcell Hbnoc Href Hncell".
        assert (Hdf : d = false)
          by (rewrite Hdtie; apply bool_decide_eq_false_2; exact Hnotmem).
        clear Hdtie. subst d.
        assert (Hbd : bool_decide (uint bno ∈ map uint W) = false)
          by (apply bool_decide_eq_false_2; exact Hnotmem).
        iEval (rewrite Hbd) in "Hcovb".
        iMod (fs_dirty_flip γfs D (uint bno) false false true with "HDauth HpD Hcovb")
          as "((%Hdd & %HDlk) & HDauth & HpD & Hcovb)".
        iDestruct "Href" as (q dv bv) "Href".
        rewrite /bref. iDestruct "Href" as "(Hrt & Hrdev & Hrbno)".
        iDestruct (word4_pointsto_agree with "Hdevh Hrdev") as %Hdveq.
        iDestruct (word4_pointsto_agree with "Hbnoc Hrbno") as %Hbveq.
        subst dv bv.
        (* one pool unit becomes the caller's refund *)
        assert (Hpl : ((LOGBLOCKS - nl) + 2)%nat = (1 + ((LOGBLOCKS - S nl) + 2))%nat)
          by (unfold LOGBLOCKS; lia).
        iEval (rewrite Hpl bslots_op) in "Hpool".
        iDestruct "Hpool" as "[Hslot Hpool]".
        assert (HbdT : bool_decide (uint bno ∈ map uint (W ++ [bno])) = true)
          by (apply bool_decide_eq_true_2; apply lw_mem_snoc).
        iModIntro.
        iSplitR "HpL HpD Hrt Hrdev Hrbno Hslk Hvalid Hdevh Hbnoc Hbdisk Hbytes
                 Hdisk HPhifsb Hop Hslot".
        + rewrite /log_res.
          iExists out, false, nc, om', Ep, (Xr ∪ {[(Ep, uint bno)]}).
          iFrame "Houtc Hcmtc Hncc Hoauth".
          iSplitR; [iPureIntro; exact HszL|].
          iSplitR; [iPureIntro; exact HbndL|].
          iSplitR; [iPureIntro; exact Hout3|].
          iSplitR; [iPureIntro; intros Hc; discriminate|].
          iFrame "Hepa".
          iSplitR; [iPureIntro; exact Hepos|].
          iFrame "Hxa".
          iSplitR; [iPureIntro; exact HliveL|].
          iSplitR.
          { iPureIntro. intros e' b' Hin.
            apply elem_of_union in Hin as [Hin|Hin].
            - exact (Hcap e' b' Hin).
            - apply elem_of_singleton in Hin. injection Hin as -> ->. lia. }
          iExists (S nl), (LB ∪ {[uint bno]}).
          (* THE APPEND BRANCH IS UNREACHABLE UNDER A CREDIT: the scan
             reported [bno] absent from lh.block[], but a credit says it is
             present.  So [cr = false] here, and the unit spent above pays
             for the lh.n this branch grows. *)
          assert (Hcrf : cr = false).
          { destruct cr; [| reflexivity].
            exfalso. exact (Hnotmem (Hcrmem eq_refl)). }
          iSplitR; [iPureIntro; exact (HsumBcr Hcrf)|].
          (* APPEND: LB grows by exactly the block this op just logged *)
          iSplitR; [iPureIntro; exact HsubB|].
          (* the minted row names the block this arm just appended, so the
             registry's current-epoch clause holds against the GROWN LB *)
          iSplitR.
          { iPureIntro. intros b' Hin.
            apply elem_of_union in Hin as [Hin|Hin].
            - apply elem_of_union_l. exact (Hreg b' Hin).
            - apply elem_of_singleton in Hin. injection Hin as ->.
              apply elem_of_union_r, elem_of_singleton. reflexivity. }
          iApply (log_state_pend_mono _ _ _ _ _ _ _ _ _ Hpend).
          rewrite /log_state. iExists (W ++ [bno]), (<[uint bno := bs]> L),
                                     (<[uint bno := true]> D), M.
          iSplitR.
          { iPureIntro. split.
            - rewrite length_app HlenW /=. lia.
            - unfold LOGBLOCKS in *. lia. }
          iSplitR.
          { iPureIntro. subst LB. rewrite map_app list_to_set_app_L /= right_id_L.
            reflexivity. }
          iSplitR; [iPureIntro; apply lw_nodup_snoc; assumption|].
          iSplitR; [iPureIntro; apply lw_wok_snoc; assumption|].
          iSplitL "Hncell".
          { assert (Hmn : (mword_of_int (Z.of_nat nl + 1) : mword 32)
                          = mword_of_int (Z.of_nat (S nl))) by (f_equal; lia).
            iEval (rewrite Hmn) in "Hncell". iExact "Hncell". }
          iSplitL "HW Hcell".
          { rewrite big_sepL_snoc -HlenW.
            iSplitL "HW"; [iExact "HW" | iExact "Hcell"]. }
          iSplitL "Hjtail"; [iExact "Hjtail"|].
          iFrame "HLauth HDauth".
          iSplitL "Hcovb Hcovrest".
          { rewrite (big_sepS_delete _ cov (uint bno) Hcovbno).
            iSplitL "Hcovb"; [rewrite HbdT; iExact "Hcovb"|].
            iApply (big_sepS_mono with "Hcovrest").
            intros x Hx. assert (Hxne : x <> uint bno).
            { apply elem_of_difference in Hx as [_ Hx].
              intro Hc. apply Hx. rewrite Hc. apply elem_of_singleton. reflexivity. }
            rewrite (lw_bd_snoc W bno x Hxne). done. }
          iFrame "Hhdr Hlogr Hpool Hmirh".
          iSplitR; [iPureIntro; exact Hmhdr|].
          (* ROW (b), the APPEND arm.  FREE: [LB] grows by exactly [uint bno],
             the one key [L] moves at, so the row's domain shrinks by it. *)
          iSplitR.
          { iPureIntro. intros b' Hb' HbLB.
            assert (Hne : uint bno <> b').
            { intros Heq. apply HbLB. rewrite -Heq.
              apply elem_of_union_r, elem_of_singleton. reflexivity. }
            rewrite (lookup_insert_ne L (uint bno) b' bs Hne).
            apply (Hmtie b' Hb').
            intros Hin. apply HbLB, elem_of_union_l. exact Hin. }
          (* the parked payload, back at the same index -- see the absorb arm *)
          iExact "Hpsi".
        + rewrite /lw_res. iFrame "Hop HPhifsb Hslot".
          rewrite /bio_locked /bio_held.
          iSplitR; [iPureIntro; exact Hk2|].
          iSplitR; [iPureIntro; exact Hcov2|].
          iSplitR; [iPureIntro; exact Hdev2|].
          iFrame "Hslk Hvalid Hdevh".
          iSplitL "Hbnoc Hbdisk Hbytes".
          { rewrite /buf_own.
            iSplitL "Hbnoc"; [iExact "Hbnoc"|].
            iSplitL "Hbdisk"; [iExact "Hbdisk"|].
            iSplitR; [iPureIntro; exact Hlenbs|]. iExact "Hbytes". }
          iSplitL "Hdisk"; [iExact "Hdisk"|].
          iApply (lw_pay_mk with "HpL HpD [Hrt Hrdev Hrbno]").
          iExists q. rewrite /bref. iFrame "Hrt Hrdev Hrbno". }
    (* ===== +0x34 blez a2 : the n == 0 entry goes straight to the store ===== *)
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x32) : mword 64) 2
                    = mword_of_int (KernelSyms.log_write + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    destruct nl as [|nlp] eqn:Hnleq.
    - (* ---- lh.n == 0: the loop is skipped; the +0x94 block appends ---- *)
      assert (Hcmp : zopz0zKzJ_s (zero_reg : mword 64) (rget T6 Ra2) = true).
      { rgne. rewrite HT6a2.
        rewrite lw_geb_s0; [| change (2^31) with 2147483648; lia].
        reflexivity. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.log_write + 0x34)) (mword_of_int 96 : mword 13)
                Ra2 T6 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (lwi_34 with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt94 : add_vec (mword_of_int (KernelSyms.log_write + 0x34) : mword 64)
                         (sign_extend' 64 (mword_of_int 96 : mword 13))
                       = mword_of_int (KernelSyms.log_write + 0x94))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt94) in "Hpc".
      assert (HWnil : W = []) by (apply nil_length_inv; lia).
      assert (Hnotmem : ~ (uint bno ∈ map uint W))
        by (rewrite HWnil; intro Hc; inversion Hc).
      iDestruct "Hjhead" as (jk) "Hjhead".
      iAssert ((⌜0%nat = 0%nat⌝ -∗ lh_block 0 ↦₄ bno -∗
                  lw_closeP Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud 0)
               ∧ (⌜0%nat <> 0%nat⌝ -∗ lh_block 0 ↦₄ bno -∗
                  lw_closeR Psi γ bn γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud 0))%I
        with "[Hcl HW]" as "Hcl94".
      { iSplit.
        - iIntros (_) "Hcell". iDestruct "Hcl" as "[_ HB]".
          rewrite /lw_closeB.
          iApply ("HB" with "[%] HW Hcell"). exact Hnotmem.
        - iIntros (Hbad). exfalso. apply Hbad. reflexivity. }
      iApply (lw_blk94 Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud
                0%nat 0%nat jk m T6 K n eb p b lks
                ltac:(exact HK) ltac:(exact Hnoff) ltac:(exact Hbeq) Hk
                ltac:(lia) ltac:(lia) Ha0 HT6regs HT6a5 HT6a2 Hno
                with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hbslot Hbnoc
                      Hjhead Hncell Hcl94 Hcont").
    - (* ---- lh.n >= 1: set up and run the scan ---- *)
      assert (Hcmp : zopz0zKzJ_s (zero_reg : mword 64) (rget T6 Ra2) = false).
      { rgne. rewrite HT6a2.
        rewrite lw_geb_s0; [| change (2^31) with 2147483648; lia].
        rewrite Z.geb_leb. apply Z.leb_gt. lia. }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.log_write + 0x34)) (mword_of_int 96 : mword 13)
                Ra2 T6 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc []").
      { iApply (lwi_34 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x34) : mword 64) 4
                      = mword_of_int (KernelSyms.log_write + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.lw a1,12(s1) : b->blockno *)
      assert (Hbaddr : add_vec (rget T6 Rs1) (sign_extend' 64 (mword_of_int 12 : mword 12))
                       = b_blockno (bpa k)).
      { rgne. rewrite HT6s1 lw_s12.
        rewrite /b_blockno /bpa /pa_add /add_vec_int. reflexivity. }
      iEval (rewrite -Hbaddr) in "Hbnoc".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (dqm := DfracOwn (1/2)) (mword_of_int (KernelSyms.log_write + 0x38)) Ra1 Rs1
                (mword_of_int 12 : mword 12) T6 (trap_res b + (K - 4))%nat bno false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hbnoc").
      { iApply (lwi_38 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hbnoc".
      iEval (rewrite Hbaddr) in "Hbnoc".
      set (T7 := <[Regidx Ra1 := regval_into_reg (sign_extend' 64 bno)]> T6).
      assert (HT7a1 : T7 !!! Regidx Ra1 = sign_extend' 64 bno)
        by (rewrite /T7; apply upd_eq).
      assert (HT7a2 : T7 !!! Regidx Ra2 = (mword_of_int (Z.of_nat (S nlp)) : mword 64))
        by (rewrite /T7 upd_ne; [exact HT6a2 | vm_compute; discriminate]).
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.log_write + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.log_write + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      (* +0x3a / +0x3e : a4 := &log.lh.block[0] *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.log_write + 0x3a)) Ra4 (mword_of_int 30 : mword 20)
                T7 (trap_res b + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (lwi_3a with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T8 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.log_write + 0x3a) : mword 64)
                       (auipc_off (mword_of_int 30 : mword 20)))]> T7).
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.log_write + 0x3a) : mword 64) 4
                      = mword_of_int (KernelSyms.log_write + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.log_write + 0x3e)) Ra4 Ra4
                (mword_of_int 1376 : mword 12) T8 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (lwi_3e with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T9 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (T8 !!! Regidx Ra4 : mword 64)
                       (sign_extend' 64 (mword_of_int 1376 : mword 12)))]> T8).
      assert (HT9a4 : T9 !!! Regidx Ra4 = lh_block 0).
      { rewrite /T9 upd_eq /T8 upd_eq /lh_block /log_pa /log_addr /pa_add /add_vec_int.
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.log_write + 0x3e) : mword 64) 4
                      = mword_of_int (KernelSyms.log_write + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* +0x42 c.li a5,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.log_write + 0x42)) Ra5 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) T9 (trap_res b + (K - 4))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(rewrite lw_s0c; apply add_vec_zero_l)
                with "Hcg Hpc []").
      { iApply (lwi_42 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (TA := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> T9).
      assert (HTAa5 : TA !!! Regidx Ra5 = (mword_of_int (Z.of_nat 0%nat) : mword 64))
        by (rewrite /TA; apply upd_eq).
      assert (HTAa4 : TA !!! Regidx Ra4 = lh_block 0)
        by (rewrite /TA upd_ne; [exact HT9a4 | vm_compute; discriminate]).
      assert (HTAa2 : TA !!! Regidx Ra2 = (mword_of_int (Z.of_nat (S nlp)) : mword 64)).
      { rewrite /TA upd_ne; [| vm_compute; discriminate].
        rewrite /T9 upd_ne; [| vm_compute; discriminate].
        rewrite /T8 upd_ne; [exact HT7a2 | vm_compute; discriminate]. }
      assert (HTAa1 : TA !!! Regidx Ra1 = sign_extend' 64 bno).
      { rewrite /TA upd_ne; [| vm_compute; discriminate].
        rewrite /T9 upd_ne; [| vm_compute; discriminate].
        rewrite /T8 upd_ne; [exact HT7a1 | vm_compute; discriminate]. }
      assert (HTAregs : lw_regs m TA).
      { rewrite /lw_regs. split_and!.
        - rewrite /TA upd_ne; [| vm_compute; discriminate].
          rewrite /T9 upd_ne; [| vm_compute; discriminate].
          rewrite /T8 upd_ne; [| vm_compute; discriminate].
          rewrite /T7 upd_ne; [| vm_compute; discriminate].
          exact (proj1 HT6regs).
        - rewrite /TA upd_ne; [| vm_compute; discriminate].
          rewrite /T9 upd_ne; [| vm_compute; discriminate].
          rewrite /T8 upd_ne; [| vm_compute; discriminate].
          rewrite /T7 upd_ne; [| vm_compute; discriminate].
          exact (proj1 (proj2 HT6regs)).
        - intros c Hcs N2 N8 N9.
          rewrite /TA upd_ne; [| regne].
          rewrite /T9 upd_ne; [| regne].
          rewrite /T8 upd_ne; [| regne].
          rewrite /T7 upd_ne; [| regne].
          exact (proj2 (proj2 HT6regs) c Hcs N2 N8 N9). }
      iApply (lw_scan Psi bn γ γfs γd cov logstart dev k pidv bno bs bsd Φfsb Bud
                (S nlp) W m K n eb p b lks (S nlp)
                ltac:(exact HK) ltac:(exact Hnoff) ltac:(exact Hbeq) Hk
                ltac:(lia) ltac:(lia) Ha0 Hno
                0%nat TA ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)
                HTAregs HTAa5 HTAa4 HTAa2 HTAa1
                with "Hcg Htext Hpc Hbio Hlctx Hcnt Hpay Htok Hframe Hbslot Hbnoc
                      HW Hjhead Hncell Hcl Hcont").
  Qed.

  (* THE WHOLE-BLOCK ATOMIC-UPDATE CONTRACT (durable-disk 2b-0), unchanged
     from what its five suppliers were written against, as the range form's
     instance at [off := 0], [len := BSIZE], [sub_new := bs].  BOTH of the
     range form's side conditions are discharged from the block's width --
     which is precisely why they are guarded by it: a caller of THIS form
     knows [length bs = BSIZE] only from inside the handle, and this
     derivation never opens one.  [lw_au_whole] does the same for the fupd:
     the range form hands its writer the two widths as wand inputs, so the
     whole-block reading [take BSIZE (drop 0 bsl) = bsl] is available
     exactly where it is needed. *)
  Lemma wp_log_write_au
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z) (e0 : nat) (vlb : nat)
      (Psi : gmap Z (list (bv 8)) -> iProp Σ)
      (Efs : coPset) (Φfsb : iProp Σ)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string)
    : wp_log_write_au_body bn γ γfs γd cov logstart dev k pidv bno
                           bs bsl bsd d u cr Sb e0 vlb Psi Efs Φfsb m n eb p K b lks.
  Proof.
    cbv beta delta [wp_log_write_au_body].
    intros pcE ret_tgt HK Hnoff Hk Ha0 Hcovbno Hnotlog HlogE Hno.
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hlctx Hbslot #Hvlb #Hcredit Hop Hau Hheld Hcont".
    iApply (wp_log_write_au_range bn γ γfs γd cov logstart dev k pidv bno
              bs bsl bsd d u 0%nat BSIZE bs cr Sb e0 vlb Psi Efs Φfsb
              m n eb p K b lks
              HK Hnoff Hk Ha0 Hcovbno Hnotlog HlogE
              ltac:(lia) ltac:(unfold BSIZE; lia)
              ltac:(intros Hlb Hlbsl; split;
                    [exact Hlb | symmetry; apply blk_splice_whole; lia])
              Hno
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hbslot Hvlb Hcredit Hop
                    [Hau] Hheld Hcont").
    iApply (lw_au_whole γ γfs (uint bno) Efs bs bsl Φfsb e0 Psi with "Hau").
  Qed.

  (* THE EPOCH-EXPOSED CONTRACT (fs-log.md §G.20), derived from the
     atomic-update one at a held [fsblock] and the trivial anchor
     ([vlb := 0], so the [⌜vlb <= e0⌝] the post carries is free and gets
     dropped here).  NOTHING IS FORGOTTEN: the entry comes back at the very
     [e0] that went in, which is the one thing [wp_log_write_gen] below
     cannot say and the reason this form exists. *)
  Lemma wp_log_write_gene
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z) (e0 : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string)
    : wp_log_write_gene_body bn γ γfs γd cov logstart dev k pidv bno
                             bs bsl bsd d u cr Sb e0 m n eb p K b lks.
  Proof.
    cbv beta delta [wp_log_write_gene_body].
    intros pcE ret_tgt HK Hnoff Hk Ha0 Hcovbno Hnotlog Hno.
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hlctx Hbslot #Hcred Hop Hfsb Hheld Hcont".
    (* THE PAYLOAD'S INDEX FUNCTION, NAMED (durable-disk 1d').  This form
       holds the byte run itself, so it owes the payload nothing -- but the
       atomic-update form below it is stated over the Psi-NAMED context, so
       the existential [LogInv.log_ctx] closes is opened here, once, and
       every caller of THIS contract is unchanged. *)
    iDestruct "Hlctx" as (Psi) "#Hlctx".
    (* the anchor at 0: a lower bound of zero is the unit, so this form costs
       its callers no epoch anchor of their own *)
    iApply fupd_wp. iMod (log_epoch_lb_0 γ) as "#Hlb0". iModIntro.
    iApply (wp_log_write_au bn γ γfs γd cov logstart dev k pidv bno
              bs bsl bsd d u cr Sb e0 0%nat Psi ⊤
              (fsblock (fs_bytes γfs) (uint bno) bs)%I
              m n eb p K b lks
              HK Hnoff Hk Ha0 Hcovbno Hnotlog ltac:(set_solver) Hno
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hbslot Hlb0 Hcred Hop [Hfsb] Hheld [Hcont]").
    all: try lkbelow.
    2: { iIntros (CIDx) "%Hchain".
         iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hchain|].
         iIntros (mr) "Hsie Hcnt Hpc %Hcs HopW Hfsb Hlk Hslot".
         rewrite /log_opSwe.
         iDestruct "HopW" as "(HopS & #Hwit & _)".
         iApply ("Hcont" $! mr with "Hsie Hcnt Hpc [%] HopS Hwit Hfsb Hlk Hslot").
         exact Hcs. }
    (* the degenerate anchor inline: this form HOLDS the half, so it parks
       the bound at zero (the [Hlb0] it already minted) and drops both of
       the closing wand's new inputs *)
    iModIntro. iExists bsl, 0%nat. iFrame "Hfsb Hlb0".
    iIntros "_ _ _ Hfsb". iIntros (D0) "Hpsi". iModIntro.
    iFrame "Hpsi Hfsb".
  Qed.

  (* THE HELD-[fsblock] CONTRACT, derived from the epoch-exposed one by
     CLOSING the epoch: a caller that threads [log_opS] opens its own [e0]
     with [log_opS_named], builds the credit's own-set disjunct from the pure
     premise it already had ([log_credit_own]), and drops both the epoch and
     the registry row on the way out.  That forgetting is what keeps every
     landed caller -- bfree's credited arm, balloc's bitmap write, writei's
     [bool_decide] -- byte-stable. *)
  Lemma wp_log_write_gen
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (cr : bool) (Sb : gset Z)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string)
    : wp_log_write_gen_body bn γ γfs γd cov logstart dev k pidv bno
                            bs bsl bsd d u cr Sb m n eb p K b lks.
  Proof.
    cbv beta delta [wp_log_write_gen_body].
    intros pcE ret_tgt HK Hnoff Hk Ha0 Hcovbno Hnotlog Hcredit Hno.
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hlctx Hbslot Hop Hfsb Hheld Hcont".
    (* THE CREDIT, IN ITS OWN-SET FORM (fs-log.md §G.19).  This form's
       premise is the PURE one it always was, and [log_credit_own] is the
       whole conversion: the birth epoch is opened here (the group form
       needs it; the own-set disjunct does not look at it), so every landed
       [wp_log_write_gen] caller -- bfree's credited arm, balloc's bitmap
       write, writei's [bool_decide] -- stays byte-stable. *)
    iDestruct (log_opS_named with "Hop") as (e0) "Hop".
    iPoseProof (log_credit_own γ cr Sb e0 (uint bno) Hcredit) as "#Hcred".
    iApply (wp_log_write_gene bn γ γfs γd cov logstart dev k pidv bno
              bs bsl bsd d u cr Sb e0 m n eb p K b lks
              HK Hnoff Hk Ha0 Hcovbno Hnotlog Hno
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hbslot Hcred Hop Hfsb Hheld [Hcont]").
    all: try lkbelow.
    (* the epoch and the witness are DROPPED here, which is what keeps every
       landed [wp_log_write_gen] caller byte-stable: only the epoch-exposed
       and atomic-update forms -- the walkers', and the one §G.3's receipt is
       deposited from -- carry the epoch-stamped row. *)
    iIntros (CIDx) "%Hchain".
    iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hchain|].
    iIntros (mr) "Hsie Hcnt Hpc %Hcs HopS _ Hfsb Hlk Hslot".
    iDestruct (log_opSe_opS with "HopS") as "HopS".
    iApply ("Hcont" $! mr with "Hsie Hcnt Hpc [%] HopS Hfsb Hlk Hslot").
    exact Hcs.
  Qed.

  (* THE SET-FORGETTING CONTRACT, derived from the general one at
     [cr = false].  Every existing caller threads [log_op] and neither
     knows nor cares which blocks this op has logged, so this is the form
     they keep using; only a caller that wants the absorption credit --
     bfree's credited arm, for itrunc -- reaches for [wp_log_write_gen]. *)
  Lemma wp_log_write_sconf
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γd : disk_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (k : nat) (pidv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) (u : nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64)
      (K : nat) (b : bool) (lks : gset string)
    : wp_log_write_sconf_body bn γ γfs γd cov logstart dev k pidv bno
                              bs bsl bsd d u m n eb p K b lks.
  Proof.
    cbv beta delta [wp_log_write_sconf_body].
    intros pcE ret_tgt HK Hnoff Hk Ha0 Hcovbno Hnotlog Hno.
    iIntros "Hcg Hcnt #Htext Hpc #Hbio #Hlctx Hbslot Hop Hfsb Hheld Hcont".
    rewrite /log_op. iDestruct "Hop" as (Sb) "Hop".
    iApply (wp_log_write_gen bn γ γfs γd cov logstart dev k pidv bno
              bs bsl bsd d u false Sb m n eb p K b lks
              HK Hnoff Hk Ha0 Hcovbno Hnotlog ltac:(discriminate) Hno
              with "Hcg Hcnt Htext Hpc Hbio Hlctx Hbslot Hop Hfsb Hheld [Hcont]").
    all: try lkbelow.
    iIntros (CIDx) "%Hchain". iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hchain|].
    iIntros (mr) "Hsie Hcnt Hpc %Hcs HopS Hfsb Hlk Hslot".
    iDestruct (log_opS_op with "HopS") as "Hop".
    iApply ("Hcont" $! mr with "Hsie Hcnt Hpc [%] Hop Hfsb Hlk Hslot").
    exact Hcs.
  Qed.

End ProofLogWrite.

End LogWriteProof.
