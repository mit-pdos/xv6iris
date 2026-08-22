(* ProofFilecloseParts.v -- the blocks fileclose's five exits SHARE, proved
   once here so [ProofFileclose.v] is only the function's own control flow.

   fileclose's frame is 8 slots ([addi sp,sp,-64]):

     slot 1 = 56(sp)  saved ra          slot 5 = 24(sp)  saved s3
     slot 2 = 48(sp)  saved s0          slot 6 = 16(sp)  saved s4
     slot 3 = 40(sp)  saved s1          slot 7 =  8(sp)  saved s5
     slot 4 = 32(sp)  saved s2          slot 8 =  0(sp)  unused

   and the two shared blocks are:

   * [fc_epi] -- the epilogue at +0x8e: restore ra/s0/s1, trade the frame
     back, [ret].  ALL FIVE exits reach it.  Note it restores only THREE
     registers: [s2..s5] are saved LAZILY, on the slow path alone (+0x26),
     so the fast path never touches slots 4..7 and the epilogue must not
     assume anything about them.  That is why they arrive here as arbitrary
     words and why [callee_saved] is discharged from a PREMISE about the
     incoming map rather than from the loads.

   * [fc_restore4] -- [ld s2..s5; j +0x8e], which gcc emitted THREE times
     (+0x64 for the FD_NONE arm, +0xa0 after pipeclose, +0xb8 after end_op).
     One lemma over the block's five pcs as LITERALS, per the recipe in
     claude-notes/durable-notes.md: an [instr] fact whose address has to be
     CONVERTED to match makes every [iApply] reduce a [Z_to_bv] over a kernel
     address, so the pcs are parameters and their successor equations are
     premises, discharged once at each call site.

   Both are hart-generic ([CID0] a binder, a fresh universally-quantified
   hart per instruction), because they run after a call returns and the call
   may have resumed the thread anywhere. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import CodeFileclose.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Notation FC := KernelSyms.fileclose (only parsing).

(* ---- the frame arithmetic, once per slot the blocks touch ---- *)
Lemma fc_frm1 (X : mword 64) :          (* 56(sp) : saved ra *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm2 (X : mword 64) :          (* 48(sp) : saved s0 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm3 (X : mword 64) :          (* 40(sp) : saved s1 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm4 (X : mword 64) :          (* 32(sp) : saved s2 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm5 (X : mword 64) :          (* 24(sp) : saved s3 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm6 (X : mword 64) :          (* 16(sp) : saved s4 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frm7 (X : mword 64) :          (*  8(sp) : saved s5 *)
  add_vec (pa_stk X 8) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fc_frame_back (K : nat) : (8 <= K)%nat -> ((K - 8) + 8)%nat = K.
Proof. lia. Qed.

(* [c.addiw a5,a5,-1] on a count -- the [f->ref--] direction of
   [VcGen.moi32_storeval_succ].  The addend is [mword_of_int 63 : mword 6],
   i.e. -1 in the compressed instruction's 6-bit signed immediate, which
   widens to the all-ones 32-bit word, so the 32-bit add wraps and the result
   is [z - 1] exactly when [z >= 1].

   Three forms, because the proof consumes all three: the 32-bit result the
   [c.sw] stores, the 64-bit register value the [bgtz] then tests, and the
   [trunc32] the store leaf hands back. *)
Lemma fc_pred_sub (z : Z) : (1 <= z)%Z -> (z < 2 ^ 31)%Z ->
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

Lemma fc_storeval_pred (z : Z) : (1 <= z)%Z -> (z < 2 ^ 31)%Z ->
  trunc32 (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 (mword_of_int z : mword 32))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
  = (mword_of_int (z - 1) : mword 32).
Proof.
  intros H1 H2. rewrite trunc32_sext. exact (fc_pred_sub z H1 H2).
Qed.

(* the 64-bit value the [bgtz] at +0x22 tests *)
Lemma fc_pred_reg (z : Z) : (1 <= z)%Z -> (z < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 (mword_of_int z : mword 32))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
  = sign_extend' 64 (mword_of_int (z - 1) : mword 32).
Proof. intros H1 H2. by rewrite (fc_pred_sub z H1 H2). Qed.

(* ...and what it decides: the count reaching zero is the ONLY way to fall
   through to the last-reference arm. *)
Lemma fc_pred_gtz (z : Z) : (2 <= z)%Z -> (z < 2 ^ 31)%Z ->
  zopz0zI_s (zero_reg : mword 64)
    (sign_extend' 64 (mword_of_int (z - 1) : mword 32)) = true.
Proof.
  intros H2 Hb. unfold zopz0zI_s. apply Z.ltb_lt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite sint64_moi32; lia.
Qed.

Lemma fc_pred_ngtz :
  zopz0zI_s (zero_reg : mword 64)
    (sign_extend' 64 (mword_of_int (1 - 1) : mword 32)) = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- the type dispatch at +0x54/+0x56 ----
   [c.li a5,1] then [beq s2,a5]: s2 holds the SIGN-EXTENDED [ff.type], so the
   comparison is at 64 bits and the arm is FD_PIPE's exactly when the 32-bit
   field is.  Sign extension is injective, and [trunc32] is its inverse. *)
Lemma fc_li1_val :
  add_vec (zero_reg : mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fc_ty_eq1 (w : mword 32) :
  eq_vec (sign_extend' 64 w) (mword_of_int 1 : mword 64)
  = eq_vec w (mword_of_int 1 : mword 32).
Proof.
  destruct (eq_vec w (mword_of_int 1 : mword 32)) eqn:Hw.
  - apply eq_vec_true_iff in Hw. rewrite Hw. vm_compute. reflexivity.
  - apply eq_vec_false_iff. intro Hc.
    apply (f_equal trunc32) in Hc.
    rewrite trunc32_sext trunc32_mword_of_int in Hc.
    apply eq_vec_false_iff in Hw. exact (Hw Hc).
Qed.

(* ---- the INODE test at +0x5a/+0x5e/+0x60 ----
   [addiw a5,s2,-2 ; c.li a4,1 ; bgeu a4,a5] is "type - 2 <=u 1", i.e. ONE
   unsigned comparison for the two-value range {FD_INODE, FD_DEVICE}.  It has
   to hold for an ARBITRARY 32-bit type field, not just the four enum values:
   the [addiw] wraps, so a field at or above 2^31 sign-extends NEGATIVE and
   must still land on the right side of the comparison.  The route that keeps
   that honest is to go through the 32-bit result, where the wrap is just
   [+ (2^32 - 2)], and to bound the sign extension separately. *)
Lemma fc_addiw_m2 (w : mword 32) :
  subrange_vec_dec (add_vec (sign_extend' 64 w)
       (sign_extend' 64 (mword_of_int 4094 : mword 12))) 31 0
  = add_vec w (mword_of_int (2 ^ 32 - 2) : mword 32).
Proof.
  rewrite <- trunc32_subrange. rewrite trunc32_add. rewrite trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (mword_of_int 4094 : mword 12))
               = (mword_of_int (2 ^ 32 - 2) : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  by rewrite HK.
Qed.

Lemma fc_addm2_val (w : mword 32) (z : Z) : (0 <= z < 2)%Z ->
  add_vec w (mword_of_int (2 ^ 32 - 2) : mword 32) = (mword_of_int z : mword 32) ->
  w = (mword_of_int (z + 2) : mword 32).
Proof.
  intros Hz Heq.
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  apply (f_equal bv_unsigned) in Heq.
  revert Heq.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  rewrite (moi32_small (2 ^ 32 - 2) ltac:(lia)).
  rewrite (moi32_small z ltac:(lia)).
  unfold bv_wrap, bv_modulus. change (Z.of_N (MachineWord.Z_idx 32)) with 32%Z.
  intro Heq.
  pose proof (bv_unsigned_in_range _ w) as Hwr.
  unfold bv_modulus in Hwr. change (Z.of_N (MachineWord.Z_idx 32)) with 32%Z in Hwr.
  apply bv_eq. rewrite (moi32_small (z + 2) ltac:(lia)).
  rewrite E32 in Heq, Hwr.
  (* [uint w + 2^32 - 2 = z] mod 2^32, with both sides in range *)
  destruct (Z.le_gt_cases 2 (bv_unsigned w)) as [Hge|Hlt].
  - rewrite (_ : (bv_unsigned w + (4294967296 - 2))%Z
                 = (bv_unsigned w - 2 + 1 * 4294967296)%Z) in Heq; [|lia].
    rewrite Z.mod_add in Heq; [|lia].
    rewrite Z.mod_small in Heq; lia.
  - rewrite Z.mod_small in Heq; lia.
Qed.

Lemma fc_sext_small (X : mword 32) :
  (uint (sign_extend' 64 X) <= 1)%Z ->
  X = (mword_of_int 0 : mword 32) \/ X = (mword_of_int 1 : mword 32).
Proof.
  intro Hle.
  rewrite (uint_unsigned (sign_extend' 64 X : mword 64)) in Hle.
  pose proof (bv_unsigned_in_range _ (sign_extend' 64 X : mword 64)) as Hr.
  unfold bv_modulus in Hr.
  assert (Hv : bv_unsigned (sign_extend' 64 X : mword 64) = 0%Z
               \/ bv_unsigned (sign_extend' 64 X : mword 64) = 1%Z)
    by (clear -Hle Hr; lia).
  assert (Hx : (sign_extend' 64 X : mword 64) = (mword_of_int 0 : mword 64)
               \/ (sign_extend' 64 X : mword 64) = (mword_of_int 1 : mword 64)).
  { destruct Hv as [Hv|Hv]; [left|right]; apply bv_eq; rewrite Hv;
      by vm_compute. }
  destruct Hx as [Hx|Hx]; [left|right];
    apply (f_equal trunc32) in Hx; rewrite trunc32_sext in Hx;
    rewrite Hx; by rewrite trunc32_mword_of_int.
Qed.

Lemma fc_ty_inode_iff (w : mword 32) :
  zopz0zKzJ_u (mword_of_int 1 : mword 64)
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 w)
                (sign_extend' 64 (mword_of_int 4094 : mword 12))) 31 0))
  = true
  <-> (w = (mword_of_int 2 : mword 32) \/ w = (mword_of_int 3 : mword 32)).
Proof.
  rewrite fc_addiw_m2. split.
  - unfold zopz0zKzJ_u. rewrite Z.geb_le. intro Hle.
    assert (Hu1 : uint (mword_of_int 1 : mword 64) = 1%Z) by (by vm_compute).
    rewrite Hu1 in Hle.
    destruct (fc_sext_small _ Hle) as [Hx|Hx].
    + left. exact (fc_addm2_val w 0 ltac:(lia) Hx).
    + right. exact (fc_addm2_val w 1 ltac:(lia) Hx).
  - intros [-> | ->]; by vm_compute.
Qed.

(* ---- pipeclose's [writable] argument ----
   a1 is [ff.writable] zero-extended, and pipeclose's contract reads the END
   off exactly its being nonzero -- which is [FileInv.fc_wbool]. *)
Lemma fc_wbool_arg (v : mword 8) :
  eq_vec (add_vec (zero_reg : mword 64) (zero_extend' 64 v)) (zero_reg : mword 64)
  = negb (negb (eq_vec v (mword_of_int 0 : mword 8))).
Proof.
  rewrite negb_involutive. rewrite add_vec_zero_l.
  assert (Hinj : eq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64) = true
                 -> v = (mword_of_int 0 : mword 8)).
  { intro Hc. apply eq_vec_true_iff in Hc.
    apply (f_equal bv_unsigned) in Hc.
    cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
         to_word get_word MachineWord.MachineWord.zero_extend] in Hc.
    rewrite bv_zero_extend_unsigned in Hc.
    assert (Hz : bv_unsigned (zero_reg : mword 64) = 0%Z) by (by vm_compute).
    rewrite Hz in Hc. apply bv_eq. rewrite Hc.
    all: by vm_compute. }
  destruct (eq_vec (zero_extend' 64 v : mword 64) (zero_reg : mword 64)) eqn:HL;
    destruct (eq_vec v (mword_of_int 0 : mword 8)) eqn:HR;
    [ reflexivity
    | exfalso; apply eq_vec_false_iff in HR; exact (HR (Hinj eq_refl))
    | exfalso; apply eq_vec_true_iff in HR; rewrite HR in HL;
      vm_compute in HL; discriminate
    | reflexivity ].
Qed.

Section ProofFilecloseParts.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* =================================================================== *)
  (*  +0x8e .. +0x96 -- THE EPILOGUE.  Every exit reaches it.             *)
  (* =================================================================== *)
  Lemma fc_epi `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 : mword 64) (w4 w5 w6 w7 w8 : mword 64)
      (p : mword 64) (b : bool) :
    (8 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (* everything but sp/s0/s1 already agrees with the entry map: the three
       the epilogue restores are the only ones it may have lost. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 8)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FC + 0x8e) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hmtsp Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hcont".
    (* ---- +0x8e: c.ldsp ra,56(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite Hmtsp; apply fc_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (FC + 0x8e)) (mword_of_int 7 : mword 6) Rra
              Mt (K - 8)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (fci_8e with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp90 : add_vec_int (mword_of_int (FC + 0x8e) : mword 64) 2
                    = mword_of_int (FC + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp90) in "Hpc".
    (* ---- +0x90: c.ldsp s0,48(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite HT1sp; apply fc_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (FC + 0x90)) (mword_of_int 6 : mword 6) Rs0
              T1 (K - 8)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (fci_90 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp92 : add_vec_int (mword_of_int (FC + 0x90) : mword 64) 2
                    = mword_of_int (FC + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp92) in "Hpc".
    (* ---- +0x92: c.ldsp s1,40(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite HT2sp; apply fc_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (FC + 0x92)) (mword_of_int 5 : mword 6) Rs1
              T2 (K - 8)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb3").
    { iApply (fci_92 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp94 : add_vec_int (mword_of_int (FC + 0x92) : mword 64) 2
                    = mword_of_int (FC + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* ---- +0x94: c.addi16sp sp,64 -- the frame goes back ---- *)
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = sp0)
      by (rewrite HT3sp; apply stk_pop_64).
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8)
      by (rewrite Hwv; exact HT3sp).
    iAssert (stack_own (KTR := KT1) sp0 8) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8]" as "Hframe".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (FC + 0x94)) (mword_of_int 4 : mword 6)
              T3 (K - 8)%nat 8 b Hpop with "Hcg Hpc [] Hframe").
    { iApply (fci_94 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hnk : ((K - 8) + 8)%nat = K) by exact (fc_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> T3) with T4.
    assert (Hpp96 : add_vec_int (mword_of_int (FC + 0x94) : mword 64) 2
                    = mword_of_int (FC + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp96) in "Hpc".
    (* ---- +0x96: c.ret ---- *)
    assert (HT4ra : T4 !!! Regidx Rra = ra0).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (FC + 0x96)) Rra T4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (fci_96 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HT4ra) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    (* callee_saved m T4 : sp and s0/s1 came back off the frame, and the
       nine the epilogue never touches came in already agreeing -- which is
       the premise, not a consequence of any load here (s2..s5 are saved
       LAZILY, so on the fast path they were never spilled at all). *)
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs1 -> r <> Rra ->
                      T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Nra.
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns1). }
    (* goals 4..13 are s2..s11, none of which this block touches; a [try]
       over all thirteen would pay for three failures of [apply Hrest] and
       cost 2 s of the file's 7. *)
    rewrite /callee_saved. split_and!.
    4-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T4 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs10. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  [ld s2,32(sp); ld s3,24(sp); ld s4,16(sp); ld s5,8(sp); j +0x8e]    *)
  (*  gcc emitted this THREE times (+0x64, +0xa0, +0xb8), so it is one    *)
  (*  lemma over the block's pcs as literals.                            *)
  (* =================================================================== *)
  Lemma fc_restore4 `{GEN : GenId} `{CID0 : CpuId}
      (Mt : regfile) (K : nat) (sp0 : mword 64)
      (v2 v3 v4 v5 : mword 64)
      (za zb zc zd ze : Z) (jimm : mword 21)
      (p : mword 64) (b : bool) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 8 ->
    (* the block's own pc chain, and where its [c.j] lands *)
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    add_vec_int (mword_of_int zc : mword 64) 2 = mword_of_int zd ->
    add_vec_int (mword_of_int zd : mword 64) 2 = mword_of_int ze ->
    add_vec (mword_of_int ze : mword 64) (sign_extend' 64 jimm)
      = mword_of_int (FC + 0x8e) ->
    sie_cap_gpr KT1 Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")),
             sp, Regidx Rs2, false, 8)) -∗
    instr (mword_of_int zb : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")),
             sp, Regidx Rs3, false, 8)) -∗
    instr (mword_of_int zc : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")),
             sp, Regidx Rs4, false, 8)) -∗
    instr (mword_of_int zd : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
             sp, Regidx Rs5, false, 8)) -∗
    instr (mword_of_int ze : mword 64) true (JAL (jimm, zreg)) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) v2 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) v3 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) v4 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) v5 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx csp_rs1 = pa_stk sp0 8
          /\ Mr !!! Regidx Rs2 = v2 /\ Mr !!! Regidx Rs3 = v3
          /\ Mr !!! Regidx Rs4 = v4 /\ Mr !!! Regidx Rs5 = v5
          /\ (forall r : mword 5, is_cs_idx r = true ->
                r <> Rs2 -> r <> Rs3 -> r <> Rs4 -> r <> Rs5 ->
                Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 Mr K b p -∗
        pc_is (mword_of_int (FC + 0x8e) : mword 64) -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) v2 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) v3 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) v4 -∗
        word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) v5 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hmtsp Hab Hbc Hcd Hde Hjt.
    iIntros "Hcg Hpc Hia Hib Hic Hid Hie Hb4 Hb5 Hb6 Hb7 Hcont".
    (* ---- s2 ---- *)
    assert (Hpa4 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk sp0 4) by (rewrite Hmtsp; apply fc_frm4).
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf (mword_of_int za) (mword_of_int 4 : mword 6) Rs2
              Mt K v2 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia Hb4").
    iIntros (CID1 Hs1) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (U1 := <[Regidx Rs2 := regval_into_reg v2]> Mt).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    iEval (rewrite Hab) in "Hpc".
    (* ---- s3 ---- *)
    assert (Hpa5 : add_vec (U1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HU1sp; apply fc_frm5).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf (mword_of_int zb) (mword_of_int 3 : mword 6) Rs3
              U1 K v3 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib Hb5").
    iIntros (CID2 Hs2) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
    set (U2 := <[Regidx Rs3 := regval_into_reg v3]> U1).
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U2 upd_ne; [exact HU1sp | vm_compute; discriminate]).
    iEval (rewrite Hbc) in "Hpc".
    (* ---- s4 ---- *)
    assert (Hpa6 : add_vec (U2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HU2sp; apply fc_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int zc) (mword_of_int 2 : mword 6) Rs4
              U2 K v4 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic Hb6").
    iIntros (CID3 Hs3) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (U3 := <[Regidx Rs4 := regval_into_reg v4]> U2).
    assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U3 upd_ne; [exact HU2sp | vm_compute; discriminate]).
    iEval (rewrite Hcd) in "Hpc".
    (* ---- s5 ---- *)
    assert (Hpa7 : add_vec (U3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 7) by (rewrite HU3sp; apply fc_frm7).
    iEval (rewrite -Hpa7) in "Hb7".
    iApply (wp_cldsp_s_sconf (mword_of_int zd) (mword_of_int 1 : mword 6) Rs5
              U3 K v5 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid Hb7").
    iIntros (CID4 Hs4) "Hcg Hpc Hb7". iEval (rewrite Hpa7) in "Hb7".
    set (U4 := <[Regidx Rs5 := regval_into_reg v5]> U3).
    iEval (rewrite Hde) in "Hpc".
    (* ---- the c.j into the epilogue ---- *)
    (* the alignment side condition is about the TARGET, which is closed
       only after [Hjt]: [vm_compute] on the open [add_vec ze jimm] does not
       come back. *)
    iApply (wp_cj_s_sconf (mword_of_int ze) jimm U4 K b
              ltac:(rewrite Hjt; vm_compute; reflexivity)
              with "Hcg Hpc Hie").
    iIntros (CID5 Hs5). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! U4 with "[%] Hcg Hpc Hb4 Hb5 Hb6 Hb7").
    assert (HU4sp : U4 !!! Regidx csp_rs1 = pa_stk sp0 8)
      by (rewrite /U4 upd_ne; [exact HU3sp | vm_compute; discriminate]).
    split; [exact HU4sp|].
    split.
    { rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1; apply upd_eq. }
    split.
    { rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3 upd_ne; [| vm_compute; discriminate].
      rewrite /U2; apply upd_eq. }
    split.
    { rewrite /U4 upd_ne; [| vm_compute; discriminate].
      rewrite /U3; apply upd_eq. }
    split; [rewrite /U4; apply upd_eq|].
    intros r Hr N2 N3 N4 N5.
    rewrite /U4 upd_ne; [| regne].
    rewrite /U3 upd_ne; [| regne].
    rewrite /U2 upd_ne; [| regne].
    rewrite /U1 upd_ne; [reflexivity | regne].
  Qed.

End ProofFilecloseParts.
