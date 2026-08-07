(* ProofFilereadParts.v -- the pure arithmetic and the two SHARED CODE BLOCKS
   of fileread, proved once so [ProofFileread.v] is only the function's own
   control flow and its ghost steps.

   fileread's frame is 6 slots ([c.addi16sp sp,-48]):

     slot 1 = 40(sp)  saved ra          slot 4 = 16(sp)  saved s2
     slot 2 = 32(sp)  saved s0          slot 5 =  8(sp)  saved s3
     slot 3 = 24(sp)  saved s1          slot 6 =  0(sp)  unused

   THE ONE STRUCTURAL FACT ABOUT THIS FRAME.  ra/s0/s2 are spilled in the
   prologue (+0x02/+0x04/+0x06), BEFORE the [f->readable] test; s1 and s3 are
   spilled at +0x10/+0x12, AFTER it.  So the "not readable" exit -- 0x0e ->
   0xaa -> 0xae -> 0x58 -- never writes frame slots 3 and 5 and never
   restores s1/s3, whose caller values are still live in the registers.  The
   shared epilogue therefore takes slots 3 and 5 as ARBITRARY words and gets
   its [callee_saved] for s1/s3 from a PREMISE about the incoming map, exactly
   as fileclose's epilogue does for its lazily-spilled s2..s5.

   The two blocks:

   * [fr_epi] -- the epilogue at +0x58 ([c.mv a0,s2] then restore ra/s0/s2,
     trade the frame back, [c.jr ra]).  ALL FIVE exits reach it, at that one
     LITERAL pc, so it needs no pc parameters.

   * [fr_rest2] -- [c.ldsp s1,24(sp); c.ldsp s3,8(sp)], which gcc emitted
     FIVE times (+0x54 falling into the epilogue, and +0x6c / +0x98 / +0xb4 /
     +0xbe each followed by a [c.j] to +0x58).  One lemma over the block's
     three pcs as LITERAL parameters, per the recipe in
     claude-notes/durable-notes.md -- an [instr] fact whose address has to be
     CONVERTED to match makes every [iApply] reduce a [Z_to_bv] over a kernel
     address.  The four [c.j]s stay at their call sites (one instruction
     each), where the alignment side condition is discharged AFTER rewriting
     the target equation.

   Both are hart-generic ([CID0] a binder): every exit runs after a call that
   may have parked and resumed the thread on another hart. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CodeFileread.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Set Printing Depth 40.

Notation FR := KernelSyms.fileread (only parsing).

(* ---- the frame arithmetic, once per slot the blocks touch ---- *)
Lemma fr_frm1 (X : mword 64) :          (* 40(sp) : saved ra *)
  add_vec (pa_stk X 6) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fr_frm2 (X : mword 64) :          (* 32(sp) : saved s0 *)
  add_vec (pa_stk X 6) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fr_frm3 (X : mword 64) :          (* 24(sp) : saved s1 *)
  add_vec (pa_stk X 6) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fr_frm4 (X : mword 64) :          (* 16(sp) : saved s2 *)
  add_vec (pa_stk X 6) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fr_frm5 (X : mword 64) :          (*  8(sp) : saved s3 *)
  add_vec (pa_stk X 6) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof.
  unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fr_frame_back (K : nat) : (6 <= K)%nat -> ((K - 6) + 6)%nat = K.
Proof. lia. Qed.

(* ---------------------------------------------------------------------- *)
(*  PURE VALUE FACTS                                                       *)
(* ---------------------------------------------------------------------- *)

(* the five [c.li] immediates the dispatch uses, as literals *)
Lemma fr_li1 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fr_li2 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))
  = (mword_of_int 2 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fr_li3 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))
  = (mword_of_int 3 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fr_li9 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 9 : mword 6)))
  = (mword_of_int 9 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fr_lim1 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [mword_of_int] arithmetic, at both widths, with NO range premise: both
   sides are a [bv_wrap] of the same integer. *)
Lemma fr_addv64_moi (a b : Z) :
  add_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64)
  = (mword_of_int (a + b) : mword 64).
Proof.
  apply bv_eq. rewrite add_vec64_unsigned !moi64_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r. reflexivity.
Qed.

Lemma fr_addv32_moi (v : mword 32) (t : Z) :
  add_vec v (mword_of_int t : mword 32)
  = (mword_of_int (bv_unsigned v + t) : mword 32).
Proof.
  apply bv_eq.
  rewrite (add_vec_unsigned v (mword_of_int t : mword 32)).
  rewrite !moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite bv_wrap_add_idemp_r. reflexivity.
Qed.

(* a non-negative 64-bit literal reads back as itself, signed *)
Lemma fr_sint64_moi (z : Z) : (0 <= z < 2 ^ 63)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned (bvw64_small z ltac:(change (2^64)%Z with (2*2^63)%Z; lia)).
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

(* [blez] on the value readi returned *)
Lemma fr_blez_m1 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (-1) : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fr_blez_zero :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int 0 : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fr_blez_pos (z : Z) : (1 <= z < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int z : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zKzJ_s. rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (fr_sint64_moi z ltac:(lia)). lia.
Qed.

(* ---- the 32-bit type/field compares, read at 64 bits ----
   [lw]/[c.lw] sign-extend, and sign extension is INJECTIVE ([trunc32] is a
   left inverse), so a [beq]/[bne] against a small literal is exactly the
   32-bit comparison of the field. *)
Lemma fr_sext_moi32 (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = (mword_of_int z : mword 64).
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bvw64_small.
  change (2^64)%Z with 18446744073709551616%Z.
  change (2^31)%Z with 2147483648%Z in Hz. lia.
Qed.

Lemma fr_ty_eqz (w : mword 32) (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  eq_vec (sign_extend' 64 w : mword 64) (mword_of_int z : mword 64)
  = eq_vec w (mword_of_int z : mword 32).
Proof.
  intro Hz.
  destruct (eq_vec w (mword_of_int z : mword 32)) eqn:Hw.
  - apply eq_vec_true_iff in Hw. rewrite Hw.
    apply eq_vec_true_iff. exact (fr_sext_moi32 z Hz).
  - apply eq_vec_false_iff. intro Hc.
    apply (f_equal trunc32) in Hc.
    rewrite trunc32_sext trunc32_mword_of_int in Hc.
    apply eq_vec_false_iff in Hw. exact (Hw Hc).
Qed.

Lemma fr_ty_neqz (w : mword 32) (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  neq_vec (sign_extend' 64 w : mword 64) (mword_of_int z : mword 64)
  = neq_vec w (mword_of_int z : mword 32).
Proof.
  intro Hz. unfold neq_vec. by rewrite (fr_ty_eqz w z Hz).
Qed.

(* ---- the OFFSET, as the [c.lw] at +0x36 delivers it ---- *)
Lemma fr_off_reg (v : mword 32) : (bv_unsigned v < 2 ^ 31)%Z ->
  (sign_extend' 64 v : mword 64) = (mword_of_int (bv_unsigned v) : mword 64).
Proof.
  intro Hv. rewrite sext32_64_moi. f_equal.
  unfold bv_signed. apply bv_swrap_small.
  pose proof (bv_unsigned_in_range _ v) as [H0 _].
  assert (Hhm : bv_half_modulus 32 = 2^31) by reflexivity. rewrite Hhm. lia.
Qed.

(* ---- [c.addw a5,a5,a0] : the advanced offset ---- *)
Lemma fr_addw_val (v : mword 32) (t : Z) :
  sign_extend' 64 (add_vec (subrange_vec_dec (sign_extend' 64 v : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int t : mword 64) 31 0 : mword 32))
  = (sign_extend' 64 (mword_of_int (bv_unsigned v + t) : mword 32) : mword 64).
Proof.
  rewrite <- !trunc32_subrange.
  rewrite trunc32_sext trunc32_mword_of_int.
  by rewrite fr_addv32_moi.
Qed.

Lemma fr_addw_store (v : mword 32) (t : Z) :
  trunc32 (sign_extend' 64 (add_vec (subrange_vec_dec (sign_extend' 64 v : mword 64) 31 0 : mword 32)
                                    (subrange_vec_dec (mword_of_int t : mword 64) 31 0 : mword 32)))
  = (mword_of_int (bv_unsigned v + t) : mword 32).
Proof. rewrite fr_addw_val. apply trunc32_sext. Qed.

(* ---- the MAJOR, sign-extended by [lh] then zero-extended by slli/srli ---- *)
Lemma fr_sext16_moi (w : mword 16) :
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_signed w).
Proof.
  apply bv_eq.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold mword_of_int, SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  reflexivity.
Qed.

Lemma fr_sext16_unsigned (w : mword 16) :
  bv_unsigned (sign_extend' 64 w : mword 64) = bv_wrap 64 (bv_signed w).
Proof. rewrite fr_sext16_moi. apply moi64_unsigned. Qed.

(* the low sixteen bits survive the sign extension -- which is exactly what
   [slli 48; srli 48] reads back *)
Lemma fr_sext16_low (w : mword 16) :
  bv_wrap 16 (bv_unsigned (sign_extend' 64 w : mword 64)) = bv_unsigned w.
Proof.
  rewrite fr_sext16_unsigned.
  rewrite (bv_wrap_bv_wrap 16 64 _ ltac:(lia)).
  unfold bv_signed. rewrite bv_wrap_swrap.
  apply bv_wrap_bv_unsigned.
Qed.

(* a major in range is non-negative, so the sign extension IS the literal *)
Lemma fr_sext16_small (w : mword 16) : (bv_unsigned w < 2 ^ 15)%Z ->
  (sign_extend' 64 w : mword 64) = (mword_of_int (bv_unsigned w) : mword 64).
Proof.
  intro Hw. rewrite fr_sext16_moi. f_equal.
  unfold bv_signed. apply bv_swrap_small.
  pose proof (bv_unsigned_in_range _ w) as [H0 _].
  assert (Hhm : bv_half_modulus 16 = 2^15) by reflexivity. rewrite Hhm. lia.
Qed.

(* [slli a5,a5,4] on a small literal: the byte offset into [devsw]. *)
Lemma fr_slli4_moi (r : Z) : (0 <= r)%Z -> (r < 16)%Z ->
  shift_bits_left (mword_of_int r : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (16 * r) : mword 64).
Proof.
  intros H0 H1.
  assert (Hs : shift_bits_left (mword_of_int r : mword 64)
                 (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
               = shiftl (mword_of_int r : mword 64) 4).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftl, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H4 : bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 64)
                 (MachineWord.MachineWord.Z_idx 4)) = 4).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H4 !moi64_unsigned.
  rewrite (bvw64_small r ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2 ^ 4)%Z with 16%Z.
  replace (r * 16)%Z with (16 * r)%Z by lia. reflexivity.
Qed.

(* [slli 48; srli 48] -- the C compiler's zero extension of a [short]. *)
Lemma fr_zext16 (w : mword 16) :
  shift_bits_right
    (shift_bits_left (sign_extend' 64 w : mword 64)
       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (bv_unsigned w) : mword 64).
Proof.
  set (x := (sign_extend' 64 w : mword 64)).
  assert (Hl : shift_bits_left x
                 (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
               = shiftl x 48).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : forall y : mword 64,
                 shift_bits_right y
                   (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                 = shiftr y 48).
  { intro y. unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned bv_shiftl_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H48 : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx 48)) = 48).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H48.
  (* the low sixteen bits of [x], shifted up and back down *)
  pose proof (fr_sext16_low w) as Hlow. fold x in Hlow.
  pose proof (bv_unsigned_in_range _ x) as Hxr.
  unfold bv_modulus in Hxr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))%Z
    with 18446744073709551616%Z in Hxr.
  pose proof (bv_unsigned_in_range _ w) as Hwr.
  unfold bv_modulus in Hwr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in Hwr.
  unfold bv_wrap, bv_modulus in Hlow.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in Hlow.
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2 ^ 48)%Z with 281474976710656%Z.
  (* [x * 2^48 mod 2^64 = (x mod 2^16) * 2^48] *)
  assert (Hmod : bv_wrap (MachineWord.MachineWord.Z_idx 64)
                   (bv_unsigned x * 281474976710656)
                 = bv_unsigned w * 281474976710656).
  { unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64))%Z
      with 18446744073709551616%Z.
    set (q := (bv_unsigned x / 65536)%Z).
    set (r := (bv_unsigned x mod 65536)%Z).
    assert (Hqr : bv_unsigned x = (65536 * q + r)%Z)
      by (unfold q, r; apply Z.div_mod; lia).
    assert (Hrw : r = bv_unsigned w) by (unfold r; exact Hlow).
    rewrite Hqr.
    replace ((65536 * q + r) * 281474976710656)%Z
      with (r * 281474976710656 + q * 18446744073709551616)%Z by lia.
    rewrite Z.mod_add; [| lia].
    rewrite Hrw. apply Z.mod_small. lia. }
  rewrite Hmod.
  rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 48)%Z with 281474976710656%Z.
  rewrite Z.div_mul; [| lia].
  rewrite moi64_unsigned. symmetry. apply bvw64_small. lia.
Qed.

Section ProofFilereadParts.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  (* =================================================================== *)
  (*  +0x58 .. +0x62 -- THE EPILOGUE.  Every exit reaches it.             *)
  (* =================================================================== *)
  Lemma fr_epi `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s20 : mword 64) (rv : mword 64) (w3 w5 w6 : mword 64)
      (p : mword 64) (b : bool) :
    (6 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    Mt !!! Regidx Rs2 = rv ->
    (* everything but sp/s0/s2 already agrees with the entry map.  s1 and s3
       are in here, and that is the whole point: the [!readable] exit never
       spilled them. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 6)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FR + 0x58) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) w3 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs20 Hmtsp Hmts2 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hcont".
    iPoseProof (fri_58 with "Htext") as "Hi58".
    iPoseProof (fri_5a with "Htext") as "Hi5a".
    iPoseProof (fri_5c with "Htext") as "Hi5c".
    iPoseProof (fri_5e with "Htext") as "Hi5e".
    iPoseProof (fri_60 with "Htext") as "Hi60".
    iPoseProof (fri_62 with "Htext") as "Hi62".
    (* ---- +0x58: c.mv a0,s2 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (FR + 0x58)) Ra0 Rs2 Mt (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs2))]> Mt).
    assert (HT0a0 : T0 !!! Regidx Ra0 = rv).
    { rewrite /T0 upd_eq. unfold regval_into_reg. rewrite Hmts2.
      apply add_vec_zero_l. }
    assert (HT0sp : T0 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T0 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp5a : add_vec_int (mword_of_int (FR + 0x58) : mword 64) 2
                    = mword_of_int (FR + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* ---- +0x5a: c.ldsp ra,40(sp) ---- *)
    assert (Hpa1 : add_vec (T0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite HT0sp; apply fr_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (FR + 0x5a)) (mword_of_int 5 : mword 6) Rra
              T0 (K - 6)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a Hb1 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> T0).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T1 upd_ne; [exact HT0sp | vm_compute; discriminate]).
    assert (Hpp5c : add_vec_int (mword_of_int (FR + 0x5a) : mword 64) 2
                    = mword_of_int (FR + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* ---- +0x5c: c.ldsp s0,32(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite HT1sp; apply fr_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (FR + 0x5c)) (mword_of_int 4 : mword 6) Rs0
              T1 (K - 6)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c Hb2 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp5e : add_vec_int (mword_of_int (FR + 0x5c) : mword 64) 2
                    = mword_of_int (FR + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* ---- +0x5e: c.ldsp s2,16(sp) ---- *)
    assert (Hpa4 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                   = pa_stk sp0 4) by (rewrite HT2sp; apply fr_frm4).
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (FR + 0x5e)) (mword_of_int 2 : mword 6) Rs2
              T2 (K - 6)%nat s20 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e Hb4 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (T3 := <[Regidx Rs2 := regval_into_reg s20]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp60 : add_vec_int (mword_of_int (FR + 0x5e) : mword 64) 2
                    = mword_of_int (FR + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* ---- +0x60: c.addi16sp sp,48 -- the frame goes back ---- *)
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = sp0)
      by (rewrite HT3sp; apply stk_pop_48).
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6)
      by (rewrite Hwv; exact HT3sp).
    iAssert (stack_own sp0 6) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (FR + 0x60)) (mword_of_int 3 : mword 6)
              T3 (K - 6)%nat 6 b Hpop with "Hcg Hpc Hi60 Hframe [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((K - 6) + 6)%nat = K) by exact (fr_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T3 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T3 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> T3) with T4.
    assert (Hpp62 : add_vec_int (mword_of_int (FR + 0x60) : mword 64) 2
                    = mword_of_int (FR + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* ---- +0x62: c.jr ra ---- *)
    assert (HT4ra : T4 !!! Regidx Rra = ra0).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (FR + 0x62)) Rra T4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi62 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HT4ra) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs2 -> r <> Rra -> r <> Ra0 ->
                      T4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns2 Nra Na0.
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      rewrite /T0 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns2). }
    assert (HT4a0 : T4 !!! Regidx Ra0 = rv).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [| vm_compute; discriminate].
      exact HT0a0. }
    split; [| exact HT4a0].
    rewrite /callee_saved. split_and!.
    5-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    3: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T4 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs20. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  [c.ldsp s1,24(sp); c.ldsp s3,8(sp)] -- five copies, one lemma over  *)
  (*  the block's pcs as LITERALS.                                        *)
  (* =================================================================== *)
  Lemma fr_rest2 `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (Mt : regfile) (K : nat) (sp0 : mword 64) (v1 v3 : mword 64)
      (za zb zc : Z) (p : mword 64) (b : bool) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    sie_cap_gpr Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")),
             sp, Regidx Rs1, false, 8)) -∗
    instr (mword_of_int zb : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
             sp, Regidx Rs3, false, 8)) -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) v1 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) v3 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx csp_rs1 = pa_stk sp0 6
          /\ Mr !!! Regidx Rs1 = v1 /\ Mr !!! Regidx Rs3 = v3
          /\ (forall r : mword 5, is_cs_idx r = true ->
                r <> Rs1 -> r <> Rs3 -> Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr Mr K b p -∗
        pc_is (mword_of_int zc : mword 64) -∗
        word_pointsto (pa_stk sp0 3) (DfracOwn 1) v1 -∗
        word_pointsto (pa_stk sp0 5) (DfracOwn 1) v3 -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hmtsp Hab Hbc.
    iIntros "Hcg Hpc Hia Hib Hb3 Hb5 Hcont".
    (* ---- s1 ---- *)
    assert (Hpa3 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite Hmtsp; apply fr_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int za) (mword_of_int 3 : mword 6) Rs1
              Mt K v1 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia Hb3 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (U1 := <[Regidx Rs1 := regval_into_reg v1]> Mt).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /U1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    iEval (rewrite Hab) in "Hpc".
    (* ---- s3 ---- *)
    assert (Hpa5 : add_vec (U1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HU1sp; apply fr_frm5).
    iEval (rewrite -Hpa5) in "Hb5".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int zb) (mword_of_int 1 : mword 6) Rs3
              U1 K v3 b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib Hb5 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
    set (U2 := <[Regidx Rs3 := regval_into_reg v3]> U1).
    iEval (rewrite Hbc) in "Hpc".
    iSpecialize ("Hcont" $! CID2 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! U2 with "[%] Hcg Hpc Hb3 Hb5").
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 6)
      by (rewrite /U2 upd_ne; [exact HU1sp | vm_compute; discriminate]).
    split; [exact HU2sp|].
    split.
    { rewrite /U2 upd_ne; [| vm_compute; discriminate].
      rewrite /U1; apply upd_eq. }
    split; [rewrite /U2; apply upd_eq|].
    intros r Hr N1 N3.
    rewrite /U2 upd_ne; [| regne].
    rewrite /U1 upd_ne; [reflexivity | regne].
  Qed.

  (* =================================================================== *)
  (*  [c.li a5,-1; c.mv s2,a5; c.ldsp s1; c.ldsp s3; c.j +0x58] -- the     *)
  (*  FD_DEVICE arm's TWO -1 exits (+0xb0 the out-of-range major, +0xba    *)
  (*  the null devsw slot).  Same block, so one lemma over its five pcs.   *)
  (* =================================================================== *)
  Lemma fr_m1j `{GEN : GenId} `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (Mt : regfile) (K : nat) (sp0 : mword 64) (v1 v3 : mword 64)
      (za zb zc zd ze : Z) (jimm : mword 21) (p : mword 64) (b : bool) :
    Mt !!! Regidx csp_rs1 = pa_stk sp0 6 ->
    add_vec_int (mword_of_int za : mword 64) 2 = mword_of_int zb ->
    add_vec_int (mword_of_int zb : mword 64) 2 = mword_of_int zc ->
    add_vec_int (mword_of_int zc : mword 64) 2 = mword_of_int zd ->
    add_vec_int (mword_of_int zd : mword 64) 2 = mword_of_int ze ->
    add_vec (mword_of_int ze : mword 64) (sign_extend' 64 jimm)
      = mword_of_int (FR + 0x58) ->
    sie_cap_gpr Mt K b p -∗
    pc_is (mword_of_int za : mword 64) -∗
    instr (mword_of_int za : mword 64) true
      (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx Ra5, ADDI)) -∗
    instr (mword_of_int zb : mword 64) true
      (RTYPE (Regidx Ra5, zreg, Regidx Rs2, ADD)) -∗
    instr (mword_of_int zc : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")),
             sp, Regidx Rs1, false, 8)) -∗
    instr (mword_of_int zd : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")),
             sp, Regidx Rs3, false, 8)) -∗
    instr (mword_of_int ze : mword 64) true (JAL (jimm, zreg)) -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) v1 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) v3 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mr : regfile,
        ⌜ Mr !!! Regidx csp_rs1 = pa_stk sp0 6
          /\ Mr !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)
          /\ Mr !!! Regidx Rs1 = v1 /\ Mr !!! Regidx Rs3 = v3
          /\ (forall r : mword 5, is_cs_idx r = true ->
                r <> Rs1 -> r <> Rs2 -> r <> Rs3 -> Mr !!! Regidx r = Mt !!! Regidx r) ⌝ -∗
        sie_cap_gpr Mr K b p -∗
        pc_is (mword_of_int (FR + 0x58) : mword 64) -∗
        word_pointsto (pa_stk sp0 3) (DfracOwn 1) v1 -∗
        word_pointsto (pa_stk sp0 5) (DfracOwn 1) v3 -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hmtsp Hab Hbc Hcd Hde Hjt.
    iIntros "Hcg Hpc Hia Hib Hic Hid Hie Hb3 Hb5 Hcont".
    (* c.li a5,-1 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int za) Ra5 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) Mt K b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
              with "Hcg Hpc Hia [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (W1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mt).
    iEval (rewrite Hab) in "Hpc".
    (* c.mv s2,a5 *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int zb) Rs2 Ra5 W1 K b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib [-]").
    iIntros (CID2 Hs2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (W2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (W1 !!! Regidx Ra5))]> W1).
    assert (HW2s2 : W2 !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
    { rewrite /W2 upd_eq. unfold regval_into_reg. rewrite /W1 upd_eq.
      apply add_vec_zero_l. }
    assert (HW2sp : W2 !!! Regidx csp_rs1 = pa_stk sp0 6).
    { rewrite /W2 upd_ne; [| vm_compute; discriminate].
      rewrite /W1 upd_ne; [exact Hmtsp | vm_compute; discriminate]. }
    iEval (rewrite Hbc) in "Hpc".
    (* the s1/s3 restore *)
    iApply (fr_rest2 (CID0 := CID2) Φ W2 K sp0 v1 v3 zc zd ze p b HW2sp Hcd Hde
              with "Hcg Hpc Hic Hid Hb3 Hb5 [-]").
    iIntros (CID3 Hs3 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
    destruct Hmr as (Hmrsp & Hmrs1 & Hmrs3 & Hmrthr).
    (* the c.j into the epilogue: the alignment side condition is about the
       TARGET, so the equation is rewritten BEFORE [vm_compute]. *)
    iApply (wp_cj_s_sconf Φ (mword_of_int ze) jimm Mr K b
              ltac:(rewrite Hjt; vm_compute; reflexivity)
              with "Hcg Hpc Hie [-]").
    iIntros (CID4 Hs4). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Hjt) in "Hpc".
    iSpecialize ("Hcont" $! CID4 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! Mr with "[%] Hcg Hpc Hb3 Hb5").
    split; [exact Hmrsp|].
    split.
    { rewrite (Hmrthr Rs2 ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact HW2s2. }
    split; [exact Hmrs1|]. split; [exact Hmrs3|].
    intros r Hr N1 N2 N3.
    rewrite (Hmrthr r Hr N1 N3).
    rewrite /W2 upd_ne; [| regne].
    rewrite /W1 upd_ne; [reflexivity | regne].
  Qed.

End ProofFilereadParts.
