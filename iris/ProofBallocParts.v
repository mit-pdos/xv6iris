(* ProofBallocParts.v -- the pieces balloc's whole-function proof needs and
   the shared layers do not yet have.

   Two S-mode ALU leaves are missing from [WpSconfAlu.v] and both are used
   by balloc (and [sllw] also by bfree):

     [sraiw rd,rs1,shamt]  -- balloc +0x9c (b / BPB), +0xc2 and +0xcc (the
                              two halves of C's SIGNED divide of [bi] by 8)
     [sllw  rd,rs1,rs2]    -- balloc +0xbe (the mask [1 << (bi % 8)]);
                              bfree +0x26 is the same instruction

   [WpSconfSrliw.v] is the precedent for exactly this situation, and its
   header records the reason such a leaf lands in a leaf file rather than
   in [WpSconfAlu.v] / [WpMmodeShiftiop.v]: both of those sit near the
   BOTTOM of the build, so editing either invalidates the whole downstream
   .vo tree and no single-file check loop survives it
   (claude-notes/durable-notes.md, "Editing a file near the BOTTOM of the
   tree").  Merging these two into their proper homes on a build that can
   afford a full rebuild is owed, exactly as it is for [wp_srliw_s_sconf]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RiscvExtras.
Require Import PrintintArith.
Require Import WpSconfMem.
Require Import BufOwn.
Require Import DinodeSlot.
Require Import FsCrash.
Require Import BitmapEnc BitmapInv.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeShiftiop.
Require Import SmodeCore.
Require Import IntrDefs WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  SRAIW -- the third branch of [execute_SHIFTIWOP]'s match.             *)
(* ===================================================================== *)

Lemma exec_execute_SHIFTIWOP_SRAIW (shamt : mword 5) (rs1 rd : regidx)
    (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64
          (shift_bits_right_arith (subrange_vec_dec a 31 0 : mword 32) shamt)))
       s = Some (tt, s') ->
  exec (execute (SHIFTIWOP (shamt, rs1, rd, SRAIW))) s
  = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIWOP (shamt, rs1, rd, SRAIW)))
    with (execute_SHIFTIWOP shamt rs1 rd SRAIW).
  unfold execute_SHIFTIWOP. cbn match.
  rewrite (exec_bind_Some _ _ _ a s Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_sraiw_val (rs1 : mword 5) (shamt : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64
    (shift_bits_right_arith (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32) shamt).

Lemma exec_execute_SHIFTIWOP_SRAIW_gpr (rs1 rd : mword 5) (shamt : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sraiw_val rs1 shamt s))).
Proof.
  unfold gpr_sraiw_val, gpr_src.
  eapply exec_execute_SHIFTIWOP_SRAIW.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ===================================================================== *)
(*  SLLW -- the register-shift branch of [execute_RTYPEW]'s match.        *)
(* ===================================================================== *)

Definition gpr_sllw_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64
    (shift_bits_left (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
       (subrange_vec_dec (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32) 4 0)).

Lemma exec_execute_RTYPEW_SLLW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sllw_val rs2 rs1 s))).
Proof.
  unfold gpr_sllw_val, gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) SLLW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Section BallocLeaves.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Context {kt : ktier}.
  (* SRAIW: shift the source's low 32 bits RIGHT ARITHMETICALLY by a 5-bit
     shamt and sign-extend the 32-bit result back.  The [wp_srliw_s_sconf]
     twin, verbatim. *)
  Lemma wp_sraiw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sign_extend' 64
      (shift_bits_right_arith (subrange_vec_dec (rget m rs1) 31 0 : mword 32) shamt)
      = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIWOP_SRAIW_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sraiw_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  (* SLLW: shift the first source's low 32 bits LEFT by the second's low
     FIVE bits, sign-extending the 32-bit result back.  This is C's
     [(int)x << (y & 31)] and is how both allocators form the bit mask
     [1 << (bi % 8)]. *)
  Lemma wp_sllw_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64
        (shift_bits_left (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
           (subrange_vec_dec (subrange_vec_dec (rget m rs2) 31 0 : mword 32) 4 0)) in
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW))
              wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_SLLW_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sllw_val, gpr_src. rewrite Hva Hvb. reflexivity.
  Qed.

End BallocLeaves.


(* ===================================================================== *)
(*  THE BIT ARITHMETIC balloc's inner scan is made of.                    *)
(*                                                                        *)
(*  All of it is dictated by the INSTRUCTIONS, not by the contract, so it  *)
(*  is stated here once, at the exact value shapes the leaves produce.     *)
(*                                                                        *)
(*    +0x0ba  andi a3,a4,7          a3 = bi % 8                            *)
(*    +0x0be  sllw a3,s3,a3         a3 = 1 << (bi % 8)          THE MASK   *)
(*    +0x0c2  sraiw a5,a4,0x1f  \                                          *)
(*    +0x0c6  srliw a5,a5,0x1d   |  gcc's SIGNED divide of the C [int]     *)
(*    +0x0ca  c.addw a5,a5,a4    |  [bi] by 8: add the sign word's low     *)
(*    +0x0cc  sraiw a5,a5,0x3   /   three bits, then shift.  For bi >= 0   *)
(*                                  the bias is 0 and it is just bi / 8.   *)
(*    +0x09c  sraiw a1,s5,0xd       b / BPB, which is 0 at b = 0           *)
(* ===================================================================== *)

(* ---- mword-FREE arithmetic: [lia] answers "Cannot find witness" with a
   [bv_unsigned] merely in context (claude-notes/durable-notes.md), so every
   range argument is packaged here over plain [Z] and applied as a closed
   fact. ---- *)
Local Lemma bal_pow_ge1 (k : Z) : 0 <= k -> 1 <= 2 ^ k.
Proof. intro Hk. rewrite <- (Z.pow_0_r 2). apply Z.pow_le_mono_r; lia. Qed.

Local Lemma bal_div_range (u k : Z) :
  0 <= u < 4294967296 -> 0 <= k -> 0 <= u / 2 ^ k < 4294967296.
Proof.
  intros [H0 H1] Hk. pose proof (bal_pow_ge1 k Hk) as Hp.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with u; [apply Z.div_le_upper_bound; [lia|nia] | lia].
Qed.

(* ---- the two W-form shifts, generic in the shift amount ----
   The shamt is a VARIABLE here and is pinned by a premise the call site
   discharges on a CLOSED term; a bare [vm_compute] on the open shamt would
   not come back (durable-notes, "a branch/jump leaf's alignment side
   condition"). ---- *)
Lemma bal_signed_small32 (w : mword 32) :
  bv_unsigned w < 2147483648 -> bv_signed w = bv_unsigned w.
Proof.
  intro H. pose proof (bv_unsigned_in_range _ w) as [Hl _].
  unfold bv_signed. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite Hhm. split; [lia | exact H].
Qed.

Lemma bal_unsigned32 (w : mword 32) : 0 <= bv_unsigned w < 4294967296.
Proof.
  pose proof (bv_unsigned_in_range _ w) as H.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  rewrite Hm in H. exact H.
Qed.

Lemma bal_sraiw_div (w : mword 32) (sh : mword 5) (k : Z) :
  int_of_mword false sh = k -> 0 <= k < 32 ->
  bv_unsigned w < 2147483648 ->
  shift_bits_right_arith w sh = (mword_of_int (bv_unsigned w / 2 ^ k) : mword 32).
Proof.
  intros Hsh Hk Hw. pose proof (bal_unsigned32 w) as Hr.
  apply bv_eq.
  unfold shift_bits_right_arith, arith_shiftr, SailStdpp.Values.with_word,
         get_word, MachineWord.MachineWord.arith_shift_right.
  rewrite bv_ashiftr_unsigned.
  assert (Hn : bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 32)
                 (MachineWord.MachineWord.Z_idx (int_of_mword false sh))) = k).
  { rewrite Hsh. unfold MachineWord.MachineWord.N_to_word,
      MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. rewrite (Z2N.id k ltac:(lia)).
    apply bv_wrap_small.
    assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
      by (vm_compute; reflexivity).
    rewrite Hm. lia. }
  rewrite Hn (bal_signed_small32 w Hw).
  rewrite Z.shiftr_div_pow2; [| lia].
  assert (Hdr : 0 <= bv_unsigned w / 2 ^ k < 4294967296)
    by (apply bal_div_range; [exact Hr | lia]).
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  rewrite (moi32_small (bv_unsigned w / 2 ^ k)
             ltac:(change (2^32)%Z with 4294967296%Z; exact Hdr)).
  apply bv_wrap_small. rewrite Hm. exact Hdr.
Qed.

(* ---- the low 32 bits of a sign-extended int are that int ---- *)
Lemma bal_sub31_sext (w : mword 32) :
  (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32) = w.
Proof.
  change (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
    with (trunc32 (sign_extend' 64 w)).
  apply trunc32_sext64.
Qed.

Lemma bal_sub31_zero :
  (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32) = mword_of_int 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bal_sext_zero : sign_extend' 64 (mword_of_int 0 : mword 32) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- +0x09c  sraiw a1,s5,0xd : b / BPB, and b IS 0 (one bitmap block) ---- *)
Lemma bal_sraiw13_zero :
  sign_extend' 64 (shift_bits_right_arith
      (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32)
      (mword_of_int 13 : mword 5))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- +0x0c2  sraiw a5,a4,0x1f : the SIGN WORD of bi, which is 0 ---- *)
Lemma bal_sraiw31_zero (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  sign_extend' 64 (shift_bits_right_arith
      (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
      (mword_of_int 31 : mword 5))
  = (mword_of_int 0 : mword 64).
Proof.
  intro Hw. pose proof (bal_unsigned32 w) as Hr.
  rewrite bal_sub31_sext.
  rewrite (bal_sraiw_div w (mword_of_int 31 : mword 5) 31
             ltac:(vm_compute; reflexivity) ltac:(lia) Hw).
  assert (Hz : bv_unsigned w / 2 ^ 31 = 0).
  { apply Z.div_small. change (2^31)%Z with 2147483648%Z. split; [lia | exact Hw]. }
  rewrite Hz. apply bal_sext_zero.
Qed.

(* ---- +0x0c6  srliw a5,a5,0x1d : the bias, still 0 ---- *)
Lemma bal_srliw29_zero :
  sign_extend' 64 (shift_bits_right
      (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32)
      (mword_of_int 29 : mword 5))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- +0x0ca  c.addw a5,a5,a4 : adding the zero bias back ---- *)
Lemma bal_addw_zero_l (w : mword 32) :
  sign_extend' 64
    (add_vec (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32)
             (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32))
  = (sign_extend' 64 w : mword 64).
Proof.
  rewrite bal_sub31_sext bal_sub31_zero.
  assert (Hz : add_vec (mword_of_int 0 : mword 32) w = w).
  { apply bv_add_0_l. vm_compute. reflexivity. }
  rewrite Hz. reflexivity.
Qed.

(* ---- +0x0cc  sraiw a5,a5,0x3 : THE BYTE INDEX bi / 8 ---- *)
Lemma bal_sraiw3_div8 (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  sign_extend' 64 (shift_bits_right_arith
      (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
      (mword_of_int 3 : mword 5))
  = (mword_of_int (bv_unsigned w / 8) : mword 64).
Proof.
  intro Hw. pose proof (bal_unsigned32 w) as Hr.
  rewrite bal_sub31_sext.
  rewrite (bal_sraiw_div w (mword_of_int 3 : mword 5) 3
             ltac:(vm_compute; reflexivity) ltac:(lia) Hw).
  change (2 ^ 3)%Z with 8%Z.
  apply sext32_64_small.
  split; [apply Z.div_pos; lia|].
  change (2^31)%Z with 2147483648%Z.
  apply Z.le_lt_trans with (bv_unsigned w); [apply Z.div_le_upper_bound; lia | exact Hw].
Qed.

(* ---- +0x0ba  andi a3,a4,7 : the BIT OFFSET bi % 8 ---- *)
Local Lemma bal_z_land7 (x : Z) : Z.land x 7 = x `mod` 8.
Proof.
  assert (Ho : (7 = Z.ones 3)%Z) by (vm_compute; reflexivity).
  rewrite Ho Z.land_ones; [| lia].
  assert (Hp : (2 ^ 3 = 8)%Z) by (vm_compute; reflexivity).
  rewrite Hp. reflexivity.
Qed.

Local Lemma bal_mod8_range (u : Z) : 0 <= u -> 0 <= u `mod` 8 < 8.
Proof. intros _. apply Z.mod_pos_bound. lia. Qed.

Lemma bal_andi7 (x : mword 64) :
  and_vec x (sign_extend' 64 (mword_of_int 7 : mword 12) : mword 64)
  = (mword_of_int (bv_unsigned x `mod` 8) : mword 64).
Proof.
  assert (Hc : (sign_extend' 64 (mword_of_int 7 : mword 12) : mword 64)
               = mword_of_int 7) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply bv_eq. rewrite and_vec64_unsigned.
  assert (H7 : bv_unsigned (mword_of_int 7 : mword 64) = 7)
    by (vm_compute; reflexivity).
  rewrite H7 moi64_unsigned bal_z_land7.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
  destruct (bal_mod8_range (bv_unsigned x) Hx0) as [Hr0 Hr1].
  symmetry. apply bvw64_small.
  change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

(* ---- +0x0be  sllw a3,s3,a3 : THE MASK 1 << (bi % 8), with s3 = 1.
   [r] is a variable, so the shamt slices cannot be [vm_compute]d open
   (durable-notes); the offset ranges over eight values, so the eight
   CLOSED instances are the proof. ---- *)
Lemma bal_sllw_mask (r : Z) :
  0 <= r < 8 ->
  sign_extend' 64
    (shift_bits_left
       (subrange_vec_dec (mword_of_int 1 : mword 64) 31 0 : mword 32)
       (subrange_vec_dec
          (subrange_vec_dec (mword_of_int r : mword 64) 31 0 : mword 32) 4 0))
  = (mword_of_int (2 ^ r) : mword 64).
Proof.
  intro Hr.
  assert (Hc : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/
               r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the [lbu] result, as a plain unsigned byte ---- *)
Lemma bal_zext8_unsigned (v : mword 8) :
  bv_unsigned (zero_extend' 64 v : mword 64) = bv_unsigned v.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Values.to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned. reflexivity.
  first [ lia | vm_compute; discriminate | done ].
Qed.

(* ===================================================================== *)
(*  THE SEAM WITH [BitmapEnc]: the two places the machine's 64-bit        *)
(*  [and]/[or] over a zero-extended [lbu] meet the pure bit vocabulary.    *)
(* ===================================================================== *)

(* NOT [Local]: ProofBalloc's scan loop needs it to bound the mask. *)
Lemma bal_pow_mod8_small (bi : Z) : 0 <= bi -> 0 < 2 ^ (bi `mod` 8) <= 128.
Proof.
  intro Hbi. pose proof (bit_off_range bi Hbi) as [Hlo Hhi].
  split.
  - apply Z.pow_pos_nonneg; lia.
  - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
Qed.

Lemma bal_mask_unsigned (bi : Z) : 0 <= bi ->
  bv_unsigned (mword_of_int (2 ^ (bi `mod` 8)) : mword 64) = 2 ^ (bi `mod` 8).
Proof.
  intro Hbi. pose proof (bal_pow_mod8_small bi Hbi) as [H0 H1].
  apply moi64_small. lia.
Qed.

(* ---- +0x0d8  and a1,a3,a2  /  +0x0dc  c.beqz a1 : THE BIT TEST ---- *)
Lemma bal_and_mask_byte (u : gset Z) (bi : Z) :
  0 <= bi ->
  and_vec (mword_of_int (2 ^ (bi `mod` 8)) : mword 64)
          (zero_extend' 64 (bm_byte u (bi `div` 8) : mword 8) : mword 64)
  = (if bool_decide (bi ∈ u)
     then (mword_of_int (2 ^ (bi `mod` 8)) : mword 64)
     else (mword_of_int 0 : mword 64)).
Proof.
  intro Hbi. apply bv_eq.
  rewrite and_vec64_unsigned bal_zext8_unsigned (bal_mask_unsigned bi Hbi).
  rewrite Z.land_comm (bm_bit_test u bi Hbi).
  destruct (bool_decide (bi ∈ u));
    [rewrite (bal_mask_unsigned bi Hbi); reflexivity | vm_compute; reflexivity].
Qed.

(* ---- +0x03a  c.or a2,a2,a3  /  +0x03c  sb a2,88(a5) : SET THE BIT ---- *)
Lemma bal_sb_setbit (u : gset Z) (bi : Z) :
  0 <= bi ->
  trunc8 (or_vec (zero_extend' 64 (bm_byte u (bi `div` 8) : mword 8) : mword 64)
                 (mword_of_int (2 ^ (bi `mod` 8)) : mword 64))
  = bm_byte (u ∪ {[ bi ]}) (bi `div` 8).
Proof.
  intro Hbi. apply bv_eq.
  unfold trunc8. rewrite autocast_id.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  rewrite or_vec64_unsigned bal_zext8_unsigned (bal_mask_unsigned bi Hbi).
  rewrite (bm_bit_set u bi Hbi).
  change (MachineWord.Z_idx 8) with 8%N.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ===================================================================== *)
(*  The remaining pure vocabulary of balloc's WP.                         *)
(*  Every arithmetic fact is packaged over plain [Z] here: inside the WP   *)
(*  context [lia] is unusable (an [mword] in scope defeats the zify hook   *)
(*  -- claude-notes/durable-notes.md), so nothing there may call it.       *)
(* ===================================================================== *)

Notation ba_uint64 := uint_unsigned.

Lemma ba_moi64_uint (z : Z) : 0 <= z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro Hz. rewrite ba_uint64. apply moi64_small. exact Hz. Qed.

(* the two branch predicates, at the words the code compares *)
Lemma ba_bgeu_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  zopz0zKzJ_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_u.
  rewrite (ba_moi64_uint x Hx) (ba_moi64_uint y Hy). reflexivity.
Qed.

Lemma ba_neq_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  neq_vec (mword_of_int x : mword 64) (mword_of_int y : mword 64)
  = negb (Z.eqb x y).
Proof.
  intros Hx Hy. unfold neq_vec. f_equal.
  destruct (Z.eqb x y) eqn:E.
  - apply Z.eqb_eq in E. subst y. apply eq_vec_true_iff. reflexivity.
  - apply Z.eqb_neq in E. apply eq_vec_false_iff. intro Heq.
    apply E. rewrite -(moi64_small x Hx) -(moi64_small y Hy) Heq. reflexivity.
Qed.

(* a 32-bit return value of zero sign-extends to the 64-bit zero the
   contract's failure arm names *)
Lemma ba_sext_zero (rv : mword 32) :
  bv_unsigned rv = 0 -> (sign_extend' 64 rv : mword 64) = mword_of_int 0.
Proof.
  intro Hz.
  assert (Hrv : rv = (mword_of_int 0 : mword 32)).
  { apply bv_eq. rewrite Hz. symmetry. vm_compute. reflexivity. }
  rewrite Hrv. apply sext32_64_small. lia.
Qed.

(* EVERY arithmetic fact the WP needs about a scanned bit index. *)
Lemma ba_range (bi : Z) :
  0 <= bi <= BPB ->
  0 <= bi
  /\ 0 <= bi <= 8192
  /\ 0 <= bi < 2 ^ 31
  /\ 0 <= bi < 2 ^ 32
  /\ 0 <= bi < 18446744073709551616
  /\ 0 <= bi `mod` 8 < 8
  /\ 0 <= bi `div` 8 <= 1024
  /\ bi < 2147483648.
Proof.
  intros Hb. rewrite BPB_value in Hb.
  assert (Hd0 : 0 <= bi `div` 8) by (apply Z.div_pos; lia).
  assert (Hd1 : bi `div` 8 <= 1024) by (apply Z.div_le_upper_bound; lia).
  assert (Hm : 0 <= bi `mod` 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (H32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  split_and!; lia.
Qed.

(* THE SCAN LOOP'S DECREASE, as ONE lemma over plain Z/nat.  The call site
   is inside a whole-function WP whose context is full of [bv_unsigned]
   terms, where [bitvector.tactics]' zify hook makes [lia] answer "Cannot
   find witness" on exactly this kind of trivial bound (durable-notes).
   Discharging both of the IH's arithmetic premises from here keeps [lia]
   in a context two hypotheses wide, where it works. *)
Lemma ba_scan_step (bi size : Z) (fuel : nat) :
  (Z.to_nat (BPB - bi) <= S fuel)%nat ->
  0 <= bi <= BPB -> bi < size -> 0 < size <= BPB ->
  (Z.to_nat (BPB - (bi + 1)) <= fuel)%nat /\ 0 <= bi + 1 <= BPB.
Proof. rewrite BPB_value. intros Hf Hb Hlt Hs. split; lia. Qed.

(* the same, sharpened for a bit that is STRICTLY inside the bitmap: the
   byte index is then a legal [bitmap_bytes] index. *)
Lemma ba_range_lt (bi : Z) :
  0 <= bi < BPB ->
  (Z.to_nat (bi `div` 8) < 1024)%nat
  /\ Z.of_nat (Z.to_nat (bi `div` 8)) = bi `div` 8.
Proof.
  intros Hb. rewrite BPB_value in Hb.
  assert (Hd0 : 0 <= bi `div` 8) by (apply Z.div_pos; lia).
  assert (Hd1 : bi `div` 8 < 1024) by (apply Z.div_lt_upper_bound; lia).
  split_and!; lia.
Qed.

Lemma ba_bm_range (st : Z) : 0 < st -> st < 2 ^ 31 ->
  0 <= st < 2147483648 /\ 0 <= st < 2 ^ 32 /\ 0 <= st < 18446744073709551616.
Proof.
  intros H0 H1.
  assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (H32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  split_and!; lia.
Qed.

(* ---- +0x0de / +0x0e0  c.addiw a4,a4,1 : the two counter bumps ---- *)
Lemma ba_addiw1 (x : Z) : 0 <= x < 8192 ->
  sign_extend' 64
    (subrange_vec_dec
       (add_vec (mword_of_int x : mword 64)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (x + 1) : mword 64).
Proof.
  intro Hx.
  assert (H1 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                : mword 64) = mword_of_int 1)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H1.
  assert (Hadd : add_vec (mword_of_int x : mword 64) (mword_of_int 1 : mword 64)
                 = (mword_of_int (x + 1) : mword 64)).
  { apply bv_eq. rewrite add_vec64_unsigned !moi64_unsigned.
    rewrite (bvw64_small x ltac:(lia)).
    assert (H1u : bv_wrap 64 1 = 1) by (vm_compute; reflexivity).
    rewrite H1u. reflexivity. }
  rewrite Hadd.
  assert (Hsub : (subrange_vec_dec (mword_of_int (x + 1) : mword 64) 31 0 : mword 32)
                 = (mword_of_int (x + 1) : mword 32))
    by (apply (iu_sub31_moi (x + 1)); lia).
  rewrite Hsub. apply sext32_64_small.
  change (2^31)%Z with 2147483648%Z. lia.
Qed.

(* ---- the byte the INLINED bzero's [memset] writes: [SpecMemset]'s
   [cbyte] at [cval = 0], spelled exactly as the spec body's [let] does so
   that the post's big-op folds onto it. ---- *)
Definition ba_cbyte : bv 8 :=
  nth_byte (autocast (T := mword)
    (subrange_vec_dec (mword_of_int 0 : mword 64) (Z.sub (Z.mul 1 8) 1) 0)
    : mword 8) 0.

Lemma ba_cbyte_zero : ba_cbyte = bv_0 8.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ba_zero_block :
  ((fun _ : nat => ba_cbyte) <$> seq 0 1024) = replicate BSIZE (bv_0 8).
Proof.
  rewrite ba_cbyte_zero. apply list_eq. intros i.
  rewrite list_lookup_fmap.
  destruct (decide (i < 1024)%nat) as [Hi|Hi].
  - rewrite (lookup_seq_lt 0 1024 i Hi). cbn [fmap option_fmap option_map].
    first [ reflexivity
          | (symmetry; apply lookup_replicate_2; unfold BSIZE; lia) ].
  - rewrite (lookup_ge_None_2 (seq 0 1024) i ltac:(rewrite length_seq; lia)).
    cbn [fmap option_fmap option_map].
    first [ reflexivity
          | (symmetry; apply lookup_ge_None_2;
             rewrite length_replicate; unfold BSIZE; lia) ].
Qed.

(* ---- the one address shape: [bp + q] then [+88] (and the commuted form
   the [c.add a5,a5,s2] at +0x38 produces), both of which are byte [q] of
   [bp->data] ---- *)
Lemma ba_add_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof. apply bv_eq. rewrite !add_vec64_unsigned. apply f_equal. lia. Qed.

Lemma ba_data_off (X : mword 64) (q : nat) :
  add_vec (add_vec X (mword_of_int (Z.of_nat q)))
          (sign_extend' 64 (mword_of_int 88 : mword 12))
  = pa_add (b_data X) q.
Proof.
  rewrite iu_pa_add_moi iu_data_addr /b_data !pa_add_add.
  f_equal. lia.
Qed.

Lemma ba_data_off' (X : mword 64) (q : nat) :
  add_vec (add_vec (mword_of_int (Z.of_nat q)) X)
          (sign_extend' 64 (mword_of_int 88 : mword 12))
  = pa_add (b_data X) q.
Proof.
  rewrite (ba_add_comm (mword_of_int (Z.of_nat q)) X). apply ba_data_off.
Qed.

(* ---- +0x012 [beqz a5,+0xf6] -- THE DEAD ARM.  The contract premises
   [0 < size], so the word the [lw] at +0x00e loaded is nonzero and the
   branch FALLS THROUGH; the arm itself (a jump straight to the printk that
   would skip the s2..s8 restore) is refuted, never proved.  Stated over
   plain [Z] so the whole-function call site runs no arithmetic at all. ---- *)
Lemma ba_moi64_nonzero (z : Z) :
  0 < z < 18446744073709551616 ->
  eq_vec (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. apply eq_vec_false_iff. intro Heq.
  assert (Hzr : (zero_reg : mword 64) = (mword_of_int 0 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hzr in Heq.
  assert (Hc : z = 0).
  { rewrite -(moi64_small z ltac:(lia)) -(moi64_small 0 ltac:(lia)) Heq.
    reflexivity. }
  lia.
Qed.

(* ---- entering [ba_scan] at [bi = 0] with a full tank.  Both of the
   induction's arithmetic premises, over plain [Z]/[nat]: the call site is
   inside a whole-function WP where [bitvector.tactics]' zify hook makes
   [lia] answer "Cannot find witness" (durable-notes), so neither is proved
   there. ---- *)
Lemma ba_fuel_full : (Z.to_nat (BPB - 0) <= Z.to_nat BPB)%nat.
Proof. rewrite Z.sub_0_r. apply Nat.le_refl. Qed.

Lemma ba_bi_zero : 0 <= 0 <= BPB.
Proof. rewrite BPB_value. lia. Qed.
