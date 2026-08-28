(* RiscvExtras.v -- shared, opcode-independent reductions & bitvector identities:
   mword/bv identities; the state-pure should_inc_minstret; the MMIO
   within_clint/sig/htif discharges; and the x2 (sp) register-write leaves. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep.
Local Open Scope Z_scope.
Import Defs.

Lemma zero_extend'_id (a : mword 64) : zero_extend' 64 a = a.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.zero_extend].
  apply bv_eq. rewrite bv_zero_extend_unsigned. reflexivity. lia.
Qed.

Lemma autocast_id (m : Z) (x : mword m) : autocast x = x.
Proof. apply autocast_refl. Qed.

(* [eq_vec] is reflexive.  Every loop whose termination test is a compare of a
   cursor against its own limit needs it at the last iteration; it is stated
   here so no proof re-proves it locally. *)
Lemma eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* The 64-bit offset an AUIPC's 20-bit immediate contributes (imm << 12,
   sign-extended).  A pure bit-shuffling definition, so it lives here rather
   than in the AUIPC WP leaf ([WpAuipc.v]) that used to hold it: the closed
   forms of several functions' returned pointers ([ProcGeom.mycpu_ret], the
   auipc/addi pairs every kernel-symbol materialization compiles to) are pure
   spec vocabulary and must not have to import a weakest precondition. *)
Definition auipc_off (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm (Ox"000")).

(* Truncate a 64-bit value to its low 32 bits (the value a 4-byte store commits).
   Lives here (rather than in [VcGen]) so the low-level S-mode load/store WPs in
   [WpPushOffMem] can state their [_ram] postconditions with it. *)
Definition trunc32 (w : mword 64) : mword 32 :=
  autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 4 8) 1) 0).

(* ---- [mword_of_int] at width 32, and its sign extension to 64 ----
   Generic bitvector facts about a small non-negative literal stored in a
   4-byte cell: its unsigned value survives, and so does its signed value
   once sign-extended.  Every proof that reads an [int] field out of a
   kernel struct (push_off's noff, filedup's f->ref) needs them, so they
   live here rather than in whichever proof happened to want them first. *)
Lemma bvw32_small (z : Z) : (0 <= z < 2^32)%Z -> bv_wrap 32 z = z.
Proof. intro. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. lia. Qed.

Lemma bvw64_small (z : Z) : (0 <= z < 2^64)%Z -> bv_wrap 64 z = z.
Proof. intro. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. lia. Qed.

Lemma moi32_unsigned (z : Z) : bv_unsigned (mword_of_int z : mword 32) = bv_wrap 32 z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N. reflexivity.
Qed.

Lemma moi32_small (z : Z) : (0 <= z < 2^32)%Z -> bv_unsigned (mword_of_int z : mword 32) = z.
Proof. intro. rewrite moi32_unsigned. apply bvw32_small. lia. Qed.

(* ---- the four 64-bit UNSIGNED READINGS everything else is built on ----
   A literal, and the three [word_binop]s an address computation is made of,
   read through [bv_unsigned].  Each is one [unfold] chain that used to be
   re-derived (or inlined) in a dozen places; state them once here, where
   every consumer already has this file in its import closure.
   [ByteCursor.bc_{moi,add_vec,sub_vec}_unsigned] are restatements of these;
   [ArrCursor] and [WpMemsetS] still carry their own copies. *)
Lemma moi64_unsigned (z : Z) : bv_unsigned (mword_of_int z : mword 64) = bv_wrap 64 z.
Proof.
  unfold mword_of_int, SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* the model's [add_vec]/[sub_vec] agree with wrapped [Z] arithmetic AT ANY
   WIDTH.  The generic statements spell the width as [Z_idx n] because that is
   what [mword n]'s bitvector index literally is; every width instance below
   closes by conversion, so use those at width 32 / 64 and reach for the
   generic form only at a symbolic width. *)
Lemma add_vec_unsigned {n : Z} (x y : mword n) :
  bv_unsigned (add_vec x y)
  = bv_wrap (MachineWord.MachineWord.Z_idx n) (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma add_vec_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc.
  reflexivity.
Qed.

Lemma sub_vec_unsigned {n : Z} (x y : mword n) :
  bv_unsigned (sub_vec x y)
  = bv_wrap (MachineWord.MachineWord.Z_idx n) (bv_unsigned x - bv_unsigned y).
Proof.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned. reflexivity.
Qed.

Lemma add_vec64_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof. exact (add_vec_unsigned x y). Qed.

Lemma sub_vec64_unsigned (x y : mword 64) :
  bv_unsigned (sub_vec x y) = bv_wrap 64 (bv_unsigned x - bv_unsigned y).
Proof. exact (sub_vec_unsigned x y). Qed.

Lemma sub_vec32_unsigned (x y : mword 32) :
  bv_unsigned (sub_vec x y) = bv_wrap 32 (bv_unsigned x - bv_unsigned y).
Proof. exact (sub_vec_unsigned x y). Qed.

Lemma and_vec64_unsigned (x y : mword 64) :
  bv_unsigned (and_vec x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.and. apply bv_and_unsigned.
Qed.

Lemma or_vec64_unsigned (x y : mword 64) :
  bv_unsigned (or_vec x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof.
  cbv [or_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.or. apply bv_or_unsigned.
Qed.

Lemma sext64_moi32_unsigned (z : Z) : (0 <= z < 2^31)%Z ->
  bv_unsigned (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = z.
Proof.
  intro Hz.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite (bvw32_small z ltac:(change (2^32) with (2*2^31); lia)).
  assert (Hhm32 : bv_half_modulus 32 = 2^31) by reflexivity;
  rewrite (bv_swrap_small 32 z ltac:(rewrite Hhm32; lia)).
  apply bvw64_small. lia.
Qed.

(* The DUAL direction, and unconditional: sign-extending a 4-byte cell to 64
   bits is materializing its SIGNED value as a 64-bit literal.  Both sides are
   [bv_wrap 64 (bv_signed w)] -- the sign extension by construction, the
   literal because [mword_of_int] is [Z_to_bv] -- so no range premise is
   needed.  This is what turns a C [int] read out of memory into an index a
   spec can talk about ([SpecArgfd.arg_fd], whose fd is [bv_signed] of the
   loaded word). *)
Lemma sext32_64_moi (w : mword 32) :
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_signed w).
Proof.
  apply bv_eq.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold mword_of_int, SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  reflexivity.
Qed.

(* wrapping a SIGNED wrap is the unsigned wrap: the half-modulus shift the
   signed view adds is invisible mod the modulus. *)
Lemma bv_wrap_swrap (n : N) (z : Z) : bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof. unfold bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

(* ...and its consequence, the round trip a C [int] out-parameter performs:
   argfd reloads its [int fd] local with an [lw] (sign-extending) and stores
   the result back with an [sw] (truncating), and that is the identity. *)
Lemma trunc32_sext64 (w : mword 32) : trunc32 (sign_extend' 64 w) = w.
Proof.
  apply bv_eq. unfold trunc32. rewrite autocast_id.
  unfold subrange_vec_dec, to_word_idx, to_word, get_word,
         MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (Z.sub (Z.mul 4 8) 1 - 0 + 1)) with 32%N.
  rewrite (bv_wrap_bv_wrap 32 64 _ ltac:(lia)).
  unfold bv_signed. rewrite bv_wrap_swrap.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ...and its immediate consequence: sign-extending to 64 bits is INJECTIVE,
   [trunc32] being a left inverse.  This is what lets a compare of two
   [lw]-loaded (hence sign-extended) words be read as the 32-bit compare of the
   cells themselves -- the scheduler's pid compare, pipewrite's index compare,
   bread's dev/blockno scan compare. *)
Lemma sext64_32_inj (x y : mword 32) :
  (sign_extend' 64 x : mword 64) = (sign_extend' 64 y : mword 64) -> x = y.
Proof.
  intro H. rewrite <- (trunc32_sext64 x), <- (trunc32_sext64 y), H. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* SIGNED AND UNSIGNED, AT WIDTH 64.                                       *)
(*                                                                         *)
(*   A branch on a C [int] is signed ([bge] against x0) while the range     *)
(*   check that follows it is not ([bltu]), so any function that does both  *)
(*   -- growproc, sys_sbrk -- has to cross once.  These three are the       *)
(*   crossing.  [sint x = bv_signed x] holds by [reflexivity] (the stdpp    *)
(*   MachineWord backend defines [word_to_Z := bv_signed]), which is what   *)
(*   makes them provable at all.                                           *)
(* ---------------------------------------------------------------------- *)

Lemma sint64_range (b : mword 64) :
  (- 9223372036854775808 <= sint b < 9223372036854775808)%Z.
Proof.
  assert (Hs : sint b = bv_signed b) by reflexivity. rewrite Hs.
  pose proof (bv_signed_in_range 64 b ltac:(discriminate)) as Hr.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808%Z) by (vm_compute; reflexivity).
  rewrite Hh in Hr. exact Hr.
Qed.

(* a NON-NEGATIVE signed value is its own unsigned value *)
Lemma sint64_unsigned (b : mword 64) : (0 <= sint b)%Z -> bv_unsigned b = sint b.
Proof.
  intros H.
  assert (Hs : sint b = bv_signed b) by reflexivity.
  rewrite Hs in H |- *.
  pose proof (bv_unsigned_in_range _ b) as Hr.
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z) by (vm_compute; reflexivity).
  rewrite Hm in Hr.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808%Z) by (vm_compute; reflexivity).
  unfold bv_signed, bv_swrap, bv_wrap in H |- *.
  rewrite Hh Hm in H |- *.
  destruct (Z.lt_ge_cases (bv_unsigned b) 9223372036854775808%Z) as [Hlo | Hhi].
  - rewrite (Z.mod_small (bv_unsigned b + 9223372036854775808) 18446744073709551616);
      lia.
  - exfalso.
    assert (Hq : ((bv_unsigned b + 9223372036854775808) mod 18446744073709551616)%Z
                 = (bv_unsigned b - 9223372036854775808)%Z).
    { replace (bv_unsigned b + 9223372036854775808)%Z
        with ((bv_unsigned b - 9223372036854775808) + 1 * 18446744073709551616)%Z by lia.
      rewrite Z.mod_add; [| lia]. apply Z.mod_small. lia. }
    rewrite Hq in H. lia.
Qed.

(* ...and the sum that does not wrap.  Note what the second premise costs a
   caller: with [bv_unsigned a] inside the user region and [sint b] bounded
   by [sint64_range] alone, it is arithmetic -- no 32-bit bound on [b] is
   needed to rule the wrap out. *)
Lemma add_vec_sint_unsigned (a b : mword 64) :
  (0 <= sint b)%Z ->
  (bv_unsigned a + sint b < 18446744073709551616)%Z ->
  bv_unsigned (add_vec a b) = (bv_unsigned a + sint b)%Z.
Proof.
  intros Hb Hlt.
  rewrite add_vec64_unsigned (sint64_unsigned b Hb).
  pose proof (bv_unsigned_in_range _ a) as [Ha0 _].
  pose proof (bv_unsigned_in_range _ b) as [Hb0 _].
  assert (Hm : bv_modulus 64 = 18446744073709551616%Z) by (vm_compute; reflexivity).
  apply bv_wrap_small. rewrite Hm.
  pose proof (sint64_unsigned b Hb). lia.
Qed.

Lemma sint64_moi32 (z : Z) : (0 <= z < 2^31)%Z ->
  sint (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite (sext64_moi32_unsigned z ltac:(lia)).
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* SUBRANGE -> UNSIGNED, ONCE, AT EVERY WIDTH.                             *)
(*                                                                         *)
(*   [subrange_vec_dec v hi lo] is bits hi..lo of [v]; read through         *)
(*   [bv_unsigned] it is the plain integer [uint v / 2^lo mod 2^(hi-lo+1)]. *)
(*   That identity does not depend on the widths, so ONE lemma serves       *)
(*   every extraction in the tree -- the PTE flag/extension fields, the     *)
(*   ppn, the [sext.w] low half, the page offset.  Instantiate it (by       *)
(*   [apply], NOT [rewrite] -- see below); do NOT re-derive the             *)
(*   [autocast]/[cast_idx]/[bv_extract] peel.                               *)
(*                                                                         *)
(*   The divisor and modulus are taken as PREMISES so a call site gives     *)
(*   them as closed literals and discharges [d = 2^lo] by [vm_compute];     *)
(*   writing [2 ^ 54] into a goal would leave a term [lia] cannot evaluate. *)
(*                                                                         *)
(*   Instances must be stated at the REDUCED width ([: mword 44], not       *)
(*   [: mword (53 - 10 + 1)]) and closed with [apply]: [bv_unsigned]'s      *)
(*   width argument is [MachineWord.Z_idx (hi - lo + 1)] here, which is     *)
(*   only CONVERTIBLE to the reduced literal, and [rewrite] matches         *)
(*   syntactically.                                                         *)
(* ---------------------------------------------------------------------- *)

(* [autocast]/[cast_idx] are transports between provably-equal widths, so
   they are invisible to [bv_unsigned]. *)
Lemma autocast_unsigned (m n : Z) (x : mword m) :
  m = n -> bv_unsigned (autocast x : mword n) = bv_unsigned x.
Proof. intros ->. rewrite autocast_refl. reflexivity. Qed.

Lemma cast_idx_unsigned (m n : N) (x : MachineWord.MachineWord.word m) (e : m = n) :
  bv_unsigned (MachineWord.MachineWord.cast_idx x e) = bv_unsigned x.
Proof. destruct e. rewrite MachineWord.MachineWord.cast_idx_refl. reflexivity. Qed.

Lemma subrange_dec_unsigned {n : Z} (v : mword n) (hi lo d m : Z) :
  0 <= lo -> lo <= hi -> d = 2 ^ lo -> m = 2 ^ (hi - lo + 1) ->
  bv_unsigned (subrange_vec_dec v hi lo : mword (hi - lo + 1))
  = bv_unsigned v / d mod m.
Proof.
  intros Hlo Hhi -> ->.
  unfold subrange_vec_dec.
  rewrite (autocast_unsigned _ _ _ (MachineWord.MachineWord.idx_Z_idx (hi - lo + 1) ltac:(lia))).
  unfold to_word_idx, Values.to_word, get_word, MachineWord.MachineWord.slice.
  rewrite cast_idx_unsigned.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  rewrite Z.shiftr_div_pow2; [| apply N2Z.is_nonneg].
  f_equal.
  - f_equal. f_equal. cbn. rewrite Z2N.id; lia.
  - f_equal. cbn. rewrite Z2N.id; lia.
Qed.

(* the [lo = 0] case, where the division drops out (a low-field extraction is
   just a truncation) -- the commonest instance by far *)
Lemma subrange_dec_unsigned_lo0 {n : Z} (v : mword n) (hi m : Z) :
  0 <= hi -> m = 2 ^ (hi + 1) ->
  bv_unsigned (subrange_vec_dec v hi 0 : mword (hi - 0 + 1)) = bv_unsigned v mod m.
Proof.
  intros Hhi Hm.
  rewrite (subrange_dec_unsigned v hi 0 1 m ltac:(lia) ltac:(lia) eq_refl
             ltac:(rewrite Hm; f_equal; lia)).
  rewrite Z.div_1_r. reflexivity.
Qed.

(* the one instance that is wanted tree-wide: the low half of a register, as
   [sext.w rd,rs1] (= ADDIW at immediate 0) reads it *)
Lemma subrange_31_0_unsigned (a : mword 64) :
  bv_unsigned (subrange_vec_dec a 31 0 : mword 32) = bv_unsigned a mod 4294967296.
Proof. apply (subrange_dec_unsigned_lo0 a 31 4294967296); [lia | vm_compute; reflexivity]. Qed.

(* sign-extending a 9-bit value to 12 bits then to 64 is the same as
   zero-extending it to 64 directly: the 12-bit zero-extension's sign bit
   (bit 11) is always 0 since a 9-bit value's magnitude is well below 2^11,
   so sign- and zero-extending it agree from there on. Used by the
   [kernelvec]/[kerneltrap] saved-register-slot address computations, each
   of which builds a byte offset as [concat_vec (reg-index : mword 6)
   ('b"000") : mword 9] and widens it to 64 for the add against sp. *)
Lemma sext9_12_64 (x : mword 9) : sign_extend' 64 (zero_extend' 12 x) = zero_extend' 64 x.
Proof.
  cbv [sign_extend' zero_extend' Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.sign_extend MachineWord.MachineWord.zero_extend].
  apply bv_eq.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_zero_extend_signed.
  rewrite bv_zero_extend_unsigned'.
  rewrite bv_swrap_small; [reflexivity |].
  pose proof (bv_unsigned_in_range 9 x) as [Hl Hh].
  unfold bv_modulus in Hh. simpl in Hh.
  unfold bv_half_modulus, bv_modulus. simpl.
  change (2 ^ 9) with 512 in Hh.
  change (2 ^ 12 / 2) with 2048.
  lia.
Qed.

(* the byte offset for saved-register slot 0 (register index 0) is the
   literal 0, so adding it to any base is a noop -- used by the
   [kernelvec]/[kerneltrap] slot-0 (sp+0) address computation. *)

(* A 1-bit word that is not 1 is 0 -- the two-element case analysis on a
   [mword 1] (e.g. an [Mstatus.SIE]/[Mstatus.MIE] bit known to be not-set).
   Pure bitvector fact; shared by the pop_off/push_off/acquire/release
   interrupt-disable proofs (do NOT re-copy it into a Wp*.v file). *)
Lemma mword1_zero_of_ne_one (x : mword 1) :
  eq_vec x ('b"1") = false -> x = ('b"0" : mword 1).
Proof.
  intro H. apply eq_vec_false_iff in H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  assert (Hmod : bv_modulus 1 = 2) by (vm_compute; reflexivity).
  rewrite Hmod in Hr.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  assert (H0 : bv_unsigned ('b"0" : mword 1) = 0) by (vm_compute; reflexivity).
  rewrite H0.
  assert (Hne : bv_unsigned x <> 1).
  { intro Hc. apply H. apply bv_eq. rewrite H1. exact Hc. }
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* should_inc_minstret is state-pure: its result is fully determined by    *)
(* the mcountinhibit and minstretcfg cells.  Owning those two CSRs thus     *)
(* discharges the `should_inc` exec-condition (no `forall s0` needed).      *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* MMIO-range discharge: an access whose base address is RAM (outside the  *)
(* CLINT/SIG ranges) is not "within" them.  Owning a memory byte at that    *)
(* address (via the RAM-constrained `↦ₘ`, lemma `mem_ram`) supplies         *)
(* `not_in_clint`/`not_in_sig`.  within_htif depends on the                 *)
(* `htif_tohost_base` register, discharged by owning it `= None`.           *)
(* ---------------------------------------------------------------------- *)
Lemma within_clint_false (a : Arch.pa) (w : Z) s :
  not_in_clint a -> (0 < w)%Z -> exec (within_clint (Physaddr a) w) s = Some (false, s).
Proof.
  intros Hnc Hw. unfold within_clint, plat_have_clint, __id. cbn [Riscv.rv64d.not negb].
  assert (Hf : (uint plat_clint_base <=? uint a) &&
               (uint a + w <=? uint plat_clint_base + uint plat_clint_size) = false).
  { destruct Hnc as [H|H]; [apply andb_false_intro1|apply andb_false_intro2]; apply Z.leb_gt; lia. }
  rewrite Hf. apply exec_returnm.
Qed.

Lemma within_sig_false (a : Arch.pa) (w : Z) s :
  not_in_sig a -> (0 < w)%Z -> exec (within_sig (Physaddr a) w) s = Some (false, s).
Proof.
  (* plat_have_sig is compiled in as a constant `false` (the SIG test device
     is disabled in model-xv6iris/sail-config-rv64d.json, since it would
     otherwise collide with the real PLIC's address window) -- `within_sig`
     already short-circuits to `false` without consulting the address range,
     so `not_in_sig`/`w` aren't needed to close this goal. Kept as hypotheses
     to avoid rippling the ~200 call sites across iris/ that supply them. *)
  intros _ _. unfold within_sig, plat_have_sig, __id. cbn [Riscv.rv64d.not negb].
  apply exec_returnm.
Qed.

Lemma within_htif_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_htif_readable (Physaddr a) w) s = Some (false, s).
Proof.
  intro Hn. unfold within_htif_readable, within_htif_writable.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_returnm.
Qed.

(* add_vec_int a 0 = a : the j=0 byte of an access sits at the access base. *)
Lemma avi0 (a : mword 64) : add_vec_int a 0 = a.
Proof.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, mword_of_int,
         MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite bv_add_unsigned Z_to_bv_unsigned.
  rewrite bv_wrap_0 Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pa_add_0 (a : Arch.pa) : pa_add a 0 = a.
Proof. unfold pa_add. change (Z.of_nat 0) with 0%Z. apply avi0. Qed.

(* [avi0] restated in the raw [add_vec … (mword_of_int 0)] form the whole-
   function proofs rewrite with (they never spell the [add_vec_int] wrapper).
   A pure identity, so it belongs here beside [avi0] — NOT in any one function's
   proof file. *)
Lemma kv_addv_zero (a : mword 64) : add_vec a (mword_of_int 0) = a.
Proof. exact (avi0 a). Qed.

(* the kernelvec/kerneltrap saved-register-slot address computation always
   writes its (always-zero) sub-word byte offset as the literal product
   "0 * 8" rather than a bare 0. *)
(* a ZERO 12-bit displacement, in the [sign_extend' 64 (mword_of_int 0)] form
   an [ld]/[sd]/[sw] with a literal 0 offset produces (distinct from
   [add_vec_zeros_r]'s [zeros' 12] spelling). *)
Lemma addv_sext0 (v : mword 64) :
  add_vec v (sign_extend' 64 (mword_of_int 0 : mword 12)) = v.
Proof.
  assert (H0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) = mword_of_int 0)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H0. apply kv_addv_zero.
Qed.

(* [sext.w rd,rs1] is ADDIW at immediate 0, and on a value that already fits
   in 31 bits the 32-bit truncate-and-sign-extend round trip is the identity.
   Both copy loops narrow their chunk length this way at a SYMBOLIC count, so
   the enumerating [PlicHart.sext32_id_hart] is no use; this is the general
   fact.  (Recipe: KstackArith's [addw_step] -- reduce [sign_extend'] to
   [bv_sign_extend] and read both sides off through [bv_unsigned].) *)
Lemma sextw_moi (k : Z) : 0 <= k -> k < 2147483648 ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int k : mword 64) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
  = (mword_of_int k : mword 64).
Proof.
  intros H0 H1.
  rewrite addv_sext0.
  apply bv_eq.
  set (w := subrange_vec_dec (mword_of_int k : mword 64) 31 0).
  assert (Hw : bv_unsigned w = k).
  { unfold w. rewrite subrange_31_0_unsigned moi64_unsigned.
    rewrite (bvw64_small k ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
    apply Z.mod_small. lia. }
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite Hw.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2147483648)
    by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [| rewrite Hhm; lia].
  rewrite moi64_unsigned. reflexivity.
Qed.

Lemma avi0_mul8 (a : mword 64) : add_vec_int a (0 * 8) = a.
Proof. change (0 * 8) with 0. apply avi0. Qed.

(* add_vec_int (mword_of_int A) k = mword_of_int (A + k) : the model's mword
   addition agrees with Z addition (everything reduces mod 2^64). *)
Lemma avi_mword (A k : Z) :
  add_vec_int (mword_of_int A : mword 64) k = mword_of_int (A + k).
Proof.
  unfold add_vec_int, add_vec, mword_of_int, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply bv_eq. rewrite bv_add_unsigned !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r. reflexivity.
Qed.

(* fetch_pa is the identity on 64-bit physical addresses (M-mode, no paging). *)
Lemma fetch_pa_id (pc : mword 64) : fetch_pa pc = pc.
Proof. unfold fetch_pa. cbn [bits_of_virtaddr]. apply zero_extend'_id. Qed.

(* The Sail [uint] of an mword is just its stdpp bv_unsigned. *)
Lemma uint_unsigned (a : mword 64) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* RAM-range geometry: facts about an address DERIVABLE from [addr_is_ram] *)
(* (the concrete range [ram_base, ram_base + ram_size)).  These let the    *)
(* higher-level S-mode WPs discharge their per-address geometry            *)
(* obligations from an owned points-to instead of carrying them as         *)
(* explicit preconditions.                                                 *)
(* ---------------------------------------------------------------------- *)

(* THE BYTE AT OFFSET [j] OF AN ACCESS, as unsigned arithmetic.  ONE home for
   this (it used to have two, in SmodePte and WpSmodeGpr); every consumer that
   needs "the last byte of an n-byte access is at [uint a + n - 1]" -- the PMA
   address classes below, the PMP range matches, the chunk lemmas -- goes
   through it. *)
Lemma uint_pa_add (a : mword 64) (j : nat) :
  (uint a + Z.of_nat j < 18446744073709551616)%Z ->
  uint (pa_add a j) = uint a + Z.of_nat j.
Proof.
  intro Hlt. rewrite !uint_unsigned in Hlt |- *.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (Z.of_nat j) : mword 64) = Z.of_nat j).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    split.
    - apply Nat2Z.is_nonneg.
    - apply Z.le_lt_trans with (bv_unsigned a + Z.of_nat j).
      + rewrite <- (Z.add_0_l (Z.of_nat j)) at 1. apply Z.add_le_mono_r. exact Har.
      + exact Hlt. }
  rewrite Hj.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split.
  - apply Z.add_nonneg_nonneg. exact Har. apply Nat2Z.is_nonneg.
  - exact Hlt.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE TWO PMA ADDRESS CLASSES.                                            *)
(*                                                                         *)
(* The platform's PMA table has THREE regions and holes between them (see  *)
(* [RiscvLang.pma_boot], which is the model's own table, tied to it by      *)
(* [ColdBoot.cold_boot_pma]), so "the table permits this access" is a       *)
(* statement about WHERE the access is -- there is no table at all under    *)
(* which every address is permitted.  Both classes carry three things: the  *)
(* model's own width proviso on a [matching_pma_region] lookup              *)
(* (1 <= n <= 4096, rv64d.v), and the two bounds that make the lookup's     *)
(* [range_subset] test succeed -- the base at or above the region's, and the *)
(* END address at or below the region's end.                                *)
(*                                                                         *)
(* THE END BOUND IS NOT IMPLIED BY THE BASE BOUND, and that is the whole    *)
(* reason these are new: [range_subset] compares the access's END against   *)
(* the region's, so an 8-byte access whose base is the last byte of DRAM    *)
(* matches NO region and faults.  Every applier owns the end bound -- the   *)
(* chunk lemmas hand back the LAST byte's [addr_is_ram] alongside the        *)
(* base's, and [PtTree.pt_slot_mem] carries both for a PTE slot.             *)
(* ---------------------------------------------------------------------- *)

(* KERNEL RAM: the DRAM bank.  Grants R/W/X, atomics, and PTE reads/writes. *)
Definition pma_ram_access (a : mword 64) (n : Z) : Prop :=
  1 <= n <= 4096 /\ ram_base <= uint a /\ uint a + n <= ram_base + ram_size.

(* THE DEVICE BAND: UART / PLIC / virtio-mmio / CLINT.  Grants R/W only --
   not execute, not PTE access, not atomics. *)
Definition pma_io_access (a : mword 64) (n : Z) : Prop :=
  1 <= n <= 4096 /\ mmio_base <= uint a /\ uint a + n <= mmio_base + mmio_size.

(* ALL the arithmetic of the class constructors, over plain [Z]: [lia] is
   unusable once an [mword] is in the context (durable-notes), so the
   inequalities are done here, in a clean one.  [k] is the offset of ANY owned
   byte at or beyond the access's last one -- an inequality, not an equality,
   because a two-byte fetch half is licensed by the four-byte window's last
   byte just as well as by its own. *)
Lemma pma_fit_last (x n k : Z) :
  0 <= k -> n - 1 <= k -> x + k < ram_base + ram_size ->
  x + n <= ram_base + ram_size.
Proof. unfold ram_base, ram_size. lia. Qed.

(* an owned byte of a RAM access cannot be the wraparound of a huge offset:
   the bank tops out at PHYSTOP and the offset is below the model's own
   maximum access width, so the sum is nowhere near 2^64. *)
Lemma pma_k_bound (n : Z) : 1 <= n <= 4096 -> n - 1 <= 4095.
Proof. lia. Qed.

Lemma pma_fit_byte (x : Z) :
  x < ram_base + ram_size -> x + 1 <= ram_base + ram_size.
Proof. unfold ram_base, ram_size. lia. Qed.

Lemma pma_nowrap_ram (x k : Z) :
  x < ram_base + ram_size -> k <= 4095 -> x + k < 18446744073709551616.
Proof. unfold ram_base, ram_size. lia. Qed.

Lemma pma_fit_io (x n hi : Z) :
  x < hi -> n <= 4096 -> hi + 4095 <= mmio_base + mmio_size ->
  x + n <= mmio_base + mmio_size.
Proof. unfold mmio_base, mmio_size. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* Discharging a CLASS MEMBERSHIP at an applier, with no tactic at all.     *)
(* Every premise below is either a fact the applier already owns or a       *)
(* boolean check closed by [eq_refl]: deliberately so, because [lia] is     *)
(* unusable at these sites -- the [bitvector.tactics] zify hook fails to    *)
(* find a witness even for a CLOSED bound like [1 <= 4 <= 4096] once a [bv] *)
(* is in the context (durable-notes).  The arithmetic is done here, in a    *)
(* clean context, once.                                                    *)
(* ---------------------------------------------------------------------- *)

(* the width half: at a literal width both checks are [eq_refl]; a variable
   width comes with its own [0 < n <= m] pair and [m] closed. *)
Lemma pma_width_ok (n : Z) :
  Z.leb 1 n = true -> Z.leb n 4096 = true -> 1 <= n <= 4096.
Proof.
  intros H1 H2. apply Z.leb_le in H1. apply Z.leb_le in H2. exact (conj H1 H2).
Qed.

Lemma pma_width_le (n m : Z) :
  0 < n -> n <= m -> Z.leb m 4096 = true -> 1 <= n <= 4096.
Proof. intros H1 H2 H3. apply Z.leb_le in H3. split; lia. Qed.

(* THE RAM CLASS, from the two [addr_is_ram] facts an applier owns: the
   access's base, and ANY owned byte at or beyond its last one ([k] is that
   byte's offset; the [Z.leb] check is [eq_refl] whenever the width and the
   offset are literals, which is every fixed-width leaf).  The
   at-or-beyond slack is what lets the two halves of a split four-byte fetch
   both be licensed by the window's last byte. *)
(* PREMISE ORDER IS LOAD-BEARING: the two [addr_is_ram]s come first (they pin
   [a] and [k]), then the width bound (it pins [n]), and only then the two
   [Z.leb] checks -- an application's arguments are elaborated left to right and
   its conclusion unified LAST, so an [eq_refl] placed before the argument that
   determines [n] is checked against [(?n - 1 <=? 3) = true] and fails. *)
Lemma pma_access_ram (a : mword 64) (n : Z) (k : nat) :
  addr_is_ram a -> addr_is_ram (pa_add a k) -> 1 <= n <= 4096 ->
  Z.leb (n - 1) (Z.of_nat k) = true -> Z.leb (Z.of_nat k) 4095 = true ->
  pma_ram_access a n.
Proof.
  intros [Hlo Hhi] Hk Hn Hnk Hk4.
  apply Z.leb_le in Hnk. apply Z.leb_le in Hk4.
  destruct Hk as [_ Hkhi].
  rewrite (uint_pa_add a k (pma_nowrap_ram (uint a) (Z.of_nat k) Hhi Hk4)) in Hkhi.
  exact (conj Hn (conj Hlo (pma_fit_last (uint a) n (Z.of_nat k)
                             (Nat2Z.is_nonneg k) Hnk Hkhi))).
Qed.

(* the VARIABLE-WIDTH form: [k] is the access's own last byte, given by an
   equation rather than a closed check (a byte-loop chunk's width is a
   variable, so no [Z.leb] on it is [eq_refl]).  Here the offset's upper bound
   comes from the equation and the width bound, so there is nothing extra to
   discharge. *)
Lemma pma_access_ram_at (a : mword 64) (n : Z) (k : nat) :
  Z.of_nat k = n - 1 -> addr_is_ram a -> addr_is_ram (pa_add a k) ->
  1 <= n <= 4096 -> pma_ram_access a n.
Proof.
  intros Hk Hlo Hhi Hn.
  apply (pma_access_ram a n k Hlo Hhi Hn).
  - apply Z.leb_le. rewrite Hk. apply Z.le_refl.
  - apply Z.leb_le. rewrite Hk. exact (pma_k_bound n Hn).
Qed.

(* a ONE-byte access needs no end bound at all: the base being in the bank IS
   the end being in the bank. *)

(* the same class from the RANGE BOUNDS themselves, where the applier has
   already computed them (several memory leaves derive an [Hlo]/[Hfit] pair
   for their PMP range match and can reuse it here). *)

(* THE DEVICE CLASS, from the window bounds the device leaves already own
   ([plic_base <= uint a8 < plic_base + plic_size], and the UART / virtio
   analogues).  [lo] and [hi] are closed at every use and the end check is
   taken at the model's MAXIMUM access width, so both band checks are [eq_refl]
   even where the width is a variable (WpUart's byte accesses). *)
Lemma pma_access_io (a : mword 64) (n lo hi : Z) :
  (lo <= uint a)%Z -> (uint a < hi)%Z ->
  Z.leb mmio_base lo = true ->
  Z.leb (hi + 4095) (mmio_base + mmio_size) = true ->
  1 <= n <= 4096 -> pma_io_access a n.
Proof.
  intros Hlo Hhi Hb1 Hb2 Hn. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  exact (conj Hn (conj (Z.le_trans _ _ _ Hb1 Hlo)
                       (pma_fit_io (uint a) n hi Hhi (proj2 Hn) Hb2))).
Qed.

(* the low 39 bits of a RAM address are the address itself (as a bv 39):
   [uint a < 2^39], so the [subrange 38:0] extraction loses nothing. *)
(* The low 39 bits of an address below 2^39 are the address.  Both the RAM
   and the below-MAXVA callers below are this fact at a tighter bound. *)
Lemma sub38_0_unsigned (a : mword 64) :
  bv_unsigned a < 549755813888 ->
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = bv_unsigned a.
Proof.
  intro Hlt.
  rewrite (subrange_dec_unsigned_lo0 a (Z.sub 39 1) 549755813888
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  apply Z.mod_small. split; [apply bv_unsigned_in_range | exact Hlt].
Qed.

Lemma ram_subrange_unsigned (a : mword 64) :
  addr_is_ram a ->
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = uint a.
Proof.
  intros [Hlo Hhi]. rewrite uint_unsigned in Hlo, Hhi |- *. unfold ram_base, ram_size in *.
  apply sub38_0_unsigned. lia.
Qed.

(* the same two facts for any LOW address (below MAXVA = 2^38 -- walk's
   premise; covers device vas that are not RAM) *)
Lemma lo_subrange_unsigned (a : mword 64) :
  uint a < 274877906944 ->
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = uint a.
Proof.
  intros Hlt. rewrite uint_unsigned in Hlt |- *.
  apply sub38_0_unsigned. lia.
Qed.

(* Sv39 canonicality of any RAM address: since [uint a < 0x88000000 < 2^38],
   bit 38 (and every bit >= 39) is 0, so sign-extending the low 39 bits back
   to 64 returns [a] unchanged.  This is exactly the [neq_vec ... = false]
   canonicality check the S-mode [translateAddr] lemmas demand. *)

(* the Sv39 VPN (bits 38:12) of an address, as a 27-bit word.  This is the
   [svpn] the S-mode WPs abstract over; defining it as the extraction lets the
   [Hvpn_def] premise ([autocast (subrange (subrange a 38 0) 38 12) = svpn])
   hold by [reflexivity], and pins its value via [svpn_of_unsigned]. *)
(* [svpn_of] itself now lives in RiscvPtsto (the VA-based points-to is
   built on it); its arithmetic lemmas stay here with their helpers. *)

Lemma svpn_of_unsigned (a : mword 64) :
  addr_is_ram a ->
  bv_unsigned (svpn_of a) = Z.shiftr (uint a) 12.
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  unfold svpn_of. cbn [bits_of_virtaddr]. rewrite autocast_id.
  unfold subrange_vec_dec at 1. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx pagesize_bits) with 12%N.
  rewrite bv_extract_unsigned.
  fold (subrange_vec_dec a (Z.sub 39 1) 0).
  rewrite (ram_subrange_unsigned a Hram).
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - pagesize_bits + 1)) with 27%N.
  rewrite bv_wrap_small.
  - rewrite uint_unsigned. reflexivity.
  - rewrite uint_unsigned.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728) as -> by (vm_compute; reflexivity).
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)).
    change (2 ^ 12) with 4096.
    split.
    + apply Z.div_pos. lia. lia.
    + apply Z.div_lt_upper_bound. lia. lia.
Qed.

Lemma svpn_of_unsigned_lo (a : mword 64) :
  uint a < 274877906944 ->
  bv_unsigned (svpn_of a) = Z.shiftr (uint a) 12.
Proof.
  intros Hlt. pose proof Hlt as Hlt'. rewrite uint_unsigned in Hlt'.
  unfold svpn_of. cbn [bits_of_virtaddr]. rewrite autocast_id.
  unfold subrange_vec_dec at 1. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx pagesize_bits) with 12%N.
  rewrite bv_extract_unsigned.
  fold (subrange_vec_dec a (Z.sub 39 1) 0).
  rewrite (lo_subrange_unsigned a Hlt).
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - pagesize_bits + 1)) with 27%N.
  rewrite bv_wrap_small.
  - rewrite uint_unsigned. reflexivity.
  - rewrite uint_unsigned.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728) as -> by (vm_compute; reflexivity).
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)).
    change (2 ^ 12) with 4096.
    split.
    + apply Z.div_pos; [exact (proj1 (bv_unsigned_in_range 64 a)) | reflexivity].
    + apply Z.div_lt_upper_bound; [reflexivity |].
      change (4096 * 134217728) with 549755813888.
      eapply Z.lt_trans; [exact Hlt' | reflexivity].
Qed.


(* svpn[26:18] = 2 for a RAM address (a[38:30] = 2), i.e. it selects the
   level-2 gigapage PTE slot 2 for the identity map. *)

(* clearing the low 18 bits of a value < 2^27 keeps only bits [26:18]. *)

(* superpage mask fact (VPN side): masking svpn's in-superpage bits gives the
   0x80000 gigapage prefix. *)

(* superpage mask fact, raw-VPN form. *)

(* adding an offset that's a multiple of 8 to an 8-aligned vaddr/paddr keeps
   it 8-aligned -- used to derive every non-slot-0 saved-register-slot
   address's alignment from slot 0's (kernelvec/kerneltrap), instead of
   requiring each slot's alignment as an independent hypothesis. *)



(* is_aligned_vaddr and is_aligned_paddr are the same check on the same
   underlying bits (both just [Z.rem (uint addr) width = 0]) -- so a vaddr
   and paddr alignment hypothesis about the same value are duplicates of
   each other, not independent facts. *)
Lemma is_aligned_vaddr_paddr (x : mword 64) (w : Z) :
  is_aligned_vaddr (Virtaddr x) w = is_aligned_paddr (Physaddr x) w.
Proof. reflexivity. Qed.

(* 4-byte alignment of PC (one fact) implies its low-two-bits-zero forms:
   the Sail fetch path checks bit 0 and bit 1 of PC separately, but both
   follow from [is_aligned_vaddr (Virtaddr pc) 4]. *)
Lemma align4_low_bits (pc : mword 64) :
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  neq_vec (access_vec_dec pc 0) ('b"0") = false
  /\ neq_vec (access_vec_dec pc 1) ('b"0") = false.
Proof.
  unfold is_aligned_vaddr. intros H%Z.eqb_eq. rewrite uint_unsigned in H.
  apply Zrem_divides in H. destruct H as [k Hk].
  split; unfold neq_vec; rewrite negb_false_iff;
    unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word;
    rewrite MachineWord.MachineWord.eqb_true_iff; apply bv_eq;
    rewrite bv_extract_unsigned;
    replace (bv_unsigned ('b"0")) with 0%Z by (vm_compute; reflexivity);
    unfold bv_wrap, bv_modulus; rewrite Hk.
  - change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0%Z.
    rewrite Z.shiftr_0_r.
    replace (2 ^ Z.of_N 1)%Z with 2%Z by reflexivity.
    replace (4 * k)%Z with ((2 * k) * 2)%Z by lia. apply Z_mod_mult.
  - change (Z.of_N (MachineWord.MachineWord.Z_idx 1)) with 1%Z.
    rewrite (Z.shiftr_div_pow2 (4 * k) 1); [ | lia ].
    replace (2 ^ 1)%Z with 2%Z by reflexivity.
    replace (2 ^ Z.of_N 1)%Z with 2%Z by reflexivity.
    replace (4 * k)%Z with ((2 * k) * 2)%Z by lia.
    rewrite (Z.div_mul (2 * k) 2); [ | lia ].
    rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* 2-byte alignment -> bit 0 = 0.  Under the C extension the model's [jump_to]
   only needs the target's bit 0 clear (IALIGN = 2), so a 2-aligned target
   suffices for the compressed jump path ([exec_jump_to_zca]). *)
Lemma align2_low_bit (pc : mword 64) :
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  neq_vec (access_vec_dec pc 0) ('b"0") = false.
Proof.
  unfold is_aligned_vaddr. intros H%Z.eqb_eq. rewrite uint_unsigned in H.
  apply Zrem_divides in H. destruct H as [k Hk].
  unfold neq_vec; rewrite negb_false_iff;
    unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word;
    rewrite MachineWord.MachineWord.eqb_true_iff; apply bv_eq;
    rewrite bv_extract_unsigned;
    replace (bv_unsigned ('b"0")) with 0%Z by (vm_compute; reflexivity);
    unfold bv_wrap, bv_modulus; rewrite Hk.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0%Z.
  rewrite Z.shiftr_0_r.
  replace (2 ^ Z.of_N 1)%Z with 2%Z by reflexivity.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.


(* 4-byte alignment of a jump target -> the two low-bit facts the model's
   [jump_to] checks (bit 0 = 0 via [eq_vec .. 'b"0"], bit 1 = 0 via
   [bit_to_bool]).  Lets JAL / JALR state a single [is_aligned_paddr .. 4]
   premise instead of two per-bit facts. *)

(* ====================================================================== *)
(* ret_pc: THE canonical return-target pc.                                 *)
(*                                                                         *)
(* Every RISC-V return-family instruction lands on its saved return        *)
(* address with the low bit cleared: [jalr x0, 0(ra)] and the compressed   *)
(* [c.ret] compute [(ra + 0) & ~1]; [mret]/[sret] take the *epc value and   *)
(* clear bit 0.  [ret_pc v] is that value -- with NO useless               *)
(* [add_vec .. (sign_extend' 64 (zeros' 12))] (which adds zero, a noop).    *)
(* Used as the pc of EVERY return postcondition: leaf return WPs produce    *)
(* it, whole-function specs state it, and the swtch context predicate       *)
(* names its resume pc with it.  [ret_pc_jalr] bridges the raw form the     *)
(* model's jalr emits; [ret_pc_aligned] is the 2-alignment fact (bit 0 is   *)
(* cleared by construction), so return WPs need no alignment premise.       *)
(* ====================================================================== *)
Definition ret_pc (v : mword 64) : mword 64 := update_vec_dec v 0 ('b"0").

(* the [add_vec .. zeros] the model's [execute_JALR] produces collapses to
   [ret_pc]: adding the sign-extended 12-bit zero immediate is a noop. *)
Lemma add_vec_zeros_r (v : mword 64) :
  add_vec v (sign_extend' 64 (zeros' 12 : mword 12)) = v.
Proof.
  unfold add_vec, word_binop, with_word', with_word, MachineWord.MachineWord.add.
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

Lemma ret_pc_jalr (v : mword 64) :
  update_vec_dec (add_vec v (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0") = ret_pc v.
Proof. unfold ret_pc. rewrite add_vec_zeros_r. reflexivity. Qed.

Lemma bv_unsigned_b0 : bv_unsigned ('b"0" : mword 1) = 0.
Proof. vm_compute. reflexivity. Qed.

(* a return pc is always 2-aligned: [ret_pc] clears bit 0 by construction. *)
Lemma ret_pc_aligned (v : mword 64) :
  eq_vec (access_vec_dec (ret_pc v) 0) ('b"0") = true.
Proof.
  unfold ret_pc, eq_vec, access_vec_dec, access_mword_dec, update_vec_dec, update_mword_dec, get_word.
  rewrite MachineWord.MachineWord.eqb_true_iff. apply bv_eq.
  cbv [MachineWord.MachineWord.slice MachineWord.MachineWord.update_slice].
  rewrite !bv_extract_unsigned.
  rewrite !bv_concat_unsigned; [ | vm_compute; reflexivity | vm_compute; reflexivity ].
  rewrite bv_unsigned_b0.
  assert (Hz : forall b : bv 0, bv_unsigned b = 0).
  { intros b. pose proof (bv_unsigned_in_range _ b) as Hr.
    change (bv_modulus 0) with 1 in Hr. lia. }
  rewrite !Hz.
  rewrite !Z.shiftl_0_l !Z.shiftr_0_r !Z.lor_0_l !Z.lor_0_r.
  assert (Hk : Z.of_N (MachineWord.MachineWord.Z_idx 0 + MachineWord.MachineWord.Z_idx 1) = 1).
  { vm_compute. reflexivity. }
  rewrite Hk.
  rewrite Z.shiftl_mul_pow2; [ | lia ].
  change (2 ^ 1) with 2.
  unfold bv_wrap. change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  rewrite Z_mod_mult. reflexivity.
Qed.

(* THE BRIDGE: the j-th byte of the fetch window for the instruction at byte
   address [A] is the physical byte address [A + j].  This is what lets a
   per-byte image (keyed by absolute byte address) feed the WP fetch windows,
   which are phrased as [pa_add (fetch_pa pc) j]. *)

(* ---------------------------------------------------------------------- *)
(* Leaf 2: rX / rX_bits read leaf for x2 (sp), mirroring run_rX_x10.        *)

(* --- x2 (sp) register-write leaves (shared by AUIPC and LOAD, both write rd=x2). --- *)





(* Single SHARED, OPAQUE minstret bump.  The chunk WPs thread [minstret] through
   ~20 bumps; written inline as [fun x => if b then add_vec_int x 1 else x] the
   term is EXPONENTIAL -- [x] occurs in BOTH if-branches, so [bump^N] expands to
   2^N nodes once iApply beta/zeta-reduces it, which made the composer's
   [iApply (wp_ti_c3 ...)] blow up to ~83s.  As one OPAQUE constant [mbump b],
   [mbump b (mbump b (... x))] stays a LINEAR chain (c3 iApply: 83s -> 0.17s). *)
Definition mbump (b : bool) (x : mword 64) : mword 64 :=
  if b then add_vec_int x 1 else x.
Global Opaque mbump.

(* The 64-bit modulus as a literal.  [lia] cannot evaluate [bv_modulus 64],
   so every proof that needs the bound rewrites with this first. *)
Lemma bv_modulus64 : bv_modulus 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.

(* [add_vec] is commutative -- which operand the encoder put in rs1 is not
   something a proof should have to care about. *)
Lemma add_vec64_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof.
  apply bv_eq. rewrite !add_vec64_unsigned. f_equal. lia.
Qed.

(* ...and the no-wrap corollary of [moi64_unsigned]. *)
Lemma moi64_small (z : Z) :
  (0 <= z < 18446744073709551616)%Z -> bv_unsigned (mword_of_int z : mword 64) = z.
Proof. intro Hz. rewrite moi64_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* The same fact with the modulus spelled as a literal -- what a proof that
   reasons in plain [Z] wants, since [lia] cannot evaluate [bv_modulus]. *)
Lemma moi64_mod (z : Z) :
  bv_unsigned (mword_of_int z : mword 64) = (z `mod` 18446744073709551616)%Z.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* ====================================================================== *)
(* THE PMA CHECK'S ALIGNED OUTCOME.                                        *)
(*                                                                         *)
(* [pmaCheck] no longer answers "no exception" ([option ExceptionType]): it *)
(* answers a [Phys_Mem_Access_Info], the SPLITTING plan for the access --   *)
(* whether it must be decomposed into several single-copy-atomic            *)
(* operations, and at what granule.  The plan comes from [mag_pma_check],   *)
(* which consults the region's Misaligned Atomicity Granule PMA            *)
(* ([RiscvLang.pma_boot_ram_attrs]'s 16 bytes, per Zama16b).                *)
(*                                                                         *)
(* EVERY ACCESS THESE PROOFS PERFORM IS NATURALLY ALIGNED, and for an       *)
(* aligned access the granule never enters into it: [mag_pma_check]         *)
(* short-circuits on [is_aligned_paddr] and answers [CannotSplit] at        *)
(* granule 0 whatever the PMA and whatever the access type.  So the whole   *)
(* new axis collapses to this one constant, and the memory-access chain      *)
(* keeps its old shape: [split_misaligned] of [CannotSplit] is one          *)
(* operation of the full width ([split_misaligned_unsplit] below).          *)
(* ====================================================================== *)

Definition pma_ok_aligned : Phys_Mem_Access_Info :=
  {| Phys_Mem_Access_Info_splittable := CannotSplit;
     Phys_Mem_Access_Info_granule_size_exp := 0 |}.

Lemma exec_mag_pma_check_aligned (pma : PMA) (acc : MemoryAccessType mem_payload)
    (paddr : physaddr) (width : Z) (b : bool) s :
  exec (is_mag_applicable_access acc width) s = Some (b, s) ->
  is_aligned_paddr paddr width = true ->
  exec (mag_pma_check pma acc paddr width) s = Some (Ok (CannotSplit, 0), s).
Proof.
  intros Hma Halign.
  unfold mag_pma_check.
  rewrite (exec_bind_Some _ _ _ _ _ Hma).
  rewrite Halign. cbn [orb]. apply exec_returnM.
Qed.

(* The premise, for the access types the proofs use: each is a [returnM] of a
   closed boolean.  (The [Atomic] arms with mismatched read/write payloads are
   an [internal_error] and have no such fact -- which is why the lemma above
   takes it as a premise rather than proving it for every access.) *)
Lemma exec_is_mag_applicable_load_data (width : Z) s :
  exec (is_mag_applicable_access (Load Data) width) s = Some (Z.leb width xlen_bytes, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_store_data (width : Z) s :
  exec (is_mag_applicable_access (Store Data) width) s = Some (Z.leb width xlen_bytes, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_load_pte (width : Z) s :
  exec (is_mag_applicable_access (Load PageTableEntry) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_store_pte (width : Z) s :
  exec (is_mag_applicable_access (Store PageTableEntry) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_fetch (width : Z) s :
  exec (is_mag_applicable_access (InstructionFetch tt) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_cache (c : cacheop) (width : Z) s :
  exec (is_mag_applicable_access (CacheAccess c) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_lr (aq rl : bool) (width : Z) s :
  exec (is_mag_applicable_access (LoadReserved (aq, rl, Data)) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_sc (aq rl : bool) (width : Z) s :
  exec (is_mag_applicable_access (StoreConditional (aq, rl, Data)) width) s = Some (false, s).
Proof. apply exec_returnM. Qed.

Lemma exec_is_mag_applicable_amo (op : amoop) (aq rl : bool) (width : Z) s :
  exec (is_mag_applicable_access (Atomic (op, aq, rl, Data, Data)) width) s = Some (true, s).
Proof. apply exec_returnM. Qed.

Lemma exec_assert_exp'_true (msg : string) s :
  exec (Defs.assert_exp' true msg) s = Some (eq_refl, s).
Proof. unfold Defs.assert_exp'. cbn match. apply exec_returnM. Qed.

(* ---------------------------------------------------------------------- *)
(* THE PMA-CHECK PEEL, once.                                               *)
(*                                                                         *)
(* Every [exec (pmaCheck …) s = Some (Ok pma_ok_aligned, s)] lemma in the   *)
(* tree is this same six-step walk down [pmaCheck]'s early-return body:     *)
(* read [pma_regions]; resolve [matching_pma_region] to the region and take  *)
(* its overridden attributes; resolve the access arm to the PMA field that  *)
(* licenses the access (some arms first assert [not res_or_con], which is    *)
(* why the arm peel dispatches on whether an [assert_exp'] is present);     *)
(* rewrite that field to [true]; and run [mag_pma_check], which an ALIGNED  *)
(* access answers [CannotSplit].  The caller supplies the four facts and    *)
(* the region's constructor form.                                          *)
(*                                                                         *)
(* Hmatch : matching_pma_region … = Some <the destructed region>            *)
(* Hfield : the access's PMA permission field = true                        *)
(* Hmag   : exec (is_mag_applicable_access <acc> <width>) s = Some (_, s)   *)
(* Halign : is_aligned_paddr <paddr> <width> = true                         *)
(* ---------------------------------------------------------------------- *)
Ltac pma_ok_peel Hmatch Hfield Hmag Halign :=
  unfold pmaCheck; rewrite exec_catch_early_return;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)); cbn beta;
  rewrite Hmatch;
  cbn [PMA_Region_attributes] in Hfield |- *;
  cbn match;
  rewrite execR_bind; rewrite execR_returnR; cbn match beta;
  lazymatch goal with
  | |- context[Defs.assert_exp' _ _] =>
      (* the assert-bind is itself the LEFT operand of the canAccess bind, so
         [execR_liftR_seq] has nothing to match until [execR_bind] exposes it *)
      cbn [Riscv.rv64d.not negb];
      rewrite execR_bind;
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)); cbn beta;
      rewrite execR_returnR; cbn match beta
  | _ =>
      rewrite execR_bind; rewrite execR_returnR; cbn match beta
  end;
  rewrite Hfield; cbn [Riscv.rv64d.not negb];
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_mag_pma_check_aligned _ _ _ _ _ _ Hmag Halign));
  cbn beta; cbn match; rewrite execR_returnR; reflexivity.

(* [split_misaligned] at the plan an aligned access yields: ONE operation of
   the full width.  [CannotSplit] alone decides it -- the address and the
   granule never enter into it. *)
Lemma exec_split_misaligned_unsplit (addr : mword 64) (width g : Z) s :
  exec (split_misaligned (Physaddr addr) width g CannotSplit) s
    = Some ((1, width), s).
Proof.
  unfold split_misaligned.
  change (generic_eq CannotSplit CannotSplit) with true.
  cbn [orb]. apply exec_returnm.
Qed.

(* ...and the two projections of [pma_ok_aligned] that feed it. *)
Lemma pma_ok_aligned_splittable :
  Phys_Mem_Access_Info_splittable pma_ok_aligned = CannotSplit.
Proof. reflexivity. Qed.

Lemma pma_ok_aligned_granule :
  Phys_Mem_Access_Info_granule_size_exp pma_ok_aligned = 0.
Proof. reflexivity. Qed.

(* One split means offset 0 only, ascending. *)
Lemma misaligned_order_1 : misaligned_order 1 = (0, 0, 1).
Proof. vm_compute. reflexivity. Qed.

(* A FULL-WIDTH [update_subrange_vec_dec] over zeros is the value itself --
   which is what [checked_mem_read]'s split loop leaves in its accumulator on
   the (always taken, since every access here is aligned) one-split path.  The
   per-width [data2_id_*] copies scattered through the WP files are instances.

   IT CANNOT BE STATED WIDTH-GENERICALLY as it stands: the value argument's
   type is [mword (hi - lo + 1)], i.e. [mword (n - 1 - (0 - 1))], which is
   convertible to [mword n] only once the arithmetic computes -- so a symbolic
   width needs an [autocast] the statement would then have to carry.  Hence a
   tactic plus per-width instances; every width the tree reads or writes is
   closed except the [k]-generic access lemmas in [MemAccessGen] /
   [UserMemAccess], which will want the cast-carrying form. *)
Ltac usvd_zeros_full_tac :=
  apply bv_eq; unfold update_subrange_vec_dec; rewrite autocast_id;
  unfold to_word_idx, to_word; rewrite MachineWord.MachineWord.cast_idx_refl;
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice;
  erewrite bv_concat_unsigned by (cbn; lia);
  erewrite bv_concat_unsigned by (cbn; lia);
  rewrite !bv_unsigned_N_0;
  rewrite Z.shiftl_0_l; rewrite Z.shiftl_0_r; rewrite Z.lor_0_r; rewrite Z.lor_0_l;
  reflexivity.

Lemma usvd_zeros_full_8 (v : mword 8) :
  update_subrange_vec_dec (zeros' (8 * 1 * 1)) (8 * (0 + 1) * 1 - 1) (8 * 0 * 1) v = v.
Proof. usvd_zeros_full_tac. Qed.

Lemma usvd_zeros_full_16 (v : mword 16) :
  update_subrange_vec_dec (zeros' (8 * 1 * 2)) (8 * (0 + 1) * 2 - 1) (8 * 0 * 2) v = v.
Proof. usvd_zeros_full_tac. Qed.

Lemma usvd_zeros_full_32 (v : mword 32) :
  update_subrange_vec_dec (zeros' (8 * 1 * 4)) (8 * (0 + 1) * 4 - 1) (8 * 0 * 4) v = v.
Proof. usvd_zeros_full_tac. Qed.

Lemma usvd_zeros_full_64 (v : mword 64) :
  update_subrange_vec_dec (zeros' (8 * 1 * 8)) (8 * (0 + 1) * 8 - 1) (8 * 0 * 8) v = v.
Proof. usvd_zeros_full_tac. Qed.

(* The width-GENERIC form the note above says the [k]-generic access lemmas
   want.  It cannot be an instance of the tactic: with a symbolic width the
   value argument's [autocast] is a REAL transport ([8*width] to
   [8*width-1-(0-1)], equal only by [lia]), so [autocast_id] -- which needs the
   two indices to unify syntactically -- never fires, and the proof has to go
   through [bv_unsigned] instead. *)
Lemma zeros'_unsigned (n : Z) : bv_unsigned (zeros' n) = 0.
Proof. unfold zeros'; destruct n; reflexivity. Qed.

Lemma usvd_zeros_full_gen (n : Z) (w : mword n) :
  0 < n ->
  update_subrange_vec_dec (zeros' n) (n - 1) 0 (autocast (T := mword) w) = w.
Proof.
  intro Hn.
  assert (EN : MachineWord.MachineWord.Z_idx (n - 1 - (0 - 1))
               = MachineWord.MachineWord.Z_idx n) by (f_equal; lia).
  pose proof (bv_unsigned_in_range (MachineWord.MachineWord.Z_idx n) w) as Hr.
  apply bv_eq.
  unfold update_subrange_vec_dec.
  rewrite (autocast_unsigned _ n _ (MachineWord.MachineWord.idx_Z_idx n ltac:(lia))).
  unfold to_word_idx, Values.to_word.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  rewrite cast_idx_unsigned.
  rewrite !bv_concat_unsigned'.
  rewrite !bv_extract_unsigned.
  rewrite !zeros'_unsigned.
  rewrite !Z.shiftr_0_l.
  rewrite !bv_wrap_0.
  rewrite Z.shiftl_0_l.
  rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftl_0_r.
  rewrite (autocast_unsigned n (n - 1 - (0 - 1)) w ltac:(lia)).
  rewrite EN. rewrite N.add_0_l.
  rewrite bv_wrap_idemp. apply bv_wrap_small. exact Hr.
Qed.

(* ...and the same problem one level up: an [autocast] between two CONVERTIBLE
   but not syntactically equal widths, which a symbolic width leaves at the top
   of a reduced goal.  [autocast_id] cannot see it; [bv_unsigned] can. *)
Ltac kill_autocast :=
  repeat
    match goal with
    | |- context[@autocast _ ?m ?nn ?I (@autocast _ ?m2 ?m ?I2 ?x)] =>
        replace (@autocast mword m nn I (@autocast mword m2 m I2 x)) with x
          by (symmetry; apply bv_eq;
              rewrite (autocast_unsigned m nn _ ltac:(lia));
              rewrite (autocast_unsigned m2 m x ltac:(lia)); reflexivity)
    | |- context[@autocast _ ?m ?nn ?I ?x] =>
        replace (@autocast mword m nn I x) with x
          by (apply bv_eq; symmetry; apply (autocast_unsigned m nn x); lia)
    end.

(* The same identity in NUMERAL form, which is the shape the vmem-level
   [update_subrange_vec_dec (zeros' (8 * width)) (8 * access_width - 1) 0 …]
   normalises to.  [rewrite] is syntactic, so a proof reaches these by
   [change]-ing the arithmetic first ([change (8 * 1 * 8) with 64], …); the
   loop-shaped instances above are the ones [checked_mem_read] wants. *)


Lemma usvd_zeros32 (v : mword 32) : update_subrange_vec_dec (zeros' 32) 31 0 v = v.
Proof. usvd_zeros_full_tac. Qed.

Lemma usvd_zeros64 (v : mword 64) : update_subrange_vec_dec (zeros' 64) 63 0 v = v.
Proof. usvd_zeros_full_tac. Qed.

(* An access that does not cross a page boundary is not split at the vmem
   level: [split_on_page_boundary] answers (width, 0), so
   [vmem_read_addr]/[vmem_write_addr]'s [do_split_access] is false. *)

(* ====================================================================== *)
(* WRITING A BIT FIELD BACK WITH ITS OWN VALUE IS THE IDENTITY.            *)
(*                                                                         *)
(* The privileged CSR legalizers now re-write a field through a            *)
(* configuration-derived window before using it -- [legalize_satp] masks    *)
(* satp's PPN to [min (physaddr_bits - pagesize_bits) 44] bits, which at    *)
(* this platform's [physaddr_bits = 56] is the FULL 44-bit field.  So the   *)
(* mask is the identity, and the right way to absorb it is this lemma       *)
(* rather than restating [satp_legalized] around the mask: the legalized    *)
(* value does not depend on the platform constant, and no downstream satp   *)
(* fact should have to carry it.                                           *)
(*                                                                         *)
(* The arithmetic is factored into two lemmas over PLAIN [Z] variables --   *)
(* [lia] answers "Cannot find witness" as soon as a [bv_unsigned] is merely *)
(* in scope (durable-notes.md), so the bitvector level must hand it closed  *)
(* [Z] goals.                                                              *)
(* ====================================================================== *)

Lemma z_lor_split (u k : Z) :
  0 <= k -> 0 <= u ->
  Z.lor (Z.shiftl (Z.shiftr u k) k) (u mod 2 ^ k) = u.
Proof.
  intros Hk Hu. apply Z.bits_inj_iff'. intros n Hn.
  rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases n k) as [Hlt|Hge].
  - assert (Hhi : Z.testbit (Z.shiftl (Z.shiftr u k) k) n = false)
      by (apply Z.shiftl_spec_low; lia).
    assert (Hlo : Z.testbit (u mod 2 ^ k) n = Z.testbit u n)
      by (apply Z.mod_pow2_bits_low; lia).
    rewrite Hhi Hlo. reflexivity.
  - assert (Hhi : Z.testbit (Z.shiftl (Z.shiftr u k) k) n = Z.testbit u n).
    { rewrite Z.shiftl_spec; [| lia]. rewrite Z.shiftr_spec; [| lia].
      f_equal. lia. }
    assert (Hlo : Z.testbit (u mod 2 ^ k) n = false)
      by (apply Z.mod_pow2_bits_high; lia).
    rewrite Hhi Hlo. rewrite orb_false_r. reflexivity.
Qed.

Lemma z_field_writeback (u k m : Z) :
  0 <= k -> 0 <= m -> 0 <= u < 2 ^ (k + m) ->
  Z.lor (Z.shiftl ((Z.shiftr u k) mod 2 ^ m) k) (u mod 2 ^ k) = u.
Proof.
  intros Hk Hm Hu.
  assert (Hsm : (Z.shiftr u k) mod 2 ^ m = Z.shiftr u k).
  { apply Z.mod_small. split; [ apply Z.shiftr_nonneg; lia | ].
    assert (Hd : Z.shiftr u k = u / 2 ^ k) by (apply Z.shiftr_div_pow2; lia).
    rewrite Hd.
    apply Z.div_lt_upper_bound; [ apply Z.pow_pos_nonneg; lia | ].
    assert (Hp : 2 ^ k * 2 ^ m = 2 ^ (k + m)) by (symmetry; apply Z.pow_add_r; lia).
    rewrite Hp. lia. }
  rewrite Hsm. apply z_lor_split; lia.
Qed.

(* The bottom-window instance the satp legalizer needs: bits 43..0 of 64. *)
Lemma usvd_get_bottom_44 (v : mword 64) :
  update_subrange_vec_dec v 43 0 (subrange_vec_dec v 43 0) = v.
Proof.
  pose proof (bv_unsigned_in_range _ v) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  apply bv_eq. unfold update_subrange_vec_dec. rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  erewrite bv_concat_unsigned; [| cbn; lia].
  erewrite bv_concat_unsigned; [| cbn; lia].
  change (MachineWord.Z_idx 0 + MachineWord.Z_idx (43 - (0 - 1)))%N with 44%N.
  change (MachineWord.Z_idx 64 - MachineWord.Z_idx (43 - (0 - 1)) - MachineWord.Z_idx 0)%N with 20%N.
  change (MachineWord.Z_idx 0) with 0%N.
  unfold subrange_vec_dec, Operators_mwords.subrange_vec_dec, get_word.
  rewrite ?bv_extract_unsigned.
  rewrite Z.shiftl_0_r.
  rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  change (MachineWord.Z_idx (43 - 0 + 1)) with 44%N.
  rewrite ?bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N 0) with 0. change (Z.of_N 44) with 44. change (Z.of_N 20) with 20.
  rewrite !Z.shiftr_0_r.
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. rewrite Z.lor_0_r.
  apply (z_field_writeback (bv_unsigned v) 44 20); [ lia | lia | ].
  change (44 + 20) with 64. exact Hr.
Qed.

(* ====================================================================== *)
(* THE TOP-BIT / BOTTOM-FIELD TOWER, and the Z-level bit toolkit it needs. *)
(*                                                                         *)
(* The S-mode trap writes scause as TWO nested [update_subrange_vec_dec]s   *)
(* -- bit 63 gets the interrupt flag, then bits 62..0 get the zero-extended *)
(* cause code -- and the pair is exactly a CONCATENATION of the two fields, *)
(* which is what makes the resulting word a computable literal (a plain     *)
(* [vm_compute] on the tower cannot get anywhere: the OLD scause value is   *)
(* symbolic, and the fact that it is entirely overwritten is the content).  *)
(* [scause_tower] is that collapse; it is stated at the generic 64 = 1 + 63 *)
(* split and mentions nothing about interrupts, so it lives here beside     *)
(* [usvd_zeros64] / [usvd_get_bottom_44] rather than in the interrupt tier. *)
(*                                                                         *)
(* NONE of this can be handed to a bitvector automation: [bitblast] does    *)
(* not exist in stdpp 1.12, and [bv_solve] ends in [lia], which cannot see  *)
(* through [Z.lor] / [Z.shiftl].  Hence the hand-driven Z layer below.      *)
(* ====================================================================== *)

(* bit [k] of [x], read as the [k]-th binary digit.  The bridge from the
   [/ 2^k mod 2] shape [subrange_dec_unsigned] produces to [Z.testbit],
   where [Z.land_spec] is available. *)
Lemma z_bit_div (x k : Z) : 0 <= k -> x / 2 ^ k mod 2 = Z.b2z (Z.testbit x k).
Proof.
  intros Hk.
  rewrite <- (Z.shiftr_div_pow2 x k Hk).
  rewrite Zmod_odd.
  rewrite <- Z.bit0_odd.
  rewrite (Z.shiftr_spec x k 0 ltac:(lia)).
  rewrite Z.add_0_l.
  destruct (Z.testbit x k); reflexivity.
Qed.

Lemma bv_wrap_width0 (z : Z) : bv_wrap 0 z = 0.
Proof. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 0) with 1. apply Z.mod_1_r. Qed.

(* the top bit of the concatenation [b :: r] is [b] *)
Lemma z_top_bit_of_lor (bu r : Z) :
  0 <= bu < 2 -> 0 <= r < 2 ^ 63 ->
  bv_wrap 1 (Z.shiftr (Z.lor (Z.shiftl bu 63) r) 63) = bu.
Proof.
  intros Hb Hr.
  rewrite Z.shiftr_lor.
  rewrite (Z.shiftl_mul_pow2 bu 63 ltac:(lia)).
  rewrite (Z.shiftr_div_pow2 (bu * 2 ^ 63) 63 ltac:(lia)).
  rewrite (Z.div_mul bu (2 ^ 63) ltac:(apply Z.pow_nonzero; lia)).
  rewrite (Z.shiftr_div_pow2 r 63 ltac:(lia)).
  rewrite (Z.div_small r (2 ^ 63) ltac:(lia)).
  rewrite Z.lor_0_r.
  apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 1) with 2. lia.
Qed.

Lemma bv_wrap_63_range (z : Z) : 0 <= bv_wrap 63 z < 2 ^ 63.
Proof.
  pose proof (bv_wrap_in_range 63 z) as H.
  unfold bv_modulus in H. change (Z.of_N 63) with 63 in H. exact H.
Qed.

(* WRITING BIT 63 AND THEN BITS 62..0 IS A CONCATENATION -- whatever the old
   word was.  Three things in this script are not guessable and each cost a
   compile round:
     - [erewrite !bv_concat_unsigned] must be run TWICE, with
       [rewrite !bv_extract_unsigned] in between: the latter CREATES fresh
       [bv_unsigned (bv_concat ...)] subterms, so one [!] pass leaves the
       inner concat unrewritten and the symptom looks like a broken [rewrite !].
     - [Z.shiftr_0_r] ALSO rewrites [Z.shiftl x 0]: [Z.shiftr a n] is
       transparently [Z.shiftl a (-n)], so keyed matching hits [shiftl] and
       silently eats the wrong subterm.  Hence the explicitly instantiated
       [Z.shiftl_0_r] / [Z.shiftr_0_r] pair.
     - the finishing rewrite is written WITH HOLES on purpose, so its pattern
       matches whichever [bv_wrap 63 ?z] shape survives normalisation; a fully
       instantiated version is brittle.  And width normalisation needs three
       [change] layers: [MachineWord.Z_idx <lit>] -> [N] literal, then
       [N]-arithmetic, then [Z.of_N <lit>] -> [Z] literal. *)
Lemma scause_tower (v : mword 64) (b : mword 1) (w : mword 63) :
  update_subrange_vec_dec (update_subrange_vec_dec v (64 - 1) (64 - 1) b) (64 - 2) 0 w
  = concat_vec b w.
Proof.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  pose proof (bv_unsigned_in_range _ w) as Hw.
  pose proof (bv_unsigned_in_range _ v) as Hv.
  unfold bv_modulus in Hb, Hw, Hv.
  change (2 ^ Z.of_N (MachineWord.Z_idx 1)) with 2 in Hb.
  change (2 ^ Z.of_N (MachineWord.Z_idx 63)) with (2 ^ 63) in Hw.
  apply bv_eq.
  unfold update_subrange_vec_dec, concat_vec.
  rewrite ?autocast_id.
  unfold to_word_idx, Values.to_word.
  rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice,
         MachineWord.MachineWord.slice, MachineWord.MachineWord.concat.
  erewrite !bv_concat_unsigned by (cbn; lia).
  rewrite !bv_extract_unsigned.
  erewrite !bv_concat_unsigned by (cbn; lia).
  rewrite !bv_extract_unsigned.
  change (MachineWord.Z_idx 64) with 64%N.
  change (MachineWord.Z_idx 63) with 63%N.
  change (MachineWord.Z_idx 1) with 1%N.
  change (MachineWord.Z_idx 0) with 0%N.
  change (MachineWord.Z_idx (64 - 1)) with 63%N.
  change (MachineWord.Z_idx (64 - 1 - (64 - 1 - 1))) with 1%N.
  change (MachineWord.Z_idx (64 - 2 - (0 - 1))) with 63%N.
  change (0 + 63)%N with 63%N.
  change (64 - 63 - 0)%N with 1%N.
  change (63 + 1)%N with 64%N.
  change (64 - 1 - 63)%N with 0%N.
  change (1 + 63)%N with 64%N.
  change (Z.of_N 0) with 0.
  change (Z.of_N 63) with 63.
  change (Z.of_N 64) with 64.
  rewrite !bv_wrap_width0.
  rewrite Z.shiftl_0_l. rewrite Z.lor_0_l. rewrite Z.lor_0_r.
  rewrite ?(Z.shiftl_0_r (bv_unsigned w)). rewrite ?(Z.shiftr_0_r (bv_unsigned v)).
  rewrite (z_top_bit_of_lor (bv_unsigned b) _ Hb (bv_wrap_63_range _)).
  reflexivity.
Qed.

(* [zero_extend'] and a full-range [subrange_vec_dec] at width 44 -- the two
   wrappers [legalize_satp]'s PPN mask puts around the field before writing it
   back, both identities at this platform's [physaddr_bits]. *)
Lemma zero_extend'_id44 (a : mword 44) : zero_extend' 44 a = a.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.zero_extend].
  apply bv_eq. rewrite bv_zero_extend_unsigned. reflexivity. lia.
Qed.

Lemma subrange_full_32 (a : mword 32) : subrange_vec_dec a 31 0 = a.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec, Operators_mwords.subrange_vec_dec, get_word.
  rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  change (MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  rewrite ?bv_extract_unsigned.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 32)) with (2 ^ 32) in Hr.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. change (Z.of_N 32) with 32.
  rewrite Z.shiftr_0_r. apply Z.mod_small. exact Hr.
Qed.

(* The width-GENERIC full-width subrange: with a symbolic width the result
   type is [mword (n-1-0+1)], so the identity can only be stated up to the
   [autocast] that transports it back to [mword n]. *)

(* ...and the same, composed with the [autocast] that transports it back --
   the shape [checked_mem_write]'s split loop hands to [write_ram]. *)
Lemma subrange_full_gen_cast (n : Z) (a : mword n) :
  0 < n -> (autocast (T := mword) (subrange_vec_dec a (n - 1) 0) : mword n) = a.
Proof.
  intro Hn.
  pose proof (bv_unsigned_in_range (MachineWord.MachineWord.Z_idx n) a) as Hr.
  unfold bv_modulus in Hr.
  assert (Hpow : 2 ^ Z.of_N (MachineWord.MachineWord.Z_idx n) = 2 ^ n)
    by (cbn; rewrite Z2N.id; [ reflexivity | lia ]).
  rewrite Hpow in Hr.
  apply bv_eq.
  rewrite (autocast_unsigned (n - 1 - 0 + 1) n _ ltac:(lia)).
  rewrite (subrange_dec_unsigned_lo0 a (n - 1) (2 ^ n) ltac:(lia) ltac:(f_equal; lia)).
  apply Z.mod_small. exact Hr.
Qed.

Lemma subrange_full_8 (a : mword 8) : subrange_vec_dec a 7 0 = a.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec, Operators_mwords.subrange_vec_dec, get_word.
  rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  change (MachineWord.Z_idx (7 - 0 + 1)) with 8%N.
  rewrite ?bv_extract_unsigned.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 8)) with (2 ^ 8) in Hr.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. change (Z.of_N 8) with 8.
  rewrite Z.shiftr_0_r. apply Z.mod_small. exact Hr.
Qed.

Lemma subrange_full_64 (a : mword 64) : subrange_vec_dec a 63 0 = a.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec, Operators_mwords.subrange_vec_dec, get_word.
  rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  change (MachineWord.Z_idx (63 - 0 + 1)) with 64%N.
  rewrite ?bv_extract_unsigned.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. change (Z.of_N 64) with 64.
  rewrite Z.shiftr_0_r. apply Z.mod_small. exact Hr.
Qed.

Lemma subrange_full_44 (a : mword 44) : subrange_vec_dec a 43 0 = a.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec, Operators_mwords.subrange_vec_dec, get_word.
  rewrite ?autocast_id.
  unfold to_word_idx, to_word. rewrite ?MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  change (MachineWord.Z_idx (43 - 0 + 1)) with 44%N.
  rewrite ?bv_extract_unsigned.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 44)) with (2 ^ 44) in Hr.
  unfold bv_wrap, bv_modulus.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0. change (Z.of_N 44) with 44.
  rewrite Z.shiftr_0_r. apply Z.mod_small. exact Hr.
Qed.

(* ...and the satp instance itself: the PPN mask [legalize_satp] applies is a
   write-back of the field's own value. *)
Lemma satp_ppn_mask_id (v : mword 64) :
  _update_Satp64_PPN v (zero_extend' 44 (subrange_vec_dec (_get_Satp64_PPN v) 43 0)) = v.
Proof.
  unfold _update_Satp64_PPN, _get_Satp64_PPN.
  rewrite subrange_full_44. rewrite zero_extend'_id44.
  apply usvd_get_bottom_44.
Qed.

(* ====================================================================== *)
(* THE VMEM LEVEL'S PAGE-BOUNDARY SPLIT.                                   *)
(*                                                                         *)
(* [vmem_read_addr]/[vmem_write_addr] no longer split on the MAG (that moved *)
(* down into [checked_mem_read], see [pma_ok_aligned]); they split on a PAGE *)
(* boundary, via [split_on_page_boundary].  A naturally aligned access never  *)
(* crosses one, so the answer is always (width, 0) and the vmem level's      *)
(* [do_split_access] is false.  Proving that is the one real bitvector fact   *)
(* the bump needs: the page mask keeps only bits 63..12, and an 8-aligned     *)
(* address leaves at least 7 bytes of room inside its page.                   *)
(* ====================================================================== *)

Lemma z_pagemask_val : 18446744073709547520 = Z.shiftl (Z.ones 52) 12.
Proof. vm_compute. reflexivity. Qed.

Lemma z_land_pagemask (x : Z) :
  0 <= x -> x < 2 ^ 64 ->
  Z.land x 18446744073709547520 = Z.shiftl (Z.shiftr x 12) 12.
Proof.
  intros Hx0 Hx1. assert (Hx : 0 <= x < 2 ^ 64) by lia. rewrite z_pagemask_val.
  apply Z.bits_inj_iff'. intros n Hn.
  rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 12) as [Hlo|Hhi].
  - assert (Hm : Z.testbit (Z.shiftl (Z.ones 52) 12) n = false)
      by (apply Z.shiftl_spec_low; lia).
    assert (Hs : Z.testbit (Z.shiftl (Z.shiftr x 12) 12) n = false)
      by (apply Z.shiftl_spec_low; lia).
    rewrite Hm. rewrite Hs. apply andb_false_r.
  - assert (Hs : Z.testbit (Z.shiftl (Z.shiftr x 12) 12) n = Z.testbit x n).
    { rewrite Z.shiftl_spec; [| lia]. rewrite Z.shiftr_spec; [| lia].
      f_equal. lia. }
    rewrite Hs.
    destruct (Z.lt_ge_cases n 64) as [Hin|Hout].
    + assert (Hm : Z.testbit (Z.shiftl (Z.ones 52) 12) n = true).
      { rewrite Z.shiftl_spec; [| lia]. apply Z.ones_spec_low. lia. }
      rewrite Hm. apply andb_true_r.
    + assert (Hxb : Z.testbit x n = false).
      { destruct (Z.eq_dec x 0) as [->|Hnz]; [ apply Z.bits_0 | ].
        apply Z.bits_above_log2; [ lia | ].
        assert (Hlg : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
      rewrite Hxb. reflexivity.
Qed.

Lemma z_shiftr12_stable (u : Z) :
  0 <= u -> u mod 8 = 0 -> Z.shiftr u 12 = Z.shiftr (u + 7) 12.
Proof.
  intros Hu H8.
  assert (Hd : Z.shiftr u 12 = u / 4096) by (apply Z.shiftr_div_pow2; lia).
  assert (Hd' : Z.shiftr (u + 7) 12 = (u + 7) / 4096) by (apply Z.shiftr_div_pow2; lia).
  rewrite Hd. rewrite Hd'.
  (* the page remainder inherits the 8-alignment (4096 = 8 * 512), so it is at
     most 4088 and adding 7 cannot cross the page boundary *)
  assert (Hm8 : (u mod 4096) mod 8 = 0).
  { assert (Hz : u mod 4096 mod 8 = u mod 8)
      by (apply Z.mod_mod_divide; exists 512; reflexivity).
    rewrite Hz. exact H8. }
  assert (Hlt : u mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hge : 0 <= u mod 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hdv : (8 | u mod 4096)) by (apply Z.mod_divide; [ lia | exact Hm8 ]).
  destruct Hdv as [k Hk].
  assert (Hle : u mod 4096 <= 4088) by lia.
  assert (Hsplit : u = 4096 * (u / 4096) + u mod 4096) by (apply Z.div_mod; lia).
  assert (Hq : (4096 * (u / 4096) + (u mod 4096 + 7)) / 4096 = u / 4096).
  { rewrite (Z.mul_comm 4096 (u / 4096)).
    assert (Hda : ((u / 4096) * 4096 + (u mod 4096 + 7)) / 4096
                  = u / 4096 + (u mod 4096 + 7) / 4096)
      by (apply Z.div_add_l; lia).
    rewrite Hda.
    assert (Hs0 : (u mod 4096 + 7) / 4096 = 0) by (apply Z.div_small; lia).
    rewrite Hs0. lia. }
  assert (Heq : u + 7 = 4096 * (u / 4096) + (u mod 4096 + 7)) by lia.
  rewrite Heq. rewrite Hq. reflexivity.
Qed.

(* the mask [split_on_page_boundary] builds at width 64: ones with the low 12
   bits cleared *)
Lemma page_mask64_val :
  bv_unsigned (update_subrange_vec_dec ((ones 64) : bits 64) (pagesize_bits - 1) 0
                 (zeros' (12 - 1 - (0 - 1))) : mword 64)
  = 18446744073709547520.
Proof. vm_compute. reflexivity. Qed.


(* an 8-aligned value below 2^64 is at most 2^64 - 8, so +7 cannot wrap *)
Lemma z_align8_room (u : Z) : 0 <= u -> u < 2 ^ 64 -> u mod 8 = 0 -> u + 7 < 2 ^ 64.
Proof.
  intros H0 H1 H8.
  assert (Hdv : (8 | u)) by (apply Z.mod_divide; [ lia | exact H8 ]).
  destruct Hdv as [k Hk].
  assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite H64 in H1. rewrite H64. lia.
Qed.


Lemma exec_split_on_page_boundary_aligned8 (a : mword 64) s :
  is_aligned_vaddr (Virtaddr a) 8 = true ->
  exec (split_on_page_boundary a 8) s = Some ((8, 0), s).
Proof.
  intro Halign.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  (* the alignment, as a plain-Z fact about the address *)
  assert (Hal : bv_unsigned a mod 8 = 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_eq in Halign.
    rewrite uint_unsigned in Halign.
    assert (Hrm : Z.rem (bv_unsigned a) 8 = (bv_unsigned a) mod 8)
      by (apply Z.rem_mod_nonneg; [ exact Hr0 | lia ]).
    rewrite Hrm in Halign. exact Halign. }
  (* an 8-aligned address is at most 2^64 - 8, so a + 7 does not wrap *)
  assert (Hnw : bv_unsigned a + 7 < 2 ^ 64)
    by (apply z_align8_room; [ exact Hr0 | exact Hr1 | exact Hal ]).
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a 8) 1) = bv_unsigned a + 7).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    (* bv_wrap is idempotent through the add and the sub, so the whole thing is
       one wrap of [a + 8 - 1]; that does not wrap, since an 8-aligned [a] leaves
       room for +7. *)
    assert (Hw8 : bv_wrap 64 8 = 8)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hw8. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + 8 - 1 = bv_unsigned a + 7) by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0; lia | exact Hnw ]. }
  unfold split_on_page_boundary.
  assert (Hintra : eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                                        (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
                          (and_vec (sub_vec_int (add_vec_int a 8) 1)
                                   (update_subrange_vec_dec ((ones 64) : bits 64)
                                      (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true).
  { apply eq_vec_true_iff. apply bv_eq.
    rewrite !and_vec64_unsigned. rewrite page_mask64_val.
    rewrite Hsub.
    assert (Hnn : 0 <= bv_unsigned a + 7) by (clear - Hr0; lia).
    rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
    rewrite (z_land_pagemask (bv_unsigned a + 7) Hnn Hnw).
    rewrite <- (z_shiftr12_stable (bv_unsigned a) Hr0 Hal). reflexivity. }
  rewrite Hintra. apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* The same, WIDTH-GENERIC.  The vmem level is proved once per width in    *)
(* some files and generically in others, so both forms are wanted.  The    *)
(* width premise is [w] in {1,2,4,8} -- what the model itself constrains   *)
(* [vmem_read_addr]/[vmem_write_addr] to -- from which the two facts the    *)
(* argument needs follow: [0 < w] and [w | 4096].                           *)
(* ---------------------------------------------------------------------- *)

Definition vmem_width (w : Z) : Prop := w = 1 \/ w = 2 \/ w = 4 \/ w = 8.

Lemma vmem_width_pos (w : Z) : vmem_width w -> 0 < w.
Proof. intros [-> | [-> | [-> | ->]]]; lia. Qed.

Lemma vmem_width_page (w : Z) : vmem_width w -> (w | 4096).
Proof.
  intros [-> | [-> | [-> | ->]]].
  - exists 4096; reflexivity.
  - exists 2048; reflexivity.
  - exists 1024; reflexivity.
  - exists 512; reflexivity.
Qed.

Lemma vmem_width_le (w : Z) : vmem_width w -> w <= 8.
Proof. intros [-> | [-> | [-> | ->]]]; lia. Qed.

Lemma z_alignw_room (u w : Z) :
  0 <= u -> u < 2 ^ 64 -> vmem_width w -> u mod w = 0 -> u + (w - 1) < 2 ^ 64.
Proof.
  intros H0 H1 Hw H8.
  assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite H64 in H1. rewrite H64.
  (* case on the width so that [u = k * w] is LINEAR (lia cannot multiply two
     variables) *)
  destruct Hw as [-> | [-> | [-> | ->]]].
  - lia.
  - assert (Hdv : (2 | u)) by (apply Z.mod_divide; [ lia | exact H8 ]).
    destruct Hdv as [k Hk]. lia.
  - assert (Hdv : (4 | u)) by (apply Z.mod_divide; [ lia | exact H8 ]).
    destruct Hdv as [k Hk]. lia.
  - assert (Hdv : (8 | u)) by (apply Z.mod_divide; [ lia | exact H8 ]).
    destruct Hdv as [k Hk]. lia.
Qed.

Lemma z_shiftr12_stable_w (u w : Z) :
  0 <= u -> vmem_width w -> u mod w = 0 ->
  Z.shiftr u 12 = Z.shiftr (u + (w - 1)) 12.
Proof.
  intros Hu Hw H8.
  assert (Hpos : 0 < w) by (apply vmem_width_pos; exact Hw).
  assert (Hle : w <= 8) by (apply vmem_width_le; exact Hw).
  assert (Hpg : (w | 4096)) by (apply vmem_width_page; exact Hw).
  assert (Hd : Z.shiftr u 12 = u / 4096) by (apply Z.shiftr_div_pow2; lia).
  assert (Hd' : Z.shiftr (u + (w - 1)) 12 = (u + (w - 1)) / 4096)
    by (apply Z.shiftr_div_pow2; lia).
  rewrite Hd. rewrite Hd'.
  (* the page remainder inherits the w-alignment, so it is at most 4096 - w *)
  assert (Hmw : (u mod 4096) mod w = 0).
  { assert (Hz : u mod 4096 mod w = u mod w) by (apply Z.mod_mod_divide; exact Hpg).
    rewrite Hz. exact H8. }
  assert (Hlt : u mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hge : 0 <= u mod 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hle' : u mod 4096 <= 4096 - w).
  { destruct Hw as [-> | [-> | [-> | ->]]].
    - lia.
    - assert (Hdv : (2 | u mod 4096)) by (apply Z.mod_divide; [ lia | exact Hmw ]).
      destruct Hdv as [k Hk]. lia.
    - assert (Hdv : (4 | u mod 4096)) by (apply Z.mod_divide; [ lia | exact Hmw ]).
      destruct Hdv as [k Hk]. lia.
    - assert (Hdv : (8 | u mod 4096)) by (apply Z.mod_divide; [ lia | exact Hmw ]).
      destruct Hdv as [k Hk]. lia. }
  assert (Hsplit : u = 4096 * (u / 4096) + u mod 4096) by (apply Z.div_mod; lia).
  assert (Hq : (4096 * (u / 4096) + (u mod 4096 + (w - 1))) / 4096 = u / 4096).
  { rewrite (Z.mul_comm 4096 (u / 4096)).
    assert (Hda : ((u / 4096) * 4096 + (u mod 4096 + (w - 1))) / 4096
                  = u / 4096 + (u mod 4096 + (w - 1)) / 4096)
      by (apply Z.div_add_l; lia).
    rewrite Hda.
    assert (Hs0 : (u mod 4096 + (w - 1)) / 4096 = 0) by (apply Z.div_small; lia).
    rewrite Hs0. lia. }
  assert (Heq : u + (w - 1) = 4096 * (u / 4096) + (u mod 4096 + (w - 1))) by lia.
  rewrite Heq. rewrite Hq. reflexivity.
Qed.

Lemma exec_split_on_page_boundary_aligned (a : mword 64) (w : Z) s :
  vmem_width w ->
  is_aligned_vaddr (Virtaddr a) w = true ->
  exec (split_on_page_boundary a w) s = Some ((w, 0), s).
Proof.
  intros Hw Halign.
  assert (Hpos : 0 < w) by (apply vmem_width_pos; exact Hw).
  assert (Hle : w <= 8) by (apply vmem_width_le; exact Hw).
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  assert (Hal : bv_unsigned a mod w = 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_eq in Halign.
    rewrite uint_unsigned in Halign.
    assert (Hrm : Z.rem (bv_unsigned a) w = (bv_unsigned a) mod w)
      by (apply Z.rem_mod_nonneg; [ exact Hr0 | lia ]).
    rewrite Hrm in Halign. exact Halign. }
  assert (Hnw : bv_unsigned a + (w - 1) < 2 ^ 64)
    by (apply z_alignw_room; assumption).
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1) = bv_unsigned a + (w - 1)).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hww : bv_wrap 64 w = w)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hww. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + w - 1 = bv_unsigned a + (w - 1)) by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0 Hpos; lia | exact Hnw ]. }
  unfold split_on_page_boundary.
  assert (Hintra : eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                                        (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
                          (and_vec (sub_vec_int (add_vec_int a w) 1)
                                   (update_subrange_vec_dec ((ones 64) : bits 64)
                                      (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true).
  { apply eq_vec_true_iff. apply bv_eq.
    rewrite !and_vec64_unsigned. rewrite page_mask64_val.
    rewrite Hsub.
    assert (Hnn : 0 <= bv_unsigned a + (w - 1)) by (clear - Hr0 Hpos; lia).
    rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
    rewrite (z_land_pagemask (bv_unsigned a + (w - 1)) Hnn Hnw).
    rewrite <- (z_shiftr12_stable_w (bv_unsigned a) w Hr0 Hw Hal). reflexivity. }
  rewrite Hintra. apply exec_returnm.
Qed.
