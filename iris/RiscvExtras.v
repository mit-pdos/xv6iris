(* RiscvExtras.v -- shared, opcode-independent reductions & bitvector identities:
   mword/bv identities; the state-pure should_inc_minstret; the MMIO
   within_clint/sig/htif discharges; and the x2 (sp) register-write leaves. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
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
Lemma pma_access_ram_byte (a : mword 64) : addr_is_ram a -> pma_ram_access a 1.
Proof.
  intros [Hlo Hhi].
  exact (conj (pma_width_ok 1 eq_refl eq_refl)
              (conj Hlo (pma_fit_byte (uint a) Hhi))).
Qed.

(* the same class from the RANGE BOUNDS themselves, where the applier has
   already computed them (several memory leaves derive an [Hlo]/[Hfit] pair
   for their PMP range match and can reuse it here). *)
Lemma pma_access_ram_fit (a : mword 64) (n : Z) :
  (ram_base <= uint a)%Z -> (uint a + n <= ram_base + ram_size)%Z ->
  1 <= n <= 4096 -> pma_ram_access a n.
Proof. intros Hlo Hfit Hn. exact (conj Hn (conj Hlo Hfit)). Qed.

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
Lemma ram_canonical (a : mword 64) :
  addr_is_ram a ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false.
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  cbn [bits_of_virtaddr].
  unfold neq_vec. rewrite negb_false_iff. unfold eq_vec.
  rewrite MachineWord.MachineWord.eqb_true_iff. apply bv_eq. symmetry.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold bv_signed.
  rewrite (ram_subrange_unsigned a Hram).
  assert (Hsw : bv_swrap (39 - 0) (uint a) = uint a).
  { apply bv_swrap_small. rewrite uint_unsigned.
    assert (bv_half_modulus (39 - 0) = 274877906944) as -> by (vm_compute; reflexivity). lia. }
  rewrite Hsw. rewrite uint_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Hr.
  assert (bv_modulus 64 = 18446744073709551616) as E by (vm_compute; reflexivity).
  rewrite E in Hr |- *. lia.
Qed.

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

Lemma aligned2_jump_bit (a : mword 64) :
  is_aligned_paddr (Physaddr a) 2 = true ->
  eq_vec (access_vec_dec a 0) ('b"0") = true.
Proof.
  intros H. pose proof (align2_low_bit a H) as H0.
  unfold neq_vec in H0. apply negb_false_iff in H0. exact H0.
Qed.

(* 4-byte alignment of a jump target -> the two low-bit facts the model's
   [jump_to] checks (bit 0 = 0 via [eq_vec .. 'b"0"], bit 1 = 0 via
   [bit_to_bool]).  Lets JAL / JALR state a single [is_aligned_paddr .. 4]
   premise instead of two per-bit facts. *)
Lemma aligned4_jump_bits (a : mword 64) :
  is_aligned_paddr (Physaddr a) 4 = true ->
  eq_vec (access_vec_dec a 0) ('b"0") = true /\
  bit_to_bool (access_vec_dec a 1) = false.
Proof.
  intros H. destruct (align4_low_bits a H) as [H0 H1].
  unfold neq_vec in H0, H1.
  apply negb_false_iff in H0. apply negb_false_iff in H1.
  split; [ exact H0 |].
  unfold bit_to_bool, eq_vec, get_word in H1.
  rewrite MachineWord.MachineWord.eqb_true_iff in H1.
  rewrite H1. reflexivity.
Qed.

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
      cbn [Riscv.rv64d.not negb];
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)); cbn beta;
      rewrite execR_bind; rewrite execR_returnR; cbn match beta
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
