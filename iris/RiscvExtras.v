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

Lemma sint64_moi32 (z : Z) : (0 <= z < 2^31)%Z ->
  sint (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite (sext64_moi32_unsigned z ltac:(lia)).
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.


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

(* the low 39 bits of a RAM address are the address itself (as a bv 39):
   [uint a < 2^39], so the [subrange 38:0] extraction loses nothing. *)
Lemma ram_subrange_unsigned (a : mword 64) :
  addr_is_ram a ->
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = uint a.
Proof.
  intros [Hlo Hhi]. rewrite uint_unsigned in Hlo, Hhi |- *. unfold ram_base, ram_size in *.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - 0 + 1)) with 39%N.
  apply bv_wrap_small. pose proof (bv_unsigned_in_range 64 a).
  change (bv_modulus 39) with 549755813888. lia.
Qed.

(* the same two facts for any LOW address (below MAXVA = 2^38 -- walk's
   premise; covers device vas that are not RAM) *)
Lemma lo_subrange_unsigned (a : mword 64) :
  uint a < 274877906944 ->
  bv_unsigned (subrange_vec_dec a (Z.sub 39 1) 0) = uint a.
Proof.
  intros Hlt. rewrite uint_unsigned in Hlt |- *.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (Z.sub 39 1 - 0 + 1)) with 39%N.
  apply bv_wrap_small.
  change (bv_modulus 39) with 549755813888.
  split; [exact (proj1 (bv_unsigned_in_range _ a)) |].
  eapply Z.lt_trans; [exact Hlt | reflexivity].
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
