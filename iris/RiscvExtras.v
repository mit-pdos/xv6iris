(* RiscvExtras.v -- shared, opcode-independent reductions & bitvector identities:
   mword/bv identities; the state-pure should_inc_minstret; the MMIO
   within_clint/sig/htif discharges; and the x2 (sp) register-write leaves. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
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
Lemma add_vec_slot0_zero (x : mword 64) :
  add_vec x (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = x.
Proof. apply bv_add_0_r. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* should_inc_minstret is state-pure: its result is fully determined by    *)
(* the mcountinhibit and minstretcfg cells.  Owning those two CSRs thus     *)
(* discharges the `should_inc` exec-condition (no `forall s0` needed).      *)
(* ---------------------------------------------------------------------- *)
Lemma exec_should_inc_M (mc : mword 32) (mcfg : mword 64) s :
  register_lookup mcountinhibit s.(sregs) = mc ->
  register_lookup minstretcfg s.(sregs) = mcfg ->
  exec (should_inc_minstret Machine) s
    = Some (andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                 (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")), s).
Proof.
  intros Hmc Hmcfg. unfold should_inc_minstret.
  assert (HA : exec ((read_reg mcountinhibit : M (mword 32)) >>=
                     (fun w__0 => returnM (eq_vec (_get_Counterin_IR w__0) ('b"0")))) s
               = Some (eq_vec (_get_Counterin_IR mc) ('b"0"), s)).
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcountinhibit s)). rewrite Hmc. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA).
  destruct (eq_vec (_get_Counterin_IR mc) ('b"0")) eqn:Ea; cbn [andb].
  - rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg minstretcfg s)). rewrite Hmcfg. apply exec_returnm.
  - reflexivity.
Qed.

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
  intros Hns Hw. unfold within_sig, plat_have_sig, __id. cbn [Riscv.rv64d.not negb].
  assert (Hf : (uint plat_sig_base <=? uint a) &&
               (uint a + w <=? uint plat_sig_base + uint plat_sig_size) = false).
  { destruct Hns as [H|H]; [apply andb_false_intro1|apply andb_false_intro2]; apply Z.leb_gt; lia. }
  rewrite Hf. apply exec_returnm.
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

(* Sv39 canonicality of any RAM address: since [uint a < 0x90000000 < 2^38],
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
Definition svpn_of (a : mword 64) : mword 27 :=
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits).

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

(* svpn[26:18] = 2 for a RAM address (a[38:30] = 2), i.e. it selects the
   level-2 gigapage PTE slot 2 for the identity map. *)
Lemma ram_svpn2 (a : mword 64) :
  addr_is_ram a ->
  subrange_vec_dec (svpn_of a) 26 18 = (mword_of_int 2 : mword 9).
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 18) with 18%N.
  rewrite bv_extract_unsigned.
  rewrite (svpn_of_unsigned a Hram).
  change (MachineWord.MachineWord.Z_idx (26 - 18 + 1)) with 9%N.
  assert (Hrhs : bv_unsigned (mword_of_int 2 : mword 9) = 2) by (vm_compute; reflexivity).
  rewrite Hrhs. rewrite uint_unsigned.
  rewrite (Z.shiftr_shiftr (bv_unsigned a) 12 18 ltac:(lia)).
  change (12 + 18) with 30.
  rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 30 ltac:(lia)).
  change (2 ^ 30) with 1073741824.
  assert (bv_unsigned a / 1073741824 = 2) as ->.
  { assert (2 <= bv_unsigned a / 1073741824) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 1073741824 < 3) by (apply Z.div_lt_upper_bound; lia). lia. }
  vm_compute. reflexivity.
Qed.

(* clearing the low 18 bits of a value < 2^27 keeps only bits [26:18]. *)
Lemma land_clear_low18 (y : Z) :
  0 <= y < 134217728 ->
  Z.land y 133955584 = Z.shiftl (Z.shiftr y 18) 18.
Proof.
  intros Hy. apply Z.bits_inj'. intros i Hi.
  assert (Hmm : 133955584 = Z.shiftl (Z.ones 9) 18) by (vm_compute; reflexivity).
  rewrite Hmm.
  rewrite Z.land_spec.
  rewrite (Z.shiftl_spec (Z.ones 9) 18 i ltac:(lia)).
  rewrite (Z.shiftl_spec (Z.shiftr y 18) 18 i ltac:(lia)).
  destruct (Z.leb_spec 18 i) as [Hge|Hlt].
  - rewrite (Z.shiftr_spec y 18 (i - 18) ltac:(lia)).
    replace (i - 18 + 18) with i by lia.
    rewrite (Z.testbit_ones_nonneg 9 (i - 18) ltac:(lia) ltac:(lia)).
    destruct (i - 18 <? 9) eqn:Hb.
    + apply andb_true_r.
    + rewrite andb_false_r. symmetry. apply Z.ltb_ge in Hb.
      assert (Hylt : y < 2 ^ 27) by (change (2 ^ 27) with 134217728; lia).
      exact (proj1 (Z.bounded_iff_bits_nonneg 27 y ltac:(lia) ltac:(lia)) Hylt i ltac:(lia)).
  - rewrite (Z.testbit_neg_r (Z.ones 9) (i - 18) ltac:(lia)).
    rewrite (Z.testbit_neg_r (Z.shiftr y 18) (i - 18) ltac:(lia)).
    apply andb_false_r.
Qed.

(* superpage mask fact (VPN side): masking svpn's in-superpage bits gives the
   0x80000 gigapage prefix. *)
Lemma ram_mask (a : mword 64) :
  addr_is_ram a ->
  and_vec (sign_extend' (57 - 12) (svpn_of a)) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45).
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  apply bv_eq.
  cbv [and_vec sign_extend' not_vec
       Operators_mwords.sign_extend Operators_mwords.exts_vec
       Operators_mwords.word_binop Operators_mwords.word_unop
       Operators_mwords.with_word' SailStdpp.Values.with_word to_word get_word
       MachineWord.MachineWord.sign_extend MachineWord.MachineWord.and MachineWord.MachineWord.not].
  rewrite bv_and_unsigned.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_not_unsigned.
  unfold bv_signed.
  rewrite (svpn_of_unsigned a Hram).
  rewrite uint_unsigned.
  assert (Hlit1 : bv_unsigned (mword_of_int 262143 : mword 45) = 262143) by (vm_compute; reflexivity).
  rewrite Hlit1.
  assert (Hlit2 : bv_unsigned (mword_of_int 524288 : mword 45) = 524288) by (vm_compute; reflexivity).
  rewrite Hlit2.
  assert (Hmask45 : bv_wrap (MachineWord.MachineWord.Z_idx (57 - 12)) (Z.lnot 262143)
                    = Z.shiftl (Z.ones 27) 18) by (vm_compute; reflexivity).
  rewrite Hmask45.
  set (x := Z.shiftr (bv_unsigned a) 12).
  assert (Hxlo : 0 <= x) by (unfold x; apply Z.shiftr_nonneg; lia).
  assert (Hxhi : x < 589824).
  { unfold x. rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)).
    change (2 ^ 12) with 4096. apply Z.div_lt_upper_bound. lia. lia. }
  assert (Hsw : bv_swrap (MachineWord.MachineWord.Z_idx 27) x = x).
  { apply bv_swrap_small.
    assert (bv_half_modulus (MachineWord.MachineWord.Z_idx 27) = 67108864) as -> by (vm_compute; reflexivity).
    lia. }
  rewrite Hsw.
  assert (Hw : bv_wrap (MachineWord.MachineWord.Z_idx (57 - 12)) x = x).
  { apply bv_wrap_small.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx (57 - 12)) = 35184372088832) as -> by (vm_compute; reflexivity).
    lia. }
  rewrite Hw.
  assert (Hx18 : Z.shiftr x 18 = 2).
  { unfold x. rewrite (Z.shiftr_shiftr (bv_unsigned a) 12 18 ltac:(lia)). change (12 + 18) with 30.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 30 ltac:(lia)). change (2 ^ 30) with 1073741824.
    assert (2 <= bv_unsigned a / 1073741824) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 1073741824 < 3) by (apply Z.div_lt_upper_bound; lia). lia. }
  change 524288 with (2 ^ 19).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  rewrite (Z.shiftl_spec (Z.ones 27) 18 i Hi).
  rewrite (Z.pow2_bits_eqb 19 i ltac:(lia)).
  destruct (Z.ltb_spec i 18) as [Hlt | Hge].
  - rewrite (Z.testbit_neg_r (Z.ones 27) (i - 18) ltac:(lia)).
    rewrite andb_false_r.
    destruct (Z.eqb_spec 19 i); [lia | reflexivity].
  - assert (Hxi : Z.testbit x i = Z.testbit 2 (i - 18)).
    { replace i with ((i - 18) + 18) at 1 by lia.
      rewrite <- (Z.shiftr_spec x 18 (i - 18) ltac:(lia)). rewrite Hx18. reflexivity. }
    rewrite Hxi.
    rewrite (Z.testbit_ones_nonneg 27 (i - 18) ltac:(lia) ltac:(lia)).
    change 2 with (2 ^ 1). rewrite (Z.pow2_bits_eqb 1 (i - 18) ltac:(lia)).
    destruct (Z.eqb_spec 1 (i - 18)) as [He | Hne].
    + assert (i = 19) by lia. subst.
      rewrite (proj2 (Z.ltb_lt (19 - 18) 27) ltac:(lia)).
      destruct (Z.eqb_spec 19 19); [reflexivity | lia].
    + cbn [andb]. destruct (Z.eqb_spec 19 i); [lia | reflexivity].
Qed.

(* superpage mask fact, raw-VPN form. *)
Lemma ram_mvpn (a : mword 64) :
  addr_is_ram a ->
  sign_extend' 45 (and_vec (svpn_of a) (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45).
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi]. rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  assert (Hand : and_vec (svpn_of a) (not_vec (zero_extend' 27 (ones 18))) = (mword_of_int 0x80000 : mword 27)).
  { apply bv_eq.
    cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word' SailStdpp.Values.with_word
         to_word get_word MachineWord.MachineWord.and].
    rewrite bv_and_unsigned.
    rewrite (svpn_of_unsigned a Hram).
    assert (HM : bv_unsigned (not_vec (zero_extend' 27 (ones 18)) : mword 27) = 133955584) by (vm_compute; reflexivity).
    rewrite HM. rewrite uint_unsigned.
    assert (Hrhs : bv_unsigned (mword_of_int 0x80000 : mword 27) = 524288) by (vm_compute; reflexivity).
    rewrite Hrhs.
    rewrite land_clear_low18.
    2:{ rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)). change (2^12) with 4096.
        split. apply Z.div_pos. lia. lia. apply Z.div_lt_upper_bound. lia. lia. }
    rewrite (Z.shiftr_shiftr (bv_unsigned a) 12 18 ltac:(lia)). change (12 + 18) with 30.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 30 ltac:(lia)). change (2 ^ 30) with 1073741824.
    assert (bv_unsigned a / 1073741824 = 2) as ->.
    { assert (2 <= bv_unsigned a / 1073741824) by (apply Z.div_le_lower_bound; lia).
      assert (bv_unsigned a / 1073741824 < 3) by (apply Z.div_lt_upper_bound; lia). lia. }
    vm_compute. reflexivity. }
  rewrite Hand. apply bv_eq. vm_compute. reflexivity.
Qed.

(* adding an offset that's a multiple of 8 to an 8-aligned vaddr/paddr keeps
   it 8-aligned -- used to derive every non-slot-0 saved-register-slot
   address's alignment from slot 0's (kernelvec/kerneltrap), instead of
   requiring each slot's alignment as an independent hypothesis. *)
Lemma align8_add_offset_unsigned (x off : mword 64) (k : Z) :
  bv_unsigned off = 8 * k ->
  Z.rem (bv_unsigned x) 8 = 0 ->
  Z.rem (bv_unsigned (add_vec x off)) 8 = 0.
Proof.
  intros Hoff H.
  apply Zrem_divides in H. destruct H as [k' Hk'].
  cbv [add_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word MachineWord.MachineWord.add].
  apply Zrem_divides.
  rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Hk' Hoff.
  replace (8 * k' + 8 * k) with (8 * (k' + k)) by ring.
  change (Z.of_N 64) with 64.
  replace (2 ^ 64) with (8 * 2305843009213693952) by (vm_compute; reflexivity).
  assert (Hmm : (8 * (k' + k)) mod (8 * 2305843009213693952)
                = 8 * ((k' + k) mod 2305843009213693952)).
  { apply Z.mul_mod_distr_l; lia. }
  rewrite Hmm.
  eexists. reflexivity.
Qed.

Lemma align8_vaddr_add_offset (x off : mword 64) (k : Z) :
  bv_unsigned off = 8 * k ->
  is_aligned_vaddr (Virtaddr x) 8 = true ->
  is_aligned_vaddr (Virtaddr (add_vec x off)) 8 = true.
Proof.
  unfold is_aligned_vaddr. intros Hoff H%Z.eqb_eq.
  rewrite uint_unsigned in H. rewrite uint_unsigned.
  apply Z.eqb_eq. apply (align8_add_offset_unsigned x off k Hoff H).
Qed.


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

(* THE BRIDGE: the j-th byte of the fetch window for the instruction at byte
   address [A] is the physical byte address [A + j].  This is what lets a
   per-byte image (keyed by absolute byte address) feed the WP fetch windows,
   which are phrased as [pa_add (fetch_pa pc) j]. *)
Lemma pa_add_fetch_mword (A : Z) (j : nat) :
  pa_add (fetch_pa (mword_of_int A)) j = mword_of_int (A + Z.of_nat j).
Proof. unfold pa_add. rewrite fetch_pa_id. apply avi_mword. Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 2: rX / rX_bits read leaf for x2 (sp), mirroring run_rX_x10.        *)

(* --- x2 (sp) register-write leaves (shared by AUIPC and LOAD, both write rd=x2). --- *)
Lemma wX_x2_eq (v : mword 64) :
  wX (Regno 2) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x2) (regval_into_reg v)) (returnM tt).
Proof. reflexivity. Qed.

Lemma run_wX_x2 s (v : mword 64) :
  run (wX (Regno 2) v) s tt (set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof.
  rewrite wX_x2_eq. apply run_bind0.
  exists (set_reg s (R_bitvector_64 x2) (regval_into_reg v)). split; split; reflexivity.
Qed.

Lemma exec_wX_x2 s (v : mword 64) :
  exec (wX (Regno 2) v) s = Some (tt, set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof.
  rewrite wX_x2_eq.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bitvector_64 x2) _ s)).
  apply exec_returnm.
Qed.

Lemma run_wX_bits_x2 (i : mword 5) s (v : mword 64) :
  uint i = 2 ->
  run (wX_bits (Regidx i) v) s tt (set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply run_wX_x2. Qed.

Lemma exec_wX_bits_x2 (i : mword 5) s (v : mword 64) :
  uint i = 2 ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply exec_wX_x2. Qed.

(* Single SHARED, OPAQUE minstret bump.  The chunk WPs thread [minstret] through
   ~20 bumps; written inline as [fun x => if b then add_vec_int x 1 else x] the
   term is EXPONENTIAL -- [x] occurs in BOTH if-branches, so [bump^N] expands to
   2^N nodes once iApply beta/zeta-reduces it, which made the composer's
   [iApply (wp_ti_c3 ...)] blow up to ~83s.  As one OPAQUE constant [mbump b],
   [mbump b (mbump b (... x))] stays a LINEAR chain (c3 iApply: 83s -> 0.17s). *)
Definition mbump (b : bool) (x : mword 64) : mword 64 :=
  if b then add_vec_int x 1 else x.
Global Opaque mbump.
