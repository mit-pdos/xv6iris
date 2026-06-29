(* RiscvExtras.v -- shared, opcode-independent reductions & bitvector identities:
   mword/bv identities; the state-pure should_inc_minstret; the MMIO
   within_clint/sig/htif discharges; and the x2 (sp) register-write leaves. *)
From Stdlib Require Import Eqdep_dec ZArith Zquot Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
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
Lemma mbump_eq (b : bool) (x : mword 64) : mbump b x = if b then add_vec_int x 1 else x.
Proof. reflexivity. Qed.
Global Opaque mbump.
