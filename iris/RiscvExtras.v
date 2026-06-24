(* RiscvExtras.v -- shared, opcode-independent reductions & bitvector identities:
   mword/bv identities; the state-pure should_inc_minstret; the MMIO
   within_clint/sig/htif discharges; and the x2 (sp) register-write leaves. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
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
