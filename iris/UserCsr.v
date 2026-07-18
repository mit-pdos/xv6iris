(* UserCsr.v -- CSR access at User privilege: the totality facts for the
   CSRReg / CSRImm families.

   VALUES NEVER MATTER (safety only): a permitted CSR access at U is a
   RETIRING READ of an existential value (the counter shadows, when the
   counter-enable bits allow them); everything else is Illegal.  The
   target statements and the proof driver are recorded in
   iris/CLAUDE.md (§CSR-AT-U PLAN): destruct each dispatch guard
   [eq_vec csr ADDR] with eqn:, SUBSTITUTE csr := ADDR in the true
   branch (everything downstream reduces concretely), chain the false
   branches linearly; the priv-bits compare is destructed first and
   kills every non-U-addressed csr in one split.

   §1 holds the extension-gate PROBE reductions the U-addressed clauses
   need: the xv6 config pins make each gate a closed boolean.           *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RiscvExtras WpGpr WpLeafCommon UserBits.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Extension-gate probes at the xv6 config.                            *)
(* ===================================================================== *)

(* Zfinx is not hart-supported: the gate is a closed false. *)
Lemma exec_currentlyEnabled_Zfinx (s : mstate) :
  exec (currentlyEnabled Ext_Zfinx) s = Some (false, s).
Proof. reflexivity. Qed.

Lemma exec_hartSupports_F (s : mstate) :
  exec (hartSupports Ext_F) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_F) 0) with true by reflexivity.
  cbn match.
  first [ apply exec_returnM
        | rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s));
          apply exec_returnM
        | reflexivity ].
Qed.

(* F is hart-supported and misa.F is set, but the FS = Off pin turns the
   gate false BEFORE the Zicsr recursion (and_boolM short-circuits), so
   the fflags/frm/fcsr clauses are ILLEGAL at U. *)
Lemma exec_currentlyEnabled_F_off (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  exec (currentlyEnabled Ext_F) s = Some (false, s).
Proof.
  intros Hms Hfs.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_F) 0) with true.
  cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_F s)).
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_F (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb;
    [ | reflexivity ].
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
      rewrite Hms. apply exec_returnM. }
  assert (Hneq : neq_vec (_get_Mstatus_FS ms_v) ('b"00") = false).
  { unfold neq_vec. rewrite Hfs. reflexivity. }
  rewrite Hneq.
  reflexivity.
Qed.

(* the hart-supported flags the U-addressed gates consult *)
Lemma exec_hartSupports_Zicntr (s : mstate) :
  exec (hartSupports Ext_Zicntr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicfiss (s : mstate) :
  exec (hartSupports Ext_Zicfiss) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zimop (s : mstate) :
  exec (hartSupports Ext_Zimop) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zimop) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zaamo (s : mstate) :
  exec (hartSupports Ext_Zaamo) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zaamo) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_A (s : mstate) :
  exec (hartSupports Ext_A) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_A) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

(* limit-instantiated recursive probes (the Zicfiss clause runs its
   sub-probes at measure-1 = 1, and Zaamo's Ext_A at 0) *)
Lemma exec_rec_cE_Zicsr_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  exec (_rec_currentlyEnabled Ext_Zicsr 1 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_rec_cE_Zimop_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  exec (_rec_currentlyEnabled Ext_Zimop 1 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_hartSupports_Zimop.
Qed.

Lemma exec_rec_cE_A_0 (s : mstate) (acc : Acc (Zwf 0) 0) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (_rec_currentlyEnabled Ext_A 0 acc) s = Some (true, s).
Proof.
  intro Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_A s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). cbn beta.
  rewrite Hmisa.
  replace (eq_vec (_get_Misa_A MISA_C) ('b"1")) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zaamo_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (_rec_currentlyEnabled Ext_Zaamo 1 acc) s = Some (true, s).
Proof.
  intro Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  unfold or_boolM.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zaamo s)). cbn beta. cbn match.
  apply exec_rec_cE_A_0. exact Hmisa.
Qed.

(* the two gates the U-addressed CSR clauses actually consult *)
Lemma exec_currentlyEnabled_Zicntr (s : mstate) :
  exec (currentlyEnabled Ext_Zicntr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicntr s)).
  apply exec_rec_cE_Zicsr.
Qed.

Lemma exec_currentlyEnabled_Zicfiss (s : mstate) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (currentlyEnabled Ext_Zicfiss) s = Some (true, s).
Proof.
  intro Hmisa.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfiss s)).
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_rec_cE_Zicsr_1 s _)).
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_rec_cE_Zimop_1 s _)).
  apply exec_rec_cE_Zaamo_1. exact Hmisa.
Qed.

(* Zve32x: hart-SUPPORTED here, but the gate reads mstatus.VS -- the
   VS = Off pin turns it false (parallel to the FS pin for F). *)
Lemma exec_hartSupports_Zve32x (s : mstate) :
  exec (hartSupports Ext_Zve32x) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zve32x) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  match goal with
  | |- exec (returnM ?v) _ = _ =>
      replace v with true by (vm_compute; reflexivity)
  end.
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zvl32b_0 (s : mstate) (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zvl32b 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  match goal with
  | |- exec ?m _ = _ =>
      first [ apply exec_returnM
            | match m with
              | returnM ?v =>
                  replace v with true by (vm_compute; reflexivity)
              end; apply exec_returnM ]
  end.
Qed.

Lemma exec_currentlyEnabled_Zve32x_off (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  exec (currentlyEnabled Ext_Zve32x) s = Some (false, s).
Proof.
  intros Hms Hvs.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zve32x) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zve32x s)).
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_rec_cE_Zvl32b_0 s _)).
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
      rewrite Hms. apply exec_returnM. }
  assert (Hneq : neq_vec (_get_Mstatus_VS ms_v) ('b"00") = false).
  { unfold neq_vec. rewrite Hvs. reflexivity. }
  rewrite Hneq.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The check-chain component reductions.                               *)
(* ===================================================================== *)

(* the privilege gate at User: pure in the ADDRESS bits -- 'b00 ≥u
   csrPriv csr, i.e. true iff bits 9:8 are 00 *)
Lemma exec_check_CSR_priv_U (csr : mword 12) (s : mstate) :
  exec (check_CSR_priv csr User) s
    = Some (zopz0zKzJ_u ('b"00") (csrPriv csr), s).
Proof.
  unfold check_CSR_priv, privLevel_to_CSR_privbits. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"00" : mword 2) s)). cbn beta.
  apply exec_returnM.
Qed.

(* feature_enabled_for_priv at U, totality: SOME result comes out
   whatever the enable bits are (all booleans destructed up front). *)
Lemma exec_feature_U_total (m sb h : mword 1) (s : mstate) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists r, exec (feature_enabled_for_priv User m sb h) s = Some (r, s).
Proof.
  intro HES.
  unfold feature_enabled_for_priv. cbn match.
  unfold and_boolM, or_boolM.
  destruct (eq_vec m ('b"1")) eqn:E1.
  - (* m-bit set: the S/senv disjunct decides *)
    destruct (eq_vec sb ('b"1")) eqn:E2.
    + eexists.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
          cbn beta. cbn match.
          erewrite exec_bind_Some.
          2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta.
              apply exec_returnM. }
          cbn beta. cbn [not negb]. cbn match.
          apply exec_returnM. }
      cbn beta. cbv zeta.
      apply exec_returnM.
    + eexists.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
          cbn beta. cbn match.
          erewrite exec_bind_Some.
          2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta.
              apply exec_returnM. }
          cbn beta. cbn [not negb]. cbn match.
          apply exec_returnM. }
      cbn beta. cbv zeta.
      apply exec_returnM.
  - (* m-bit clear: short-circuit false *)
    eexists.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
        cbn beta. cbn match.
        apply exec_returnM. }
    cbn beta. cbv zeta.
    apply exec_returnM.
Qed.

(* counter enables at U: SOME boolean comes out (values never matter) *)
Lemma exec_counter_enabled_U_total (i : Z) (s : mstate) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists en : bool, exec (counter_enabled i User) s = Some (en, s).
Proof.
  intro HES.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)). cbn beta.
  unfold feature_enabled_for_priv_bool.
  destruct (exec_feature_U_total
              (access_vec_dec (register_lookup mcounteren s.(sregs)) i)
              (access_vec_dec (register_lookup scounteren s.(sregs)) i)
              ('b"0") s HES) as [r Hr].
  eexists.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  apply exec_returnM.
Qed.

(* ssp (0x011) is inaccessible: Zicfiss is enabled, but MENVCFG_S has SSE
   clear, so the User arm's menvcfg conjunct is false (and_boolM
   short-circuits before senvcfg is consulted). *)
Lemma exec_is_ssp_accessible_U_off (s : mstate) :
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (is_ssp_accessible User) s = Some (false, s).
Proof.
  intros Hmisa Hmenv.
  unfold is_ssp_accessible.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicfiss s Hmisa)).
  cbn match.
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
      rewrite Hmenv. apply exec_returnM. }
  match goal with
  | |- context [ if ?g then _ else _ ] =>
      replace g with false by (vm_compute; reflexivity)
  end.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The traversal groundwork: address-bit arithmetic.                   *)
(* ===================================================================== *)

(* the two CSR-address subranges, as unsigned arithmetic *)
Lemma sub114_unsigned (x : mword 12) :
  bv_unsigned (subrange_vec_dec x 11 4) = (bv_unsigned x / 16) mod 256.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (11 - 4 + 1))) with 256.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 4)) with 4.
  change (2 ^ 4) with 16.
  reflexivity.
Qed.

Lemma csrPriv_unsigned (x : mword 12) :
  bv_unsigned (csrPriv x) = (bv_unsigned x / 256) mod 4.
Proof.
  unfold csrPriv, subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (9 - 8 + 1))) with 4.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 8.
  change (2 ^ 8) with 256.
  reflexivity.
Qed.

(* a PMP-file subrange guard contradicts the U priv gate: the address's
   bits 9:8 sit inside the matched high byte (0x3A-0x3E all have bits
   5:4 = 11, i.e. h / 16 = 3). *)
Lemma pmp_subrange_dead (csr : mword 12) (h : mword 8) :
  eq_vec (subrange_vec_dec csr 11 4) h = true ->
  bv_unsigned h / 16 = 3 ->
  zopz0zKzJ_u ('b"00") (csrPriv csr) = true -> False.
Proof.
  intros E Hh EP.
  apply eq_vec_true_iff in E.
  apply (f_equal bv_unsigned) in E.
  rewrite sub114_unsigned in E.
  unfold zopz0zKzJ_u in EP. apply Z.geb_le in EP.
  rewrite !(uint_unsigned_n _) in EP.
  rewrite csrPriv_unsigned in EP.
  change (bv_unsigned ('b"00" : mword 2)) with 0 in EP.
  set (c := bv_unsigned csr) in *.
  pose proof (Z.mod_pos_bound (c / 256) 4 ltac:(lia)) as Hb.
  assert (Hz : (c / 256) mod 4 = 0) by lia.
  assert (Hdd : c / 256 = (c / 16) / 16).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 16) in *.
  assert (Hh16 : q / 16 = 16 * (q / 256) + 3).
  { assert (Hq2 : q = 16 * (q / 256) * 16 + bv_unsigned h).
    { pose proof (Z_div_mod_eq_full q 256) as Hd.
      rewrite E in Hd.
      replace (16 * (q / 256) * 16) with (256 * (q / 256)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia.
    rewrite Hh. reflexivity. }
  rewrite Hdd, Hh16 in Hz.
  replace (16 * (q / 256) + 3) with (3 + (q / 256) * 4 * 4) in Hz by lia.
  rewrite Z_mod_plus_full in Hz.
  vm_compute in Hz. discriminate Hz.
Qed.
