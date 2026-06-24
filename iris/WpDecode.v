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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpAdd WpFetch.

(* cE Zicsr = hartSupports Zicsr = true, at any Acc level. *)
Lemma exec_rec_cE_Zicsr_any (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_Zicsr k acc) s = Some (true, s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_hartSupports_Zicfilp s : exec (hartSupports Ext_Zicfilp) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_cE_zicfilp_M s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exists b, exec (currentlyEnabled Ext_Zicfilp) s = Some (b, s).
Proof.
  intro Hpriv.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* outer and_boolM: cE Zicsr = true *)
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  (* inner and_boolM: hartSupports Zicfilp = true *)
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  (* read cur_privilege = Machine *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  (* get_xLPE Machine = read mseccfg >>= returnM (MLPE bit) *)
  match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). cbn match.
  eexists. apply exec_returnM.
Qed.

Lemma exec_cE_pause s : exists b, exec (currentlyEnabled Ext_Zihintpause) s = Some (b, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zihintpause) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  eexists; reflexivity.
Qed.

Definition w_auipc : mword 32 := mword_of_int 0xa117.

Ltac skip_pure_clause :=
  match goal with
  | |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity)
  end;
  cbn match;
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) _));
  cbn match.

Definition imm_auipc : mword 20 := subrange_vec_dec w_auipc 31 12.
Definition i_auipc : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_auipc 11 7) (regidx_bit_width - 1) 0).

Lemma decode_auipc s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode w_auipc) s = Some (UTYPE (imm_auipc, Regidx i_auipc, AUIPC), s).
Proof.
  intro Hpriv. unfold imm_auipc, i_auipc.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  (* replace PAUSE/Zicfilp pattern checks (vm_compute) with false *)
  match goal with |- context[eq_vec w_auipc ?c] =>
    replace (eq_vec w_auipc c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_auipc 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_auipc 11 0) c) with false by (vm_compute; reflexivity) end.
  (* PAUSE and_boolM -> false *)
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  (* Zicfilp and_boolM -> false (nested under another bind) *)
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  (* UTYPE pure guard = true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  (* UTYPE body: encdec_reg_backwards then encdec_uop_backwards *)
  unfold encdec_reg_backwards.
  match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
  unfold encdec_uop_backwards.
  match goal with |- context[if ?g then returnM LUI else _] =>
    replace g with false by (vm_compute; reflexivity) end.
  match goal with |- context[if ?g then returnM AUIPC else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
  (* body fully reduced to [returnM (Some (UTYPE ...))]; collapse the two matches *)
  match goal with |- context[exec (returnM ?x) s] => rewrite (exec_returnM x s) end.
  cbn match. cbn match.
  apply exec_returnM.
Qed.

Definition w_ld : mword 32 := mword_of_int 0x1d813103.

(* the shared PAUSE/Zicfilp prefix: 2 pure skips + the two currentlyEnabled
   and_boolM clauses (both collapse to [false] for any non-LPAD/PAUSE word). *)
Ltac decode_pause_prefix s Hpriv :=
  unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
  skip_pure_clause; skip_pure_clause;
  match goal with |- context[eq_vec ?w (?c : mword 32)] =>
    replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
  match goal with |- context[eq_vec (subrange_vec_dec ?w 11 0) (?c : mword 12)] =>
    replace (eq_vec (subrange_vec_dec w 11 0) c) with false by (vm_compute; reflexivity) end;
  let HA1 := fresh "HA1" in
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)) by
    (let bp := fresh in let Hbp := fresh in
     destruct (exec_cE_pause s) as [bp Hbp];
     rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]);
  rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match; clear HA1;
  rewrite exec_bind;
  let HA2 := fresh "HA2" in
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)) by
    (let bz := fresh in let Hbz := fresh in
     destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz];
     rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
  rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match; clear HA2.

Definition imm_ld : mword 12 := subrange_vec_dec w_ld 31 20.
Definition i_ld : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_ld 11 7) (regidx_bit_width - 1) 0).

Lemma decode_ld s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode w_ld) s = Some (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8), s).
Proof.
  intro Hpriv. unfold imm_ld, i_ld.
  decode_pause_prefix s Hpriv.
  (* UTYPE guard is FALSE for ld -> returnM None, fall through to JAL... *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  match goal with |- context[exec (returnM ?x) s] => rewrite (exec_returnM x s) end.
  cbn match. cbn match.
  repeat skip_pure_clause.
  (* LOAD clause: guard true *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  unfold encdec_reg_backwards.
  match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn match.
  (* body collapsed to [returnM (LOAD ...)]; normalize fields to the expected form *)
  match goal with
  | |- context[exec (returnM (LOAD (_, Regidx ?rs1, Regidx ?rd, ?u, ?wd))) s] =>
      replace rs1 with rd by (vm_compute; reflexivity);
      replace u with false by (vm_compute; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity)
  end.
  apply exec_returnM.
Qed.
