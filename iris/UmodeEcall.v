(* UmodeEcall.v -- decode + execute leaves for the first U-mode instruction:
   ecall (word 0x00000073).

   §1 extends the WpDecodeBridge concrete/symbolic transport to USER mode:
      [dstateU] is the concrete reference state at privilege User (senvcfg
      and every other config CSR zero, misa = MISA_C, menvcfg = MENVCFG_S);
      [D_u] is the User decode read-set (the landing-pad probe's get_xLPE
      dispatches through the U arm, which reads senvcfg / the stateen
      gates in addition to menvcfg).
   §2 [exec_execute_ECALL_U]: execute (ECALL tt) in User mode produces the
      Trap (User, E_U_EnvCall sync exception, pc) execution result and
      leaves the state untouched.                                        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpDecodeBridge.
From stdpp Require Import gmap.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The User-mode decode bridge.                                        *)
(* ===================================================================== *)

Notation dstateU := (dstate MENVCFG_S User).

(* User decode read-set: cur_privilege + misa (extension gates) + the
   registers the get_xLPE User arm probes (menvcfg / senvcfg / the
   mstateen0-sstateen0 gates). *)
Definition D_u (r : register) : bool :=
  register_beq r (R_Privilege cur_privilege) ||
  register_beq r (R_bitvector_64 menvcfg) ||
  register_beq r (R_bitvector_64 senvcfg) ||
  register_beq r (R_bitvector_64 mstateen0) ||
  register_beq r (R_bitvector_32 sstateen0) ||
  register_beq r (R_bitvector_64 misa).

Lemma agree_u (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup mstateen0 s.(sregs) = mword_of_int 0 ->
  register_lookup sstateen0 s.(sregs) = (mword_of_int 0 : mword 32) ->
  register_lookup misa s.(sregs) = MISA_C ->
  agree_on D_u s dstateU.
Proof.
  intros Hp Hme Hse Hms0 Hss0 Hmi r Hr. unfold D_u in Hr.
  repeat (apply orb_true_elim in Hr as [Hr|Hr]);
    apply register_beq_eq in Hr; subst r;
    [ rewrite Hp | rewrite Hme | rewrite Hse | rewrite Hms0 | rewrite Hss0 | rewrite Hmi ];
    first [ vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* the ecall word decodes to ECALL over any U state agreeing with dstateU *)
Lemma decode_ecall_u (s : mstate) :
  agree_on D_u s dstateU ->
  exec (ext_decode (mword_of_int 0x73 : mword 32)) s = Some (ECALL tt, s).
Proof.
  intros Hag.
  apply (decode_state_bridge D_u _ dstateU);
    [ exact Hag | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(* §2 execute (ECALL tt) in User mode: the Trap execution result.         *)
(* ===================================================================== *)

Definition ecall_u_exc : sync_exception :=
  {| sync_exception_trap := E_U_EnvCall tt;
     sync_exception_excinfo := None;
     sync_exception_ext := None |}.

Lemma exec_execute_ECALL_U (pc0 : mword 64) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup PC s.(sregs) = pc0 ->
  exec (execute (ECALL tt)) s
    = Some (rv64d_types.Trap (User, ecall_u_exc, pc0), s).
Proof.
  intros Hpriv Hpc.
  change (execute (ECALL tt)) with (execute_ECALL tt).
  unfold execute_ECALL.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (E_U_EnvCall tt) s)).
  cbn beta. cbv zeta.
  unfold trap.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite Hpc. cbn beta.
  apply exec_returnm.
Qed.
