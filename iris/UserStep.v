(* UserStep.v -- step-engine bricks for arbitrary user-mode execution
   (UserExec.v).  First brick: the INTERRUPT DISPATCH decision at User.

   At User privilege the effective mIE and sIE are both unconditionally
   true (priv < M and priv < S): interrupts are architecturally UNMASKABLE,
   and the device loop may raise the sig_seip wire concurrently at any
   time.  So every user-phase step begins with a genuine case split on the
   dispatch decision [u_dispatch] over the CURRENT wire/CSR values:
     - Some (i, Supervisor): a pending delegated interrupt -- the step
       takes the interrupt trap to stvec (the interrupt arm of the step
       obligation, landing in [user_trap_frame]);
     - None: the step proceeds to fetch/execute.
   The M-destined set is empty by [uc_mm] (mie & ~mideleg = 0, a boot
   constant), so a dispatched interrupt always goes to Supervisor.

   [exec_getPendingSet_U_reduce] / [exec_dispatchInterrupt_U_reduce] reduce
   the model's dispatcher to [u_dispatch], parameterized by the current
   register values; the Iris form [dispatch_U_from_regs] takes the cells at
   arbitrary dfracs, so it works both with today's pinned cells and with
   values borrowed from the future invariant shared with the device WP
   (neither the user- nor the kernel-side proofs are plumbed for that
   sharing yet).  Mirrors WpIntrCore's Supervisor reductions
   ([exec_getPendingSet_S_reduce] / [dispatch_S_from_regs]); the User
   variants are simpler because neither mstatus.MIE nor mstatus.SIE is
   consulted below the current privilege.                                 *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore WpIntrCore.
Require Import UserPt UserExec.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The dispatch decision at User: purely the S-destined pending set     *)
(* [s_pending] (no mstatus gate -- both effective enables are true).       *)
(* ===================================================================== *)

Definition u_dispatch (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv : mword 64) : option (InterruptType * Privilege) :=
  if neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64)
  then match findPendingInterrupt (s_pending mip_v meip seip mie_v mdv) with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Lemma exec_getPendingSet_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (getPendingSet User) s
    = Some ((if neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)
             then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
             else None), s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  assert (Hguard : exec (or_boolM (currentlyEnabled Ext_S)
                     (bind (read_reg mideleg)
                        (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
                   = Some (true, s)).
  { rewrite (exec_or_boolM_Some _ _ _ _ _ HES). reflexivity. }
  assert (Hae : exec (Defs.assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                = Some (eq_refl, s)).
  { unfold assert_exp'. cbn match. apply exec_returnm. }
  (* effective mIE at User: priv < Machine, so unconditionally true *)
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq User Supervisor) (generic_eq User User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Machine) s)).
      change (generic_eq User Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq User Supervisor) (generic_eq User User)) with true.
    apply exec_returnm. }
  (* effective sIE at User: priv < Supervisor, so unconditionally true *)
  assert (HsIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq User User))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Supervisor) s)).
      change (generic_eq User Supervisor) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq User User) with true.
    apply exec_returnm. }
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ Hguard).
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIEt).
  rewrite Hmie Hmdl Hmm.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq.
  rewrite andb_false_r andb_true_l.
  unfold s_pending, s_mip_bits.
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt User) s
    = Some (u_dispatch mip_v meip seip mie_v mdv_v, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_getPendingSet_U_reduce s mip_v mie_v mdv_v meip seip
               HES Hmip Hmeip Hseip Hmie Hmdl Hmm)).
  unfold u_dispatch.
  destruct (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)).
  - cbn match. destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
      apply exec_returnm.
  - cbn match. apply exec_returnm.
Qed.

(* the no-pending corollary: with the S-destined set empty AT THIS STEP,
   the dispatcher is a no-op and the step proceeds to fetch/execute *)
Lemma exec_dispatchInterrupt_U_none (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt User) s = Some (None, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm Hs0.
  rewrite (exec_dispatchInterrupt_U_reduce s mip_v mie_v mdv_v meip seip
             HES Hmip Hmeip Hseip Hmie Hmdl Hmm).
  unfold u_dispatch, s_pending. rewrite Hs0.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The frame-level form: the dispatch decision from BORROWED cells.     *)
(* All cells are dfrac-generic, so the wire cells (sig_meip / sig_seip)    *)
(* can come from the future invariant shared with the device WP -- the     *)
(* engine opens it, applies this with the current wire values, and closes  *)
(* it before the step commits.                                             *)
(* ===================================================================== *)
Section UserStepIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma dispatch_U_from_regs (σ : mstate)
      (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1)
      {dqp dqe1 dqe2 dqi dqd : dfrac} :
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    hw_config -∗
    mstate_interp σ -∗
    mip ↦ᵣ{ dqp } mip_v -∗
    sig_meip ↦ᵣ{ dqe1 } meip -∗
    sig_seip ↦ᵣ{ dqe2 } seip -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv_v -∗
    ⌜exec (dispatchInterrupt User) σ
       = Some (u_dispatch mip_v meip seip mie_v mdv_v, σ)⌝.
  Proof.
    iIntros (Hmm) "Hhw [Hreg [Hmem Hdev]] Hmip Hmeip Hseip Hmie Hmdl".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmip")  as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmie")  as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl")  as %Lmdl.
    iPureIntro.
    apply exec_dispatchInterrupt_U_reduce; try assumption.
    rewrite exec_currentlyEnabled_S. rewrite Lmisa. rewrite HmisaS. reflexivity.
  Qed.

End UserStepIris.
