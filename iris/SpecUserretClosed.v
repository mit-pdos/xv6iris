(* SpecUserretClosed.v -- userret, CLOSED: the public interface of the whole
   trap loop, stated where the kernel first enters it.

   [SpecUserret]'s [wp_userret_pt] is a CONTINUATION spec -- it hands its
   caller a User-mode machine and asks what happens next.  This is the same
   contract with that question answered: run userret from forkret's tail and
   the machine keeps running, forever, through arbitrarily many rounds of

     userret -> user code -> uservec -> usertrap -> userret -> ...

   There is no premise about user-mode execution and none about the kernel's
   re-entry: [SpecUser]'s WP supplies the first and the Löb induction in
   ProofUserretClosed.v supplies the second.

   WHAT IS LEFT ON THE OUTSIDE.  Three things, and each is a premise that
   already existed one level down rather than anything this statement
   invents:

   * [loop_ok C pt] -- the four config fields the loop pins (stvec at the
     trampoline, mie at [MIE_S], medeleg at [MEDELEG_S], the config fraction
     whole) plus the two descriptor facts uservec's own satp switch needs.
     Every round re-establishes it, which is what makes it a loop invariant
     rather than an assumption about the first round.
   * THE mstatus GAP and THE TRAPFRAME KERNEL-WORDS GAP -- [SpecUservec]'s
     own two undischarged premises, verbatim.  They are cross-round
     historical facts ("userret's sret set SPIE, so the trap saw it";
     "prepare_return armed the four kernel words"), and closing them needs
     ghost tracking that no tier carries yet.  Passing them through is the
     honest thing: they are the same obligation, not a new one.
   * The kernel-side residue, as [Rut_at]: the bundle usertrap hands the loop
     and gets back unchanged on the next trap.

   THE TRAPFRAME'S 31 SAVE SLOTS ARE NOT ON THIS BOUNDARY, and an earlier
   statement of it that listed them beside the residue was UNSATISFIABLE:
   the residue OWNS that page ([UsertrapRes.ut_res_bare] -> [proc_priv_nopt]
   -> [ProcInv.tf_page], at full ownership), so
   [tf_page tfp ws -∗ tf_pa tfp 40 ↦ₚ₈{dq} v -∗ False] refutes any caller
   holding both.  userret only READS those words, and the proof opens them
   out of the residue itself ([usertrap_res_tf_open]) and closes them back
   before user mode -- which is also what every LOOP round already did.  A
   caller therefore hands over the residue and nothing about the page. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WireInv.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import PtTree.
Require Import TrampPt UptTree KptShare UserretDefs.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import ProcGeom ProcPtOwn.
Require Import IrefSlots.
Require Import FdSlots FileInvDefs.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import SpecUsertrap.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* the loop-invariant shape of the config record and the descriptor *)
Definition loop_ok (C : ucfg) (pt : uptd) : Prop :=
  uc_stvec C = (mword_of_int TRAMPOLINE : mword 64) /\
  uc_dqc C = DfracOwn 1 /\
  uc_mie C = MIE_S /\
  uc_medeleg C = MEDELEG_S /\
  ud_data pt = ud_pas pt /\
  proc_pt_wf pt.

(* ===================================================================== *)
(* THE DELEGATION WORD DELEGATES EVERY USER EXCEPTION.                  *)
(*                                                                         *)
(* [IntrDefs.MEDELEG_S] is what [start()]'s [csrw medeleg, 0xffff] leaves   *)
(* ([legalize_medeleg] ignores its old-value argument), so this is a closed *)
(* computation over the twelve exception kinds [UserExec.user_exc] admits.  *)
(* It is the [uc_del] field of every [ucfg] the loop builds.                *)
(* ===================================================================== *)
Lemma medeleg_S_delegates (e : ExceptionType) :
  user_exc e = true ->
  bit_to_bool (access_vec_dec MEDELEG_S
    (uint (exceptionType_bits_forwards e))) = true.
Proof.
  (* the payload has to go first: [exceptionType_bits_forwards] MATCHES on
     the constructor's unit argument, so with it a variable the whole
     computation is stuck. *)
  destruct e; intro He; try discriminate He;
    repeat (match goal with
            | u : unit |- _ => destruct u
            | b : breakpoint_cause |- _ => destruct b
            end);
    vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* THE SHAPE OF THE CONFIG RECORD EVERY ROUND RUNS AT --- the one every
   entrant into the loop has to build, so it belongs beside [loop_ok].                  *)
(* ===================================================================== *)
Definition loop_tvd :
  trapVectorMode_forwards (_get_Mtvec_Mode (mword_of_int TRAMPOLINE : mword 64))
    = TV_Direct.
Proof. vm_compute. reflexivity. Defined.

Definition loop_ucfg (mdv0 : mword 64)
    (Hmm : and_vec MIE_S (not_vec mdv0) = zeros' 64) : ucfg :=
  UCfg (mword_of_int TRAMPOLINE) MIE_S mdv0 MEDELEG_S (DfracOwn 1)
       loop_tvd Hmm medeleg_S_delegates.

Lemma loop_ok_loop_ucfg (mdv0 : mword 64)
    (Hmm : and_vec MIE_S (not_vec mdv0) = zeros' 64) (pt : uptd) :
  ud_data pt = ud_pas pt -> proc_pt_wf pt -> loop_ok (loop_ucfg mdv0 Hmm) pt.
Proof.
  intros H1 H2. rewrite /loop_ok /=.
  split; [reflexivity | split; [reflexivity | split; [reflexivity |
    split; [reflexivity | split; [exact H1 | exact H2]]]]].
Qed.

Definition wp_userret_closed_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (* the kernel-side residue, abstract exactly as [SpecUservec] takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd)
    (kroot : mword 44) (j : nat) (ksp : mword 64)
    (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64) :=
  (* ---- the loop's own shape, re-established every round ---- *)
  loop_ok C pt ->
  (j < NPROC)%nat ->
  (* ---- SpecUservec's two gaps, passed through verbatim ---- *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (forall (h : CpuId) (ksp' : mword 64) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := h) kroot ksp' ws) ->
  (* ---- userret's own premises ---- *)
  eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
  eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
  _get_Mstatus_SXL mstatus0 = 'b"10" ->
  eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
  eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
  eq_vec (_get_Mstatus_FS mstatus0) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS mstatus0) ('b"00") = true ->
  sret_newpriv mstatus0 = User ->
  upt_map_wf (ud_um pt) ->
  m !!! Regidx (mword_of_int 10) = usatp ->
  satp_rooted usatp (ud_root pt) ->
  uva_pa_inj pt ->
  upt_acc_wf (ud_um pt) ->
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  kpt_inv kroot -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  cur_privilege ↦ᵣ Supervisor -∗
  mstatus ↦ᵣ mstatus0 -∗
  mie ↦ᵣ uc_mie C -∗
  mideleg ↦ᵣ uc_mideleg C -∗
  menvcfg ↦ᵣ MENVCFG_S -∗
  senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
  sepc ↦ᵣ sepc0 -∗
  scause ↦ᵣ sc_v -∗
  stval ↦ᵣ stval_v -∗
  stvec ↦ᵣ uc_stvec C -∗
  medeleg ↦ᵣ□ uc_medeleg C -∗
  mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
  sstateen0 ↦ᵣ□ (mword_of_int 0 : mword 32) -∗
  tlb_res_pt kroot -∗
  pt_frame (upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt)) -∗
  umem_any pt -∗
  pc_is (uva 0x9c) -∗
  gpr_file m -∗
  (* ---- the kernel-side bundle, at THIS hart ---- *)
  URes CID pt ksp -∗
  WP (Loop : expr riscv_lang).

Module Type USERRET_CLOSED.
  (* the residue is the module-type parameter it is everywhere else *)
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_userret_closed :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd)
      (kroot : mword 44) (j : nat) (ksp : mword 64)
      (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64),
      wp_userret_closed_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt kroot j ksp m usatp mstatus0 sepc0 sc_v stval_v.
End USERRET_CLOSED.
