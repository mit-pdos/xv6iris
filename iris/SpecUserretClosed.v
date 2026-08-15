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
     and gets back unchanged on the next trap. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WireInv.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import SmodeCore.
Require Import PtTree.
Require Import TrampPt UptTree KptShare UserretDefs.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import ProcGeom ProcInv ProcPtOwn.
Require Import WpLock FdSlots FileInvDefs BioInv DiskPtsto WpUart.
Require Import FsBlocks LogInv FsCrash KallocInv IrefSlots InodeRegion.
Require Import ProcAvail.
Require Import SpecUsertrap.
From Kernel Require KernelSyms.
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

Definition wp_userret_closed_body `{!riscvGS Σ, !sieG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (* the kernel-side residue, abstract exactly as [SpecUservec] takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd)
    (kroot : mword 44) (j : nat) (ksp : mword 64)
    (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64)
    (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
    (dqm : dfrac) :=
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
  udata_cov (ud_um pt) (ud_data pt) ->
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
  udata_own (ud_data pt) -∗
  pc_is (uva 0x9c) -∗
  gpr_file m -∗
  tf_pa (ud_tfp pt) 40 ↦ₚ₈{ dqm } vra -∗
  tf_pa (ud_tfp pt) 48 ↦ₚ₈{ dqm } vsp -∗
  tf_pa (ud_tfp pt) 56 ↦ₚ₈{ dqm } vgp -∗
  tf_pa (ud_tfp pt) 64 ↦ₚ₈{ dqm } vtp -∗
  tf_pa (ud_tfp pt) 72 ↦ₚ₈{ dqm } vt0 -∗
  tf_pa (ud_tfp pt) 80 ↦ₚ₈{ dqm } vt1 -∗
  tf_pa (ud_tfp pt) 88 ↦ₚ₈{ dqm } vt2 -∗
  tf_pa (ud_tfp pt) 96 ↦ₚ₈{ dqm } vs0 -∗
  tf_pa (ud_tfp pt) 104 ↦ₚ₈{ dqm } vs1 -∗
  tf_pa (ud_tfp pt) 120 ↦ₚ₈{ dqm } va1 -∗
  tf_pa (ud_tfp pt) 128 ↦ₚ₈{ dqm } va2 -∗
  tf_pa (ud_tfp pt) 136 ↦ₚ₈{ dqm } va3 -∗
  tf_pa (ud_tfp pt) 144 ↦ₚ₈{ dqm } va4 -∗
  tf_pa (ud_tfp pt) 152 ↦ₚ₈{ dqm } va5 -∗
  tf_pa (ud_tfp pt) 160 ↦ₚ₈{ dqm } va6 -∗
  tf_pa (ud_tfp pt) 168 ↦ₚ₈{ dqm } va7 -∗
  tf_pa (ud_tfp pt) 176 ↦ₚ₈{ dqm } vs2 -∗
  tf_pa (ud_tfp pt) 184 ↦ₚ₈{ dqm } vs3 -∗
  tf_pa (ud_tfp pt) 192 ↦ₚ₈{ dqm } vs4 -∗
  tf_pa (ud_tfp pt) 200 ↦ₚ₈{ dqm } vs5 -∗
  tf_pa (ud_tfp pt) 208 ↦ₚ₈{ dqm } vs6 -∗
  tf_pa (ud_tfp pt) 216 ↦ₚ₈{ dqm } vs7 -∗
  tf_pa (ud_tfp pt) 224 ↦ₚ₈{ dqm } vs8 -∗
  tf_pa (ud_tfp pt) 232 ↦ₚ₈{ dqm } vs9 -∗
  tf_pa (ud_tfp pt) 240 ↦ₚ₈{ dqm } vs10 -∗
  tf_pa (ud_tfp pt) 248 ↦ₚ₈{ dqm } vs11 -∗
  tf_pa (ud_tfp pt) 256 ↦ₚ₈{ dqm } vt3 -∗
  tf_pa (ud_tfp pt) 264 ↦ₚ₈{ dqm } vt4 -∗
  tf_pa (ud_tfp pt) 272 ↦ₚ₈{ dqm } vt5 -∗
  tf_pa (ud_tfp pt) 280 ↦ₚ₈{ dqm } vt6 -∗
  tf_pa (ud_tfp pt) 112 ↦ₚ₈{ dqm } va0f -∗
  (* ---- the kernel-side bundle, at THIS hart ---- *)
  URes CID pt ksp -∗
  WP (Loop : expr riscv_lang).

Module Type USERRET_CLOSED.
  (* the residue is the module-type parameter it is everywhere else *)
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_userret_closed :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd)
      (kroot : mword 44) (j : nat) (ksp : mword 64)
      (m : regfile) (usatp mstatus0 sepc0 sc_v stval_v : mword 64)
      (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64)
      (dqm : dfrac),
      wp_userret_closed_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt kroot j ksp m usatp mstatus0 sepc0 sc_v stval_v
        vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f dqm.
End USERRET_CLOSED.
