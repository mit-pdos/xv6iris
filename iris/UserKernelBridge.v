(* UserKernelBridge.v -- item (E) of the user-mode WP worklist: KERNEL
   INTEGRATION.

   This file bridges the postcondition of [wp_userret_pt] (UserretAllPt.v)
   -- the machine state the kernel's userret trampoline leaves once it has
   sret'd into User mode -- into [user_inv C pt] (UserExec.v), the loop
   invariant the user-execution capstone [wp_user_exec] consumes.

   THE OBSERVATION.  [wp_userret_pt]'s continuation already hands back
   EXACTLY [utlb_inv_pt uroot tfp um] -- the very same installed-table
   invariant [user_pt_inv] wraps -- together with a User-privilege machine
   whose mstatus is [sret_ms5 mstatus0].  So the bridge is a pure
   REPACKAGING: no translation move, no page-walk, no fupd.  What it needs
   beyond userret's guarantees are the CELLS userret never touched (they
   stay kernel-owned across the whole trampoline): the two remaining trap
   CSRs [scause]/[stval] (stale until the next trap writes them), the four
   config CSRs userret does not thread ([stvec]/[medeleg] and the
   [mstateen0]/[sstateen0] state-enable pins; [mip] is NOT among them --
   it has no loop-constant value, and the hart owns it inside
   [user_regs]'s [clock_res] rider, which arrives here as part of the
   [pc_is] userret hands back, see [UserExec.ucfg]), and the user data
   memory [umem_any] with its no-aliasing / access-classification
   facts.

   THE ONE PURE OBLIGATION is [user_mstatus_ok (sret_ms5 mstatus0)] -- the
   SXL=64 / MPRV=0 / MXR=0 pins survive the sret transform.  This is
   discharged from the pre-sret pins by the existing bit lemmas
   [sret_ms5_SXL]/[sret_ms5_MXR]/[sret_ms5_MPRV] (MstatusBits.v): sret
   clears MPRV (bit 17) and leaves SXL (bits 35:34) and MXR (bit 19)
   untouched.

   The [ucfg] record's own well-formedness proofs (stvec TV_Direct
   [uc_tvd], the mie&~mideleg=0 M-interrupt pin [uc_mm], the delegation of
   every user exception [uc_del]) ride along inside the abstract [C] the
   caller supplies -- they are established once when the boot config is
   fixed, and this bridge does not re-derive them. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes WpGpr RegFile.
Require Import MstatusBits WpIntrCore.
Require Import UserFrame.
Require Import UptTree UserPtTree UserExec.
Local Open Scope Z_scope.
Import Defs.

Section UserKernelBridge.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* -------------------------------------------------------------------- *)
  (* The pure mstatus obligation, factored out: the User-execution mstatus *)
  (* pins survive the sret transform.                                      *)
  (* -------------------------------------------------------------------- *)
  Lemma user_mstatus_ok_sret_ms5 (ms0 : mword 64) :
    _get_Mstatus_SXL ms0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR ms0) ('b"0") = true ->
    eq_vec (_get_Mstatus_FS ms0) ('b"00") = true ->
    eq_vec (_get_Mstatus_VS ms0) ('b"00") = true ->
    eq_vec (_get_Mstatus_TVM ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false ->
    (* the kernel-tier pins [user_mstatus_ok] now carries: XS/SD/MPP ride
       through the sret untouched, and SIE = 1 in user mode is SPIE = 1
       before it ([sret_ms5_SIE]) -- which is what prepare_return wrote
       and what the trap will copy back ([UserTrap.utrap_ms_SPIE]). *)
    _get_Mstatus_XS ms0 = extStatus_map_forwards Off ->
    _get_Mstatus_SD ms0 = ('b"0" : mword 1) ->
    eq_vec (_get_Mstatus_MPP ms0) ('b"10") = false ->
    _get_Mstatus_SPIE ms0 = ('b"1" : mword 1) ->
    user_mstatus_ok (sret_ms5 ms0).
  Proof.
    intros HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE.
    unfold user_mstatus_ok.
    split_and!.
    - rewrite sret_ms5_SXL. exact HSXL.
    - rewrite sret_ms5_MPRV. vm_compute. reflexivity.
    - rewrite sret_ms5_MXR. exact HMXR.
    - rewrite sret_ms5_FS. exact HFS.
    - rewrite sret_ms5_VS. exact HVS.
    - rewrite sret_ms5_TVM. exact HTVM.
    - rewrite sret_ms5_TSR. exact HTSR.
    - rewrite sret_ms5_XS. exact HXS.
    - rewrite sret_ms5_SD. exact HSD.
    - rewrite sret_ms5_MPP. exact HMPP.
    - rewrite sret_ms5_SIE HSPIE. vm_compute. reflexivity.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* THE BRIDGE.  [C]/[pt] are abstract (so the [ucfg] proof fields ride    *)
  (* along); the field equations pin their DATA fields to the concrete     *)
  (* values the machine cells carry.  The config-cell fraction is required  *)
  (* full ([uc_dqc C = DfracOwn 1]) -- at userret's join the kernel owns    *)
  (* every config cell outright on this hart, and it hands the whole cell   *)
  (* to [user_cfg].                                                         *)
  (* -------------------------------------------------------------------- *)
  Lemma userret_to_user_inv
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (mstatus0 sepc0 sc_v stval_v mie_v mdv0 menvcfg0 senvcfg0 : mword 64)
      (stv medeleg_v : mword 64)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (mstateen0v : mword 64) (sstateen0v : mword 32)
      (mcounteren_v scounteren_v : mword 32)
      (mhpmcounter_v : type_of_register mhpmcounter)
      (g : regfile) :
    (* mstatus pins on the pre-sret value (FS/VS = Off: FP/vector disabled --
       the user machine runs with the FP and vector units off, an invariant
       [user_mstatus_ok] now carries and the kernel establishes) *)
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    eq_vec (_get_Mstatus_FS mstatus0) ('b"00") = true ->
    eq_vec (_get_Mstatus_VS mstatus0) ('b"00") = true ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    (* the kernel-tier pins -- see [user_mstatus_ok_sret_ms5] *)
    _get_Mstatus_XS mstatus0 = extStatus_map_forwards Off ->
    _get_Mstatus_SD mstatus0 = ('b"0" : mword 1) ->
    eq_vec (_get_Mstatus_MPP mstatus0) ('b"10") = false ->
    _get_Mstatus_SPIE mstatus0 = ('b"1" : mword 1) ->
    (* config-record data fields pinned to the cell values *)
    uc_dqc C = DfracOwn 1 ->
    uc_stvec C = stv ->
    uc_mie C = mie_v ->
    uc_mideleg C = mdv0 ->
    uc_medeleg C = medeleg_v ->
    (* page-table-descriptor fields pinned to the userret roots *)
    ud_root pt = uroot ->
    ud_tfp pt = tfp ->
    ud_um pt = um ->
    (* the two constant config values userret returns *)
    menvcfg0 = MENVCFG_S ->
    senvcfg0 = (mword_of_int 0 : mword 64) ->
    (* the state-enable pins user_cfg fixes at zero *)
    mstateen0v = (mword_of_int 0 : mword 64) ->
    sstateen0v = (mword_of_int 0 : mword 32) ->
    (* the user address space's no-aliasing / access classification *)
    uva_pa_inj pt ->
    upt_acc_wf pt.(ud_um) ->
    (* ---- the cells [wp_userret_pt] hands back ---- *)
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ sret_ms5 mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    senvcfg ↦ᵣ□ senvcfg0 -∗
    sepc ↦ᵣ sepc0 -∗
    utlb_inv_pt uroot tfp um -∗
    pc_is (ret_pc sepc0) -∗
    gpr_file g -∗
    (* ---- the cells userret never touched (kernel-owned) ---- *)
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    stvec ↦ᵣ stv -∗
    (* PERSISTENT: never written after M-mode boot, and the kernel residue
       ([IntrDefs.hart_csrs]) holds the same three -- see [user_cfg]. *)
    medeleg ↦ᵣ□ medeleg_v -∗
    mstateen0 ↦ᵣ□ mstateen0v -∗
    sstateen0 ↦ᵣ□ sstateen0v -∗
    (* THE COUNTER-PERMISSION CELLS.  New with the port, and forced by it:
       a U-mode [csrr] of a counter CSR reads mcounteren / scounteren /
       mhpmcounter, and under per-node stepping every read the cycle makes
       must be answerable from what the hart OWNS.  All three are [box] --
       nothing writes them after M-mode boot -- so handing them over costs
       the kernel nothing, and their VALUES are unconstrained (a denied
       counter read is Illegal_Instruction, which the user tier classifies). *)
    (R_bitvector_32 mcounteren) ↦ᵣ□ mcounteren_v -∗
    (R_bitvector_32 scounteren) ↦ᵣ□ scounteren_v -∗
    mhpmcounter ↦ᵣ□ mhpmcounter_v -∗
    (* ---- the process's memory (contents quantified: the bridge says
           nothing about the bytes, only that the process owns them) ---- *)
    umem_any pt -∗
    (* ---- the exclusive usertrap-residue conjunct [user_inv] now carries ---- *)
    Rut pt -∗
    user_inv C pt Rut.
  Proof.
    intros HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE Hdqc Hstvec Hmie Hmdl Hmedl
      Hroot Htfp Hum Hmenv Hsenv Hmse Hsse Hinj Hacc.
    subst menvcfg0 senvcfg0 mstateen0v sstateen0v.
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsenv Hsepc Hutlb Hpc Hgpr
             Hsc Hstval Hstvec Hmedl Hmse Hsse Hmcen Hscen Hhpm Hdata Hrut".
    unfold user_inv.
    iExists (HART_ACTIVE tt), (sret_ms5 mstatus0), sc_v, stval_v, sepc0,
            (ret_pc sepc0), (ret_pc sepc0), g.
    (* user_hart_ok *)
    iSplitR; [iPureIntro; exact I |].
    (* user_mstatus_ok *)
    iSplitR; [iPureIntro; exact (user_mstatus_ok_sret_ms5 mstatus0 HSXL HMXR HFS HVS HTVM HTSR HXS HSD HMPP HSPIE) |].
    (* lock-step va' = va *)
    iSplitR; [iPureIntro; intros u _; reflexivity |].
    iSplitL "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr".
    { (* [user_regs] IS [UserFrame.u_regs], and the three riders it now
         carries -- [minstret_res], [clock_res], [resv_any] -- are exactly
         the three [pc_is] bundles beside PC/nextPC.  So the bridge does NOT
         take [pc_is] APART any more: [u_regs_pc_is] is the whole step, and
         it is what makes the entry boundary free. *)
      unfold user_regs. rewrite u_regs_pc_is.
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr". }
    iSplitL "Hutlb Hdata".
    { (* user_pt_any *)
      rewrite user_pt_any_unfold.
      rewrite Hroot Htfp Hum.
      iFrame "Hutlb Hdata".
      rewrite Hum in Hacc.
      iPureIntro. split; [exact Hinj | exact Hacc]. }
    iSplitL "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse Hmcen Hscen Hhpm".
    { (* user_cfg *)
      unfold user_cfg.
      rewrite Hdqc Hstvec Hmie Hmdl Hmedl.
      iFrame "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse".
      iSplitL "Hmcen Hscen".
      - iExists mcounteren_v, scounteren_v. iFrame "Hmcen Hscen".
      - iExists mhpmcounter_v. iFrame "Hhpm". }
    (* Rut pt *)
    iFrame "Hrut".
  Qed.

  (* -------------------------------------------------------------------- *)
  (* SUB-GOAL 2 SCAFFOLD: the trap-frame opener.                            *)
  (*                                                                        *)
  (* [stvec_handler_wp C pt Φ = user_trap_frame C pt -∗ WP Loop {{ Φ }}]:   *)
  (* discharging it means proving uservec (the trampoline handler at        *)
  (* [stvec_base (uc_stvec C)]) safe from ANY trapped-out-of-user machine.  *)
  (* uservec's proof begins by taking [user_trap_frame] apart into the raw  *)
  (* register cells + the fully-unpacked user table invariant + the         *)
  (* fully-unpacked config cells, which is exactly what the trampoline step *)
  (* engines ([wp_instr_u_pt] user-table phase, [wp_instr_pt2_tramp] switch *)
  (* window, [wp_instr_ktramp_pt] kernel phase) consume.  This opener is    *)
  (* the mirror of [user_trap_frame_intro] (UserExec.v) and the clean entry *)
  (* point for that proof.                                                  *)
  (* -------------------------------------------------------------------- *)
  Lemma user_trap_frame_open (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) :
    user_trap_frame C pt Rut -∗
    ∃ (ms_v sc_v stval_v sepc_v : mword 64) (g : regfile),
      ⌜trap_mstatus_ok ms_v⌝ ∗
      hart_state ↦ᵣ HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ Supervisor ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      (* [pc_is], NOT the two cells: post-port it also carries
         [minstret_res], [clock_res] and [resv_any cpu_id], and splitting
         PC/nextPC off would DROP them on the floor -- the kernel phase
         needs all five. *)
      pc_is (stvec_base (uc_stvec C)) ∗
      gpr_file g ∗
      (* user_pt_any pt, fully unpacked *)
      utlb_inv_pt pt.(ud_root) pt.(ud_tfp) pt.(ud_um) ∗
      umem_any pt ∗
      ⌜uva_pa_inj pt⌝ ∗
      ⌜upt_acc_wf pt.(ud_um)⌝ ∗
      (* user_cfg C, fully unpacked *)
      stvec ↦ᵣ{ uc_dqc C } uc_stvec C ∗
      mie ↦ᵣ{ uc_dqc C } uc_mie C ∗
      mideleg ↦ᵣ{ uc_dqc C } uc_mideleg C ∗
      medeleg ↦ᵣ□ uc_medeleg C ∗
      menvcfg ↦ᵣ{ uc_dqc C } MENVCFG_S ∗
      senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
      mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
      sstateen0 ↦ᵣ□ (mword_of_int 0 : mword 32) ∗
      (* THE THREE COUNTER-PERMISSION CELLS ARE NOT HANDED BACK.  They are
         [box], so [user_cfg] holding them costs the kernel nothing to
         RE-establish: whoever built this frame still has its own copies.
         Returning them would only widen this opener's output -- and every
         ipattern that eliminates it -- for resources the caller already
         has.  (They are still inside [user_cfg], and [user_trap_frame_intro]
         still asks for them there; this is the OPENER's output only.) *)
      Rut pt.
  Proof.
    iIntros "H".
    unfold user_trap_frame.
    iDestruct "H" as (ms_v sc_v stval_v sepc_v g)
      "(%Hok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hgpr & Hupt & Hcfg & Hrut)".
    rewrite user_pt_any_unfold.
    iDestruct "Hupt" as "(Hutlb & Hdata & %Hinj & %Hacc)".
    unfold user_cfg.
    iDestruct "Hcfg" as
      "(Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hsenv & Hmse & Hsse & #Hctr & #Hhpm)".
    iExists ms_v, sc_v, stval_v, sepc_v, g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr
            Hutlb Hdata Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse
            Hrut".
    iPureIntro. split; [exact Hok | split; [exact Hinj | exact Hacc]].
  Qed.

End UserKernelBridge.
