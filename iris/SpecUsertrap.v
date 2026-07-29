(* SpecUsertrap.v -- the public interface of usertrap() (trap.c), stated
   ahead of its proof (which does not exist yet: syscall / devintr /
   vmfault / kexit / prepare_return are all still unproven).  What is
   load-bearing NOW is the BOUNDARY: usertrap is the C function between
   the two trampoline halves, and its entry/return machine states are
   fixed by uservec's postcondition (SpecUservec.v) and userret's
   precondition (SpecUserret.v).  This file pins that boundary; the
   kernel-internal resources usertrap consumes (process bundle, kernel
   stack, scheduler context, file table, ticks lock, PLIC, ...) are the
   abstract per-process predicate [usertrap_res] of the module type,
   which the eventual proof will define concretely -- consumers thread it
   opaquely, so refining it does not churn the boundary.

   THE BOUNDARY.

   Entry (= uservec's continuation, SpecUservec.v): called by [jalr] from
   the trampoline with ra = uva 0x9c (userret -- usertrap RETURNS INTO
   userret), sp = the process's kernel stack top, tp = this hart's id;
   Supervisor, mstatus with the [trap_mstatus_ok] pins (SIE=0, SPP=User,
   MPRV=0, MXR=0, SXL=64, TVM=0, TSR=0); scause/stval/sepc holding
   whatever the trap wrote (usertrap must handle EVERY cause -- the trap
   frame's values are existential); the KERNEL page table live
   ([tlb_inv_pt kroot]), the user table parked ([pt_frame]), the user
   data pages owned, and the whole trapframe page's words owned by the
   kernel (the 31 save slots hold the interrupted user registers, the
   4+1 kernel words -- kernel_satp/kernel_sp/kernel_trap/kernel_hartid
   and epc -- are usertrap's to rewrite).

   Return (= userret's precondition, SpecUserret.v): back at ra (= uva
   0x9c) with callee-saved registers restored and a0 = the USER satp
   value (Sv39, asid 0, rooted at the process's table -- possibly with
   NEW mappings, [pt'], from vmfault; the root and the trapframe page
   never change); mstatus ready for sret to User ([usertrap_ret_ms]:
   SIE=0 again via prepare_return's intr_off, SPP=User, SPIE set, the
   M-mode pins intact); sepc = the user pc to resume; stvec back at
   TRAMPOLINE (uservec); the trapframe's kernel words re-armed for the
   NEXT trap (kernel_trap := usertrap, kernel_hartid := this hart,
   kernel_satp := a kroot-rooted satp value); the 31 save slots holding
   the user registers to restore (existential: syscalls overwrite the
   a0 slot, kexit'd processes never return at all).  usertrap does not
   return on every path (kexit) and may return only after scheduling
   away and back (yield) -- the continuation is simply not invoked on
   non-returning paths. *)
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
Require Import CalleeSaved.
Require Import WpLock.
Require Import FdSlots FileInv.
Require Import ProcGeom.
Require Import PtTree.
Require Import TrampPt KptTree UptTree.
Require Import UserPtTree UserExec.
Require Import SpecUserret.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Notation UT := KernelSyms.usertrap.

(* the mstatus facts usertrap's return guarantees: exactly userret's
   premises (the sret decodes to User and does not trap) plus the FS/VS
   pins the user-mode invariant carries across the sret
   ([userret_to_user_inv], UserKernelBridge.v). *)
Definition usertrap_ret_ms (ms : mword 64) : Prop :=
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_FS ms) ('b"00") = true /\
  eq_vec (_get_Mstatus_VS ms) ('b"00") = true /\
  sret_newpriv ms = User.

(* the satp-value facts both trampoline switches need, shared spec
   vocabulary: [v] is a Sv39, asid-0 satp value rooted at [root]. *)
Definition satp_rooted (v : mword 64) (root : mword 44) : Prop :=
  _get_Satp64_Mode (Mk_Satp64 v) = ('b"1000" : mword 4) /\
  zero_extend' 16 (satp_to_asid (autocast (T := mword) v : mword 64)) = (mword_of_int 0 : mword 16) /\
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) v : mword 64)) = root.

(* The statement, parameterized over the abstract kernel-internal resource
   [R : uptd -> mword 64 -> iProp Σ] (the process bundle: R pt ksp is
   everything usertrap needs beyond the boundary, for the process whose
   user table is [pt] and whose kernel stack top is [ksp]).  The module
   type instantiates it with its own [usertrap_res]. *)
Definition wp_usertrap_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
    (R : uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd) (kroot : mword 44) (Φ : mval -> iProp Σ)
    (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
    (w0 w8 w16 w24 w32 : bv 64)
    (u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160
     u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264
     u272 u280 u112 : bv 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.usertrap in
  let tfp := ud_tfp pt in
  let ret_tgt : mword 64 := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the trap delivered the [trap_mstatus_ok] pins *)
  trap_mstatus_ok ms_v ->
  (* stvec still points at the trampoline (uservec set nothing; the trap
     entered through it), and the config cells are kernel-owned outright *)
  uc_stvec C = mword_of_int TRAMPOLINE ->
  uc_dqc C = DfracOwn 1 ->
  (* calling convention: sp = the process's kernel stack top, tp = this
     hart's id (myproc), ra = userret *)
  m !!! Regidx (mword_of_int 2 : mword 5) = ksp ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the user data pages' pure facts, as the trap frame carried them *)
  udata_cov (ud_um pt) (ud_data pt) ->
  upt_acc_wf (ud_um pt) ->
  upt_map_wf (ud_um pt) ->
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  wire_inv -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  cur_privilege ↦ᵣ Supervisor -∗
  mstatus ↦ᵣ ms_v -∗
  scause ↦ᵣ sc_v -∗
  stval ↦ᵣ stval_v -∗
  sepc ↦ᵣ sepc_v -∗
  pc_is pcE -∗
  gpr_file m -∗
  (* the kernel table live, the user table parked, the user pages owned *)
  tlb_inv_pt kroot -∗
  pt_frame (upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt)) -∗
  udata_own (ud_data pt) -∗
  (* the boot config cells (stvec is rewritten twice inside; it comes
     back at TRAMPOLINE, i.e. user_cfg is returned intact) *)
  user_cfg C -∗
  (* the whole trapframe page's words: the 4+1 kernel words ... *)
  tf_pa tfp 0 ↦ₚ₈ w0 -∗
  tf_pa tfp 8 ↦ₚ₈ w8 -∗
  tf_pa tfp 16 ↦ₚ₈ w16 -∗
  tf_pa tfp 24 ↦ₚ₈ w24 -∗
  tf_pa tfp 32 ↦ₚ₈ w32 -∗
  (* ... and the 31 save slots, holding the interrupted user registers *)
  tf_pa tfp 40 ↦ₚ₈ u40 -∗
  tf_pa tfp 48 ↦ₚ₈ u48 -∗
  tf_pa tfp 56 ↦ₚ₈ u56 -∗
  tf_pa tfp 64 ↦ₚ₈ u64 -∗
  tf_pa tfp 72 ↦ₚ₈ u72 -∗
  tf_pa tfp 80 ↦ₚ₈ u80 -∗
  tf_pa tfp 88 ↦ₚ₈ u88 -∗
  tf_pa tfp 96 ↦ₚ₈ u96 -∗
  tf_pa tfp 104 ↦ₚ₈ u104 -∗
  tf_pa tfp 120 ↦ₚ₈ u120 -∗
  tf_pa tfp 128 ↦ₚ₈ u128 -∗
  tf_pa tfp 136 ↦ₚ₈ u136 -∗
  tf_pa tfp 144 ↦ₚ₈ u144 -∗
  tf_pa tfp 152 ↦ₚ₈ u152 -∗
  tf_pa tfp 160 ↦ₚ₈ u160 -∗
  tf_pa tfp 168 ↦ₚ₈ u168 -∗
  tf_pa tfp 176 ↦ₚ₈ u176 -∗
  tf_pa tfp 184 ↦ₚ₈ u184 -∗
  tf_pa tfp 192 ↦ₚ₈ u192 -∗
  tf_pa tfp 200 ↦ₚ₈ u200 -∗
  tf_pa tfp 208 ↦ₚ₈ u208 -∗
  tf_pa tfp 216 ↦ₚ₈ u216 -∗
  tf_pa tfp 224 ↦ₚ₈ u224 -∗
  tf_pa tfp 232 ↦ₚ₈ u232 -∗
  tf_pa tfp 240 ↦ₚ₈ u240 -∗
  tf_pa tfp 248 ↦ₚ₈ u248 -∗
  tf_pa tfp 256 ↦ₚ₈ u256 -∗
  tf_pa tfp 264 ↦ₚ₈ u264 -∗
  tf_pa tfp 272 ↦ₚ₈ u272 -∗
  tf_pa tfp 280 ↦ₚ₈ u280 -∗
  tf_pa tfp 112 ↦ₚ₈ u112 -∗
  (* the kernel-internal process bundle *)
  R pt ksp -∗
  (* the continuation: back at userret, sret-ready.  [pt'] is the user
     table as usertrap leaves it (vmfault may have mapped new pages; the
     root and the trapframe page are stable), [mf] the returned register
     file (callee-saved restored, a0 = the user satp), the [v*] the user
     register values userret will restore. *)
  ( ∀ (pt' : uptd) (mf : regfile)
      (ms' usatp uepc sc' stval' vksat' : mword 64)
      (ksp' vkhart' : bv 64)
      (v40 v48 v56 v64 v72 v80 v88 v96 v104 v120 v128 v136 v144 v152 v160
       v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264
       v272 v280 v112 : bv 64),
    ⌜ud_root pt' = ud_root pt⌝ -∗
    ⌜ud_tfp pt' = ud_tfp pt⌝ -∗
    ⌜udata_cov (ud_um pt') (ud_data pt')⌝ -∗
    ⌜upt_acc_wf (ud_um pt')⌝ -∗
    ⌜upt_map_wf (ud_um pt')⌝ -∗
    ⌜usertrap_ret_ms ms'⌝ -∗
    ⌜callee_saved m mf⌝ -∗
    ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = usatp⌝ -∗
    ⌜satp_rooted usatp (ud_root pt')⌝ -∗
    ⌜satp_rooted vksat' kroot⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms' -∗
    scause ↦ᵣ sc' -∗
    stval ↦ᵣ stval' -∗
    sepc ↦ᵣ uepc -∗
    pc_is ret_tgt -∗
    gpr_file mf -∗
    tlb_inv_pt kroot -∗
    pt_frame (upt_tree_spec (ud_root pt') (ud_tfp pt') (ud_um pt')) -∗
    udata_own (ud_data pt') -∗
    user_cfg C -∗
    (* the trapframe's kernel words, re-armed for the NEXT trap *)
    tf_pa tfp 0 ↦ₚ₈ vksat' -∗
    tf_pa tfp 8 ↦ₚ₈ ksp' -∗
    tf_pa tfp 16 ↦ₚ₈ (mword_of_int KernelSyms.usertrap : mword 64) -∗
    tf_pa tfp 24 ↦ₚ₈ uepc -∗
    tf_pa tfp 32 ↦ₚ₈ vkhart' -∗
    (* the 31 save slots, holding the registers userret restores *)
    tf_pa tfp 40 ↦ₚ₈ v40 -∗
    tf_pa tfp 48 ↦ₚ₈ v48 -∗
    tf_pa tfp 56 ↦ₚ₈ v56 -∗
    tf_pa tfp 64 ↦ₚ₈ v64 -∗
    tf_pa tfp 72 ↦ₚ₈ v72 -∗
    tf_pa tfp 80 ↦ₚ₈ v80 -∗
    tf_pa tfp 88 ↦ₚ₈ v88 -∗
    tf_pa tfp 96 ↦ₚ₈ v96 -∗
    tf_pa tfp 104 ↦ₚ₈ v104 -∗
    tf_pa tfp 120 ↦ₚ₈ v120 -∗
    tf_pa tfp 128 ↦ₚ₈ v128 -∗
    tf_pa tfp 136 ↦ₚ₈ v136 -∗
    tf_pa tfp 144 ↦ₚ₈ v144 -∗
    tf_pa tfp 152 ↦ₚ₈ v152 -∗
    tf_pa tfp 160 ↦ₚ₈ v160 -∗
    tf_pa tfp 168 ↦ₚ₈ v168 -∗
    tf_pa tfp 176 ↦ₚ₈ v176 -∗
    tf_pa tfp 184 ↦ₚ₈ v184 -∗
    tf_pa tfp 192 ↦ₚ₈ v192 -∗
    tf_pa tfp 200 ↦ₚ₈ v200 -∗
    tf_pa tfp 208 ↦ₚ₈ v208 -∗
    tf_pa tfp 216 ↦ₚ₈ v216 -∗
    tf_pa tfp 224 ↦ₚ₈ v224 -∗
    tf_pa tfp 232 ↦ₚ₈ v232 -∗
    tf_pa tfp 240 ↦ₚ₈ v240 -∗
    tf_pa tfp 248 ↦ₚ₈ v248 -∗
    tf_pa tfp 256 ↦ₚ₈ v256 -∗
    tf_pa tfp 264 ↦ₚ₈ v264 -∗
    tf_pa tfp 272 ↦ₚ₈ v272 -∗
    tf_pa tfp 280 ↦ₚ₈ v280 -∗
    tf_pa tfp 112 ↦ₚ₈ v112 -∗
    R pt' (autocast (T := mword) (ksp' : mword 64)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type USERTRAP.
  (* the kernel-internal resources usertrap consumes, for the process
     whose user table is [pt] and whose kernel stack top is [ksp]:
     defined concretely by the (future) proof; threaded opaquely by
     consumers. *)
  Parameter usertrap_res :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId},
      uptd -> mword 64 -> iProp Σ.
  Parameter wp_usertrap :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (kroot : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
      (w0 w8 w16 w24 w32 : bv 64)
      (u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160
       u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264
       u272 u280 u112 : bv 64),
      wp_usertrap_body usertrap_res C pt kroot Φ m ms_v sc_v stval_v sepc_v ksp
        w0 w8 w16 w24 w32
        u40 u48 u56 u64 u72 u80 u88 u96 u104 u120 u128 u136 u144 u152 u160
        u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 u264
        u272 u280 u112.
End USERTRAP.
