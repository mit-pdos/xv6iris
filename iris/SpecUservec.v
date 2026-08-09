(* SpecUservec.v -- the public interface of uservec (trampoline.S), stated
   independently of its proof.

   uservec is the kernel's stvec handler for traps OUT OF USER MODE: it
   begins executing at virtual address TRAMPOLINE (= stvec's direct base)
   with the USER page table still installed, saves the 31 user registers
   into the TRAPFRAME page (through the user table's trapframe leaf),
   loads the kernel sp / hartid / usertrap pointer / kernel satp from the
   trapframe's kernel words, switches satp to the KERNEL table (the pt2
   window, roles swapped relative to userret), and jalr's to usertrap with
   ra pointing at userret (uva 0x9c).

   THE INTERFACE MATCHES THE USER-MODE WP.  [wp_user_exec_closed]
   (SpecUser.v) assumes [stvec_handler_wp C pt Φ], which is by definition
   [user_trap_frame C pt -∗ WP Loop {{ Φ }}].  This spec consumes exactly
   [user_trap_frame C pt] -- the machine as the trap hands it over:
   Supervisor, pc at [stvec_base (uc_stvec C)], mstatus with the
   [trap_mstatus_ok] pins (SIE=0 SPP=User MPRV=0 MXR=0 SXL=64 TVM=0 TSR=0
   -- the TVM/TSR pins are what license the sfence.vma / csrw satp here),
   ARBITRARY register file / trap CSR values, the user page-table bundle
   [user_pt_inv pt] and the config [user_cfg C].  So discharging
   [stvec_handler_wp] is: apply [wp_uservec_pt] to the trap frame plus the
   KERNEL-side resources below (which ride outside user execution), and
   continue at usertrap.

   The kernel-side resources (owned by whoever parks the kernel while user
   code runs -- they cannot live inside [user_inv], since user code must
   not touch them):
     - [sscratch]: written (user a0) then read back; full cell.
     - the 31 trapframe SAVE slots [tf_pa tfp 40..280, 112]: WRITTEN with
       the user registers, so owned at full fraction, old contents
       forgotten (existential [w*] in, user values out).
     - the 4 trapframe KERNEL words (offset 0 = kernel_satp, 8 =
       kernel_sp, 16 = kernel_trap, 32 = kernel_hartid): only READ, so
       dfrac-generic.  kernel_satp must be a Sv39/asid-0 value rooted at
       [kroot] (the premises mirror userret's user-satp premises with the
       roles swapped); the jalr target is [ret_pc vktr] (bit 0 cleared by
       the hardware), which a consumer pins to KernelSyms.usertrap.
     - [kpt_frame kroot]: the parked kernel table (userret's post); the
       exit switch re-seals it into the live [tlb_inv_pt kroot].

   The continuation is universally quantified over the trap frame's
   existentials (the user register file [g], the delivered mstatus and
   trap-CSR values): uservec preserves them all -- the trap CSRs are
   exactly what usertrap will read, the user registers are handed over
   IN the trapframe words, and the register file it leaves is the
   deterministic [uservec_gpr g ...] tower. *)
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
Require Import MinstretInv InstrBytes.
Require Import WpGpr.
Require Import KernelText.
Require Import SmodeCore.
Require Import PtTree.
Require Import TrampPt KptTree UptTree TransPt UserretDefs.
Require Import UserPtTree UserExec.
Require Import SpecUserret.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* the register file uservec leaves for usertrap (insert order = execution
   order): a0 := TRAPFRAME (the li), t0 := the saved user a0 (csrr
   sscratch, later overwritten), sp := kernel_sp, tp := kernel_hartid,
   t0 := usertrap pointer, t1 := kernel_satp, ra := uva 0x9c (the c.jalr
   link -- usertrap returns straight into userret). *)
Definition uservec_gpr (g : regfile) (vksp vkhart vktr vksat : bv 64) : regfile :=
  <[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]>
  (<[Regidx (mword_of_int 6) := regval_into_reg vksat]>
  (<[Regidx (mword_of_int 5) := regval_into_reg vktr]>
  (<[Regidx (mword_of_int 4) := regval_into_reg vkhart]>
  (<[Regidx (mword_of_int 2) := regval_into_reg vksp]>
  (<[Regidx (mword_of_int 5) := regval_into_reg (g !!! Regidx (mword_of_int 10) : mword 64)]>
  (<[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> g)))))).

Definition wp_uservec_pt_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (C : ucfg) (pt : uptd) (kroot : mword 44) (Φ : mval -> iProp Σ)
    (sscr0 : mword 64)
    (vksat vksp vktr vkhart : bv 64)
    (w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160
     w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264
     w272 w280 w112 : bv 64)
    (dqk : dfrac) :=
  let uroot := ud_root pt in
  let tfp := ud_tfp pt in
  let um := ud_um pt in
  (* stvec points at the trampoline base *)
  uc_stvec C = mword_of_int TRAMPOLINE ->
  (* the kernel owns the config cells outright at this join (same fact the
     userret-side bridge [userret_to_user_inv] requires): the step leaves
     drive all six machine/config cells at ONE dfrac, and the trap frame
     holds hart_state/cur_privilege/mstatus at full *)
  uc_dqc C = DfracOwn 1 ->
  (* trapframe word 0 holds the KERNEL satp value, rooted at [kroot] *)
  _get_Satp64_Mode (Mk_Satp64 (vksat : mword 64)) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) (vksat : mword 64) : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) (vksat : mword 64) : mword 64)) = kroot ->
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  (* the trampoline claim, threaded to the exit switch (persistent; the
     caller holds it from kvminithart's postcondition -- same premise
     [wp_userret_pt] takes) *)
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  (* the machine, exactly as the trap delivers it *)
  user_trap_frame C pt -∗
  (* the kernel-side resources parked while user code ran *)
  sscratch ↦ᵣ sscr0 -∗
  kpt_frame kroot -∗
  tf_pa tfp 0 ↦ₚ₈{ dqk } vksat -∗
  tf_pa tfp 8 ↦ₚ₈{ dqk } vksp -∗
  tf_pa tfp 16 ↦ₚ₈{ dqk } vktr -∗
  tf_pa tfp 32 ↦ₚ₈{ dqk } vkhart -∗
  tf_pa tfp 40 ↦ₚ₈ w40 -∗
  tf_pa tfp 48 ↦ₚ₈ w48 -∗
  tf_pa tfp 56 ↦ₚ₈ w56 -∗
  tf_pa tfp 64 ↦ₚ₈ w64 -∗
  tf_pa tfp 72 ↦ₚ₈ w72 -∗
  tf_pa tfp 80 ↦ₚ₈ w80 -∗
  tf_pa tfp 88 ↦ₚ₈ w88 -∗
  tf_pa tfp 96 ↦ₚ₈ w96 -∗
  tf_pa tfp 104 ↦ₚ₈ w104 -∗
  tf_pa tfp 120 ↦ₚ₈ w120 -∗
  tf_pa tfp 128 ↦ₚ₈ w128 -∗
  tf_pa tfp 136 ↦ₚ₈ w136 -∗
  tf_pa tfp 144 ↦ₚ₈ w144 -∗
  tf_pa tfp 152 ↦ₚ₈ w152 -∗
  tf_pa tfp 160 ↦ₚ₈ w160 -∗
  tf_pa tfp 168 ↦ₚ₈ w168 -∗
  tf_pa tfp 176 ↦ₚ₈ w176 -∗
  tf_pa tfp 184 ↦ₚ₈ w184 -∗
  tf_pa tfp 192 ↦ₚ₈ w192 -∗
  tf_pa tfp 200 ↦ₚ₈ w200 -∗
  tf_pa tfp 208 ↦ₚ₈ w208 -∗
  tf_pa tfp 216 ↦ₚ₈ w216 -∗
  tf_pa tfp 224 ↦ₚ₈ w224 -∗
  tf_pa tfp 232 ↦ₚ₈ w232 -∗
  tf_pa tfp 240 ↦ₚ₈ w240 -∗
  tf_pa tfp 248 ↦ₚ₈ w248 -∗
  tf_pa tfp 256 ↦ₚ₈ w256 -∗
  tf_pa tfp 264 ↦ₚ₈ w264 -∗
  tf_pa tfp 272 ↦ₚ₈ w272 -∗
  tf_pa tfp 280 ↦ₚ₈ w280 -∗
  tf_pa tfp 112 ↦ₚ₈ w112 -∗
  (* the continuation: at usertrap, on the kernel table, the user machine
     fully banked into the trapframe.  Universally quantified over the trap
     frame's existentials -- [g] is the interrupted USER register file. *)
  ( ∀ (g : regfile) (ms_v sc_v stval_v sepc_v : mword 64),
    ⌜trap_mstatus_ok ms_v⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    sscratch ↦ᵣ (g !!! Regidx (mword_of_int 10) : mword 64) -∗
    tlb_inv_pt kroot -∗
    pt_frame (upt_tree_spec uroot tfp um) -∗
    udata_own (ud_data pt) -∗
    user_cfg C -∗
    pc_is (ret_pc (vktr : mword 64)) -∗
    gpr_file (uservec_gpr g vksp vkhart vktr vksat) -∗
    tf_pa tfp 0 ↦ₚ₈{ dqk } vksat -∗
    tf_pa tfp 8 ↦ₚ₈{ dqk } vksp -∗
    tf_pa tfp 16 ↦ₚ₈{ dqk } vktr -∗
    tf_pa tfp 32 ↦ₚ₈{ dqk } vkhart -∗
    tf_pa tfp 40 ↦ₚ₈ (g !!! Regidx (mword_of_int 1) : mword 64) -∗
    tf_pa tfp 48 ↦ₚ₈ (g !!! Regidx (mword_of_int 2) : mword 64) -∗
    tf_pa tfp 56 ↦ₚ₈ (g !!! Regidx (mword_of_int 3) : mword 64) -∗
    tf_pa tfp 64 ↦ₚ₈ (g !!! Regidx (mword_of_int 4) : mword 64) -∗
    tf_pa tfp 72 ↦ₚ₈ (g !!! Regidx (mword_of_int 5) : mword 64) -∗
    tf_pa tfp 80 ↦ₚ₈ (g !!! Regidx (mword_of_int 6) : mword 64) -∗
    tf_pa tfp 88 ↦ₚ₈ (g !!! Regidx (mword_of_int 7) : mword 64) -∗
    tf_pa tfp 96 ↦ₚ₈ (g !!! Regidx (mword_of_int 8) : mword 64) -∗
    tf_pa tfp 104 ↦ₚ₈ (g !!! Regidx (mword_of_int 9) : mword 64) -∗
    tf_pa tfp 120 ↦ₚ₈ (g !!! Regidx (mword_of_int 11) : mword 64) -∗
    tf_pa tfp 128 ↦ₚ₈ (g !!! Regidx (mword_of_int 12) : mword 64) -∗
    tf_pa tfp 136 ↦ₚ₈ (g !!! Regidx (mword_of_int 13) : mword 64) -∗
    tf_pa tfp 144 ↦ₚ₈ (g !!! Regidx (mword_of_int 14) : mword 64) -∗
    tf_pa tfp 152 ↦ₚ₈ (g !!! Regidx (mword_of_int 15) : mword 64) -∗
    tf_pa tfp 160 ↦ₚ₈ (g !!! Regidx (mword_of_int 16) : mword 64) -∗
    tf_pa tfp 168 ↦ₚ₈ (g !!! Regidx (mword_of_int 17) : mword 64) -∗
    tf_pa tfp 176 ↦ₚ₈ (g !!! Regidx (mword_of_int 18) : mword 64) -∗
    tf_pa tfp 184 ↦ₚ₈ (g !!! Regidx (mword_of_int 19) : mword 64) -∗
    tf_pa tfp 192 ↦ₚ₈ (g !!! Regidx (mword_of_int 20) : mword 64) -∗
    tf_pa tfp 200 ↦ₚ₈ (g !!! Regidx (mword_of_int 21) : mword 64) -∗
    tf_pa tfp 208 ↦ₚ₈ (g !!! Regidx (mword_of_int 22) : mword 64) -∗
    tf_pa tfp 216 ↦ₚ₈ (g !!! Regidx (mword_of_int 23) : mword 64) -∗
    tf_pa tfp 224 ↦ₚ₈ (g !!! Regidx (mword_of_int 24) : mword 64) -∗
    tf_pa tfp 232 ↦ₚ₈ (g !!! Regidx (mword_of_int 25) : mword 64) -∗
    tf_pa tfp 240 ↦ₚ₈ (g !!! Regidx (mword_of_int 26) : mword 64) -∗
    tf_pa tfp 248 ↦ₚ₈ (g !!! Regidx (mword_of_int 27) : mword 64) -∗
    tf_pa tfp 256 ↦ₚ₈ (g !!! Regidx (mword_of_int 28) : mword 64) -∗
    tf_pa tfp 264 ↦ₚ₈ (g !!! Regidx (mword_of_int 29) : mword 64) -∗
    tf_pa tfp 272 ↦ₚ₈ (g !!! Regidx (mword_of_int 30) : mword 64) -∗
    tf_pa tfp 280 ↦ₚ₈ (g !!! Regidx (mword_of_int 31) : mword 64) -∗
    tf_pa tfp 112 ↦ₚ₈ (g !!! Regidx (mword_of_int 10) : mword 64) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type USERVEC.
  Parameter wp_uservec_pt :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (kroot : mword 44) (Φ : mval -> iProp Σ)
      (sscr0 : mword 64)
      (vksat vksp vktr vkhart : bv 64)
      (w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160
       w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264
       w272 w280 w112 : bv 64)
      (dqk : dfrac),
      wp_uservec_pt_body C pt kroot Φ sscr0 vksat vksp vktr vkhart
        w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160
        w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264
        w272 w280 w112 dqk.
End USERVEC.
