(* SpecEntry.v -- the public interface of the M-mode boot path, stated once:
   ONE weakest precondition for starting execution at [_entry] (the state the
   CPU is in coming out of reset: PC = 0x80000000, Machine mode, all-OFF PMP)
   and running all the way to <main> in SUPERVISOR mode.

   The kernel code this covers is the whole M-mode boot, in three pieces the
   spec deliberately does NOT expose separately:

     _entry      (entry.S)   la sp,stack0; sp += 4096*(mhartid+1); call start
     start()     (start.c)   MPP=S, mepc=main, delegate traps, open the PMP,
                             timerinit(), tp = mhartid, MRET
     timerinit() (start.c)   stimecmp = time + interval, menvcfg.STCE,
                             mcounteren.TM, mie.STIE

   so a client sees exactly one contract: "power up here, arrive at <main> in
   S-mode with these registers".  The piecemeal lemmas the proof is composed
   from ([wp_entry], [wp_start], [wp_timerinit]) stay where they are and are
   linked together in ProofEntry.v.

   The postcondition is the exact machine state <main> starts on: Supervisor
   privilege, the legalized CSR values start() wrote (mstatus / medeleg /
   mideleg / mie / satp / menvcfg / mcounteren / stimecmp), the widened PMP
   entry 0, and the register file [st_mout ...] with tp = mhartid.  [tv] is
   the (unconstrained) value timerinit() read out of the mtime device, and
   [ms0] the entry mstatus, hidden behind the ∀ in the continuation together
   with the three facts [mmode_config] pins about it.

   NOTE on requires: unlike the other Spec files, this one is not stated over
   the definitional layer alone -- the post-state vocabulary it needs
   ([m_jal], [entry_ld_ea], [st_mout], [st_pmpcfg1], [ti_deadline], ...) is
   defined inside WpEntryNew.v / WpStartNew.v / WpTimerinit.v, so it requires
   those.  Splitting that pure vocabulary into a definitional file would make
   this spec decouple from the M-mode proofs the way the S-mode Spec files do
   from theirs; nothing else here depends on that split. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvFetchExec WpEntry WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpGprCsrwA WpGprCsrwB.
Require Import WpGprMretWp.
Require Import InstrBytes WpEntryNew WpTimerinit WpStartNew StackOwn.
Require Import KernelText.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* The whole M-mode boot as one WP: [_entry] -> start() -> timerinit() ->
   MRET -> <main> in Supervisor mode. *)
Definition wp_entry_boot_body `{!riscvGS Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
    (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
    (mcounteren0 : mword 32)
    (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
    (n : nat) (dq : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms._entry in
  let pcMain : mword 64 := mword_of_int KernelSyms.main in
  (* the stack pointer start() runs on: _entry's computed sp
     (= v_stack0 + 4096 * (mhartid + 1)). *)
  let sp0 : mword 64 := m_jal m v_stack0 mhartid_in !!! Regidx csp_rs1 in
  (4 <= n)%nat ->
  (* boot pmp config: all entries OFF. *)
  pmp_all_off pmpcfg0 ->
  (* boot menvcfg has the Zicfilp landing-pad enable clear. *)
  _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
  (* stack geometry, over the symbolic sp0: timerinit's two frame slots are
     inside the written PMP TOR region [0, 0xfffffffffffffc). *)
  uint (ti_ea_ra (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
  uint (ti_ea_s0 (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
  mmode_config (DfracOwn 1) -∗
  pmpcfg_n ↦ᵣ pmpcfg0 -∗
  pmpaddr_n ↦ᵣ pmpaddr00 -∗
  pc_is pcE -∗
  gpr_file m -∗
  mhartid ↦ᵣ mhartid_in -∗
  mepc ↦ᵣ mepc0 -∗
  satp ↦ᵣ satp0 -∗
  medeleg ↦ᵣ medeleg0 -∗
  mideleg ↦ᵣ mideleg0 -∗
  mie ↦ᵣ mie0 -∗
  menvcfg ↦ᵣ menvcfg0 -∗
  mcounteren ↦ᵣ mcounteren0 -∗
  stimecmp ↦ᵣ stimecmp0 -∗
  (* the per-CPU stack0 pointer word _entry loads *)
  entry_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
  (* start()'s 4-slot frame (own ra/s0 + child timerinit's ra/s0) as the
     bottom four slots of [stack_own_phys sp0 n] (any depth n >= 4). *)
  stack_own_phys sp0 n -∗
  kernel_text -∗
  ( ∀ (tv : mword 64) (ms0 : mword 64)
      (HoIE : eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false)
      (HoPRV : eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false)
      (HoSXL : _get_Mstatus_SXL ms0 = ('b"10")),
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ cms5 (st_ms1 ms0) -∗
    pmpcfg_n ↦ᵣ st_pmpcfg1 pmpcfg0 -∗
    pmpaddr_n ↦ᵣ st_pmpaddr1 pmpcfg0 pmpaddr00 -∗
    pc_is pcMain -∗
    gpr_file (st_mout (m_jal m v_stack0 mhartid_in) sp0 ms0 mie0 mideleg0
                menvcfg0 mcounteren0 tv mhartid_in) -∗
    mhartid ↦ᵣ mhartid_in -∗
    mepc ↦ᵣ pcMain -∗
    satp ↦ᵣ satp_legalized satp0 (mword_of_int 0) -∗
    medeleg ↦ᵣ legalize_medeleg medeleg0 st_ffff -∗
    mideleg ↦ᵣ st_mdl1 mideleg0 -∗
    mie ↦ᵣ st_mie1 mie0 mideleg0 -∗
    menvcfg ↦ᵣ menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)) -∗
    mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (ti_mcen1 mcounteren0) -∗
    stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
    entry_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
    stack_own_phys sp0 n -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ENTRY.
  Parameter wp_entry_boot :
    forall `{!riscvGS Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (n : nat) {dq : dfrac},
      wp_entry_boot_body Φ m v_stack0 mhartid_in mepc0 satp0 medeleg0 mideleg0
        mie0 menvcfg0 stimecmp0 mcounteren0 pmpcfg0 pmpaddr00 n dq.
End ENTRY.
