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

   WHAT THE POSTCONDITION SAYS, AND WHY IT IS SHAPED THIS WAY.  The machine
   state <main> starts on is quantified, not spelled: the contract hands back
   an arbitrary register file and an arbitrary value for each CSR the boot
   writes, plus the FACTS a client consumes about them.  It used to name the
   post-state literally -- [st_mout (m_jal m v_stack0 mhartid_in) sp0 ms0 ...],
   the top of a 27-deep tower of one [Definition] per register write over
   timerinit's 15 over _entry's 8 -- which put fifty proof-internal
   definitions, and through them three [Code*.v] files, into the require
   closure of every Spec file that could reach this one.  It also said far
   more than anybody reads: the sole client ([BootBridge.boot_bridge])
   projects sp and tp out of that file with two lemmas and then existentially
   quantifies it.  So the two projections are stated here as equations, and
   the tower stays behind [WpStartNew.st_mout_sp] / [st_mout_tp].

   The facts, and who wants them:

     sp = [mb_frame sp0]     start() MRETs from inside itself, so its 16-byte
                             frame is never popped; the S-mode side takes the
                             stack from there down.
     tp = [mb_tpv mhartid]   the hart id, which is the cid convention.
     [mstatus_kernel_facts]  of the FINAL mstatus -- this is what makes the
                             contract composable with the S-mode side, since
                             [IntrDefs.sconf_ms_facts_of_kernel] and
                             [MstatusFacts.mstatus_kernel_SIE] are both one
                             step off it.
     menvcfg = [MENVCFG_S],  the sconf tier's four CSR side conditions.  [mie]
     mie & ~mideleg = 0,     is handed over as an exact value and not only as a
     mie = [MIE_S],          relation with mideleg because the set of interrupt
     satp.Mode = Bare        causes that can ever be delivered is masked by it,
                             so the S-mode side can only compute that set from
                             a pinned [mie] -- see
                             claude-notes/projects/kerneltrap.md.
     [mb_pmp_open]           PMP entry 0 as [SmodeCore.pmp_config_intro] wants
                             it, so the Bare translation arm can be built
                             without knowing which pmpcfg the machine powered
                             up with.

   Deriving those needs the entry machine to be a reset machine in three
   registers ([menvcfg0] / [mie0] / [mideleg0] all zero), which is a PREMISE
   here rather than, as before, a proof obligation exported to the client
   together with the entry mstatus.  Nothing is lost: the entry mstatus is
   hidden inside [mmode_config], so a client could never have discharged it
   itself, and the only client already pins all three off [reset_regs].

   Everything this is stated over lives in [MbootVocab.v] and the definitional
   layer -- no [Code*.v], no weakest precondition. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvFetchExec WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import InstrBytes StackOwn.
Require Import MbootVocab.
Require Import MstatusFacts.
Require Import KernelText.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* The whole M-mode boot as one WP: [_entry] -> start() -> timerinit() ->
   MRET -> <main> in Supervisor mode. *)
Definition wp_entry_boot_body `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
    (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
    (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
    (mcounteren0 : mword 32)
    (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
    (sp0 : mword 64) (n : nat) (dq : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms._entry in
  let pcMain : mword 64 := mword_of_int KernelSyms.main in
  (* the stack pointer _entry computes and start() runs on.  It is a
     PARAMETER with a defining premise rather than a [let], so a caller that
     knows where the linker put [stack0] names its own concrete address and
     every occurrence below -- the stack resource, the frame bounds, the
     final sp -- is already at it. *)
  mb_entry_sp v_stack0 mhartid_in = sp0 ->
  (4 <= n)%nat ->
  (* boot pmp config: all entries OFF. *)
  pmp_all_off pmpcfg0 ->
  (* a reset machine in the three CSRs the post-state facts are derived from *)
  menvcfg0 = (mword_of_int 0 : mword 64) ->
  mie0 = (mword_of_int 0 : mword 64) ->
  mideleg0 = (mword_of_int 0 : mword 64) ->
  (* stack geometry, over the symbolic sp0: timerinit's two frame slots are
     inside the written PMP TOR region [0, 0xfffffffffffffc). *)
  uint (mb_ti_ra sp0) + 8 <= 0xfffffffffffffc ->
  uint (mb_ti_s0 sp0) + 8 <= 0xfffffffffffffc ->
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
  mb_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
  (* start()'s 4-slot frame (own ra/s0 + child timerinit's ra/s0) as the
     bottom four slots of [stack_own_phys sp0 n] (any depth n >= 4). *)
  stack_own_phys sp0 n -∗
  kernel_text -∗
  ( ∀ (Mf : regfile)
      (msf satpf medelegf midelegf mief menvcfgf stimecmpf : mword 64)
      (mcounterenf : mword 32)
      (pmpcfgf : type_of_register pmpcfg_n)
      (pmpaddrf : type_of_register pmpaddr_n),
    ⌜ Mf !!! Regidx csp_rs1 = mb_frame sp0
      /\ Mf !!! Regidx (mword_of_int 4 : mword 5) = mb_tpv mhartid_in
      /\ mstatus_kernel_facts msf
      /\ menvcfgf = MENVCFG_S
      /\ and_vec mief (not_vec midelegf) = zeros' 64
      /\ mief = MIE_S
      /\ _get_Satp64_Mode (Mk_Satp64 satpf) = ('b"0000" : mword 4)
      /\ mb_pmp_open pmpcfgf pmpaddrf
      (* THE TIMER BIT.  timerinit sets mcounteren.TM ([ori a5,a5,2] then
         [csrw mcounteren]), and S-mode needs to KNOW it: [TimerCap.timer_cap]
         -- the credential clockintr runs under, and therefore one of the
         things kerneltrap's cone closes over -- is exactly this fact plus the
         two cells below.  Stated here for the same reason [mief = MIE_S] is:
         the M-mode proof computes the value, so it is free there and
         unobtainable anywhere else. *)
      /\ eq_vec (_get_Counteren_TM mcounterenf) ('b"1" : mword 1) = true ⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ msf -∗
    pmpcfg_n ↦ᵣ pmpcfgf -∗
    pmpaddr_n ↦ᵣ pmpaddrf -∗
    pc_is pcMain -∗
    gpr_file Mf -∗
    mhartid ↦ᵣ mhartid_in -∗
    mepc ↦ᵣ pcMain -∗
    satp ↦ᵣ satpf -∗
    medeleg ↦ᵣ medelegf -∗
    mideleg ↦ᵣ midelegf -∗
    mie ↦ᵣ mief -∗
    menvcfg ↦ᵣ menvcfgf -∗
    mcounteren ↦ᵣ mcounterenf -∗
    stimecmp ↦ᵣ stimecmpf -∗
    mb_ld_ea ↦ₚ₈{ dq } v_stack0 -∗
    stack_own_phys sp0 n -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ENTRY.
  Parameter wp_entry_boot :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (sp0 : mword 64) (n : nat) {dq : dfrac},
      wp_entry_boot_body m v_stack0 mhartid_in mepc0 satp0 medeleg0 mideleg0
        mie0 menvcfg0 stimecmp0 mcounteren0 pmpcfg0 pmpaddr00 sp0 n dq.
End ENTRY.
