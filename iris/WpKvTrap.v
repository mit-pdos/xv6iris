From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvTrap.v — AXIOMATIZED specification of kerneltrap.

   This axiom is about EXECUTING the kerneltrap function body (entry at
   0x800026a2), NOT the `jal` that calls it.  kerneltrap is a normal C
   procedure: it runs starting from its entry with a return address in the
   return register ra, and eventually RETURNS (via its own `ret`) to the
   address held in ra.

   We assume this rather than verifying kerneltrap's body: from PC = the
   kerneltrap entry (0x800026a2) with ra holding an arbitrary return address
   rava, the handler reaches PC = rava, preserving the stack pointer sp, the
   caller's saved-register stack frame, all CSRs/control state, and the page
   tables / TLB.  The general-purpose registers other than sp are
   left ARBITRARY (kerneltrap may clobber the caller-saved temporaries that
   kernelvec is about to restore), so the continuation is universally
   quantified over the resulting register file m' with sp preserved. *)

Section KVTRAP.
  Context `{!riscvGS Σ}.

  (* the 8-byte stack cell at address [a] currently holds [v] *)
  Definition kv_cell (a : mword 64) (v : bv 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ nth_byte v j).

  (* the bundle of control/CSR state kerneltrap preserves across the call *)
  Definition kv_csrs (misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (mc : mword 32) (mcfg : mword 64) (elp0 : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbf2 : vec (option TLB_Entry) (2 ^ 6)) : iProp Σ :=
    (misa ↦ᵣ misa0 ∗ cur_privilege ↦ᵣ Supervisor ∗ hart_state ↦ᵣ HART_ACTIVE tt ∗
     (R_bitvector_64 mideleg) ↦ᵣ mdv0 ∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 ∗ satp ↦ᵣ satp0 ∗
     tlb ↦ᵣ tlbf2 ∗ menvcfg ↦ᵣ menvcfg0 ∗ mseccfg ↦ᵣ mseccfg0 ∗ mie ↦ᵣ mie_v ∗
     elp ↦ᵣ elp0 ∗ mcountinhibit ↦ᵣ mc ∗ minstretcfg ↦ᵣ mcfg ∗
     pmpcfg_n ↦ᵣ pmpcfg0 ∗ pmpaddr_n ↦ᵣ pmpaddr00 ∗ pma_regions ↦ᵣ pmar0 ∗
     htif_tohost_base ↦ᵣ None)%I.
End KVTRAP.

(* The kerneltrap contract: EXECUTING the handler body, entered at its function
   address 0x800026a2 with a return address rava in ra (= gpr1), returns to
   PC = rava — with sp and the saved-register frame and the CSRs preserved and
   the other GPRs arbitrary (but the register file keeps the SAME DOMAIN: the
   handler reads and writes existing registers, it never adds or removes a GPR
   slot — so kernelvec's `ld` restores can still find every callee register). *)
Axiom kerneltrap_returns :
  forall `{!riscvGS Σ}
    (m : gmap register_bitvector_64 (mword 64)) (spnew rava : mword 64)
    (vra vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 : bv 64)
    (pa pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 pa18 : mword 64)
    (misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
    (mc : mword 32) (mcfg : mword 64) (elp0 : mword 1)
    (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
    (pmar0 : list PMA_Region) (tlbf2 : vec (option TLB_Entry) (2 ^ 6))
    (npc0 : mword 64)
    E (Phi : mval -> iProp Σ),
    m !! gpr_of_Z 2 = Some spnew ->     (* sp = frame pointer *)
    m !! gpr_of_Z 1 = Some rava ->      (* ra = return address *)
    PC ↦ᵣ (mword_of_int 0x800026a2 : mword 64) -∗ nextPC ↦ᵣ npc0 -∗ gpr_file m -∗ minstret_inv -∗
    kv_csrs misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbf2 -∗
    kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
    kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
    kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
    kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
    ▷ ( ∀ (m' : gmap register_bitvector_64 (mword 64)) (npc' : mword 64),
        ⌜ m' !! gpr_of_Z 2 = Some spnew ⌝ -∗ ⌜ dom m' = dom m ⌝ -∗
        PC ↦ᵣ rava -∗ nextPC ↦ᵣ npc' -∗ gpr_file m' -∗ minstret_inv -∗
        kv_csrs misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbf2 -∗
        kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
        kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
        kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
        kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
