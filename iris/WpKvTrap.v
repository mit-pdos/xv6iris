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

   kernelvec, after saving the caller's registers, does `jal kerneltrap`
   @0x80005404 (which sets ra = 0x80005408, the following instruction) and
   kerneltrap eventually RETURNS to the address held in ra (0x80005408).

   We assume this as an axiom rather than verifying kerneltrap's body. The
   axiom absorbs the jal and the whole handler: from the post-prologue state
   (PC at the jal) it reaches PC = the return address (= ra), preserving the
   stack pointer sp, the saved-register stack frame, all CSRs/control state,
   and the page tables / TLB.  The general-purpose registers other than sp are
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

(* The kerneltrap contract: jal kerneltrap @0x80005404 followed by the handler
   returns to PC = 0x80005408 (the address in ra), with sp and the frame and the
   CSRs preserved and the other GPRs arbitrary. *)
Axiom kerneltrap_jal_returns :
  forall `{!riscvGS Σ}
    (m : gmap register_bitvector_64 (mword 64)) (spnew : mword 64)
    (vra vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 : bv 64)
    (pa pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 pa18 : mword 64)
    (misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
    (mc : mword 32) (mcfg : mword 64) (elp0 : mword 1)
    (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
    (pmar0 : list PMA_Region) (tlbf2 : vec (option TLB_Entry) (2 ^ 6))
    (npc0 : mword 64) (wjal : mword 32)
    E (Phi : mval -> iProp Σ) {dq : dfrac},
    m !! gpr_of_Z 2 = Some spnew ->
    PC ↦ᵣ (mword_of_int 0x80005404 : mword 64) -∗ nextPC ↦ᵣ npc0 -∗ gpr_file m -∗ minstret_inv -∗
    kv_csrs misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbf2 -∗
    kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
    kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
    kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
    kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x80005404) j) ↦ₘ{dq} nth_byte wjal j) -∗
    ▷ ( ∀ (m' : gmap register_bitvector_64 (mword 64)) (npc' : mword 64),
        ⌜ m' !! gpr_of_Z 2 = Some spnew ⌝ -∗
        PC ↦ᵣ (mword_of_int 0x80005408 : mword 64) -∗ nextPC ↦ᵣ npc' -∗ gpr_file m' -∗ minstret_inv -∗
        kv_csrs misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v mc mcfg elp0 pmpcfg0 pmpaddr00 pmar0 tlbf2 -∗
        kv_cell pa vra -∗ kv_cell pa3 vgp -∗ kv_cell pa4 vt0 -∗ kv_cell pa5 vR5 -∗ kv_cell pa6 vR6 -∗
        kv_cell pa7 vR7 -∗ kv_cell pa8 vR8 -∗ kv_cell pa9 vR9 -∗ kv_cell pa10 vR10 -∗ kv_cell pa11 vR11 -∗
        kv_cell pa12 vR12 -∗ kv_cell pa13 vR13 -∗ kv_cell pa14 vR14 -∗ kv_cell pa15 vR15 -∗ kv_cell pa16 vR16 -∗
        kv_cell pa17 vR17 -∗ kv_cell pa18 vR18 -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x80005404) j) ↦ₘ{dq} nth_byte wjal j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
