(* WpIntrOff.v -- intr_off() at push_off level 0, FROM EITHER INDEX.

   xv6's [intr_off()] is one instruction, [csrci sstatus,2], and until now
   the tier had a leaf for it only at the ENABLED index:
   [WpSconfCsr.wp_csrci_sstatus_x0_s_sconf] is the real '1' -> '0' flip and
   REFUTES its [b = false] arm outright (its [intr_count_pre b 0 true]
   premise is unsatisfiable there -- the count eighth at '1' contradicts the
   capability's '0' eighth).  So a caller that reaches an [intr_off()] with
   interrupts ALREADY off had no leaf at all.

   THAT CALLER IS prepare_return, AND THROUGH IT usertrap.  usertrap enters
   from uservec with SIE = 0 and enables interrupts only on the SYSCALL path
   ([csrsi sstatus,2] just before the [jal syscall]); the devintr, vmfault
   and unexpected-scause paths all reach [prepare_return] still disabled.
   A contract for prepare_return pinned at [b = true] therefore covers only
   one of usertrap's four routes into it.

   THE COMPOSITE BELOW IS WHAT MAKES THE CONTRACT INDEX-GENERIC, and it is
   stated over [CpuOwn.cpu_own] rather than over the leaf's raw pieces
   because that is what makes its POSTCONDITION index-free: whichever arm the
   caller came in on, it leaves holding [cpu_own 0 false p C false] and
   [trap_csrs], so the code after the [csrci] is proved ONCE.  The two arms
   differ only in where those come from:

     b = true   the flip is real.  [sie_arm true p] is dismantled and pays
                out the trap CSRs, the per-cpu cells, the counting token at
                [sie_bit false], and the reserve [trap_res true] -- so
                [trap_csrs_ext true = emp]: the caller brings nothing.
     b = false  the write clears a bit that is already clear
                ([wp_csrci_sstatus_x0_idem_s_sconf]).  Nothing moves and
                nothing is paid out, so the caller brings the trap CSRs
                itself ([trap_csrs_ext false = trap_csrs]) and keeps its own
                cells; [trap_res false = 0], so the index does not move
                either.

   [trap_csrs_ext] is exactly the complement [IntrDefs] already defines for
   this seam ("what a caller has to BRING because the bundle does not already
   own it"), which is what SpecYield/SpecSched use to park at [eb = false];
   this file is the same accounting one instruction lower down.               *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import HartTp WpNext.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpPushOffCsr.   (* [csr_sstatus] -- WpSconfCsr's copy is [Local] *)
Require Import WpSconfCsr.
Local Open Scope Z_scope.
Import Defs.

Section WpIntrOff.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_intr_off_lvl0_s_sconf
      (pc : mword 64) (b : bool) (p : mword 64)
      (m : regfile) (n : nat) (C : iProp Σ) :
    sie_cap_gpr m n b p -∗
    cpu_own 0%nat b p C b -∗
    trap_csrs_ext b -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m (trap_res b + n)%nat false p -∗
      cpu_own 0%nat false p C false -∗
      trap_csrs -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    destruct b.
    - (* ---- ENABLED: the real flip.  Everything comes out of the arm. ---- *)
      iIntros "Hcg Hcpu _ Hpc Hinstr Hcont".
      iDestruct "Hcpu" as "[_ HC]".
      iApply (wp_csrci_sstatus_x0_s_sconf pc m n true with "Hcg [] Hpc Hinstr [HC Hcont]").
      { iPureIntro. exact (conj eq_refl eq_refl). }
      iIntros (CIDn Hk ms) "%Hmsf Hcg Hcnt Hcsrs Hcells Hpc".
      iDestruct (wp_next_at true p _ CIDn Hk with "Hcont") as "Hcont".
      iApply ("Hcont" $! ms with "[%//] Hcg [Hcells Hcnt HC] Hcsrs Hpc").
      rewrite /cpu_own /cpu_hart /cpu_cells_pay. iFrame "Hcells Hcnt HC".
    - (* ---- ALREADY DISABLED: a no-op; the caller brought the CSRs. ---- *)
      iIntros "Hcg Hcpu Hcsrs Hpc Hinstr Hcont".
      iApply (wp_csrci_sstatus_x0_idem_s_sconf pc m n with "Hcg Hpc Hinstr").
      iApply wp_next_off_intro. iIntros (ms) "%Hmsf Hcg Hpc".
      iDestruct (wp_next_here false p with "Hcont") as "Hcont".
      iApply ("Hcont" $! ms with "[%//] Hcg Hcpu Hcsrs Hpc").
  Qed.

End WpIntrOff.

(* THE TRANSPORT THE CALLERS NEED, the [trap_csrs_ext] twin of
   [CpuOwn.cpu_own_transport].  A caller that holds the complement at [b =
   false] holds REAL per-hart CSR cells, so it cannot simply frame them past
   a step whose continuation rebinds the hart -- but at [b = false] no step
   moves the hart, and at [b = true] the complement is [emp].  Both arms are
   therefore free, which is the whole point of guarding on the same index.

   Stated here rather than beside [trap_csrs_ext] in IntrDefs because this is
   the file about that seam, and nothing below it needs the lemma. *)
Lemma trap_csrs_ext_transport `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId}
    (CID0 CID1 : CpuId) (p : mword 64) (b : bool) :
  (b = false \/ p = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
  trap_csrs_ext (CID := CID0) b -∗ trap_csrs_ext (CID := CID1) b.
Proof.
  intros Heq. destruct b.
  - iIntros "$".
  - rewrite (_ : CID1 = CID0); [ iIntros "$" | exact (Heq (or_introl eq_refl)) ].
Qed.
