(* SpecFreeDesc.v -- the public interface of free_desc, stated independently
   of its proof.

   free_desc(i) runs UNDER the caller's vdisk_lock critical section, so it
   takes no lock: the caller opens [disk_res], hands this spec the pieces
   free_desc touches (the free[i] cell, at 0, and descriptor entry i's four
   words), and folds the returned pieces back into the free-slot bundle
   (the caller supplies ops/status/info from its own holdings).

   Both panic arms are REFUTED, not assumed:
     - "free_desc 1" (i >= NUM): by the caller's bound i < 8;
     - "free_desc 2" (disk.free[i] already set): the caller's cell reads 0.
   The wakeup(&disk.free[0]) call threads SpecWakeup's plumbing. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import VirtioModel DiskPtsto DiskInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* free_desc's own frame is 16 bytes (2 slots); its only callee is wakeup (18) *)
Definition K_free_desc : nat := 20%nat.

Definition wp_free_desc_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname)
    (pd : mword 64) (i : nat)
    (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
    (va : mword 64) (vl : mword 32) (vf vn : mword 16) :=
  let pcE : mword 64 := mword_of_int KernelSyms.free_desc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_free_desc <= K)%nat ->
  (i < 8)%nat ->
  uint (m !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = Z.of_nat i ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr γ m K -∗
  cpu_own γ lvl eb pme C -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp -∗ procs_inv γ Φ γs -∗
  (* the descriptor-page pointer cell: free_desc RE-READS [disk.desc] (twice)
     to reach entry [i], so it needs the persistent half of [disk_geom] that
     names the page [pd] the four descriptor words below live on. *)
  d_desc_ptr ↦₈□ pd -∗
  (* the free cell, provably clear *)
  d_free_cell i ↦ₘ byte_zero -∗
  (* descriptor entry i's four words *)
  d_desc pd i ↦₈ va -∗
  pa_add pd (16 * i + 8)  ↦₄ vl -∗
  pa_add pd (16 * i + 12) ↦₂ vf -∗
  pa_add pd (16 * i + 14) ↦₂ vn -∗
  ( ∀ mf : regfile,
      ⌜callee_saved m mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf))⌝ -∗
      sie_cap_gpr γ mf K -∗
      cpu_own γ lvl eb pme C -∗
      kernel_text -∗ pc_is ret_tgt -∗
      d_free_cell i ↦ₘ Z_to_bv 8 1 -∗
      d_desc pd i ↦₈ (zero_reg : mword 64) -∗
      pa_add pd (16 * i + 8)  ↦₄ (mword_of_int 0 : mword 32) -∗
      pa_add pd (16 * i + 12) ↦₂ (mword_of_int 0 : mword 16) -∗
      pa_add pd (16 * i + 14) ↦₂ (mword_of_int 0 : mword 16) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FREEDESC.
  Parameter wp_free_desc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γs : list gname)
      (pd : mword 64) (i : nat)
      (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (va : mword 64) (vl : mword 32) (vf vn : mword 16),
      wp_free_desc_sconf_body γ Φ γs pd i m K lvl eb pme C va vl vf vn.
End FREEDESC.
