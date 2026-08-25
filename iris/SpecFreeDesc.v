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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import VirtioModel DiskInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* free_desc's own frame is 16 bytes (2 slots); its only callee is wakeup (18) *)
Notation K_free_desc := (20%nat) (only parsing).
Definition wp_free_desc_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
     (γs : list gname)
    (pd : mword 64) (i : nat)
    (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64)
    (va : mword 64) (vl : mword 32) (vf vn : mword 16) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.free_desc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_free_desc <= K)%nat ->
  (i < 8)%nat ->
  uint (m !!! Regidx (mword_of_int 10 : mword 5) : mword 64) = Z.of_nat i ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (* free_desc's only callee is wakeup, whose bound is "proc" (11). *)
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
 procs_inv γs -∗
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
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf))⌝ -∗
      sie_cap_gpr KT1 mf K b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is ret_tgt -∗
      d_free_cell i ↦ₘ Z_to_bv 8 1 -∗
      d_desc pd i ↦₈ (zero_reg : mword 64) -∗
      pa_add pd (16 * i + 8)  ↦₄ (mword_of_int 0 : mword 32) -∗
      pa_add pd (16 * i + 12) ↦₂ (mword_of_int 0 : mword 16) -∗
      pa_add pd (16 * i + 14) ↦₂ (mword_of_int 0 : mword 16) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FREEDESC.
  Parameter wp_free_desc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
       (γs : list gname)
      (pd : mword 64) (i : nat)
      (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64)
      (va : mword 64) (vl : mword 32) (vf vn : mword 16) (b : bool) (lks : gset string),
      wp_free_desc_sconf_body γs pd i m K lvl eb pme va vl vf vn b lks.
End FREEDESC.
