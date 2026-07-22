(* SpecMyproc.v -- the public interface of Myproc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   THE current-process contract: myproc() returns exactly the process the
   current-process resource says is assigned to this CPU ([cur_proc p],
   ProcGeom.v -- ownership of cpus[cpuid].proc holding p), reading the cell
   under push_off/pop_off.  The hart id is the ambient CpuId: the spec pins
   tp = [cid_word].

   (SpecWakeup.v's [wp_myproc_sconf_any] axiom is the older, weaker ∃-j
   interface used by wakeup, which threads no current-process resource.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpIntenaBits.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation MP := KernelSyms.myproc.

Definition wp_myproc_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (m : regfile) (av n : nat) (noffv intena_old : mword 32) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.myproc in
  (* the noff cell value after push_off's increment (its own storeval form);
     the pop_off restores it to exactly [noffv] (noff_push_pop_id). *)
  let noff1 : mword 32 :=
    (autocast (T := mword) (subrange_vec_dec (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 noffv)
                (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
       (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let nv1 := sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 noff1)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* the hart id is the ambient CpuId *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* pop_off's level/cell correlation and positivity, at the incremented cell *)
  (neq_vec nv1 zero_reg = false <-> n = 0%nat) ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 noff1) = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (10 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  a_cpu_noff cid_word ↦₄ noffv -∗
  a_cpu_int cid_word ↦₄ intena_old -∗
  cur_proc p -∗
  ( ∀ (ms : mword 64) (mf : regfile),
      ⌜ sconf_ms_facts ms ⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap_gpr γ root_ppn mf av -∗
      intr_count γ root_ppn n -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = p ⌝ -∗
      a_cpu_noff cid_word ↦₄ noffv -∗
      a_cpu_int cid_word ↦₄ (if eq_vec (sign_extend' 64 noffv) zero_reg
                             then po_intena_val ms else intena_old) -∗
      cur_proc p -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MYPROC.
  Parameter wp_myproc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m : regfile) (av n : nat) (noffv intena_old : mword 32) (p : mword 64),
      wp_myproc_sconf_body γ root_ppn Φ m av n noffv intena_old p.
End MYPROC.
