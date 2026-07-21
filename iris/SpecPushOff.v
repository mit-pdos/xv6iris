(* SpecPushOff.v -- the public interface of PushOff, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpIntenaBits WpMycpu SpecMycpu WpPushOffTop WpPopOff.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation PO := KernelSyms.push_off.
Notation PP := KernelSyms.pop_off.

Definition wp_push_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (av : nat) (noff intena_old : mword 32) (a0f : mword 64) (n : nat) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  (* push_off's mstatus0-dependent register chain N2..N8 + storeval32 (which
     read [sstatus_read mstatus0]) are reconstructed inside the proof over the
     unbundled mstatus0; the statement stays mstatus0-free. *)
  let noff_a5 := sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
  let noff_store := (autocast (T := mword) (subrange_vec_dec noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let caller_ret := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec (access_vec_dec caller_ret 0) ('b"0") = true ->
  mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
  (6 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.push_off + 0x00) : mword 64) -∗
  a_noff ↦₄ noff -∗
  a_intena ↦₄ intena_old -∗
  ( ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn mfin av -∗
    tlb_inv_pt root_ppn -∗
    pc_is caller_ret -∗
    ⌜ callee_saved m mfin ⌝ -∗
    a_noff ↦₄ noff_store -∗
    a_intena ↦₄ (if eq_vec (sign_extend' 64 noff) zero_reg
                 then po_intena_val ms else intena_old) -∗
    intr_count γ root_ppn (S n) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_pop_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (av : nat) (noffv intenav : mword 32) (n : nat) (dqi : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pop_off in
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let a0v := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
  let storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* the counting token's level mirrors the noff cell: the machine
     branch [noff-1 == 0] holds iff we are popping to level 0. *)
  (neq_vec nv1 zero_reg = false <-> n = 0%nat) ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (4 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn (S n) -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  a_noff ↦₄ noffv -∗
  a_int ↦₄{ dqi } intenav -∗
  ( ∀ mf,
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn mf av -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mf ⌝ -∗
    a_noff ↦₄ storeval -∗
    a_int ↦₄{ dqi } intenav -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PUSHOFF.
  Parameter wp_push_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (av : nat) (noff intena_old : mword 32) (a0f : mword 64) (n : nat),
      wp_push_off_sconf_body γ root_ppn Φ m av noff intena_old a0f n.
  Parameter wp_pop_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (av : nat) (noffv intenav : mword 32) (n : nat) {dqi : dfrac},
      wp_pop_off_sconf_body γ root_ppn Φ m av noffv intenav n dqi.
End PUSHOFF.
