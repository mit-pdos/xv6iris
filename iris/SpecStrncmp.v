(* SpecStrncmp.v -- the public interface of strncmp(), stated independently of
   its proof.

     int strncmp(const char *p, const char *q, uint n)

   @ KernelSyms.strncmp = 0x80000d9c, 58 bytes; a 2-slot ra/s0 frame.

   strncmp compares at most [n] bytes of [p] and [q].  Comparison stops at the
   first index [k < n] where [p[k] == 0] or [p[k] != q[k]].  If no such [k]
   exists within the first [n] bytes, it returns 0.  Otherwise, it returns the
   signed difference between (unsigned char)p[k] and (unsigned char)q[k]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ByteBuf.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* Pure characterization of strncmp stopping at index [k < n]. *)
Definition strncmp_stop (f g : nat -> bv 8) (n k : nat) : Prop :=
  (k < n)%nat /\
  bb_nonul f k /\
  (forall j, (j < k)%nat -> f j = g j) /\
  (f k = (mword_of_int 0 : mword 8) \/ f k <> g k).

(* The result returned by strncmp in register a0. *)
Definition strncmp_res (f g : nat -> bv 8) (n : nat) (res : mword 64) : Prop :=
  (n = 0%nat /\ res = (mword_of_int 0 : mword 64)) \/
  ((0 < n)%nat /\
   ((exists k, strncmp_stop f g n k /\
       res = (mword_of_int (bv_unsigned (f k) - bv_unsigned (g k)) : mword 64)) \/
    ((forall j, (j < n)%nat -> f j = g j /\ f j <> (mword_of_int 0 : mword 8)) /\
     res = (mword_of_int 0 : mword 64)))).

Definition wp_strncmp_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (ktf ktg : ktier) (mm : regfile)
    (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.strncmp in
  let s1 := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let s2 := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the 2-slot frame; strncmp calls nothing *)
  (2 <= K)%nat ->
  mm !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜strncmp_res f g n (mr !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type STRNCMP.
  Parameter wp_strncmp_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (ktf ktg : ktier) (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64),
      wp_strncmp_sconf_body ktf ktg mm n f g K dq1 dq2 b p.
End STRNCMP.
