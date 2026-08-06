(* SpecCpuid.v -- the public interface of cpuid, stated independently of its
   proof.  [cpuid] (xv6-riscv/kernel/proc.c) reads the thread pointer [tp]
   (which start() initialises to the hart id) and returns it as an [int]:

     0x800018d0 <cpuid>:
       ...prologue...
       mv     a0,tp        a0 = tp
       sext.w a0,a0        a0 = sign_extend(tp[31:0])   (the [int] truncation)
       ...epilogue...

   So the return value is [cpuid_ret tp] = the sign-extension of tp's low 32
   bits.  For any legal hart id (< NCPU) the top bits are clear and
   [cpuid_ret tp = tp] ([cpuid_ret_id_small]).

   Requires only the definitional layer -- never a whole-function proof file --
   so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import ProcGeom PlicHart IntrDefs HartTp.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import RiscvExtras.
Import Defs.


(* the [int]-truncated hart id returned by cpuid: sign-extend tp's low 32. *)
Definition cpuid_ret (tp : mword 64) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec tp 31 0 : mword 32).

Lemma cpuid_ret_cid `{GEN : GenId} `{CID : CpuId} : cpuid_ret cid_word = cid_word.
Proof.
  destruct tp_ok_cid as [_ H].
  rewrite uint_unsigned in H.
  change 8 with (Z.of_nat dev_ncpu) in H.
  exact (sext32_id_hart cid_word H).
Qed.

  (* INTERRUPTS MUST BE DISABLED -- xv6 says so in as many words above
     mycpu() ("Interrupts must be disabled"), and the explicit-cpuid refactor
     turns that comment into a premise.  The [tp] read happens MID-function, so
     with interrupts enabled a migration before it would have the instruction
     read the RESUMING hart's tp: the returned id would be neither the entry
     hart's nor the exit hart's, and no [let] outside the continuation can name
     it.  At [b = false] no trap is taken, the hart cannot move, and the id is
     the entry hart's -- so the contract is stated at [false] and needs no
     [wp_next] at all (it would collapse by [wp_next_off] anyway). *)
Definition wp_cpuid_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.cpuid in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (* the tp READ happens on the entry hart, before any possible migration --
     [cret] is computed here, outside [wp_next], so it names the entry hart's
     id regardless of which hart the continuation resumes on. *)
  let cret := cpuid_ret (rget m0 tp_idx) in
  (2 <= n)%nat ->
  sie_cap_gpr m0 n false p -∗
  kernel_text -∗ pc_is pcE -∗
  ( ∀ m' : regfile,
    sie_cap_gpr m' n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\
      m' !!! Regidx a0_idx = cret ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* the JAL-call form (mirror of [wp_call_mycpu_sconf_cs]): a caller at [P] with
   [instr P false (JAL (jimm, ra))] whose target is [cpuid] runs the callee and
   returns to [P+4]. *)
  (* INTERRUPTS MUST BE DISABLED -- xv6 says so in as many words above
     mycpu() ("Interrupts must be disabled"), and the explicit-cpuid refactor
     turns that comment into a premise.  The [tp] read happens MID-function, so
     with interrupts enabled a migration before it would have the instruction
     read the RESUMING hart's tp: the returned id would be neither the entry
     hart's nor the exit hart's, and no [let] outside the continuation can name
     it.  At [b = false] no trap is taken, the hart cannot move, and the id is
     the entry hart's -- so the contract is stated at [false] and needs no
     [wp_next] at all (it would collapse by [wp_next_off] anyway). *)
Definition wp_call_cpuid_sconf_cs_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
  let pcE := mword_of_int KernelSyms.cpuid in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let cret := cpuid_ret (rget m tp_idx) in
  add_vec P (sign_extend' 64 jimm) = pcE ->
  eq_vec (access_vec_dec (pcE : mword 64) 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sie_cap_gpr m n false p -∗
  kernel_text -∗ pc_is P -∗
  instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
  ( ∀ mo,
    sie_cap_gpr mo n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mo /\
      mo !!! Regidx a0_idx = cret ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type CPUID.
  Parameter wp_cpuid_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : mword 64),
      wp_cpuid_sconf_body Φ m0 n p.
  Parameter wp_call_cpuid_sconf_cs :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (p : mword 64),
      wp_call_cpuid_sconf_cs_body Φ P jimm m n p.
End CPUID.
