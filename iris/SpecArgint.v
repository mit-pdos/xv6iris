(* SpecArgint.v -- the public interface of argint(), stated independently of
   its proof.

     void argint(int n, int *ip) { *ip = argraw(n); }

   @ KernelSyms.argint = 0x80002804, thirteen instructions:

     +0x00  1101        c.addi     sp,sp,-32     32-byte frame
     +0x02  ec06        c.sdsp     ra,24(sp)
     +0x04  e822        c.sdsp     s0,16(sp)
     +0x06  e426        c.sdsp     s1,8(sp)
     +0x08  1000        c.addi4spn s0,sp,32
     +0x0a  84ae        c.mv       s1,a1         s1 := ip  (survives the call)
     +0x0c  f0bff0ef    jal        ra,argraw     a0 := the nth argument
     +0x10  c088        c.sw       a0,0(s1)      *ip = (int)a0
     +0x12  60e2        c.ldsp     ra,24(sp)
     ...    epilogue

   argint is a thin wrapper: it holds [ip] in the callee-saved s1 across the
   argraw call and narrows the 64-bit result to the [int] cell with a
   [c.sw].  So its postcondition is [ip ↦₄[KT1] trunc32 v] where [v] is argraw's
   result -- the low 32 bits of the trapframe slot, which is exactly C's
   [int] conversion.

   Resources are argraw's, plus the caller's destination cell [ip ↦₄[KT1] old].
   Nothing about [proc_priv] appears: see SpecArgraw.v for why the trapframe
   pointer travels as a bare fraction. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import FileInvDefs.
Require Import PageGeom.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


(* the [c.sw]'s narrowing IS C's (int) conversion of argraw's uint64 result;
   [RiscvExtras.trunc32] is the model's own name for it, so use that rather
   than restating the subrange. *)
Notation arg_int32 := trunc32.

Definition wp_argint_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
    (old : mword 32) (dqt : dfrac) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.argint in
  let ip := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (i < NARG)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i) ->
  ws !! tf_arg_idx i = Some v ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 14 for argraw's *)
  (18 <= av)%nat ->
  (* what argraw's own load needs -- see SpecArgraw's matching premise. *)
  page_valid (page_base tfp) ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  p_trapframe p ↦₈{dqt} page_base tfp -∗
  tf_page tfp ws -∗
  ip ↦₄[KT1] old -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      p_trapframe p ↦₈{dqt} page_base tfp -∗
      tf_page tfp ws -∗
      ip ↦₄[KT1] arg_int32 v -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ARGINT.
  Parameter wp_argint_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (old : mword 32) (dqt : dfrac) (b : bool) (lks : gset string),
      wp_argint_sconf_body m av n eb p i tfp ws v old dqt b lks.
End ARGINT.
