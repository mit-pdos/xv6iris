(* SpecArgaddr.v -- the public interface of argaddr(), stated independently
   of its proof.

     void argaddr(int n, uint64 *ip) { *ip = argraw(n); }

   @ KernelSyms.argaddr = 0x80002820, thirteen instructions -- and the SAME
   thirteen as argint (SpecArgint.v), byte for byte, except the one store:

     +0x00  1101        c.addi     sp,sp,-32     32-byte frame
     +0x02  ec06        c.sdsp     ra,24(sp)
     +0x04  e822        c.sdsp     s0,16(sp)
     +0x06  e426        c.sdsp     s1,8(sp)
     +0x08  1000        c.addi4spn s0,sp,32
     +0x0a  84ae        c.mv       s1,a1         s1 := ip  (survives the call)
     +0x0c  eefff0ef    jal        ra,argraw     a0 := the nth argument
     +0x10  e088        c.sd       a0,0(s1)      *ip = a0     <-- argint: c.sw
     +0x12  60e2        c.ldsp     ra,24(sp)
     ...    epilogue

   So this contract is argint's with the narrowing removed: argaddr stores
   the WHOLE 64-bit trapframe slot, and its postcondition is [ip ↦₈[kt] v] where
   [v] is argraw's result.  There is no [trunc32] and no range clause -- a
   [uint64] argument is whatever the user put in the register, which is
   precisely why the C comment says argaddr "doesn't check for legality,
   since copyin/copyout will do that".

   Resources are argraw's, plus the caller's destination cell [ip ↦₈[kt] old].
   Nothing about [proc_priv] appears: see SpecArgraw.v for why the trapframe
   pointer travels as a bare fraction (a caller holding the block splits it
   out with [ProcInv.proc_priv_tf]). *)
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
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import FileInvDefs.
Require Import PageGeom.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


(* 4 slots for argaddr's own frame, 14 for argraw's -- argint's number,
   since the two functions have identical frames. *)
Notation argaddr_stack := (18%nat) (only parsing).
Definition wp_argaddr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
    (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
    (old : mword 64) (dqt : dfrac) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.argaddr in
  let ip := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (i < NARG)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i) ->
  ws !! tf_arg_idx i = Some v ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (argaddr_stack <= av)%nat ->
  (* what argraw's own load needs -- see SpecArgraw's matching premise. *)
  page_valid (page_base tfp) ->
  sie_cap_gpr kt m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  p_trapframe p ↦₈{dqt} page_base tfp -∗
  tf_page tfp ws -∗
  ip ↦₈[kt] old -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr kt mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      p_trapframe p ↦₈{dqt} page_base tfp -∗
      tf_page tfp ws -∗
      ip ↦₈[kt] v -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ARGADDR.
  Parameter wp_argaddr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (old : mword 64) (dqt : dfrac) (b : bool) (lks : gset string),
      wp_argaddr_sconf_body kt m av n eb p i tfp ws v old dqt b lks.
End ARGADDR.
