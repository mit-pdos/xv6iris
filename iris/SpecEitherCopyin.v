(* SpecEitherCopyin.v -- the public interface of either_copyin(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     int either_copyin(void *dst, int user_src, uint64 src, uint64 len) {
       struct proc *p = myproc();
       if (user_src) {
         return copyin(p->pagetable, dst, src, len);
       } else {
         memmove(dst, (char * )src, len);
         return 0;
       }
     }

   @ KernelSyms.either_copyin = 0x800022aa, 31 instructions / 74 bytes; a
   48-byte frame with all six slots used (ra / s0 / s1 = user_src /
   s2 = len / s3 = src / s4 = dst).  Instruction for instruction the mirror
   of either_copyout -- gcc emitted the same block with a0/a1 swapped and a
   different callee -- so read SpecEitherCopyout.v for why the flag is a
   ghost boolean and why [proc_priv] is required only on the user arm.

   WHAT DIFFERS from either_copyout is which end of the copy is the caller's
   buffer, and therefore where the postcondition can say anything:

   - the DESTINATION is a kernel buffer on both arms, so the caller hands it
     over unconditionally -- but what it ends up holding depends on the arm.
     On the kernel arm it holds [src_bytes] (memmove's guarantee).  On the
     user arm it holds NOTHING NAMEABLE: the bytes come from user memory,
     about which the kernel may assume nothing, and a copyin that gives up
     part-way has still written a prefix, so [∃ dst_new] is the right
     statement on both of copyin's exits (SpecCopyin.v).  A caller that
     needs to constrain what it read must validate it.
   - the SOURCE is a user virtual address on the user arm ([proc_priv], the
     descriptor coming back EXTENDED) and a kernel buffer on the kernel arm
     (returned unchanged). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots FileInv ProcInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


(* 6 own slots + the 50 copyin wants below it (myproc's 10 and memmove's 2
   both fit inside that). *)
Definition either_copyin_stack : nat := 56%nat.

Section SpecEitherCopyin.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ}.

  (* What comes back, keyed by the flag and by the returned a0. *)
  Definition either_copyin_post (user : bool) (γf : gname) (p : mword 64)
      (pid : mword 32) (V : pprivate) (dst src : mword 64) (len : nat)
      (src_bytes : nat -> bv 8) (r : mword 64) : iProp Σ :=
    (if user
     then ⌜r = (mword_of_int 0 : mword 64) \/ r = (mword_of_int (-1) : mword 64)⌝ ∗
          (∃ P' : uptd, ⌜uptd_ext (pv_upt V) P'⌝ ∗ proc_priv γf p pid (upd_upt V P')) ∗
          (∃ dst_new : nat -> bv 8,
             [∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ dst_new j)
     else ⌜r = (mword_of_int 0 : mword 64)⌝ ∗
          ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) ∗
          ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ src_bytes j))%I.

End SpecEitherCopyin.

Definition wp_either_copyin_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (user : bool) (len : nat)
    (src_bytes dst_olds : nat -> bv 8) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.either_copyin in
  let dst := m !!! Regidx (mword_of_int 10 : mword 5) in
  let src := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (either_copyin_stack <= av)%nat ->
  (* THE FLAG, reflected: [user_src] is nonzero exactly when [user] *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = negb user ->
  m !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (* the kernel arm narrows the count with [sext.w] before memmove *)
  (Z.of_nat len < if user then 2 ^ 64 else 2 ^ 31) ->
  (* myproc's push_off, and vmfault's kalloc inside copyin, keep their
     transient noff increments in int range *)
  (Z.of_nat lvl + 1 < 2 ^ 31) ->
  sie_cap_gpr m av b p -∗
  cpu_own lvl eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ dst_olds j) -∗
  (if user
   then proc_priv γf p pid V
   else [∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own lvl eb p C b -∗
      pc_is ret_tgt -∗
      either_copyin_post user γf p pid V dst src len src_bytes
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type EITHER_COPYIN.
  Parameter wp_either_copyin_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (user : bool) (len : nat)
      (src_bytes dst_olds : nat -> bv 8) (b : bool),
      wp_either_copyin_sconf_body γa γf Φ m av lvl eb p C pid V user len
        src_bytes dst_olds b.
End EITHER_COPYIN.
