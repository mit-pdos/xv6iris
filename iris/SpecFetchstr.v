(* SpecFetchstr.v -- the public interface of fetchstr(), stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     int fetchstr(uint64 addr, char *buf, int max) {
       struct proc *p = myproc();
       if (copyinstr(p->pagetable, buf, addr, max) < 0)
         return -1;
       return strlen(buf);
     }

   @ KernelSyms.fetchstr = 0x800027c4, 32 instructions / 64 bytes; a 48-byte
   (6-slot) frame with five slots used (ra / s0 / s1 = buf / s2 = max /
   s3 = addr).

   THE POINT OF THE CONTRACT is that copyinstr's and strlen's vocabularies
   MEET here, and nothing has to be translated between them.  copyinstr
   promises [ByteBuf.bb_cstr new k] for some [k < max] (SpecCopyinstr.v);
   strlen assumes exactly that and answers [k] (SpecStrlen.v).  So fetchstr's
   postcondition is a SINGLE existential [k] carrying both the buffer's shape
   and the return value -- which is what makes it usable: a caller learns
   that [buf] now holds a NUL-terminated string AND that the number it got
   back is that string's length.  That is strictly more than copyinstr alone
   says, and it is why xv6 has fetchstr at all.

   THREE THINGS THE CONTRACT DELIBERATELY DOES NOT SAY.

   - Nothing about the individual bytes.  They came from user memory
     (SpecCopyin.v's reasoning applies verbatim); [bb_cstr] is a STRUCTURAL
     property of the naming function and that is all a kernel caller can use.
   - Nothing distinguishing the two failure modes.  [-1] means either an
     unmapped page or [max] bytes with no NUL among them.  No caller
     separates them, and copyinstr's contract does not either.
   - Nothing about [p->sz].  Unlike fetchaddr, fetchstr does NO range test:
     it hands [addr] straight to copyinstr, whose only defence is walkaddr
     returning 0.  So [proc_priv]'s [p->sz] never enters.

   WHY [proc_priv] COMES BACK UNCHANGED.  copyinstr does not fault pages in
   (it has no vmfault / kalloc tier, see SpecCopyinstr.v), so the descriptor
   that goes into [ProcInv.proc_priv_copy] is the descriptor that comes out --
   no [uptd_ext], no [upd_upt] in the postcondition.  fetchstr is therefore
   the one member of the fetch* family whose contract leaves the process
   block literally alone.

   [max] IS BOUNDED BY 2^31, not 2^64.  copyinstr would take any [max] below
   2^64, but strlen's answer is a C [int] computed with a [subw]
   (SpecStrlen.v), so the length must fit; a caller's buffer is a fixed-size
   kernel array (argstr's is [MAXPATH]), which discharges this trivially. *)
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
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots FileInv ProcInv.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Notation FS := KernelSyms.fetchstr.

(* fetchstr's own frame is 6 slots; below it sit myproc's 10, copyinstr's 20
   (its own 10 plus walkaddr's 10) and strlen's 2, so 20 covers every call. *)
Definition fetchstr_stack : nat := 26%nat.

(* fetchstr's answer, keyed by the returned a0 -- and, unlike copyinstr's,
   the success arm names the return value, because that value IS the [k] the
   buffer's shape is stated at. *)
Definition fetchstr_ret (maxn : nat) (f : nat -> bv 8) (r : mword 64) : Prop :=
  (exists k : nat, (k < maxn)%nat /\ bb_cstr f k
                   /\ r = (mword_of_int (Z.of_nat k) : mword 64))
  \/ r = (mword_of_int (-1) : mword 64).

Definition wp_fetchstr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
    (γf : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fetchstr in
  let buf := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* push_off's transient noff increment stays in int range (myproc) *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (fetchstr_stack <= av)%nat ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat maxn) : mword 64) ->
  (Z.of_nat maxn < 2 ^ 31)%Z ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  proc_priv γf p pid V -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (buf_new : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid V -∗
      ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_new j) -∗
      ⌜fetchstr_ret maxn buf_new (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FETCHSTR.
  Parameter wp_fetchstr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{CID : CpuId}
      (γf : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool),
      wp_fetchstr_sconf_body γf Φ m av n eb p C pid V maxn buf_olds b.
End FETCHSTR.
