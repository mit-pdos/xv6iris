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
   - Nothing about [p->sz].  Unlike fetchaddr, fetchstr does NO range test of
     its own: it hands [addr] straight to copyinstr.  copyinstr's defences are
     walkaddr returning 0 and -- now -- vmfault's [va >= psz] test, and the
     [psz] it passes down is [pv_sz V], read out of the block fetchstr already
     holds.  So no SIZE PREMISE enters this contract, even though a size now
     reaches the machine.

   *** [proc_priv] NO LONGER COMES BACK UNCHANGED. ***  It used to: copyinstr
   did not fault pages in, so the descriptor that went into
   [ProcInv.proc_priv_copy] was the descriptor that came out, and fetchstr was
   the one member of the fetch* family whose contract left the process block
   literally alone.  xv6 `4f2fc8b` gave copyinstr's [pa0 == 0] arm a
   [vmfault] call (SpecCopyinstr.v), which lifts it to copyin's altitude and
   takes fetchstr with it:

     - the kalloc tier is threaded through ([!kallocG], [γa],
       [kalloc_env γa None]) -- fetchstr allocates nothing of its own, it is
       vmfault underneath that does;
     - the process comes back with its descriptor EXTENDED, so the
       postcondition quantifies [P'] under [uptd_ext (pv_upt V) P'] and
       returns [proc_priv γf p pid (upd_upt V P')].  This is exactly
       SpecFetchaddr.v's shape, and for exactly its reason;
     - [fetchstr_stack] went 26 -> 56, because copyinstr's own budget went
       20 -> 50 and fetchstr's frame is 6 slots (48 bytes).

   The size copyinstr now demands is [pv_sz V], whose [<= 2^38] bound comes
   from [ProcInv.proc_priv_sz_bound] -- so fetchstr still takes no [szv]
   parameter and still does NO range test of its own.

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
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* fetchstr's own frame is 6 slots; below it sit myproc's 10, copyinstr's 20
   (its own 10 plus walkaddr's 10) and strlen's 2, so 20 covers every call. *)
Definition fetchstr_stack : nat := 56%nat.

(* fetchstr's answer, keyed by the returned a0 -- and, unlike copyinstr's,
   the success arm names the return value, because that value IS the [k] the
   buffer's shape is stated at. *)
Definition fetchstr_ret (maxn : nat) (f : nat -> bv 8) (r : mword 64) : Prop :=
  (exists k : nat, (k < maxn)%nat /\ bb_cstr f k
                   /\ r = (mword_of_int (Z.of_nat k) : mword 64))
  \/ r = (mword_of_int (-1) : mword 64).

Definition wp_fetchstr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γf : gname)
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
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (P' : uptd) (buf_new : nat -> bv 8),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt V) P'⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      proc_priv γf p pid (upd_upt V P') -∗
      ([∗ list] j ∈ seq 0 maxn, (pa_add buf j) ↦ₘ buf_new j) -∗
      ⌜fetchstr_ret maxn buf_new (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FETCHSTR.
  Parameter wp_fetchstr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname) (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (maxn : nat) (buf_olds : nat -> bv 8) (b : bool),
      wp_fetchstr_sconf_body γa γf m av n eb p C pid V maxn buf_olds b.
End FETCHSTR.
