(* SpecEitherCopyout.v -- the public interface of either_copyout(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     int either_copyout(int user_dst, uint64 dst, void *src, uint64 len) {
       struct proc *p = myproc();
       if (user_dst) {
         return copyout(p->pagetable, dst, src, len);
       } else {
         memmove((char * )dst, src, len);
         return 0;
       }
     }

   @ KernelSyms.either_copyout = 0x80002260, 31 instructions / 74 bytes; a
   48-byte frame with all six slots used (ra / s0 / s1 = user_dst /
   s2 = len / s3 = src / s4 = dst).

   THE ONE THING THIS CONTRACT HAS TO SAY that neither copyout's nor
   memmove's does: [dst] is a pointer into ONE OF TWO ADDRESS SPACES, and
   which one is a run-time argument.  So the flag is reflected into the spec
   as a ghost boolean [user] pinned to the register by one premise, and both
   the precondition and [either_copyout_post] are keyed on it:

   - [user = true]  -- [dst] is a user virtual address, about which the
     caller owns nothing.  What it must hand over instead is [proc_priv]:
     the copy runs through the process's own page table, may fault pages in
     on the way, and so gives back a descriptor EXTENDING the one that went
     out ([uptd_ext] -- see SpecCopyin.v).  The answer is copyout's, 0 or -1.
   - [user = false] -- [dst] is a kernel address and the caller owns [len]
     bytes there; the body is a bare memmove, [proc_priv] is never touched
     (p->pagetable is not even read), and the answer is always 0.

   Requiring [proc_priv] only on the user arm is deliberate and not just
   economy: a kernel-to-kernel either_copyout is correct with no process
   assigned to this CPU at all.

   THE SOURCE BUFFER is a kernel buffer on BOTH arms and comes back
   unchanged on both, which is what makes it the one conjunct outside the
   [if].  On the kernel arm the caller additionally learns the destination
   now holds [src_bytes] -- memmove's guarantee, carried through verbatim.
   On the user arm the caller learns what the PROCESS will read back
   instead: the block's image comes back as the image it went in at with
   the copied prefix written at [dst] ([either_copyout_post] below).  That
   is an EQUATION on the image, not a one-sided promise -- it pins the
   untouched bytes as firmly as the written ones.

   TWO PREMISES ARE ALSO KEYED ON THE FLAG, for one reason each:
   - the length bound.  copyout takes any [len < 2^64], but the kernel arm
     narrows the count with [sext.w a2,s2] before calling memmove, so it is
     the identity only below 2^31.  That is a real restriction of the
     COMPILED code, not of the model, and it is honest to state it where it
     bites rather than to impose it on both arms.
   - [p->sz <= MAXVA] is NOT a premise at all: it lives inside [proc_priv]
     ([proc_priv_sz_bound]) and this proof pays copyout's premise out of it,
     exactly as fetchaddr does. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import CpuOwn.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FdSlots ProcInv.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* either_copyout's own frame is 6 slots (`addi sp,sp,-48`); copyout wants 52
   below it and myproc 10, so 52 covers every call it makes.

   52, NOT 50, AND ITS TWIN IS STILL 56 -- the asymmetry is real, not a typo.
   copyout keeps [psz] alive across walkaddr / vmfault / memmove, so gcc parks
   it in s11 and copyout's frame grew to 14 slots (`addi sp,sp,-112`), making
   its budget 14 + 38 = 52 (SpecCopyout.v).  copyIN's and copyinstr's extra
   argument dies before their first call, so their frames stayed at 12 slots
   and their budget stayed 50 -- which is why [either_copyin_stack] is
   correctly still 56 while this one is 58. *)
Notation either_copyout_stack := (58%nat) (only parsing).

(* HOW MUCH OF THE SOURCE REACHED THE PROCESS, as a pure fact about the
   returned a0.  copyout writes page by page and can give up on a later
   page (bad va, no backing, a read-only leaf), so a -1 means SOME prefix
   crossed -- and STRICTLY less than all of it, since the failure exits
   with bytes still to go ([SpecCopyout.copyout_wrote]).  A 0 means all of
   it did.  At [len = 1] the two arms are therefore "wrote the byte" and
   "wrote nothing", which is what consoleread's and piperead's one-byte
   copy loops need to say they wrote exactly what they return.  This is
   the ONLY existential left in the user arm's memory story -- a prefix
   LENGTH, not an image. *)
Definition either_copyout_ran (len : nat) (r : mword 64) (d : nat) : Prop :=
  (r = (mword_of_int 0 : mword 64) /\ d = len)
  \/ (r = (mword_of_int (-1) : mword 64) /\ (d < len)%nat).

Lemma either_copyout_ran_ret (len : nat) (r : mword 64) (d : nat) :
  either_copyout_ran len r d ->
  r = (mword_of_int 0 : mword 64) \/ r = (mword_of_int (-1) : mword 64).
Proof. intros [[Hr _] | [Hr _]]; [by left | by right]. Qed.

Section SpecEitherCopyout.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ}.
  Context `{XI : CurCtx}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.
  (* the kernel arm's destination is the CALLER's buffer; the body supplies
     its tier ([ktb]) at the use below. *)

  (* What comes back, keyed by the flag and by the returned a0. *)
  Definition either_copyout_post (ktb : ktier) (user : bool) (γf : gname) (p : mword 64)
      (pid : mword 32) (U : ustate) (dst : mword 64) (len : nat)
      (src_bytes : nat -> bv 8) (r : mword 64) : iProp Σ :=
    (if user
     then
     (* WHAT THE PROCESS'S MEMORY ENDS UP HOLDING, AS AN EQUATION.  The
        block comes back at [umem_wr (us_M U) dst d src_bytes]: the image
        it went in at, with the source buffer written at user va
        [dst + j] for every [j < d].  [UserPtTree.umem_wr] is keyed by the
        64-bit va rather than by an integer base precisely so this
        statement need not promise that [dst + len] does not wrap; a
        caller that knows it does not reads individual bytes back out with
        [umem_wr_lookup_in] and untouched ones with [umem_wr_lookup_out].
        [d] is pinned by the return value ([either_copyout_ran]).

        THE VMFAULT INSIDE THE COPY MOVES NOTHING: the pages it backs were
        already in the view, as lazy pages reading 0.  So the memmove is
        the only thing that touches [M], and this equation pins both what
        changed and what did not.  The DESCRIPTOR still grows, which is
        what the ∃ [P'] and [uptd_ext] are. *)
          ∃ (P' : uptd) (d : nat),
            ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ ∗
            ⌜either_copyout_ran len r d⌝ ∗
            proc_priv_core p pid
              (upd_usM (us_upt U P') (umem_wr (us_M U) dst d src_bytes))
     else ⌜r = (mword_of_int 0 : mword 64)⌝ ∗
          [∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] src_bytes j)%I.

End SpecEitherCopyout.

(* THE BUFFER CARRIES ITS OWN TIER [ktb], below the hart's regime [KT1].
   It is FORCED and it is the same two-tier shape [WpSconfMem]'s merged
   leaves have: this function's kernel buffer is a FRAME local at [KT1] for
   one caller and a KT0 page/bio window for the next, and one shared tier
   cannot state both.  See SpecMemmove.v's note. *)
Definition wp_either_copyout_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (ktb : ktier) `{!KtierLe ktb KT1} (kts : ktier) `{!KtierLe kts KT1} (γa : gname) (γf : gname)
    (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64)
    (pid : mword 32) (U : ustate) (user : bool) (len : nat)
    (src_bytes dst_olds : nat -> bv 8) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.either_copyout in
  let dst := m !!! Regidx (mword_of_int 11 : mword 5) in
  let src := m !!! Regidx (mword_of_int 12 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (either_copyout_stack <= av)%nat ->
  (* THE FLAG, reflected: [user_dst] is nonzero exactly when [user] *)
  eq_vec (m !!! Regidx (mword_of_int 10 : mword 5)) zero_reg = negb user ->
  m !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (* the kernel arm narrows the count with [sext.w] before memmove *)
  (Z.of_nat len < if user then 2 ^ 64 else 2 ^ 31) ->
  (* myproc's push_off, and vmfault's kalloc inside copyout, keep their
     transient noff increments in int range *)
  (Z.of_nat lvl + 1 < 2 ^ 31) ->
  (* either_copyout -> copyout -> walkaddr -> walk *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own lvl eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ[kts] src_bytes j) -∗
  (if user
   then proc_priv_core p pid U
   else [∗ list] j ∈ seq 0 len, (pa_add dst j) ↦ₘ[ktb] dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own lvl eb p b lks -∗
      pc_is ret_tgt -∗
      ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ[kts] src_bytes j) -∗
      either_copyout_post ktb user γf p pid U dst len src_bytes
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type EITHER_COPYOUT.
  Parameter wp_either_copyout_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (ktb : ktier) `{!KtierLe ktb KT1} (kts : ktier) `{!KtierLe kts KT1} (γa : gname) (γf : gname) (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64)
      (pid : mword 32) (U : ustate) (user : bool) (len : nat)
      (src_bytes dst_olds : nat -> bv 8) (b : bool) (lks : gset string),
      wp_either_copyout_sconf_body ktb kts γa γf m av lvl eb p pid U user len
        src_bytes dst_olds b lks.
End EITHER_COPYOUT.
