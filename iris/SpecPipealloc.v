(* SpecPipealloc.v -- the public interface of pipealloc, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int pipealloc(struct file **f0, struct file **f1) {
       struct pipe *pi = 0;
       f0[0] = f1[0] = 0;
       if ((f0[0] = filealloc()) == 0 || (f1[0] = filealloc()) == 0) goto bad;
       if ((pi = (struct pipe * ) kalloc()) == 0)                     goto bad;
       pi->readopen = 1; pi->writeopen = 1; pi->nwrite = 0; pi->nread = 0;
       initlock(&pi->lock, "pipe");
       f0[0]->type = FD_PIPE; f0[0]->readable = 1;
       f0[0]->writable = 0;   f0[0]->pipe = pi;
       f1[0]->type = FD_PIPE; f1[0]->readable = 0;
       f1[0]->writable = 1;   f1[0]->pipe = pi;
       return 0;
     bad:
       if (pi) kfree((char * ) pi);
       if (f0[0]) fileclose(f0[0]);
       if (f1[0]) fileclose(f1[0]);
       return -1;
     }

   (the [f0[0]] spelling is just to keep the C out of Rocq's comment lexer)

   pipealloc is the sole constructor of a pipe, and it is where the two halves
   of the model meet: the two exclusive [file_ref]s filealloc hands back (which
   is what licenses the eight unlocked stores into the two [struct file]s), and
   the fresh page kalloc hands back, which becomes the pipe.  What comes out is
   one [is_pipe] and its TWO end references, one per file -- exactly the pairing
   the caller (sys_pipe) then installs as each file's FD_PIPE payload.

   Two things worth reading off the disassembly rather than the C:

   * the [if (pi) kfree(...)] arm is DEAD and gcc removed it -- every path that
     reaches [bad] has pi = 0 -- so pipealloc never frees a pipe, and none of
     the page-reclamation question (see PipeInv.v's header) touches this proof;
   * on the [bad] paths the two [struct file *] cells are NOT restored: the
     second-filealloc failure leaves a stale non-null pointer in [*f0], and the
     kalloc failure leaves stale pointers in both.  So the failure
     postcondition promises the cells back, and nothing about their contents.

   pipealloc holds no lock across a call and acquires none itself, so the
   [cpu_own] level [n] and [C] come back untouched; its callees
   (filealloc / kalloc / initlock / fileclose) are each push/pop balanced.

   Design: claude-notes/design/pipe.md and claude-notes/design/file-table.md. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import KallocInv.
Require Import PipeInv.
Require Import WpLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Notation PA := KernelSyms.pipealloc.

(* The address of the string literal "pipe" that pipealloc passes to initlock.
   It sits in .rodata past etext with no ELF symbol of its own, so it is spelled
   out here (kernel.asm: 80007598 <etext+0x598>). *)
Definition pipe_name_str : Z := 0x80007598%Z.

Section SpecPipealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !kallocG Σ, !pipeG Σ}.

  (* the four content fields pipealloc writes into each [struct file]: it makes
     the [w = false] file the READ end and the [w = true] file the WRITE end,
     both pointing at the same pipe.  [ip], [off] and [major] are NOT written
     -- a pipe file inherits whatever the recycled table slot held, which is
     the real xv6 behaviour -- so they stay existentially quantified in the
     postcondition's [fcontent]. *)
  Definition pipe_file (pi : mword 64) (w : bool) (C : fcontent) : Prop :=
    fc_type C = FD_PIPE /\
    fc_pipe C = pi /\
    fc_readable C = ((if w then mword_of_int 0 else mword_of_int 1) : mword 8) /\
    fc_writable C = ((if w then mword_of_int 1 else mword_of_int 0) : mword 8).

  Definition pipealloc_post (γf : gname) (γk : gname * gname) (on : option nat)
      (pf0 pf1 r : mword 64) : iProp Σ :=
    ((* FAILURE (a0 = -1): the ftable was full, or kalloc found no page.  Every
        file reference taken on the way was given back (fileclose), the page
        count is untouched, and the caller's two pointer cells come back with
        unspecified contents. *)
     ⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
     kalloc_avail γk on ∗
     (∃ w0 w1 : mword 64, pf0 ↦₈ w0 ∗ pf1 ↦₈ w1)
     ∨
     (* SUCCESS (a0 = 0): a live pipe, plus the two files naming it.  Each
        [file_ref] is EXCLUSIVE (fraction 1) -- pipealloc's own unlocked stores
        are what proves that legal, and the caller inherits the same right (it
        must, since sys_pipe still has to install them in its fd table). *)
     ⌜r = (zero_reg : mword 64)⌝ ∗
     kalloc_avail γk (avail_dec on) ∗
     (∃ (γl : gname) (γp : pipe_names) (pi : mword 64)
        (k0 k1 : nat) (C0 C1 : fcontent),
        ⌜(k0 < NFILE)%nat /\ (k1 < NFILE)%nat⌝ ∗
        ⌜pipe_file pi false C0⌝ ∗ ⌜pipe_file pi true C1⌝ ∗
        pf0 ↦₈ fnode k0 ∗ pf1 ↦₈ fnode k1 ∗
        is_pipe γl γp pi ∗
        file_ref γf k0 1 C0 ∗ pipe_ref γp false 1 ∗
        file_ref γf k1 1 C1 ∗ pipe_ref γp true 1))%I.

End SpecPipealloc.

Definition wp_pipealloc_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !kallocG Σ, !pipeG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γfl γf : gname)                    (* ftable.lock, the file refcount ghost, the fd-slot ghost *)
    (γkl : gname) (γk : gname * gname) (fl : mword 64)   (* kmem.lock, kalloc's ghosts *)
    (m : regfile) (v0 v1 : mword 64) (on : option nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pipealloc in
  (* a0 = f0 (the read end's slot), a1 = f1 (the write end's slot).  They are
     SEPARATE conjuncts below, which is how the spec says the caller must pass
     two distinct cells -- the same separation-as-hypothesis idiom memmove
     uses for its two buffers. *)
  let pf0 : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pf1 : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* pipealloc's own frame is 6 slots (c.addi16sp sp,-48); of its four callees
     fileclose is the deepest, wanting [fileclose_stack] = 18 below that. *)
  (24 <= K)%nat ->
  (* the tp register holds THIS cpu's id (acquire/release cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr γ m K -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the two object pools pipealloc draws on *)
  is_ftable γfl γf -∗
  is_lock γkl (mword_of_int KernelSyms.kmem) "kmem"%string (kmem_res γk fl) -∗
  kalloc_avail γk on -∗
  (* acquire's [if(holding(lk)) panic] arm, in filealloc / kalloc / fileclose *)
  panic_wp -∗
  (* pipealloc creates TWO references, so it needs two fd slots -- one per
     end of the pipe.  Both come back from the fileclose calls on the error
     paths. *)
  fd_slot -∗
  fd_slot -∗
  (* the caller's two [struct file *] cells; both are overwritten on entry, so
     their incoming contents are arbitrary *)
  pf0 ↦₈ v0 -∗
  pf1 ↦₈ v1 -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    cpu_own γ n eb p C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    pipealloc_post γf γk on pf0 pf1 (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PIPEALLOC.
  Parameter wp_pipealloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !kallocG Σ, !pipeG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γfl γf : gname) (γkl : gname) (γk : gname * gname) (fl : mword 64)
      (m : regfile) (v0 v1 : mword 64) (on : option nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat),
      wp_pipealloc_sconf_body γ Φ γfl γf γkl γk fl m v0 v1 on n eb p C K.
End PIPEALLOC.
