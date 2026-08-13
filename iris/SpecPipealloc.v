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
   the fresh page kalloc hands back, which becomes the pipe.  It is also where
   a file's PAYLOAD is PUBLISHED: the [sd] that writes [f->pipe] is the moment
   the file starts owning one end, and pipealloc installs the pipe's ghost
   names in the slot's payload-names field ([FileInv.fpay_tok_update]) as it
   does so -- legal with no lock in hand precisely because it holds the only
   reference.  So the two ends do NOT come out separately: each is inside its
   own [file_ref], which is what makes the caller's descriptors mean
   something, and what hands the last [fileclose] a whole end to close.

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
Require Import WpLock.
Require Import WpNext.
Require Import PanicStub.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import IrefSlots InodeRegion.
From Kernel Require KernelSyms.
Require Import IrefSlots.
Local Open Scope Z_scope.


(* The address of the string literal "pipe" that pipealloc passes to initlock.
   It sits in .rodata past etext with no ELF symbol of its own, so it is spelled
   out here (kernel.asm: 80007598 <etext+0x598>). *)
Definition pipe_name_str : Z := 0x800075b8%Z.

Section SpecPipealloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !kallocG Σ}.

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
        unspecified contents.

        BOTH fd UNITS COME BACK.  Whichever of the three bad paths ran, the
        two units the caller supplied are accounted for: an unspent one is
        returned by filealloc's own failure arm, and a spent one comes back
        out of the fileclose that undoes it.  Without this the caller could
        not balance its books -- sys_pipe's postcondition returns its whole
        allowance on all four of its exits, and this is the only arm that
        could break that. *)
     ⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
     kalloc_avail γk on ∗ fd_slot ∗ fd_slot ∗
     (∃ w0 w1 : mword 64, pf0 ↦₈ w0 ∗ pf1 ↦₈ w1)
     ∨
     (* SUCCESS (a0 = 0): the two files, each owning one end of a live pipe.
        Each [file_ref] is EXCLUSIVE (fraction 1) -- pipealloc's own unlocked
        stores are what proves that legal, and the caller inherits the same
        right (it must, since sys_pipe still has to install them in its fd
        table).  The pipe itself is not a separate conjunct: [pipe_file]
        pins each file's type and pipe pointer, and [FileInv.file_payload]
        reads the end off exactly those fields. *)
     ⌜r = (zero_reg : mword 64)⌝ ∗
     kalloc_avail γk (avail_dec on) ∗
     (∃ (pi : mword 64) (k0 k1 : nat) (C0 C1 : fcontent),
        ⌜(k0 < NFILE)%nat /\ (k1 < NFILE)%nat⌝ ∗
        ⌜pipe_file pi false C0⌝ ∗ ⌜pipe_file pi true C1⌝ ∗
        pf0 ↦₈ fnode k0 ∗ pf1 ↦₈ fnode k1 ∗
        file_ref γf k0 1 C0 ∗ file_ref γf k1 1 C1))%I.

End SpecPipealloc.

Definition wp_pipealloc_sconf_body
    `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γfl γf : gname)                    (* ftable.lock, the file refcount ghost, the fd-slot ghost *)
    (γkl : gname) (γk : gname * gname) (fl : mword 64)   (* kmem.lock, kalloc's ghosts *)
    (m : regfile) (v0 v1 : mword 64) (on : option nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pipealloc in
  (* a0 = f0 (the read end's slot), a1 = f1 (the write end's slot).  They are
     SEPARATE conjuncts below, which is how the spec says the caller must pass
     two distinct cells -- the same separation-as-hypothesis idiom memmove
     uses for its two buffers. *)
  let pf0 : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pf1 : mword 64 := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* pipealloc's own frame is 6 slots (c.addi16sp sp,-48); of its four callees
     fileclose is the deepest, wanting [fileclose_stack] = 68 below that. *)
  (74 <= K)%nat ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true], so no existing
     call site changes; at [eb = false] the real pair, which can only have
     come from the TRAP.  pipealloc acquires no lock of its own, so it mints
     nothing and is a pure PASS-THROUGH: the two files it closes on its error
     paths are untyped ([SpecFileclose.fileclose_env_none], so neither arm can
     park), but fileclose's crossing is the literal [true] on EVERY arm, and a
     hart-indexed resource cannot be framed across such a call -- it has to be
     handed over and given back.  See
     claude-notes/completed/eb-generic-sweep.md. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the two object pools pipealloc draws on *)
  is_ftable γfl γf -∗
  is_lock γkl (mword_of_int KernelSyms.kmem) "kmem"%string (kmem_res γk fl) -∗
  kalloc_avail γk on -∗
  (* acquire's [if(holding(lk)) panic] arm, in filealloc / kalloc / fileclose *)
  panic_wp_any -∗
  (* pipealloc creates TWO references, so it needs two fd slots -- one per
     end of the pipe.  Both come back from the fileclose calls on the error
     paths. *)
  fd_slot -∗
  fd_slot -∗
  (* the caller's two [struct file *] cells; both are overwritten on entry, so
     their incoming contents are arbitrary *)
  pf0 ↦₈ v0 -∗
  pf1 ↦₈ v1 -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  pipealloc's error paths
     call fileclose, whose crossing is [true] on every arm, so pipealloc can
     return on another hart; the cost is the CALLER's, which must supply its
     continuation hart-generically. *)
  wp_next true p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    pipealloc_post γf γk on pf0 pf1 (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* The FS ghost CLASSES appear in the interface below although nothing in
   pipealloc's contract mentions the file system.  They are there because
   pipealloc calls fileclose, whose inode arm calls iput -- capacity only, no
   resource: the untyped files pipealloc closes make [fileclose_env] [emp]
   (SpecFileclose.fileclose_env_none), so the CONTRACT is unchanged.  There is
   no way to hide them behind a derived FD_NONE-only interface: the
   derivation's proof needs them and section discharge puts them back into the
   derived lemma's statement. *)
Module Type PIPEALLOC.
  Parameter wp_pipealloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !fileG Σ, !fdslotG Σ, !kallocG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ, !irefslotG Σ, !iregG Σ} `{GEN : GenId} `{CID : CpuId} (γfl γf : gname) (γkl : gname) (γk : gname * gname) (fl : mword 64)
      (m : regfile) (v0 v1 : mword 64) (on : option nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool),
      wp_pipealloc_sconf_body γfl γf γkl γk fl m v0 v1 on n eb p C K b.
End PIPEALLOC.
