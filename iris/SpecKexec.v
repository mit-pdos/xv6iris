(* SpecKexec.v -- the public interface of kexec() (kernel/exec.c), stated
   independently of its proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

     int kexec(char *path, char **argv)

   @ KernelSyms.kexec = 0x800046bc, 287 instructions / 860 bytes -- THE
   LARGEST FUNCTION IN THE TREE, three times the next one (kfork, 270 B), and
   the only one that is simultaneously an FS client, a page-table builder and
   a [struct proc] mutator.  A 544-byte frame (68 slots) holding four
   objects the contract never mentions because they are frame-resident
   ([StackBytes.slot_bytes_own], the way namei's [name[DIRSIZ]] is):

     s0-432  struct elfhdr elf     64 B   readi's first destination
     s0-488  struct proghdr ph     56 B   readi's per-segment destination
     s0-368  uint64 ustack[33]    264 B   the argv pointer vector
     s0-536/-528/-520/-512/-504    the spilled 0xfff mask, path, sz1, argv, off

   ---- THE FOUR THINGS IT DOES ------------------------------------------

   (1) OPENS THE EXECUTABLE, inside one log transaction:
         begin_op(); ip = namei(path); ilock(ip); readi(elf hdr)
       and closes it with iunlockput(ip); end_op() on every path.
   (2) BUILDS A SECOND ADDRESS SPACE -- proc_pagetable(p) for a table that is
       NOT p->pagetable, then per PT_LOAD program header uvmalloc + an
       INLINED loadseg (walkaddr + readi straight into the physical page).
   (3) PUSHES THE ARGUMENTS onto a fresh one-page user stack under a guard
       page (uvmalloc + uvmclear + copyout per argument + copyout of the
       pointer vector).
   (4) COMMITS: stores the new root, size, name, and three trapframe words,
       then frees the OLD table.  Everything before the commit is undone by
       [bad:] -- which is why the failure arm hands the process back at the
       IDENTICAL [V].

   ---- THE ALTITUDE, AND WHY IT IS TWO AT ONCE --------------------------

   kexec holds [ProcInv.proc_priv] (it writes p->sz, p->pagetable,
   p->trapframe's words and p->name) AND drives the [ProcPtOwn.proc_pt] tier
   directly, on a SECOND descriptor that no [proc_priv] describes yet.  That
   second descriptor is the whole difficulty: every existing bridge out of
   [proc_priv] ([proc_priv_addrspace], [proc_priv_copy]) pins [ud_root],
   because until now every caller grew or shrank the table it already had.
   [ProcInv.proc_priv_newspace] is the bridge that does not, and its ONE
   remaining pin is [ud_tfp] -- the trapframe page genuinely does not move
   across an exec (proc_pagetable maps whatever p->trapframe already holds,
   and [tf_page], the page's bytes, is outside [proc_pt] entirely, so it
   survives proc_freepagetable of the old table and is re-attached to the
   new descriptor).

   ---- WHAT THE SUCCESS ARM SAYS, AND WHAT IT DELIBERATELY DOES NOT -----

   SAYS: the process's private block is re-established at a NEW descriptor
   and a NEW size, the return value is [argc], and the three trapframe words
   the C writes hold the ELF entry point and the final stack pointer
   ([kxc_tf]).  Those are the facts a caller returning to user mode needs.

   DOES NOT SAY WHAT THE USER PAGES HOLD.  [proc_pt] owns its pages at
   EXISTENTIAL contents (the user-safety altitude -- see SpecVmfault.v and
   SpecCopyout.v, which record the same limitation for the same reason), so
   there is no resource in this contract that could record "the image is
   loaded".  Stating that the process will actually RUN the file's text needs
   a contents-indexed refinement of [proc_pt]; noted, not built, and it is
   the single largest thing this contract gives up.  What survives is
   structural: the entry PC, the stack pointer, the size, and the coherence
   between them.

   DOES NOT PIN THE NEW SIZE to the ELF's segment table either.  [szv'] is
   existential, related to [sp'] only by the stack geometry ([kxc_stack_ok]):
   the stack is the top page of the image and the guard page is below it.
   Pinning [szv'] would mean modelling the phdr loop's fold over
   [ph.vaddr + ph.memsz], which is stateable ([ElfEnc.v] has the field
   readers) but has no consumer while the contents are existential anyway.

   DOES NOT PIN p->name.  It is existential at the right length.  xv6 reads
   [p->name] only from procdump, which design/proc-struct.md already records
   as unprovable as written (it reads other processes' names with no lock).

   ---- THE FAILURE ARM IS EXACT ----------------------------------------

   [r = -1] hands back [proc_priv γf p pid V] at the SAME [V].  Every one of
   the eight [bad:] entries is reached before the commit block at +0x2dc, and
   the new table -- if one was built -- has gone through proc_freepagetable.
   This is what makes exec's failure invisible to the caller, and it is the
   property sys_exec needs to keep its own [proc_priv] story straight.

   ---- THERE IS NO LOG-BUDGET PREMISE, AND THERE USED TO BE ------------

   The log ledger has to cover namei AND the closing iunlockput out of ONE
   begin_op, and begin_op mints only [MAXOPBLOCKS = 10].  Priced through
   SpecNamei's COUNTED contract that is [(L+1) * iput_units + iput_units <=
   MAXOPBLOCKS], i.e. [3L + 6 <= 10] -- one path element, enough for "/init"
   and "sh" and not for "/bin/sh".  That premise stood here until sys_exec
   needed it: sys_exec's path arrives through [argstr], so its contents are
   EXISTENTIAL and no caller can ever discharge a claim about [L].  A
   contract with a premise its only caller cannot pay is not a bound on what
   the theorem covers -- it is an unusable contract.

   The fix is not to tighten the charge but to take the SET form.
   [SpecNamei.wp_namei_gen] over [LogInv.log_opS] prices the walk at
   [SpecNamex.walk_need L], which is 4 WHATEVER THE DEPTH, and spends at most
   two -- leaving eight for an iunlockput that needs three.  [log_op] is by
   definition [∃ Sb, log_opS], so phase A enters the set form with one
   [iDestruct] at the namei call and leaves it with [LogInv.log_opS_op]; the
   only other change is that the +0x032 seam carries [iput_units <= n1]
   rather than an interval in [L].  sys_chdir was the first syscall to need
   this (SpecSysChdir.v's ledger section); kexec is the second.

   * [na <= MAXARG]: the argument-count bound the C enforces with its
     [bne s1,s8] against 32.  Above it the function takes [bad:], which is
     the -1 arm, so this is a premise only of the SUCCESS disjunct.

   * [kxc_stack_ok]: the arguments fit in the one-page user stack.  Also only
     a success-arm condition; the C's two [bltu ...,s7] tests against
     [stackbase] take [bad:] otherwise.

   ---- THE TWO CALLEE CONTRACTS THIS FUNCTION FORCED OPEN ----------------

   Both were stated for the callers they had, and neither was usable here.
   Both have been generalised; the story is in claude-notes/projects/kexec.md.

   * SpecCopyout used to demand [p_pagetable p ↦₈ page_base P.(ud_root)] --
     i.e. that the table copied into IS the running process's -- because
     copyout may call vmfault, and vmfault read p->sz and mapped into
     p->pagetable rather than the table it was passed.  kexec copies into a
     table it has built and not yet installed, so this was a real blocker.

     *** RETIRED UPSTREAM. ***  xv6 `4f2fc8b` made vmfault take the size as
     an ARGUMENT and map into the table it was handed, and gave copyout a
     matching [psz] parameter in a1.  copyout is now stated over an
     arbitrary [proc_pt P] with no process cells at all, so kexec just
     passes the new image's size and the blocker is gone.  The [co_license]
     / [co_mapped] / [arm] apparatus that had been built to work around it
     is deleted (SpecCopyout.v) -- which is cheaper for kexec than the
     workaround was: it no longer has to establish [pte_vu] over its
     destination range at all.

   * SpecSafestrcpy used to demand the FULL [n = 16] source bytes, an
     over-ask its own header admitted.  kexec's source is [last], a pointer
     INTO the path string, and sixteen bytes past it run off the end of the
     caller's buffer.  It now takes an owned length [ns] with
     [SpecSafestrcpy.ssc_src_ok], and kexec pays the "there is a NUL inside
     what you own" disjunct out of the path's own [bb_cstr]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecIput.
(* [SpecNamex] for [ROOTDEV] -- a param.h constant that happens to live in a
   Spec file.  It should be hoisted the way [tf_epc_idx] was (see ProcGeom.v):
   a Spec should not have to require another function's Spec to name a
   constant.  Recorded in projects/kexec.md's cleanup list. *)
(* [SpecDirlink] for [ic_sleeplocks], and it must be THIS one: the definition
   exists three times, identically, in IcacheBoot.v / SpecFileclose.v /
   SpecDirlink.v, and in SpecNamei's import scope the name resolves to
   SpecDirlink's.  Since the two contracts have to compose, kexec's
   precondition must be the SYNTACTICALLY same proposition namei's is.  The
   three copies should be one; also in the cleanup list. *)
Require Import SpecDirlink.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.


(* ===================================================================== *)
(*  Constants the contract quotes by name.                                *)
(* ===================================================================== *)

(* param.h.  Both appear in the instruction stream as literals -- MAXARG as
   the [li s8,32] the argument loop compares against, USERSTACK inside the
   [lui a2,0x2] that makes [(USERSTACK + 1) * PGSIZE = 8192]. *)
Definition MAXARG : nat := 32%nat.
Definition USERSTACK : nat := 1%nat.

(* kexec's own 68-slot frame over namei's 106, which is the tallest callee
   (readi 78, iunlockput 64, end_op 58, copyout 52, uvmalloc 42, ilock 44,
   proc_pagetable / proc_freepagetable 40, begin_op 26, walkaddr 10,
   flags2perm / safestrcpy / strlen 2).

   THE TOP OF THE BMAP CHAIN now, not the psz/copyout one: printk's real
   stack need (48, printk_stack) dominates bmap (64), which dominates
   balloc's out-of-blocks arm (58), which propagated readi 72 -> 78 ->
   dirlookup 84 -> 90 -> namex 96 -> 102 -> namei 100 -> 106, and so this
   one 168 -> 174.  None of it is a soundness question, it is all just "the
   callee needs six more slots than it did" (SpecReadi.v's header has the
   arithmetic). *)
Definition K_kexec : nat := 174%nat.

(* ===================================================================== *)
(*  The argument-stack model.                                             *)
(* ===================================================================== *)
(* The pointer arithmetic of the two push loops, transcribed from the
   instructions rather than from the C, because the C's [sp -= sp % 16] is a
   MASK on the machine ([andi s2,a5,-16]) and the two agree only because the
   stack top is itself 16-aligned.

     sp -= strlen(argv[i]) + 1        [addiw a5,a0,1] [sub a5,s2,a5]
     sp &= ~15                        [andi s2,a5,-16]

   [kxc_round16] is that mask at the Z tier; every value the success arm
   quantifies over is at or above [stackbase] and hence non-negative, so the
   mask and [x - x mod 16] agree and no wrap can occur -- which is exactly
   what [kxc_stack_ok]'s in-range conjuncts buy. *)
Definition kxc_round16 (x : Z) : Z := x - x `mod` 16.

(* The stack pointer after pushing arguments [0 .. i).  [len i] is
   [strlen(argv[i])] -- the string's length, NOT counting its NUL, which is
   why the recurrence subtracts [len i + 1]. *)
Fixpoint kxc_sp (top : Z) (len : nat -> nat) (i : nat) : Z :=
  match i with
  | O => top
  | S i' => kxc_round16 (kxc_sp top len i' - (Z.of_nat (len i') + 1))
  end.

(* ...and after the pointer vector [ustack[0 .. argc]] is pushed on top of
   them: [sp -= (argc + 1) * 8; sp &= ~15]. *)
Definition kxc_sp_final (top : Z) (len : nat -> nat) (argc : nat) : Z :=
  kxc_round16 (kxc_sp top len argc - 8 * (Z.of_nat argc + 1)).

(* THE FIT CONDITION, one conjunct per [bltu ...,s7] the C executes: the
   pointer is tested against [stackbase] after every argument and once more
   after the vector.  [base] is [top - USERSTACK * PGSIZE]. *)
Definition kxc_stack_ok (top base : Z) (len : nat -> nat) (argc : nat) : Prop :=
  (forall i, (1 <= i)%nat -> (i <= argc)%nat -> base <= kxc_sp top len i)
  /\ base <= kxc_sp_final top len argc.

(* ===================================================================== *)
(*  What the commit block writes into the trapframe.                      *)
(* ===================================================================== *)
(*   p->trapframe->a1  = sp     [sd s2,120(a5)]   word 15 = tf_arg_idx 1
     p->trapframe->epc = entry  [sd a4,24(a5)]    word  3 = tf_epc_idx
     p->trapframe->sp  = sp     [sd s2,48(a5)]    word  6
   (ProcGeom's trapframe layout; word 6 has no name of its own yet.)  The
   three indices are distinct, so the order the C writes them in does not
   matter and the result is one simultaneous update. *)
Definition kxc_tf_sp_idx : nat := 6%nat.

Definition kxc_tf (ws ws' : list (mword 64)) (entry spv : mword 64) : Prop :=
  ws' = <[tf_epc_idx := entry]>
          (<[kxc_tf_sp_idx := spv]>
             (<[tf_arg_idx 1 := spv]> ws)).

(* ===================================================================== *)
(*  The result relation.                                                  *)
(* ===================================================================== *)
(* [V] is the private block on entry, [V'] the one on exit and [r] the
   returned a0.  Two arms, and the failure arm is an EQUALITY on the whole
   block -- see the header. *)
Definition kexec_ok (V V' : pprivate) (r : mword 64)
    (entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) : Prop :=
  (* FAILED: nothing moved.  Eight [bad:] entries, all before the commit. *)
  (r = (mword_of_int (-1) : mword 64) /\ V' = V)
  \/
  (* SUCCEEDED: a new address space, a new size, the three trapframe words,
     an existential name at the right length, and [argc] in a0.  The
     descriptor array and the working directory are untouched -- xv6's exec
     closes no descriptor and does not chdir.
       The two conditions the C tests and this arm therefore ASSERTS (rather
     than taking as premises: above them the machine goes to [bad:], which is
     the other arm) are the argument-count bound and the stack fit. *)
  (r = (mword_of_int (Z.of_nat na) : mword 64) /\
   (na <= MAXARG)%nat /\
   kxc_stack_ok (uint szv') (uint szv' - 4096) alen na /\
   pv_sz V' = szv' /\
   spv = (mword_of_int (kxc_sp_final (uint szv') alen na) : mword 64) /\
   ud_tfp (pv_upt V') = ud_tfp (pv_upt V) /\
   kxc_tf (pv_tf V) (pv_tf V') entry spv /\
   pv_ofile V' = pv_ofile V /\
   pv_cwd V' = pv_cwd V /\
   length (pv_name V') = PNAMELEN /\
   (* the stack geometry: [sp] sits in the top page of the image, above the
      guard page uvmclear turned unusable *)
   (uint szv' - 4096 <= uint spv)%Z /\
   (uint spv <= uint szv')%Z).

(* ===================================================================== *)
(*  THE FILE SYSTEM FABRIC, as one bundle.                                *)
(* ===================================================================== *)
(* Thirteen resources that every FS client's contract lists one by one --
   SpecNamei, SpecIlock, SpecReadi and SpecIunlockput each spell out their
   own subset, and kexec needs the union of all four.  EVERY ONE OF THEM IS
   PERSISTENT (machine-checked: the two invariants, the two ctx's, the four
   icache pieces, the crash seam, the era certificate, the disk lock and its
   geometry, and procs_inv, which is a big-op of [is_lock]).  So the bundle
   costs nothing to carry, nothing to split, and nothing to give back --
   which is what makes it worth having: kexec's four phases would otherwise
   each restate the thirteen, and a block statement that is thirteen lines of
   fabric before its first real resource is unreadable.

   A caller unbundles with one [iDestruct] at each callee call site.

   ITS HOME IS HERE ONLY UNTIL A SECOND CONTRACT WANTS IT.  Nothing about
   this is kexec-specific, and the right home is a shared [FsFabric.v] that
   SpecNamei / SpecIlock / SpecReadi / SpecIunlockput are all restated over.
   That is a sweep across eight Spec files and their proofs, it is not needed
   to prove kexec, and the tree's rule is to promote on the second consumer
   (as [ProcInv.proc_priv_name] and [InodeInv.ireg_blocks_ok] both were).
   Promote it then. *)
Definition fs_fabric
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (gs : list gname) (gu : uart_names) (gd : disk_names) (gk : gname)
    (pd pav pu : mword 64) (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname) (cn : ic_names) (gtl : gname)
    (cov : gset Z) (logstart inodestart : Z) (nib : nat) (dev : mword 32)
    : iProp Σ :=
  (bio_ctx bn (fs_view gfs gd dev cov) ∗
   log_ctx g bn gfs cov logstart dev ∗
   fs_crash_seam cov logstart ∗
   gen_cert ∗
   is_itable2 gtl cn gfs gi cov logstart nib dev ∗
   itable_inv ∗
   ic_escrows cn gfs gi cov logstart ∗
   ic_sleeplocks cn ∗
   ireg_inv gi gfs inodestart nib ∗
   procs_inv gs ∗
   dev_inv gu gd ∗
   disk_geom gd pd pav pu ∗
   is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu))%I.

Global Instance fs_fabric_persistent
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    gs gu gd gk pd pav pu bn g gfs gi cn gtl cov logstart inodestart nib dev :
  Persistent (fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
                        cov logstart inodestart nib dev).
Proof. apply _. Qed.

(* ===================================================================== *)
(*  The contract.                                                         *)
(* ===================================================================== *)
Definition wp_kexec_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (jp : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                       (* the icache + itable *)
    (ga : gname) (gf : gname)                           (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (used : gset Z)
    (plen : nat) (pfun : nat -> bv 8)                   (* the path buffer     *)
    (na : nat) (avf : nat -> mword 64)                  (* argv[0 .. na]       *)
    (alen : nat -> nat) (aslen : nat -> nat)            (* strlen / owned len  *)
    (afun : nat -> nat -> bv 8)                         (* the argument bytes  *)
    (pidv : mword 32) (V : pprivate)
    (dqb dqs dqa : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexec in
  let pj := proc_addr jp in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let av := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = argv *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kexec <= K)%nat ->
  (* ---- the file system's geometry, verbatim from SpecNamei ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* ...including the inode region's two ambient ties (fs-log.md §G.25):
     namei's walk MINTS the group receipt at its nlink guard, and
     [InodeRegion]'s vocabulary is ambient, so a contract that threads its
     own [g] and [inodestart] meets it through a pure equation.  Same
     pattern as the two above, and true at boot by [IcacheRef.icfg_alloc]. *)
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  (* ---- the path ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- the argument vector: [na] non-null pointers then a NULL ---- *)
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (* ...AND THE NULL IS INSIDE THE FIRST [MAXARG] ELEMENTS.  This is a
     PREMISE rather than something kexec discovers, because kexec cannot
     discover it: its own [argc >= MAXARG] test runs only once [argv[argc]]
     is known non-null, so a vector whose first null sits exactly at index
     [MAXARG] walks straight out of the loop with [argc = MAXARG] and the
     following [ustack[argc] = 0] writes one past [uint64 ustack[MAXARG]].
     sys_exec is the only caller and it guarantees the null is below MAXARG,
     which is what makes that store unreachable; see
     claude-notes/kernel-defects.md for the C-level story.  With the premise
     the argv loop's exit invariant can say [argc < MAXARG] outright instead
     of carrying the off-by-one as slack. *)
  (na < MAXARG)%nat ->
  (* each argument is a NUL-terminated string of [alen i] characters inside
     the [aslen i] bytes the caller owns *)
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (* EACH ARGUMENT FITS IN A PAGE, and this is load-bearing rather than a
     convenience.  The push at +0x222 is a 64-bit [sub], and the [bltu
     s2,s7] that guards it does NOT catch an underflow: a wrapped [sp] is
     ABOVE stackbase as an unsigned word, so the machine sails past the
     test with a stack pointer near 2^64.  The success arm's
     [kxc_stack_ok] -- an assertion, since [szv'] is existential and it
     therefore cannot be a premise -- is a Z-level claim and is simply
     FALSE on such a run, so something has to rule the underflow out.
     This does: with every argument at most PGSIZE-1 the decrement is at
     most 4096, and the invariant [stackbase <= sp] (established by the
     previous iteration's own [bltu]) plus [stackbase = sz1 - 4096] and
     [sz1 >= 8192] leaves [sp - (len+1) >= 0].
       sys_exec pays it for free: [fetchstr] copies each argument into a
     kalloc'd page and passes [max = PGSIZE], so no argument it hands over
     is longer.  It also subsumes the [< 2^31] bound strlen asks for. *)
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
  (* ---- the running process ---- *)
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  (* ---- THE INTERRUPT INDEX IS NOT A CHOICE THIS CONTRACT MAKES ----------
     [b = true] is FORCED by kexec's own callees, not by anything in its
     body: [SpecBeginOp], [SpecNamei], [SpecIlock], [SpecReadi],
     [SpecIunlockput] and [SpecEndOp] all state their continuation as
     [wp_next true pj], i.e. they are callable only with interrupts enabled,
     and phase A reaches the first of them at +0x00c.  That is a tree-wide
     convention (50 Spec files spell it the same way), not kexec's to
     change; relaxing it is an FS-layer sweep, recorded in
     claude-notes/projects/kexec.md.

     ONCE [b = true], THE OTHER THREE INDICES ARE THEOREMS RATHER THAN
     PREMISES.  [CpuOwn.cpu_own_on] reads
       [cpu_own n eb p C true lks  ⊣⊢  ⌜n = 0 /\ eb = true /\ lks = ∅⌝ ∗ C]
     so the nesting level is 0, the saved enable state is [true] and the
     held-lock set is empty on any run this contract describes -- a caller
     supplies them by supplying the bundle, and every seam in the proof can
     read them back off it.  [eb = true] below is therefore redundant with
     [b = true]; it is kept because it is what the callee contracts quote. *)
  b = true ->
  eb = true ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kalloc_env ga None -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_res gfs bmapstart cov logstart size used -∗
  (* THE PROCESS'S PRIVATE BLOCK.  p->pid, p->cwd and the cwd reference namei
     needs are all inside it (ProcInv.proc_priv_cwd_pid); so are the p->name
     bytes safestrcpy writes and the trapframe words the commit block writes. *)
  proc_priv gf pj pidv V -∗
  (* THE PATH AND THE ARGUMENT STRINGS ARE OWNED OUTRIGHT; only the argv
     POINTER VECTOR is fractional.  Not a preference -- namei demands the whole
     path buffer (SpecNamei.v:162) and copyout demands the whole source
     (SpecCopyout.v:174), and kexec hands its path straight to the first and
     each argument straight to the second.  Both callees only READ what they
     are given, so both over-ask; but unlike safestrcpy's and copyout's
     destination-table over-asks, THIS ONE COSTS KEXEC NOTHING -- sys_exec has
     [char path[MAXPATH]] on its own stack and kalloc's a page per argument, so
     it owns both outright.  Relaxing namei/namex/nameiparent and copyout's
     source to a fraction is the "right" shape and has no consumer; recorded in
     projects/kexec.md, not done.
       The pointer vector stays at [dqa] because kexec only loads from it. *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
  bslots bn 3 -∗
  iref_slots 2 -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
    (entry spv szv' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      ⌜kexec_ok V V' (mf !!! Regidx (mword_of_int 10 : mword 5))
                entry spv szv' na alen⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      ⌜used' ⊆ used⌝ -∗
      bitmap_res gfs bmapstart cov logstart size used' -∗
      kalloc_env ga None -∗
      proc_priv gf pj pidv V' -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
      ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
      ([∗ list] i ∈ seq 0 na,
         [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
      bslots bn 3 -∗
      iref_slots 2 -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KEXEC.
  Parameter wp_kexec_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_kexec_sconf_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                          ga gf cov logstart bmapstart inodestart nib
                          size dev used plen pfun na avf alen aslen afun
                          pidv V dqb dqs dqa m K eb b lks.
End KEXEC.
