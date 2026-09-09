(* KexecDefs.v -- kexec()'s VOCABULARY LEAF (kernel/exec.c): the frame
   constants, the stack geometry and the RESULT RELATION [kexec_ok], stated
   independently of any proof.  Requires only the definitional layer -- never
   a whole-function proof file -- so every function proof can be checked in
   parallel.

   THE CONTRACT ITSELF IS [SpecKexec.KEXEC] ([wp_kexec_sconf]), above this
   file: kexec has ONE contract -- the walk, the single observation of the
   file, and the caller's own WP for the program observed
   (fs-syscall-specs.md, "ONE CONTRACT PER SYSCALL").  The
   frame there is this file's own premise list row for row, and its armed
   post implies the [kexec_ok] below at some entry
   ([SpecKexec.exec_arms_landed]), so everything this header says about
   what kexec promises is still read off [kexec_ok] here.  What lives here
   is what a caller or a block lemma needs WITHOUT the abstract-state layer:
   [K_kexec], [MAXARG], the [kxc_*] stack algebra, [kexec_ok] and
   [fs_fabric].

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
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import UserPtTree.
Require Import ProcDefs.
Require Import FileInvDefs.
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
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import FsReady. (* [fs_ready]: the fabric IS this predicate now *)
Import Defs.
Require Import TsoCtx.

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
Notation K_kexec := (184%nat) (only parsing).
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
   (* ...AND ITS fd-STATE GHOST NAME, which follows: exec never opens the
      descriptor block, so the [proc_ofiles] it hands back is the one it was
      given, authorities and all, and that is keyed on [pv_fdg].  Stated
      because the syscall dispatcher's return needs it -- the fd-state
      fragment bundle rides beside the block and has to be re-keyed. *)
   pv_fdg V' = pv_fdg V /\
   pv_cwd V' = pv_cwd V /\
   (* ...and the cwd's inum beside the pointer (lane C1): exec does not
      chdir, so [ProcDefs.pv_cwi] is untouched like the cell it labels *)
   pv_cwi V' = pv_cwi V /\
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
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname)
    (pd pav pu : mword 64)
    : iProp Σ :=
  (* FOUR ROWS WHERE THERE WERE SEVENTEEN (rank 1d).  This bundle used to
     SPELL the file system out -- the .rodata image, panic's credentials,
     the block and log ctx's, the crash seam, the era certificate, the
     icache's four, the inode region and its sealed regime, the device
     invariant -- at names each caller threaded.  Every one of those names
     is a [FsCfg.fscfg] / [IcacheRefDefs.icfg] field now, and a bundle spelled
     entirely at ambient names IS [FsReady.fs_ready]: a copy of a
     parameter-free predicate is still a copy.  [fs_fabric_all] below hands
     back the sixteen rows in the ORDER the cone's destructs read them, so
     nothing downstream had to move.

     WHAT IS NOT [fs_ready], and why each is here.  [procs_inv gs] is a
     PROCESS resource at the CALLER's own proc array -- the file system has
     no process content at all (FsCfg.v's header).  The disk fabric is at
     the caller's own three ring pages, which [fs_ready] QUANTIFIES (that
     record's ruling R1: [virtio_disk_init] [kalloc]s them at WP time), and
     the kexec cone threads them down to [bread]; [FsReady.disk_geom_agree]
     is the bridge in the other direction. *)
  (FsReady.fs_ready ∗
   procs_inv gs ∗
   disk_geom fsc_disk pd pav pu ∗
   is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu))%I.

Global Instance fs_fabric_persistent
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    gs pd pav pu :
  Persistent (fs_fabric gs pd pav pu).
Proof. rewrite /fs_fabric. apply _. Qed.

(* THE UNPACK, in the bundle's own historical order -- which is what keeps
   the cone's six positional [iDestruct]s verbatim across the collapse.
   Twelve of the sixteen rows are one [FsReady] projection each; the other
   four ride in the bundle. *)
Lemma fs_fabric_all
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname) (pd pav pu : mword 64) :
  fs_fabric gs pd pav pu -∗
  kernel_data ∗
  panic_env ∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) ∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev ∗
  fs_crash_seam fsc_cov fsc_logst ∗
  gen_cert ∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev ∗
  itable_inv ∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst ∗
  ic_sleeplocks fsc_ic ∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
  ireg_open ∗
  procs_inv gs ∗
  dev_inv fsc_uart fsc_disk ∗
  disk_geom fsc_disk pd pav pu ∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu).
Proof.
  (* row by row, not one [iFrame]: every conjunct is definition-valued, so a
     named frame pays a goal-side conversion per hypothesis -- the same
     measurement (107.7 s and 90.6 s at two call sites) that made the old
     constructor lemma worth having. *)
  iIntros "(#Hrdy & #Hprocs & #Hgeom & #Hdlock)".
  iDestruct (FsReady.fs_ready_icache with "Hrdy") as "(#Hitab & #Hitinv & #Hesc & #Hslks)".
  iDestruct (FsReady.fs_ready_region with "Hrdy") as "[#Hireg #Hropen]".
  iDestruct (FsReady.fs_ready_disk with "Hrdy") as "[#Hdevi _]".
  iSplitR; [iApply (FsReady.fs_ready_data with "Hrdy") |].
  iSplitR; [iApply (FsReady.fs_ready_panic with "Hrdy") |].
  iSplitR; [iApply (FsReady.fs_ready_bio with "Hrdy") |].
  iSplitR; [iApply (FsReady.fs_ready_log with "Hrdy") |].
  iSplitR; [iApply (FsReady.fs_ready_seam with "Hrdy") |].
  iSplitR; [iApply (FsReady.fs_ready_gen with "Hrdy") |].
  iSplitR; [iExact "Hitab"  |].
  iSplitR; [iExact "Hitinv" |].
  iSplitR; [iExact "Hesc"   |].
  iSplitR; [iExact "Hslks"  |].
  iSplitR; [iExact "Hireg"  |].
  iSplitR; [iExact "Hropen" |].
  iSplitR; [iExact "Hprocs" |].
  iSplitR; [iExact "Hdevi"  |].
  iSplitR; [iExact "Hgeom"  |].
  iExact "Hdlock".
Qed.

