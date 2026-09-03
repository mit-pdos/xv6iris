(* SpecSyscall.v -- the public interface of syscall() (syscall.c), stated
   ahead of its proof.  THIS CONTRACT IS ASSUMED: LinkSyscall.v supplies it
   with an [Axiom], the way LinkPrintk.v and LinkConsoleintr.v do for
   their functions.  It exists so usertrap can be proved against a stated
   interface rather than against nothing.

     void syscall(void) {
       struct proc *p = myproc();
       int num = p->trapframe->a7;
       if (num > 0 && num < NELEM(syscalls) && syscalls[num]) {
         p->trapframe->a0 = syscalls[num]();
       } else {
         printk("%d %s: unknown sys call %d\n", p->pid, p->name, num);
         p->trapframe->a0 = -1;
       }
     }

   @ KernelSyms.syscall = 0x80002872, 100 bytes / 33 instructions, a 32-byte
   ra/s0/s1/s2 frame.

   WHAT MAKES THIS ONE HARD TO STATE HONESTLY, and how the statement below
   handles it: syscall is an INDIRECT CALL through [syscalls[]], so its
   footprint is the UNION of all twenty-two sys_* functions' -- the file
   table, the buffer cache, the log, the inode cache, kalloc, the wait lock,
   the initproc cell, the fd and iref allowances.  Spelling that union out
   here would be to restate SpecSysExit.v's thirty parameters and then some,
   and every one of them would have to be threaded verbatim through
   usertrap's own contract for no gain: usertrap does not touch any of it,
   it only hands it over.

   MOST of that union is therefore still ONE ABSTRACT PARAMETER,
   [syscall_env γf pj], exactly as [SpecUsertrap.v]'s original boundary
   statement abstracted its kernel-internal resources: consumers thread it
   opaquely, and [ProofSyscall.v] defines it (as the union of whatever is
   NOT listed below, indexed by the ghost names the table's entries want)
   without churning usertrap's own proof.

   FOUR FAMILIES ARE PULLED OUT AS EXPLICIT PARAMETERS INSTEAD, and this is
   not an inconsistency with the paragraph above -- it is forced by a
   SHARING constraint [syscall_env] cannot express on its own.
   [UsertrapRes.ut_own] already threads [bslots]/the [initproc]
   cell/[fd_slots]/[iref_slots] to fund usertrap's OWN direct [kexit]
   calls on the killed-before/killed-after arms (both of which run OUTSIDE
   this call, never through [syscall_env]).  [SpecSysExit.v]'s own
   contract needs exactly the same four families for the SAME physical
   pool, reached only when the dispatch table selects [SYS_exit] -- so if
   [syscall_env] carried an independent copy of any of them, [ut_res]'s
   existential would be asking for TWO disjoint fundings of one pool, which
   no boot-time construction could discharge (durable-notes.md's "two
   owners of one address space" trap, in ghost-resource form: `own γ (◯ n)
   ∗ own γ (◯ n)` is not [False], but it silently doubles the authority a
   real allocation would have to supply).  So these four ride through
   [syscall()] itself on the SAME channel [ut_own] already uses for them,
   in and out, exactly like [proc_priv] -- not through [syscall_env].
   Everything else in the union genuinely has no competing outer copy
   ([UsertrapRes.v] never mentions the icache/inode-region invariants, the
   superblock cells, or the bitmap invariant at all), so it stays inside the
   still-abstract [syscall_env] -- but [syscall_env] is ALSO INDEXED BY
   [bn]/[fn], not just [γf]/[pj], for a second reason discovered writing
   [ProofSyscall.v]: eight entries (exit, pipe, close, chdir, mknod, link,
   mkdir, exec) need filesystem-fabric facts -- [bio_ctx], the kmem/itable
   locks, the icache invariants -- keyed to the SAME [bn]/[fn] the four
   explicit families above already carry.  Without the extra indices,
   [syscall_env]'s own internal existential witnesses for those facts could
   never be shown equal to the AMBIENT [bn]/[fn] a caller already fixed --
   not a competing-owner problem this time, but an unreachable-witness one,
   and the fix is the same shape: widen the index rather than smuggle the
   fact through an unrelated channel. [UsertrapRes.ut_own]'s own [Rsys]
   slot widened to match (`Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)`),
   which every one of its ~25 mentions in that file threads opaquely --
   NOTHING in [ProofUsertrapSys.v]'s call site needed to change, since it
   never applies [Rsys]/[syscall_env] itself, only names the resource
   `Rsys ...` produces.

   What the contract does say concretely is the part usertrap actually depends on:

     - the process block goes in and comes back, at a MOVED record [V'] --
       every syscall may write [p->trapframe->a0] (the return value), and
       sbrk/exec/chdir/open move [pv_sz] / [pv_upt] / [pv_cwd] / [pv_ofile]
       besides.  The one thing pinned is [ud_tfp]: the trapframe PAGE never
       changes (even exec, which builds a whole new table, maps the existing
       [p->trapframe]), and prepare_return's stores land there;
     - callee-saved registers are preserved and the pc returns to ra;
     - the crossing is REAL ([wp_next]): sys_wait / sys_pause / sys_read
       park, so syscall can return on a different hart;
     - and syscall MIGHT NOT RETURN AT ALL, without the contract having to
       say when.  [sys_exit] parks the thread as a ZOMBIE, and which entry
       runs is the syscall number, decided inside the dispatch -- so the exit
       slot is an ADDITIVE CONJUNCTION of the return continuation and a
       [ProcDefs.kstack_closer], and the callee picks.  The note at the slot
       itself is the argument for why [∧] is the only one of the three
       connectives that can be paid here.

   THE INDEX IS PINNED AT [true], AND UNLIKE prepare_return'S THAT IS NOT A
   GAP.  syscall has exactly one call site -- usertrap's [jal syscall] --
   and the instruction immediately before it is [csrsi sstatus,2], xv6's
   [intr_on()].  The sys_* cone below needs it: everything that sleeps
   ([SpecSleep]) or parks ([SpecKexit]) demands [eb = true], and at push_off
   level 0 the base-enable and the live index coincide
   ([CpuOwn.cpu_own_eb_agree]).  So the pinned index states a property of the
   only reachable configuration, rather than excluding one.                 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import WpMmodeLeafBase.  (* [csp_rs1] *)
Require Import ProcDefs.  (* [kstack_closer] -- the exit slot's right conjunct *)
Require Import FdSlots.
Require Import UsysMemOk.   (* [usys_fd_ok] -- the descriptor rows, shared *)
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import BioDefs.        (* [bio_names], for [bslots] *)
Require Import SpecFileclose. (* [fclose_names] -- see the header *)
(* The classes the widened binder list now generalizes over
   ([kallocG]/[bioG]/[diskGhostG]/[uartGhostG]/[fsLogG]/[logG]/[fsCrashG]/
   [iregG]) -- [Require Import SpecFileclose]/[SpecSysExit] does not put
   them in scope transitively, and backtick generalization then silently
   invents fresh binders with those names (durable-notes.md's typeclass-sweep
   trap: the tell is [UNDEFINED EVARS]/"unresolved implicit arguments"
   naming exactly these). *)
Require Import SpecSysExec.   (* [K_sys_exec]: the deepest entry in the table *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import WpLock.       (* [is_lock] *)
Require Import SpecProcinit. (* [wait_lock_addr] *)
Require Import WaitInv.      (* [wait_res] *)
Require Import FileInv.      (* [is_ftable] *)
Require Import DiskInv.      (* [disk_geom] *)
Require Import FirstTok.     (* [first_done] -- what the environment's producer takes *)
Require Import SyscParkEnv. (* [sysc_park_extra] -- and the four rows it does not *)
Require Import ParkCap.     (* [park_token] -- the park, as the resource fork hands down *)
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.  (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import UserPtTree.       (* [umem_wr] *)
Import Defs.

(* ===================================================================== *)
(*  WHICH USER BYTES A SYSCALL CAN HAVE MOVED.                            *)
(* ===================================================================== *)
(* The dispatch hands back a fresh [U'] and, until this predicate, said
   nothing whatever about the image inside it.  That is the [proc_pt_any]
   smell one tier up -- a contract that cannot say what happened to the
   process state -- and at THIS altitude the answer is a function of the
   syscall NUMBER, which the ENTRY state already determines.

   [sysc_num V] is the number the dispatch itself reads: [p->trapframe->a7],
   trapframe word 21 = [tf_arg_idx 7], as a SIGNED 32-bit value because the C
   reads it into an [int] and tests [num > 0 && num < NELEM(syscalls)].  The
   [ld a5,168(s2)] at +0x16 and the [addiw a3,a5,0] at +0x1a are where that
   reading comes from.

   THE FOUR ENTRIES THAT WRITE USER MEMORY GET A ROW EACH, SPELLED OUT.
   There used to be a [sysc_window] table naming only WHICH ARGUMENT the
   write is based at, with the length left entirely existential -- which
   made the row nearly vacuous: a caller passing a null pointer to [wait]
   learned only that the kernel had written SOME run from address 0
   upward, which is enough to clobber the caller's own text.  Each entry
   now says how far the write can reach, which is what every one of the
   four callee contracts already proved and this table discarded
   ([SpecKwait]'s [d <= 4], [SpecSysPipe]'s [d <= 8], [SpecFilestat]'s
   [d <= 24], [SpecSysRead]'s [d <= max 0 count]).

   WHAT STAYS EXISTENTIAL IS THE LENGTH WITHIN THAT BOUND AND THE BYTES,
   NEVER AN IMAGE.  A caller learns that nothing outside the run
   [arg .. arg+d) moved, which is what it can act on
   ([UserPtTree.umem_wr_lookup_out]); which bytes landed there is the
   ENTRY's own contract to say, and the console and pipe arms cannot say
   it at all.

   TWO ENTRIES MOVE THE ADDRESS SPACE ITSELF and a window is the wrong
   shape for them.  [sbrk] gets [sysc_sbrk_ok] below -- a FUNCTION of the
   entry and exit sizes, saying which way the address space went and how
   far, descriptor included; [exec] replaces the address space outright and
   is unconstrained here, its image being [SpecKexec]'s to pin. *)
Definition sysc_num (V : pprivate) : Z :=
  bv_signed (subrange_vec_dec (pv_tf V !!! tf_arg_idx 7) 31 0 : mword 32).

(* [read]'s count, as the C reads it: argument 2 into an [int].  The read
   row is the one whose length is not a constant. *)
Definition sysc_rdcount (V : pprivate) : Z :=
  bv_signed (subrange_vec_dec (pv_tf V !!! tf_arg_idx 2) 31 0 : mword 32).

(* SBRK SAYS WHAT HAPPENS.  Not "one of three things may have moved", but:
   at the OLD size [szv] and the NEW one [szv'], either extend the memory up
   with zeroed pages or cut it down -- and, because the U tier's permission
   row needs it, WHICH DESCRIPTOR came back.

   On the way UP the table is only ever EXTENDED, and every leaf it gains is
   vmfault's own RW-user leaf inside the new size ([ProcPtOwn.uptd_ext_sz]):
   the lazy path maps nothing at all, and the eager path's uvmalloc maps
   [PTE_R|PTE_W|PTE_U].  On the way DOWN the descriptor is uvmdealloc's run,
   named exactly -- the count is [ProcPtOwn.uvmd_np] of the two sizes, which
   is 0 (hence the whole row an identity) on growproc's WRAP sub-case, which
   is why that one lands in the FIRST branch beside the failures. *)
Definition sysc_sbrk_ok (P P' : uptd) (szv szv' : mword 64)
    (M M' : gmap Z (bv 8)) : Prop :=
  if decide (uint szv <= uint szv')%Z
  then ProcPtOwn.uptd_ext_sz szv' P P' /\ M' = umem_grow M (uint szv')
  else P' = ProcPtOwn.uptd_del_run P (svpn_of (ProcPtOwn.pgroundup szv'))
                                     (ProcPtOwn.uvmd_np szv szv')
       /\ M' = umem_del M (uint (ProcPtOwn.pgroundup szv'))
                          (4096 * ProcPtOwn.uvmd_np szv szv').

Definition sysc_mem_ok (V V' : pprivate) (M M' : gmap Z (bv 8)) : Prop :=
  if decide (sysc_num V = 7) then True                    (* exec *)
  else if decide (sysc_num V = 12) then                   (* sbrk *)
    sysc_sbrk_ok (pv_upt V) (pv_upt V') (pv_sz V) (pv_sz V') M M'
  else if decide (sysc_num V = 3) then                    (* wait *)
    (* copyout of the zombie's four-byte [xstate] at argument 0 -- and
       kwait's own [addr != 0] test means a NULL destination is not a
       destination at all, which is what lets a caller passing a null
       status pointer keep every byte it held across the call. *)
    exists (d : nat) (bs : nat -> bv 8),
      (d <= 4)%nat /\
      (pv_tf V !!! tf_arg_idx 0 = (zero_reg : mword 64) -> d = 0%nat) /\
      M' = umem_wr M (pv_tf V !!! tf_arg_idx 0) d bs
  else if decide (sysc_num V = 4) then                    (* pipe *)
    (* two four-byte fds, back to back at argument 0 *)
    exists (d : nat) (bs : nat -> bv 8),
      (d <= 8)%nat /\ M' = umem_wr M (pv_tf V !!! tf_arg_idx 0) d bs
  else if decide (sysc_num V = 5) then                    (* read *)
    (* at most the caller's own count, at argument 1 *)
    exists (d : nat) (bs : nat -> bv 8),
      (Z.of_nat d <= Z.max 0 (sysc_rdcount V))%Z /\
      M' = umem_wr M (pv_tf V !!! tf_arg_idx 1) d bs
  else if decide (sysc_num V = 8) then                    (* fstat *)
    (* one [struct stat]: dev@0 ino@4 type@8 nlink@10 size@16, so 24 *)
    exists (d : nat) (bs : nat -> bv 8),
      (d <= 24)%nat /\ M' = umem_wr M (pv_tf V !!! tf_arg_idx 1) d bs
  else M' = M.

(* THE DESCRIPTOR TABLE'S ROWS, beside the image's.  [sysc_mem_ok] above
   says what syscall() does to the process's memory; this says what it does
   to [p->ofile[]], keyed on the same [sysc_num V] and in the same shape.

   TWO PREDICATES RATHER THAN ONE, for the reason the two halves of the
   round are separate everywhere else on this path: a syscall proof
   discharges them against different resources -- the page table and the
   image on one side, [FdSlots.fd_frags] and the ofile array on the other --
   so a single conjunction would force every entry's proof to have both in
   hand at once.  They are stated adjacently so that "what this entry
   moves" is still one thing to read.

   THE STATES ARE A PARAMETER, not a field of [pprivate].  [pv_fdg V] is the
   per-incarnation GHOST NAME; the states under it are what
   [FdSlots.fd_frags (pv_fdg V) sts] holds, so the row takes them the way
   [UsysMemOk.usys_fd_ok] does.  [UsysMemOkSpec.sysc_fd_ok_usys] is the
   bridge, exactly as [sysc_mem_ok_usys] is for the image. *)
(* PIPE'S TWO ROWS, JOINED.  [sysc_mem_ok] says eight bytes appeared at
   argument 0; [sysc_fd_ok] says two slots opened.  Separately they are two
   existentials and a caller learns nothing it can act on -- it cannot close
   what pipe gave it.  This says it ONCE: the two descriptors the table
   moved ARE the two words the image gained.

   Stated on the WRITTEN FUNCTION rather than on byte lookups, because the
   no-wrap side condition a lookup needs is the caller's own (it comes from
   owning the run).  See [SpecSysPipe.sys_pipe_post], which is where the
   fact is proved, by [reflexivity]. *)
(* ...and PIPE'S TWO ROWS JOINED, at the dispatcher's vocabulary.  The
   statement itself is [UsysMemOk.usys_pipe_ok] -- the same table the
   descriptor row is stated against -- so that the four layers above this
   one carry ONE proposition rather than a chain of restatements, and its
   two congruences ([usys_pipe_ok_arg_cong] / [..._epc]) serve all of them.
   See [UsysMemOk.v]'s SS2c for what the join buys and why the bytes are
   stated on the written function rather than on lookups in [M']. *)
Definition sysc_pipe_ok (V : pprivate) (M M' : gmap Z (bv 8))
    (r : mword 64) (sts sts' : list fdstate) : Prop :=
  UsysMemOk.usys_pipe_ok (sysc_num V) (pv_tf V) r M M' sts sts'.

(* the quiet reading: every other entry owes nothing here *)
Lemma sysc_pipe_ok_quiet (V : pprivate) (M M' : gmap Z (bv 8))
    (r : mword 64) (sts sts' : list fdstate) :
  sysc_num V <> UsysMemOk.USYS_pipe -> sysc_pipe_ok V M M' r sts sts'.
Proof. intros Hne. exact (UsysMemOk.usys_pipe_ok_quiet _ _ _ _ _ _ _ Hne). Qed.

Definition sysc_fd_ok (V : pprivate) (r : mword 64)
    (sts sts' : list fdstate) : Prop :=
  UsysMemOk.usys_fd_ok (sysc_num V) (pv_tf V) r sts sts'.

(* ...and the same at the kernel's vocabulary, which is what a dispatch arm
   applies: it knows [sysc_num (us_V U) = k] for its own literal [k]. *)
Lemma sysc_fd_ok_refl_at (V : pprivate) (r : mword 64) (sts : list fdstate)
    (k : Z) :
  sysc_num V = k ->
  k <> 21 -> k <> 10 -> k <> 15 -> k <> 4 ->
  sysc_fd_ok V r sts sts.
Proof.
  intros Hk Hc Hd Ho Hp. unfold sysc_fd_ok.
  exact (UsysMemOk.usys_fd_ok_refl_at _ k (pv_tf V) r sts Hk Hc Hd Ho Hp).
Qed.

(* syscall's own frame is 4 slots; below it the deepest table entry, which is
   sys_exit at [K_sys_exit] = 4 + kexit's 74.  Written as an expression, not
   a literal, so a change to kexit's budget cannot silently leave this one
   behind -- the drift would be invisible until a caller's [av] premise
   failed somewhere far away. *)
Notation K_syscall := ((4 + K_sys_exec)%nat) (only parsing).
Definition wp_syscall_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (R : gname -> mword 64 -> fclose_names -> iProp Σ)
    (γf : gname) (γs : list gname) (j : nat) (γl : gname)
    (fn : fclose_names)
    (ip : mword 64) (dqi : dfrac)
    (m : regfile) (av : nat)
    (pid : mword 32) (U : ustate)
    (* THE DESCRIPTOR STATES syscall() IS ENTERED AT.  The post below states
       [sysc_fd_ok] against them, beside [sysc_mem_ok] against the image. *)
    (sts : list fdstate) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.syscall in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_syscall <= av)%nat ->
  (* THE ONE TIE BETWEEN [fn]'s FIELDS AND A DISPATCH PARAMETER THAT [fn]'s
     OWN INDEX LIST CANNOT REACH.  [sys_exit]'s contract asks for [fn] to BE
     the record built out of the running process's names, and every field of
     that record except this one is either a field of [fn] itself or an index
     of [syscall_env] ([pj], [bn]) -- so every other tie is statable inside
     the bundle.  [pid] is neither, hence a premise.
     IT COSTS THE CALLER NOTHING: [UsertrapRes.un_fn] is DEFINED as
     [MkFCloseNames ... (un_pid N) ...] out of the very fields this names, so
     usertrap discharges it by [reflexivity].  Widening [syscall_env] with a
     [pid] index instead would have reached [wp_syscall_sconf_body]'s [R] and
     [UsertrapRes.ut_own]'s [Rsys] slot for the same effect. *)
  fcn_pid fn = pid ->
  (* INTERRUPTS ON, at push_off level 0 -- see the header: the [csrsi] that
     precedes the only call site, and what the parking entries need. *)
  sie_cap_gpr KT1 m av true pj -∗
  cpu_own 0%nat true pj true lks -∗
  (* [kernel_data] is the jump table itself ([syscalls] lives in .rodata) and
     argraw's below it; [procs_inv] is the proc array and the
     panic arms every acquire/release in the cone reaches. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  procs_inv γs -∗
  (* THE FIVE FAMILIES [ut_own] ALSO holds -- see the header for why they
     ride here rather than inside [R].  [sys_exit] (reached through the
     table) is the only entry that draws on them; the other twenty-one
     simply frame them across their own call. *)
  bslots 3 -∗
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  fd_slots FDSPARE -∗
  iref_slots IREFSPARE -∗
  (* everything else the twenty-two entries consume, abstractly -- header.
     Indexed by [bn]/[fn] too, not just [γf]/[pj]: eight of the entries need
     filesystem-fabric facts (bio_ctx, the kmem/itable locks, icache
     invariants) keyed to the SAME [bn]/[fn] the four explicit families
     above already carry, and an [R] that could not reference them would
     have no way to prove its own internal witnesses equal the ambient
     ones -- the "two owners" trap in reverse: not a competing copy, but an
     UNREACHABLE one. *)
  R γf pj fn -∗
  proc_priv γf pj pid U -∗
  (* THE DESCRIPTOR-STATE FRAGMENTS, in and out on the same channel as the
     four families above and for the same reason: [UsertrapRes.ut_own] holds
     them, and four of the twenty-two entries (open, close, pipe, dup) spend
     them -- retyping a descriptor takes both halves after [ProcInv]'s
     auth/frag split, and the array holds only the authority.  exit and fork
     spend them too, through the process they end or start.

     AT A NAMED TABLE, so the post can say which descriptors moved. *)
  fd_frags (pv_fdg (us_V U)) sts -∗
  (* THE EXIT SLOT IS AN ADDITIVE CONJUNCTION, AND THAT IS WHAT LETS ONE
     TABLE ENTRY NOT RETURN WITHOUT THE CONTRACT SAYING WHICH ONE.

     Twenty-one entries return; [sys_exit] parks the thread as a ZOMBIE and
     never does.  The choice is made INSIDE the dispatch (it is the table
     index), so both outcomes have to be available at entry -- and the two
     are funded by the SAME resources, namely the caller's own frame cells,
     since only one of them ever happens.  That is exactly what [∧] means in
     a separation logic and what neither of its neighbours can say:

       [∗] would make the caller supply both AT ONCE, out of disjoint
           resources -- usertrap cannot, its frame cells are needed by each;
       [∨] would make the CALLER pick -- usertrap cannot, it does not know
           the syscall number;
       [∧] makes the caller prove EACH from its full context and lets the
           CALLEE pick, which is the real control flow.

     So syscall() never has to expose whether it returns.  What is proved is
     only the conditional: IF an entry declines to return, THEN it can
     reclaim the kernel stack.  A returning arm takes the left conjunct and
     is written exactly as it was before this slot changed.

     The right conjunct is anchored at syscall's OWN entry sp with depth
     [trap_res true + av], which is the anchor and depth [SpecSysExit] wants
     one frame further down: an arm walks it there with
     [ProcDefs.kstack_closer_frame] over syscall's own four slots.  It costs
     the caller nothing it did not already have -- usertrap is entered with
     sp AT THE PAGE TOP, where [ProcDefs.kstack_closer_top] mints a closer
     out of the PERSISTENT [is_kstack] alone -- which is why this change
     stops here and reaches neither [SpecUsertrap] nor [SpecUservec]. *)
  (wp_next true pj (fun (CID : CpuId) =>
    (* ...AND THE IMAGE MOVES, BY AN AMOUNT THE TABLE INDEX DETERMINES.
       The dispatch reaches entries that write user memory (wait, pipe,
       read, fstat through copyout; sbrk and exec through the address space
       itself), and [sysc_mem_ok] below says which of those happened.  A
       copyin's page fault is NOT one of them: at the lazy [proc_ptm] view
       backing a page moves no byte ([SpecVmfault]), which is what lets the
       sixteen remaining entries read [us_M U' = us_M U] on the nose. *)
    ∀ (mf : regfile) (U' : ustate)
      (* THE DESCRIPTOR STATES THE CALL LEFT, beside the record it left *)
      (sts' : list fdstate),
      ⌜ callee_saved m mf ⌝ -∗
      (* ...AND WHICH USER BYTES CAN HAVE MOVED, by table index -- see
         [sysc_mem_ok] above.  Sixteen of the twenty-two entries touch no
         user memory at all and this reads [us_M U' = us_M U] for them. *)
      ⌜ sysc_mem_ok (us_V U) (us_V U') (us_M U) (us_M U') ⌝ -∗
      (* ...AND WHICH DESCRIPTORS MOVED, by the same table index.  Eighteen
         of the twenty-two never receive the fragment bundle at all, so this
         reads [sts' = sts] for them; the four that do (open, close, dup,
         pipe) each say exactly which slot they changed and to what.  See
         [sysc_fd_ok] above and [UsysMemOk.usys_fd_ok] beneath it.

         THE RETURN VALUE IS READ OUT OF THE OUTGOING TRAPFRAME, not out of
         a register: the a0 slot is what the [sd a0,112(s2)] at
         [syscall + 0x3a] just stored, and it is the word the USER will
         see.  Reading it here rather than at [mf]'s a0 is what lets the
         caller compose -- usertrap's own fd row and the user tier's ecall
         arm both speak the trapframe word, and nothing above this frame
         can see a register.  (The out-of-range fallback stores from a4,
         not a0, so a register-keyed clause would have been false there
         anyway; its row is the quiet one and reads no return value.) *)
      ⌜ sysc_fd_ok (us_V U)
                   (pv_tf (us_V U') !!! tf_arg_idx 0) sts sts' ⌝ -∗
      (* ...and PIPE's two rows joined, so a caller can close what it got *)
      ⌜ sysc_pipe_ok (us_V U) (us_M U) (us_M U')
                     (pv_tf (us_V U') !!! tf_arg_idx 0) sts sts' ⌝ -∗
      (* ...AND THIS ARM RETURNED, WHICH RULES [exit] OUT (milestone J,
         K1).  [sysc_mem_ok] does NOT: exit falls into the quiet
         "nothing moved" row, so the table alone cannot tell a returning
         round from the one that never comes back -- and the
         user-execution contract hands back [emp] at exit
         ([UexecRet.uexec_ret]'s own arm), so a loop that could not
         refute "the process exited and returned nothing" would be
         stuck.  This clause is the refutation, and it is FREE: it sits
         in the RETURNING conjunct of the exit slot, which only the
         twenty-one returning entries ever take -- each off its own
         table index -- while [sys_exit] takes the divergent conjunct
         and owes nothing. *)
      ⌜ sysc_num (us_V U) <> 2 ⌝ -∗
      (* ...AND THE RESUME RECORD IS PINNED.  The three rows below are what
         the user-execution slot (milestone J) needs and nothing above says;
         each is stated to what is TRUE rather than to what would be tidy.

         (i)  THE TRAPFRAME WORDS.  Literal equality is FALSE -- the return
              value IS written into the a0 slot, by the [sd a0,112(s2)] at
              [syscall + 0x3a], i.e. AFTER the dispatch returns -- so what
              holds is that the outgoing list is the entry list with the a0
              word replaced.  The word itself is not named: [uexec_ret]'s
              ecall arm forall-binds the return value and the caller
              instantiates it at whatever was stored.
         (ii) THE PAGE-TABLE DESCRIPTOR.  Literal equality is FALSE on the
              eleven buffer-touching entries -- a copyin/copyout lazy fault
              grows [ud_um] -- so what holds is [ProcPtOwn.uptd_ext_sz] at
              the process's OWN SIZE: same root, same trapframe page, a user
              map that only gained entries, each of them BELOW [p->sz] and
              carrying vmfault's own RW-user bits.  The size and the bits
              are what [UserPerm.perm_of_uptd_ext_sz] needs to see that the
              PERMISSION PROJECTION does not move under a lazy fill, which
              is the [pi' = pi] the user-execution round
              ([UexecRound.uround_ok]) is stated with -- a bare [uptd_ext]
              cannot get there ([upt_acc_wf] permits R+X user leaves, and
              text pages genuinely are R+X below [p->sz]).  Every producer
              has it: copyin / copyout / copyinstr return it and the whole
              chain between them and this post now relays it.
         (iii) THE SIZE, verbatim.

         [exec] escapes all three (it replaces the address space, trapframe
         and all) and [sbrk] escapes (ii) and (iii) (it resizes it).  The
         escapes are by [sysc_num], which the ENTRY record already
         determines, so an arm selects its branch exactly as it does for
         [sysc_mem_ok]. *)
      ⌜ sysc_num (us_V U) = 7 \/ exists w : mword 64,
          pv_tf (us_V U') = <[tf_arg_idx 0 := w]> (pv_tf (us_V U)) ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ sysc_num (us_V U) = 12 \/
          ProcPtOwn.uptd_ext_sz (pv_sz (us_V U))
            (pv_upt (us_V U)) (pv_upt (us_V U')) ⌝ -∗
      ⌜ sysc_num (us_V U) = 7 \/ sysc_num (us_V U) = 12 \/
          pv_sz (us_V U') = pv_sz (us_V U) ⌝ -∗
      (* THE TRAPFRAME PAGE IS THE ONE THING THAT CANNOT MOVE.  Everything
         else in the record may: [pv_tf] always does (the a0 slot is the
         return value), and sbrk / exec / chdir / open move the rest. *)
      ⌜ ud_tfp (pv_upt (us_V U')) = ud_tfp (pv_upt (us_V U)) ⌝ -∗
      (* ...and the fd-state ghost name, which no syscall reassigns: only
         allocproc chooses one ([ProcInv.proc_dormant_unused]), and fork
         chooses the CHILD's.  So the bundle below is stated at the ENTRY
         record and this equation is what lets the caller re-key it. *)
      ⌜ pv_fdg (us_V U') = pv_fdg (us_V U) ⌝ -∗
      sie_cap_gpr KT1 mf av true pj -∗
      cpu_own 0%nat true pj true lks -∗
      bslots 3 -∗
      (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      R γf pj fn -∗
      proc_priv γf pj pid U' -∗
      fd_frags (pv_fdg (us_V U)) sts' -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang))
   ∧ kstack_closer pj (m !!! Regidx csp_rs1) (trap_res true + av)) -∗
  WP (Loop : expr riscv_lang).

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Module Type SYSCALL.
  (* the kernel-side resources the syscall table's entries consume, for the
     process at [pj] whose open-file table is named by [γf].  Defined
     concretely by the (future) proof; threaded opaquely by usertrap.

     HART-FREE, AND THAT IS PART OF THE CONTRACT rather than an accident of
     the binder list.  The environment is FRAMED across steps that run at
     [b = true] -- syscall's own tail after a parking table entry returns, and
     usertrap's whole tail on this arm ([jal killed], [jal prepare_return]) --
     and at that index a step may resume on a DIFFERENT hart.  A hart-indexed
     resource cannot cross: [IntrDefs.trap_csrs_ext_transport] and its
     siblings work only because their propositions are [emp] at [true], and
     nothing of that kind is available for an abstract family.  So the union
     of the twenty-two entries' footprints has to be hart-free, which it is:
     locks, invariants, ghost fragments and memory points-to, no per-hart
     register cell and no [tick_hart].  (Compare [SpecDevintr.devintr_caps],
     which genuinely is per-hart -- [TimerCap.timer_cap] holds this hart's
     mcounteren/stimecmp -- and which usertrap therefore carries in the
     hart-generic [UsertrapRes.devintr_caps_any] form instead.) *)
  Parameter syscall_env :
    forall {Σ : gFunctors} `{XI : CurCtx}
           `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId},
      gname -> mword 64 -> fclose_names -> iProp Σ.
  (* ===================================================================== *)
  (* THE ENVIRONMENT'S PRODUCER -- the one thing about [syscall_env] that   *)
  (* has never had one.                                                     *)
  (* ===================================================================== *)
  (* [LinkSyscall.v] has said all along that establishing the environment is
     the boot chain's job and is still owed: the dispatch is LINKED, all
     twenty-two arms, no axiom, but nothing anywhere BUILDS a
     [syscall_env].  It only ever arrives abstractly, as usertrap's [Rsys].
     That is fine for a process already in the trap loop and impossible for
     a process being put INTO it, which is why parking a fresh process has
     been assumed since kfork was written.

     THIS IS THAT PRODUCER, and its premise list is the point.  Everything
     the environment needs about the FILE SYSTEM comes from [first_done]
     ([first_addr |->4[] 0 and FsReady.fs_ready]) -- including the
     environment's own fourth conjunct, which IS [first_done].  What is left
     is four persistent rows the file system does not carry
     ([SyscParkEnv.v] names them) and four the caller is holding anyway for
     [UsertrapRes.ut_caps] (the [wait_lock], [is_ftable], [procs_inv],
     [disk_geom]).  Nothing here is exclusive and nothing here is boot
     state.

     WHY [first_done] AND NOT [fs_ready]: the environment's fourth conjunct
     is the steady arm of proc.c's [static int first], whose discarded cell
     is written by exactly one instruction in the kernel -- the release
     store on forkret's boot arm.  A producer given only [fs_ready] would
     be short a row that userinit, which parks the very process that runs
     that store, could not possibly supply.  See SpecForkret.v's last
     header section for the whole ordering argument.

     THE INDICES ARE READ OFF [fn] rather than taken as parameters, because
     [sysc_proc_ties] pins them: [pj] must be [proc_addr (fcn_j fn)].  The
     three pure premises below ARE that record, which since rank 1d is the
     PROCESS half and nothing else. *)
  Parameter syscall_env_park :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
      (γf γw γft γtk : gname) (fn : fclose_names),
      (fcn_j fn < NPROC)%nat ->
      fcn_procs fn !! fcn_j fn = Some (fcn_plock fn) ->
      fcn_dq fn = DfracOwn (1/4) ->
      sysc_park_extra γtk -∗
      is_lock γw wait_lock_addr "wait_lock"%string wait_res_at -∗
      is_ftable γft γf -∗
      procs_inv (fcn_procs fn) -∗
      disk_geom (fsc_disk) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) -∗
      first_done -∗
      (* the world a child's park needs, copied in -- see [ProofSyscall]'s
         [syscall_env] *)
      park_world (fcn_procs fn) -∗
      (* ...and THE PARK TOKEN ([ParkCap.park_token]): the park itself, as
         the resource a process hands its children.  Supplied at the
         resume, by forkret, which holds it outright. *)
      park_token (fcn_procs fn) -∗
      syscall_env γf (proc_addr (fcn_j fn)) fn.

  (* ...and read back out, for fork's sake *)
  Parameter syscall_env_world :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
      (γf : gname) (pj : mword 64) (fn : fclose_names),
      syscall_env γf pj fn -∗ park_world (fcn_procs fn).
  Parameter syscall_env_token :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{XI : CurCtx}
      (γf : gname) (pj : mword 64) (fn : fclose_names),
      syscall_env γf pj fn -∗ park_token (fcn_procs fn).

  Parameter wp_syscall_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (fn : fclose_names)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (lks : gset string),
      wp_syscall_sconf_body (syscall_env) γf γs j γl fn ip dqi m av pid U sts lks.
End SYSCALL.
