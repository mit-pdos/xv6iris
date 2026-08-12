(* UsertrapRes.v -- [usertrap_res] DEFINED: the kernel-side bundle
   [SpecUsertrap.v] abstracts.  Definitional layer only -- Spec files and
   below, never a whole-function proof -- so the phases of ProofUsertrap can
   each open it without depending on one another.

   [SpecUsertrap.v]'s boundary is "machine state in, machine state out, plus
   [R pt ksp]".  This file says what R is.  It splits three ways:

     [ut_trap]  -- the TRAP-SIDE pieces: everything [IntrDefs.sie_cap] and
                   [IntrDefs.sconf] need that is not the mstatus cell the
                   boundary hands over raw, the per-cpu bundle, and the four
                   loose ghost fractions the excursion through user mode
                   parks (see below).  This is what Phase A assembles.
     [ut_env]   -- the UNION OF THE FIVE CONES' environments (syscall,
                   devintr, vmfault, printk-general, kexit), which usertrap
                   only ever hands over.  Most of it is [syscall_env]'s union
                   already -- kexit's list IS sys_exit's -- so the real
                   content is what syscall does not need: devintr's device
                   caps, vmfault's kalloc side, and printk-general's pr lock.
     [ut_res]   -- the two above, existentially closed over every ghost name
                   and over the process record, keyed on (pt, ksp) because
                   those are the only two the TRAMPOLINE knows.

   WHY THE GHOST FRACTIONS ARE LOOSE HERE.  [sie_gname] is split 1/2 (in
   [sconf]) + 1/4 (in [intr_res]) + 1/8 ([sie_arm]) + 1/8 ([intr_count]).
   At usertrap's entry there IS no [intr_res] -- stvec points at the
   trampoline, no kernel handler is installed -- so that quarter is dangling,
   which is prepare_return's safety argument arriving intact.  And [sconf]
   cannot survive the [sret] either (it ties the SIE half to the LIVE
   mstatus, and the sret sets SIE := SPIE = 1 in user mode), so its half is
   loose too, at 'b"0" -- the value it had when prepare_return left and the
   value the trap restores by clearing SIE.  Same for the sret mirror: R
   holds BOTH halves, which is what makes the pair UPDATABLE across the sret
   that changes SPP/SPIE.  So the whole excursion moves no ghost, and the
   only fraction still bundled is [intr_count]'s, inside [cpu_own].

   THE STACK BUDGET is inside R rather than on the boundary for the same
   reason [av] is: the trampoline has no business knowing usertrap's frame
   depth.  [ut_res] carries [K_usertrap <= av] as a pure conjunct. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp.
Require Import SmodeCore.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import StackOwn.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KallocInv KvmSpec.
Require Import IcacheEscrow IrefSlots InodeRegion.
Require Import WaitInv.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import UserPtTree.
Require Import SpecPanic.
Require Import SpecProcinit.
Require Import SpecFileclose.
Require Import SpecDevintr.
Require Import SpecPrintkGen.
Require Import SpecSyscall.
Require Import SpecKexit.
Require Import SpecUsertrap.   (* USERTRAP_RES -- the fit is checked at the foot *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

(* usertrap's own 32-byte frame is 4 slots; below it the deepest callee is
   syscall (whose own deepest table entry is sys_exit over kexit).  Written
   as an expression for the reason SpecSyscall.v writes K_syscall as one: a
   change to kexit's budget must not silently leave this one behind.  The
   others are all smaller and subsumed -- devintr 40, vmfault 38,
   printk-general 38, yield 20, killed/setkilled 14, prepare_return 12,
   myproc 10, and kexit itself 74 (which syscall's 82 already covers). *)
Definition K_usertrap : nat := (4 + K_syscall)%nat.

Section UsertrapRes.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* THE TRAP SIDE.  What Phase A turns into [sie_cap_gpr] + [cpu_own] +   *)
  (* [trap_csrs] once the boundary's raw cells are added to it.            *)
  (* ------------------------------------------------------------------- *)
  (* [ksp] is the kernel stack TOP, which is what uservec loaded into sp
     out of the trapframe's kernel_sp word -- so [stack_own ksp av] is
     exactly [sie_cap]'s carve at [m !!! sp = ksp], which is the boundary's
     own premise.  [trap_res false = 0], so no reserve is owed: the disabled
     index is not holding an enabled arm's window. *)
  Definition ut_stack (ksp : mword 64) (av : nat) : iProp Σ :=
    stack_own ksp (trap_res false + av)%nat.

  (* [sconf] MINUS the mstatus cell, as its own CLOSER rather than as a
     restatement of the bundle's internals: [sconf_at]'s second conjunct is
     precisely "the rest of sconf", and re-spelling hw_config / minstret /
     the mie / menvcfg pins here would be a second place for them to drift.
     Phase A builds [sconf_msown ms_v] out of the boundary's mstatus cell and
     the two loose halves below, then applies this. *)
  Definition ut_sconf_closer : iProp Σ :=
    (∀ ms' : mword 64, sconf_msown ms' -∗ sconf)%I.

  (* THE FOUR LOOSE GHOSTS -- see the header.  Values are PINNED, not
     existential: [usertrap_entry_ms] pins SPP = 0 / SPIE = 1 / SIE = 0, and
     an existential here would only have to be identified with those pins
     again at the first agreement. *)
  Definition ut_ghosts : iProp Σ :=
    (ghost_var sie_gname (1/2) ('b"0" : mword 1) ∗
     ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"1" : mword 1) ∗
     sret_bits ('b"0" : mword 1) ('b"1" : mword 1))%I.

  Definition ut_trap (pj : mword 64) (ksp : mword 64) (av : nat)
      (C : iProp Σ) : iProp Σ :=
    (ut_stack ksp av ∗
     (* the translation slot, in its KPT arm: THE KERNEL PAGE TABLE, on the
        SHARED tier ([KptShare.tlb_res_pt] inside), which is the whole point
        of SpecUsertrap.v's restatement *)
     strans_inv ∗
     sie_arm false pj ∗
     strans_bit strans_bit_kpt ∗
     ut_sconf_closer ∗
     ut_ghosts ∗
     cpu_own 0%nat false pj C false ∗
     (* the running claim.  It is what [SpecYield] / [SpecKexit] want as
        [cpu_claim_ext false pj], and the trap is where it comes from. *)
     cpu_claim pj ∗
     (* the handler the [csrw stvec] at +0x1e installs -- persistent, and the
        one thing in this bundle that is about code rather than state *)
     intr_handler_spec (mword_of_int KernelSyms.kernelvec))%I.

  (* ------------------------------------------------------------------- *)
  (* THE FIVE CONES' ENVIRONMENTS.  usertrap hands these over and, except  *)
  (* on the kexit paths, takes them back; nothing here is read by usertrap *)
  (* itself.  The parameter list is long for the reason SpecKexit.v's is,  *)
  (* and every name is existentially closed one definition down.          *)
  (* ------------------------------------------------------------------- *)
  (* WHAT THE NAMES ARE SHARED BY -- this is the content of the union, and
     the reason it is one bundle rather than five:
       [γu] (uart) is devintr's uartintr, printk-general's console, and
             kexit's [dev_inv];
       [γv] (disk) and [γk] (the virtio lock) are devintr's disk interrupt
             and kexit's begin_op/end_op cone;
       [γs]  is the proc array, shared by killed / setkilled / yield /
             devintr's tick_keeper / kexit;
       [γkl]/[γka] are kexit's kalloc pieces AND vmfault's [kalloc_env];
       [γf]  is the open-file table, shared by syscall and kexit.
     Getting those identifications right is what makes the bundle coherent;
     five independently-named piles would be satisfiable by nobody. *)
  Definition ut_env
      (Rsys : gname -> mword 64 -> iProp Σ)
      (γft γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γv : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (γtx γtk : gname)                                  (* tx lock, ticks *)
      (γpr : gname)                                      (* the pr lock    *)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (dqi : dfrac)
      (γkl : gname) (γka : gname * gname)
      (γi : gname) (cn : ic_names) (γtl : gname)
      (bmapstart inodestart : Z) (nib : nat) (size : Z)
      (dqb dqs : dfrac) (us : gset Z)
      (fn : fclose_names)
      (ks : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
    let pj := proc_addr j in
    (* ---- persistent, so free to carry ---- *)
    (procs_inv γs ∗
     panic_wp_any ∗
     kernel_data ∗
     is_kstack pj ks ∗
     devintr_caps γu γv γtx γk γtk γs pd pav pu ∗
     printk_env γpr γu γv ∗
     is_lock γw wait_lock_addr "wait_lock"%string wait_res ∗
     is_ftable γft γf ∗
     is_lock γkl (mword_of_int KernelSyms.kmem) "kmem"%string
       (kmem_res γka (mword_of_int (KernelSyms.kmem + 24))) ∗
     is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) ∗
     bio_ctx bn (fs_view γfs γv dev cov) ∗
     log_ctx γ bn γfs cov logstart dev ∗
     fs_crash_seam cov logstart ∗
     gen_cert ∗
     dev_inv γu γv ∗
     disk_geom γv pd pav pu ∗
     (* ---- exclusive ---- *)
     kalloc_avail γka None ∗
     bslots bn 3 ∗
     fileclose_ic_env fn ∗
     fileclose_bm fn us ∗
     (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip ∗
     fd_slots FDSPARE ∗
     iref_slots IREFSPARE ∗
     (* THE PROCESS BLOCK.  The one owner of the user page table and of the
        trapframe page (at the VA tier) -- which is why SpecUsertrap.v's
        boundary hands over neither. *)
     proc_priv γf pj pid V ∗
     (* everything the twenty-two syscall table entries consume, abstractly *)
     Rsys γf pj)%I.

  (* ------------------------------------------------------------------- *)
  (* [usertrap_res] itself.                                              *)
  (* ------------------------------------------------------------------- *)
  Definition ut_res (Rsys : gname -> mword 64 -> iProp Σ)
      (pt : uptd) (ksp : mword 64) : iProp Σ :=
    (∃ (γft γf γw : gname) (γs : list gname) (j : nat) (γl : gname)
       (γu : uart_names) (γv : disk_names) (γk : gname)
       (pd pav pu : mword 64) (γtx γtk γpr : gname)
       (bn : bio_names) (γ : log_names) (γfs : fs_names)
       (cov : gset Z) (logstart : Z) (dev : mword 32)
       (ip : mword 64) (dqi : dfrac)
       (γkl : gname) (γka : gname * gname)
       (γi : gname) (cn : ic_names) (γtl : gname)
       (bmapstart inodestart : Z) (nib : nat) (size : Z)
       (dqb dqs : dfrac) (us : gset Z) (fn : fclose_names)
       (ks : mword 64) (pid : mword 32) (V : pprivate) (av : nat) (C : iProp Σ),
       (* THE PROCESS RUNNING IS THE ONE WHOSE TABLE THE TRAMPOLINE PARKED.
          This equation is the whole reason R is keyed on [pt]: it is what
          lets userret install [MAKE_SATP(p->pagetable)] and know it is the
          table uservec came out of. *)
       ⌜ pv_upt V = pt ⌝ ∗
       (* ...and the stack the trapframe's kernel_sp word named *)
       ⌜ add_vec ks (mword_of_int 4096) = ksp ⌝ ∗
       ⌜ (j < NPROC)%nat ⌝ ∗
       ⌜ γs !! j = Some γl ⌝ ∗
       ⌜ length γs = NPROC ⌝ ∗
       ⌜ (K_usertrap <= av)%nat ⌝ ∗
       ⌜ log_geom_ok cov logstart ⌝ ∗
       (* fileclose's environment index is not a degree of freedom: it is
          kexit's own ghosts, bundled the way fileclose wants them.  One
          equation rather than fifteen coherence conjuncts, exactly as
          SpecKexit.v takes it. *)
       ⌜ fn = MkFCloseNames γs j γl γkl γka γu γv γk pd pav pu bn γ γfs
                cov logstart dev pid (DfracOwn (1/4))
                γi cn γtl bmapstart inodestart nib size dqb dqs ⌝ ∗
       ut_trap (proc_addr j) ksp av C ∗
       ut_env Rsys γft γf γw γs j γl γu γv γk pd pav pu γtx γtk γpr
              bn γ γfs cov logstart dev ip dqi γkl γka
              γi cn γtl bmapstart inodestart nib size dqb dqs us fn
              ks pid V)%I.

End UsertrapRes.

(* ---------------------------------------------------------------------- *)
(* THE FIT, CHECKED HERE.                                                  *)
(*                                                                         *)
(* [SpecUsertrap.USERTRAP] declares [usertrap_res] as a PARAMETER, so its   *)
(* type has to be the one its instantiation has -- and the instantiation's  *)
(* instance list is not the boundary's, it is the union of the five cones'. *)
(* Nothing checks that until ProofUsertrap seals the module, which is a     *)
(* long way from here and a bad place to discover a missing class.  This    *)
(* functor is that check and nothing else: its one definition is written    *)
(* with the module type's binder list VERBATIM, so it fails to compile the  *)
(* moment [ut_res] needs a class [USERTRAP] does not offer (or offers one   *)
(* it does not need, which is just as worth knowing).                      *)
(*                                                                         *)
(* [syscall_env] is why it is a functor: that one member of the union is    *)
(* itself still abstract (SpecSyscall's contract is ASSUMED), so the        *)
(* definition can only be written under a SYSCALL.                         *)
(* ---------------------------------------------------------------------- *)
Module UtResFits (SY : SYSCALL) <: USERTRAP_RES.

  Definition usertrap_res
      `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
        !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
        !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res SY.syscall_env.

End UtResFits.
