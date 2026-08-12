(* SpecUsertrap.v -- the public interface of usertrap() (trap.c), stated
   ahead of its proof.  Everything the five cones below it consume is the
   ABSTRACT per-process predicate [usertrap_res] of the module type, which
   the proof will define concretely -- consumers thread it opaquely, so
   refining it does not churn the boundary.

     uint64 usertrap(void)   @ KernelSyms.usertrap, 262 bytes / 90 instrs

   ==== THIS CONTRACT IS IN THE KERNEL TIER, NOT THE TRAMPOLINE'S ========

   The first statement of this file (10892e92) read the boundary off the two
   trampoline halves: it took [tlb_inv_pt kroot], the parked user table, the
   36 trapframe words at the PHYSICAL tier, and [user_cfg].  That is uservec's
   postcondition verbatim, and it cannot be usertrap's precondition, because
   every function usertrap CALLS describes the same objects one tier up and
   the two descriptions are not merely different -- together they are
   UNSATISFIABLE.  Three collisions, one shape (see
   claude-notes/projects/usertrap.md for the long form):

   * THE KERNEL PAGE TABLE.  [tlb_inv_pt kroot] owns [ptree_own 2 1] of the
     kernel tree; the kernel cone reaches the same tree through
     [IntrDefs.sie_cap]'s [strans_inv], whose KPT arm is
     [KptShare.tlb_res_pt], which carries the INVARIANT [kpt_inv root] that
     holds it.  Hold both and one [iInv kptN] gives two exclusive owners of
     one tree, i.e. [False] -- and every leaf's [sr_absorb] opens [kptN], so
     the interior would go through BY ABSURDITY.  usertrap never writes satp
     (only the trampoline halves do), so it has no business owning a tree:
     the kernel table reaches it the way it reaches every other kernel
     function, inside [usertrap_res].  The exclusive/shared seam belongs to
     uservec/userret, which is the only code that needs exclusivity, and
     closing it is completed/kpt-share.md's named follow-up.
   * THE TRAPFRAME PAGE.  [ProcInv.proc_priv] -- which every callee below
     takes, and which usertrap itself needs for [p->trapframe->epc] -- owns
     that page as [tf_page] at the VA tier.  So the words are NOT in this
     contract; the physical<->VA crossing belongs on the trampoline side,
     where the mapping is in scope.
   * [user_cfg]'s mie/mideleg/menvcfg cells ARE [sconf]'s cells, so they ride
     inside [usertrap_res] too.  The one config cell that stays here is the
     one usertrap WRITES: [stvec].

   ==== THE ENTRY PAYLOAD IS prepare_return'S EXIT PAYLOAD ===============

   What is left once those three are out is exactly the state
   [SpecPrepareReturn.v]'s postcondition hands over, with the trap's own
   writes applied -- which is the check that this boundary is the right one:

     stvec at TRAMPOLINE with NO [intr_res] (no kernel handler installed);
     the [sie_gname] 1/4 that lived in [intr_res] still DANGLING; the KPT
     receipt loose; the sret mirror at (SPP = User, SPIE = 1) -- prepare_return
     wrote that pair, the [sret] set SIE := SPIE = 1, and the trap set
     SPP := User, SPIE := SIE = 1, so it comes back UNCHANGED; mstatus with
     SIE = 0 again (prepare_return's [intr_off] cleared it, the sret set it,
     the trap cleared it); scause/stval/sepc at whatever the trap wrote.

   EVERY GHOST FRACTION IS WHERE prepare_return LEFT IT, and the two mstatus
   bits the mirror tracks return to the same values -- so the excursion
   through userret / user mode / uservec moves no ghost at all and
   [usertrap_res] simply carries the mirror halves across it.  That is why
   this contract mentions no ghost variable of its own.

   AND usertrap'S FIRST ACT CLOSES THE LOOP: the [csrw stvec, kernelvec] at
   +0x1e folds the dangling quarter + the stvec cell + [intr_handler_spec
   kernelvec] into a real [IntrDefs.intr_res], hence [trap_csrs] -- precisely
   the [intr_res] prepare_return's [csrci] will unfold again on the way out.
   The C comment ("send interrupts and exceptions to kerneltrap(), since
   we're now in the kernel") IS that fold, and the order is forced: before
   +0x1e this hart has no kernel handler, so nothing there may enable
   interrupts.

   ==== THE POST CROSSES ================================================

   usertrap PARKS -- yield on the timer arm, and every sleeping syscall
   through [SpecSyscall]'s own [wp_next true pj] -- so it may return on a
   different hart and the post has to be a crossing.  The consequence is on
   the CALLER (see eb-generic-sweep.md on [wp_next]'s polarity): the trap-loop
   composition must build its continuation hart-generically.

   ==== WHAT IS STILL OWED (the trampoline dovetail) =====================

   This statement moves the trampoline seam rather than closing it: composing
   uservec -> usertrap -> userret (the Loeb theorem that discharges
   [UserExec.stvec_handler_wp]) owes three conversions -- the kernel table
   exclusive<->shared, the trapframe page physical<->VA, and
   [user_cfg] <-> [sconf]'s cells (which needs [uc_mie C = MIE_S]; sconf pins
   mie and [ucfg] only constrains [mie & ~mideleg = 0]).  All three are
   trampoline-side work and all three are tracked in
   claude-notes/projects/usertrap.md.  [usertrap_ret_ms] and [satp_rooted]
   stay here: they are the shared vocabulary that seam will be stated in, and
   SpecPrepareReturn's post already spells [satp_rooted]'s three conjuncts out
   longhand rather than importing it (this file has no [Require]ing consumer
   yet -- the two Specs that name it, name it in prose). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile HartTp WpNext.
Require Import MinstretInv InstrBytes WireInv.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpLock.
Require Import FdSlots.
Require Import FileInvDefs.
(* the classes the module type's [usertrap_res] parameter needs -- see the
   note above [Module Type USERTRAP] at the foot of this file *)
Require Import BioInv.
Require Import DiskPtsto DiskInv.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import KallocInv.
Require Import IrefSlots InodeRegion.
Require Import ProcGeom.
Require Import PtTree.
Require Import TrampPt KptTree UptTree.
Require Import UserPtTree UserExec.
Require Import SpecUserret.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.


(* the mstatus facts usertrap's return guarantees: exactly userret's
   premises (the sret decodes to User and does not trap) plus the FS/VS
   pins the user-mode invariant carries across the sret
   ([userret_to_user_inv], UserKernelBridge.v). *)
Definition usertrap_ret_ms (ms : mword 64) : Prop :=
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_FS ms) ('b"00") = true /\
  eq_vec (_get_Mstatus_VS ms) ('b"00") = true /\
  sret_newpriv ms = User.

(* the satp-value facts both trampoline switches need, shared spec
   vocabulary: [v] is a Sv39, asid-0 satp value rooted at [root]. *)
Definition satp_rooted (v : mword 64) (root : mword 44) : Prop :=
  _get_Satp64_Mode (Mk_Satp64 v) = ('b"1000" : mword 4) /\
  zero_extend' 16 (satp_to_asid (autocast (T := mword) v : mword 64)) = (mword_of_int 0 : mword 16) /\
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) v : mword 64)) = root.

(* WHAT THE TRAP DELIVERED, in the vocabulary the two tiers meet in.

   [trap_mstatus_ok] is the trampoline's pin set (UserExec.v: SIE = 0,
   SPP = User, MPRV = MXR = 0, SXL = 64, TVM = TSR = 0) -- what uservec's
   own [csrw satp] / [sfence] gates need.  [sconf_ms_facts] is the kernel
   tier's (IntrDefs.v), which additionally pins the FS/VS/XS extension
   states, SD and a nominal MPP: it is what [IntrDefs.sconf] carries, so
   usertrap cannot assemble the bundle its callees take without it.  The two
   overlap and neither implies the other.

   [SPIE = 1] is the third: it is what the mirror half inside
   [usertrap_res] agrees with ([IntrDefs.sret_tie]), and it is a fact about
   the code rather than an assumption about the user -- userret's [sret] set
   SPIE := 1, so user mode ran with SIE = 1, so the trap copied SIE into
   SPIE.  Nothing user mode can execute changes it. *)
Definition usertrap_entry_ms (ms : mword 64) : Prop :=
  trap_mstatus_ok ms /\
  sconf_ms_facts ms /\
  _get_Mstatus_SPIE ms = ('b"1" : mword 1).

(* The statement, parameterized over the abstract kernel-internal resource
   [R : uptd -> mword 64 -> iProp Σ]: [R pt ksp] is everything usertrap needs
   beyond the machine state above, for the process whose user page table is
   [pt] and whose kernel stack top is [ksp].  The module type instantiates it
   with its own [usertrap_res].

   The key is (pt, ksp) and not the process's ghost names because those are
   the only two the TRAMPOLINE knows: the proof's definition existentially
   packages the rest (the fd-table name, the slot index, the pid, the private
   record [V] with [pv_upt V = pt], the stack budget, the per-cpu frame) --
   see claude-notes/projects/usertrap.md.  [ksp] appears because [sie_cap] is
   keyed on sp, which is what the [m !!! sp = ksp] premise below licenses. *)
Definition usertrap_post `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (R : uptd -> mword 64 -> iProp Σ) (pt : uptd) (ksp : mword 64) (m : regfile) : iProp Σ :=
  let ret_tgt : mword 64 := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  ( ∀ (pt' : uptd) (mf : regfile)
      (ms' usatp uepc sc' stval' : mword 64),
    (* THE TRAPFRAME PAGE IS THE ONE THING THAT CANNOT MOVE, and the ROOT IS
       NOT.  The first draft promised [ud_root pt' = ud_root pt] as well, on
       the strength of the vmfault arm (which only inserts leaves).  It is
       FALSE on the syscall arm: exec() replaces the address space wholesale,
       so [SpecSyscall]'s post pins [ud_tfp] and nothing else, and no proof of
       the stronger conjunct exists.  Nothing wanted it either -- what the
       trampoline needs is that the satp usertrap RETURNS is rooted at the
       table it hands over, which is [satp_rooted usatp (ud_root pt')]
       below. *)
    ⌜ud_tfp pt' = ud_tfp pt⌝ -∗
    (* the pure facts the trampoline halves need about it, which the process
       block's [proc_pt_at] carries *)
    ⌜udata_cov (ud_um pt') (ud_data pt')⌝ -∗
    ⌜upt_acc_wf (ud_um pt')⌝ -∗
    ⌜upt_map_wf (ud_um pt')⌝ -∗
    (* sret-ready, and still a legal S-mode configuration *)
    ⌜usertrap_ret_ms ms'⌝ -∗
    ⌜sconf_ms_facts ms'⌝ -∗
    ⌜callee_saved m mf⌝ -∗
    ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word⌝ -∗
    (* the return value: MAKE_SATP(p->pagetable) *)
    ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = usatp⌝ -∗
    ⌜satp_rooted usatp (ud_root pt')⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms' -∗
    scause ↦ᵣ sc' -∗
    stval ↦ᵣ stval' -∗
    (* the user pc to resume, which prepare_return's [csrw sepc] wrote *)
    sepc ↦ᵣ uepc -∗
    (* THE VECTOR IS BACK AT uservec, and still owned outright: after
       prepare_return this hart has no kernel handler installed, which is
       what forbids re-enabling interrupts before the sret. *)
    stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
    pc_is ret_tgt -∗
    gpr_file mf -∗
    R pt' ksp -∗
    WP (Loop : expr riscv_lang)).

Definition wp_usertrap_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (R : uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.usertrap in
  let pj := proc_addr j in
  (* the trap delivered a legal S-mode configuration -- see above *)
  usertrap_entry_ms ms_v ->
  (j < NPROC)%nat ->
  (* calling convention: sp = the process's kernel stack top (uservec loaded
     it out of the trapframe's kernel_sp), tp = this hart's id (myproc),
     ra = uva 0x9c, i.e. userret -- usertrap RETURNS INTO userret. *)
  m !!! Regidx (mword_of_int 2 : mword 5) = ksp ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  kernel_text -∗ pc_is pcE -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  cur_privilege ↦ᵣ Supervisor -∗
  mstatus ↦ᵣ ms_v -∗
  scause ↦ᵣ sc_v -∗
  stval ↦ᵣ stval_v -∗
  sepc ↦ᵣ sepc_v -∗
  (* NO KERNEL HANDLER IS INSTALLED: the cell is owned raw, at the
     trampoline, and the [csrw stvec] at +0x1e is what turns it into an
     [intr_res].  The dangling SIE quarter that pairs with it rides inside
     [R] -- see the header. *)
  stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
  gpr_file m -∗
  (* everything kernel-side, abstractly *)
  R pt ksp -∗
  (* THE CROSSING: usertrap parks (yield, and every sleeping syscall), so it
     may return on a different hart. *)
  wp_next true pj (fun (CID' : CpuId) => usertrap_post (CID := CID') R pt ksp m) -∗
  WP (Loop : expr riscv_lang).

(* THE MODULE TYPE'S INSTANCE LIST IS THE UNION OF THE FIVE CONES', NOT THE
   BOUNDARY'S.  [wp_usertrap_body] above needs almost none of these -- its
   own statement is register cells, [wp_next] and the abstract [R] -- but
   [usertrap_res] is a PARAMETER, so its type has to be the one its
   instantiation has, and [UsertrapRes.ut_res] is the union of syscall's /
   devintr's / vmfault's / printk-general's / kexit's environments.  It is
   SpecKexit.v's list verbatim (kexit is the deepest of the five, and the
   other four add no class of their own).  A consumer that only wants the
   boundary pays nothing for them: they are Sigma constraints, discharged by
   whatever Sigma the whole-system composition is built over. *)
(* SPLIT OUT so the definition can be checked against it WHERE IT IS WRITTEN.
   [UsertrapRes.v] defines the bundle long before ProofUsertrap can seal
   USERTRAP (its [wp_usertrap] is the whole proof), and a parameter's instance
   list that does not admit its instantiation is a thing to discover there
   rather than at the seal.  [UsertrapRes.UtResFits] is a
   [<: USERTRAP_RES], which makes that mechanical. *)
Module Type USERTRAP_RES.
  (* the kernel-internal resources usertrap consumes, for the process whose
     user page table is [pt] and whose kernel stack top is [ksp]: defined
     concretely by the proof (as [UsertrapRes.ut_res SY.syscall_env], the
     functor's syscall environment being the one piece that is itself still
     abstract); threaded opaquely by consumers. *)
  Parameter usertrap_res :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId},
      uptd -> mword 64 -> iProp Σ.
End USERTRAP_RES.

Module Type USERTRAP.
  Include USERTRAP_RES.
  Parameter wp_usertrap :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (pt : uptd) (j : nat)
      (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64),
      wp_usertrap_body usertrap_res pt j m ms_v sc_v stval_v sepc_v ksp.
End USERTRAP.
