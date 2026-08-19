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
Require Import MinstretInv.
Require Import InstrBytes.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpLock.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import ProcPtOwn.   (* [proc_pt] / [ud_norm] -- the bare residue's vocabulary *)
(* the classes the module type's [usertrap_res] parameter needs -- see the
   note above [Module Type USERTRAP] at the foot of this file *)
Require Import BioDefs.
Require Import DiskPtsto.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import KallocInv.
Require Import IrefSlots InodeRegion.
Require Import ProcGeom.
Require Import TrampPt UptTree.
Require Import KptShare.   (* [tlb_res_pt] -- the translation slot the parked residue drops *)
Require Import UserPtTree UserExec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import TimerCap.   (* [sstc_enabled]: the residue's mcounteren pin *)
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
    (R : uptd -> mword 64 -> iProp Σ) (pt : uptd) (ksp : mword 64) (m : regfile)
    (mie_v menvcfg0 : mword 64) : iProp Σ :=
  let ret_tgt : mword 64 := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  ( ∀ (pt' : uptd) (mf : regfile)
      (ms' usatp uepc sc' stval' mdv0 : mword 64),
    (* [mideleg]'s VALUE is not pinned to whatever usertrap was handed at
       entry -- unlike [mie_v]/[menvcfg0] (each a unique architectural
       constant, so their exit value provably equals the entry one),
       [mideleg] is a genuine existential inside [IntrDefs.sconf], and
       nothing tracks "the same witness" across usertrap's internal
       instruction-step lemmas (which carry [sconf] opaquely, never
       re-destructuring it) -- so the caller only gets a FRESH value
       satisfying the same mask, discovered at the exit. *)
    ⌜and_vec mie_v (not_vec mdv0) = zeros' 64⌝ -∗
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
       block's [proc_pt_at] carries -- and there are TWO of them, not three.
       [udata_cov (ud_um pt') (ud_data pt')] used to be here and is NOT
       provable: [ProcPtOwn] deliberately retired the field-to-field coupling
       between [ud_um] and [ud_data] ("the footprint derived from [um]", its
       §1), so [proc_pt] says nothing about [ud_data]; and on the syscall arm
       the descriptor is whatever the table entry left, of which
       [SpecSyscall]'s post pins only [ud_tfp].  Nor is it usertrap's fact to
       state: the trampoline needs it beside [udata_own (ud_data pt')], and
       the conversion that BUILDS that resource -- the page-footprint side of
       the dovetail, conversion 2 -- derives the footprint from [ud_um] and so
       establishes the coverage by construction ([ProcPtOwn.ud_pas_cov]).
       Asking for it here would be asking usertrap to prove a property of a
       resource it never holds. *)
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
    (* the three [sconf] cells usertrap borrowed for its own call and hands
       back UNCHANGED (usertrap never writes them) -- see [wp_usertrap_body]'s
       matching entry premise. *)
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    (* [hw_config]/[minstret_inv], AT THE RESUMING HART.  Both are persistent
       and ride at the head of [sconf] -- [wp_usertrap_body]'s own entry
       premise hands them in as a free borrow (see its comment) on the
       strength that "persistent costs the caller nothing", but that is only
       true AT ONE HART: usertrap may cross to a different hart before it
       returns (the whole reason [R] above is hart-indexed), and a caller's
       pre-crossing copy is a DIFFERENT resource from the post-crossing one
       (same shape, different hart index, indistinguishable on the page).
       The proof already has the resuming hart's own copies on hand at this
       exact point -- [ut_ret2] unpacks them straight out of [sconf] just
       like [ut_dup_hw] does -- so exposing them here costs nothing new to
       prove, only to thread through. *)
    hw_config -∗
    minstret_inv -∗
    R pt' ksp -∗
    WP (Loop : expr riscv_lang)).

(* [R] IS A HART-INDEXED FAMILY, AND IT HAS TO BE.  usertrap is handed the
   kernel-side bundle at the hart the TRAP came in on and gives it back at the
   hart it RESUMES on -- the two are different whenever the function parks
   (yield, and every sleeping syscall through [SpecSyscall]'s own crossing),
   and everything inside [UsertrapRes.ut_res] except the stack is per-hart
   ([sie_arm], [cpu_own], [cpu_claim], the [sconf] closer's register cells,
   the SIE ghost).  Written as a plain [uptd -> mword 64 -> iProp Σ] the
   post's [R] is pinned to the ENTRY hart, and no proof of it exists: the tail
   rebuilds the bundle out of what prepare_return handed back, which is at the
   resuming hart ([ProofUsertrapTail.ut_ret2], whose whole reason for being
   its own section is that hart).  So [R] takes the hart: [R CID] going in,
   [R CID'] coming out, where [CID'] is the crossing's own binder.  The
   module type below supplies [fun h => usertrap_res (CID := h)]. *)
Definition wp_usertrap_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
    (R : CpuId -> uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
    (mie_v mdv0 menvcfg0 : mword 64) :=
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
  (* the three [sconf] pins usertrap needs of the CSRs it borrows -- see the
     matching conjunct of [mie]/[mideleg]/[menvcfg] below *)
  mie_v = MIE_S ->
  and_vec mie_v (not_vec mdv0) = zeros' 64 ->
  menvcfg0 = MENVCFG_S ->
  kernel_text -∗ pc_is pcE -∗
  (* [hw_config]/[minstret_inv] are persistent, so borrowing a copy for the
     duration of the call costs the caller nothing -- unlike [mie]/
     [mideleg]/[menvcfg] below, which usertrap needs at FULL ownership
     (it assembles [IntrDefs.sconf], hence [sie_cap_gpr], out of them for its
     own internal kernel-tier step lemmas) and must therefore borrow and
     give back explicitly, exactly like every other loose cell here.
     [usertrap_post] hands a copy back too, in spite of that -- NOT because
     the call could otherwise lose them (a persistent proposition is never
     consumed), but because usertrap may CROSS HARTS before it returns, and
     the entry copy is a resource AT THE ENTRY HART, silent on any other
     one.  A caller that needs [hw_config] again after the call (uservec's
     tail does, to reach userret) needs it AT THE RESUMING HART, which only
     [usertrap_post] itself is in a position to hand over. *)
  hw_config -∗ minstret_inv -∗
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
  mie ↦ᵣ mie_v -∗
  mideleg ↦ᵣ mdv0 -∗
  menvcfg ↦ᵣ menvcfg0 -∗
  gpr_file m -∗
  (* everything kernel-side, abstractly, AT THE ENTRY HART *)
  R CID pt ksp -∗
  (* THE CROSSING: usertrap parks (yield, and every sleeping syscall), so it
     may return on a different hart -- and the bundle comes back at THAT
     hart, which is why [R] is a family (see the note above). *)
  wp_next true pj (fun (CID' : CpuId) =>
    usertrap_post (CID := CID') (R CID') pt ksp m mie_v menvcfg0) -∗
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
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId},
      uptd -> mword 64 -> iProp Σ.

  (* THE TRAPFRAME BORROW.  [usertrap_res] owns the trapframe page at the
     VA tier internally (via [ProcInv.proc_priv]/[tf_page]) -- it is the
     ONE OWNER, per [UsertrapRes.ut_own]'s own header comment -- but uservec
     ALSO owns the same page's bytes, at the physical tier, as [tf_pa]
     cells (SpecUserret.v's vocabulary), for the whole 44-instruction save/
     restore walk.  Rather than have [usertrap_res] itself borrow-and-return
     the page (which would ripple [wp_usertrap_body]'s type and, through it,
     ONLY every internal usertrap block that already threads [usertrap_res]
     opaquely -- no external file), this accessor lets a HOLDER of
     [usertrap_res] pull [tf_page] out for a moment and hand back a
     (possibly different) one to reseal it -- exactly the shape uservec's
     tail needs: open, convert its own [tf_pa] cells in, close. Concrete
     proof: [UsertrapRes.usertrap_res_tf_open], via [proc_priv_split] +
     [ut_own_priv]. *)
  (* THE PARKED FORM: [usertrap_res] WITHOUT THE TRANSLATION SLOT.
     [usertrap_res] owns [satp] (its internal [strans_inv] sits in the KPT
     arm, i.e. [KptShare.tlb_res_pt]) -- right for the state usertrap RUNS
     in, and impossible for anything parked across user execution, where
     [UptTree.utlb_inv_pt] owns [satp] at the USER root instead.  Holding
     both is contradictory, so a consumer that took [usertrap_res] beside a
     user-mode table would be vacuous rather than wrong-looking.  uservec
     therefore takes the PARKED residue, and its exit switch's own
     [tlb_res_pt] is exactly what completes it; userret's entry switch takes
     that back out.  Concrete: [UsertrapRes.ut_res_parked]. *)
  Parameter usertrap_res_parked :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId},
      uptd -> mword 64 -> iProp Σ.

  (* uservec's move: the switch just installed the kernel table, so the
     residue can be completed into the state usertrap consumes. *)
  Parameter usertrap_res_tlb_close :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44),
      usertrap_res_parked pt ksp -∗ tlb_res_pt kroot -∗ usertrap_res pt ksp.

  (* userret's move: its entry switch is about to install the USER table, so
     it needs the kernel one back out first.  The root is existential --
     nothing outside pins which table the slot holds, and userret is
     parametric in it. *)
  Parameter usertrap_res_tlb_open :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res pt ksp -∗
      ∃ kroot : mword 44, tlb_res_pt kroot ∗ usertrap_res_parked pt ksp.

  (* THE BARE FORM: the parked residue WITHOUT THE USER ADDRESS SPACE.
     [usertrap_res_parked] fixed ONE of four overlaps with the user tier
     (satp).  The other three are all [proc_pt], which rides inside
     [usertrap_res] via [ProcInv.proc_priv]: the user page-table TREE
     ([ptree_own 2 (DfracOwn 1)]) and the user DATA PAGES, which
     [UserPtTree.user_pt_inv] carries too.  So the parked form is still
     unsatisfiable beside a user-mode frame, and it is the BARE form that
     parks across user execution.  Concrete: [UsertrapRes.ut_res_bare].

     What the bare form still HAS is everything the kernel genuinely owns
     while user code runs -- including [p->pagetable]/[p->trapframe] (cells
     that merely name the table) and the trapframe page itself (physical
     tier, U = 0 leaf, unreachable from user mode).  That is why
     [usertrap_res_tf_open] below is stated on THIS form: the trapframe is
     available in exactly the window the address space is not. *)
  Parameter usertrap_res_bare :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId},
      uptd -> mword 64 -> iProp Σ.

  (* uservec's move, one tier under [_tlb_close]: its exit switch converted
     the user table back to a [pt_frame], and the pages never moved, so
     [ProcPtOwn.user_pt_inv_open] rebuilds [proc_pt] and this reseals it
     into the residue. *)
  Parameter usertrap_res_pt_close :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_bare pt ksp -∗ proc_pt pt -∗ usertrap_res_parked pt ksp.

  (* userret's move: the address space is about to be installed again, so
     it comes back out, to be split into the tree the entry switch consumes
     and the pages [ProcPtOwn.user_pt_inv_close] hands the user tier. *)
  Parameter usertrap_res_pt_open :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_parked pt ksp -∗ proc_pt pt ∗ usertrap_res_bare pt ksp.

  (* THE FOOTPRINT RENORMALISATION.  The bare residue reads its descriptor
     only through [ud_root]/[ud_tfp]/[ud_um] -- [proc_pt], the one conjunct
     whose user-side partner names [ud_data], is what it just gave up -- so
     it may be re-keyed on [ProcPtOwn.ud_norm].  That is what lets the trap
     loop hand the user tier a descriptor whose [udata_cov] side condition
     holds by construction, which is the fact this file's [usertrap_post]
     explains it cannot ask usertrap for. *)
  Parameter usertrap_res_bare_norm :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_bare pt ksp -∗ usertrap_res_bare (ud_norm pt) ksp.

  (* THE PER-HART CSRs, borrowed out of the parked residue.  [IntrDefs.
     hart_csrs] -- [sscratch] at an arbitrary value, [medeleg] at
     [MEDELEG_S], the two state-enable pins at zero -- lives in [cpu_priv],
     hence inside the [cpu_own] this residue already carries, because that
     is the bundle a migration re-delivers.  Two consumers, both needing the
     bare form: uservec borrows [sscratch] across its save walk (its own
     [csrw sscratch,a0] at +0x00 writes it and the [csrr] at +0x76 reads it
     back, so a value-agnostic invariant would not serve), and the trap loop
     hands the three pinned cells to [UserExec.user_cfg] for the user phase,
     parking the closer wand in their place.  Concrete:
     [UsertrapRes.ut_res_bare_csrs_open]. *)
  Parameter usertrap_res_csrs_open :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_bare pt ksp -∗
      hart_csrs ∗ (hart_csrs -∗ usertrap_res_bare pt ksp).

  (* THE TIMER CAPABILITY'S mcounteren PIN.  The U tier needs
     [mcounteren ↦ᵣ□] and it cannot come from [hw_config] (timerinit writes
     mcounteren after that bundle is frozen); the residue carries it inside
     [devintr_caps_any]'s [timer_cap], at every hart.  Persistent, so it is
     handed straight back.  Concrete: [UsertrapRes.ut_res_bare_sstc]. *)
  Parameter usertrap_res_sstc :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64),
      usertrap_res_bare pt ksp -∗ sstc_enabled ∗ usertrap_res_bare pt ksp.

  (* ... AND BOTH AT ONCE, which is what uservec needs: its save walk holds
     the trapframe page open across the same stretch its [csrw sscratch,a0] /
     [csrr t0,sscratch] pair holds the [sscratch] cell.  Each single accessor
     consumes the whole sealed residue, so neither composes with the other's
     remainder -- simultaneous borrows of a sealed bundle come out of ONE
     opener.  Concrete: [UsertrapRes.ut_res_bare_tf_csrs_open]. *)
  Parameter usertrap_res_tf_csrs_open :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44),
      (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
      usertrap_res_bare pt ksp -∗
      ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗
        tf_page (ud_tfp pt) ws ∗ hart_csrs ∗
        (∀ ws' : list (mword 64),
           tf_page (ud_tfp pt) ws' -∗ hart_csrs -∗ usertrap_res_bare pt ksp).

  Parameter usertrap_res_tf_open :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44),
      (* THE CROSS-ROUND HISTORICAL FACT, bare and undischarged -- see
         [ProcGeom.tf_kernel_words_ok]'s own header. *)
      (forall ws : list (mword 64), length ws = TFWORDS -> tf_kernel_words_ok kroot ksp ws) ->
      usertrap_res_bare pt ksp -∗
      ∃ ws : list (mword 64), ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗ tf_page (ud_tfp pt) ws ∗
        (∀ ws' : list (mword 64), tf_page (ud_tfp pt) ws' -∗ usertrap_res_bare pt ksp).
End USERTRAP_RES.

Module Type USERTRAP.
  Include USERTRAP_RES.
  Parameter wp_usertrap :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (pt : uptd) (j : nat)
      (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
      (mie_v mdv0 menvcfg0 : mword 64),
      wp_usertrap_body (fun h : CpuId => usertrap_res (CID := h))
        pt j m ms_v sc_v stval_v sepc_v ksp mie_v mdv0 menvcfg0.
End USERTRAP.
