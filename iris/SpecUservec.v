(* SpecUservec.v -- the public interface of uservec (trampoline.S), stated
   independently of its proof.

   uservec is the kernel's stvec handler for traps OUT OF USER MODE: it
   begins executing at virtual address TRAMPOLINE (= stvec's direct base)
   with the USER page table still installed, saves the 31 user registers
   into the TRAPFRAME page (through the user table's trapframe leaf),
   loads the kernel sp / hartid / usertrap pointer / kernel satp from the
   trapframe's kernel words, switches satp to the KERNEL table (the pt2
   window, roles swapped relative to userret), and jalr's to usertrap with
   ra pointing at userret (uva 0x9c).

   THIS SPEC CHAINS THROUGH usertrap AND userret DIRECTLY, the way any
   function-calls-function edge in this project works: uservec's own proof
   depends on USERTRAP's and USERRET's spec modules and invokes their WPs
   at its own call sites (ProofUservec.v becomes a functor over both).

   ==== THE PRECONDITION IS THE *BARE* RESIDUE, AND THAT IS THE POINT ====

   uservec IS THE VIEW CHANGE.  The user address space -- the page-table
   tree, the data pages, and satp/tlb -- is ONE resource that the kernel
   holds parked ([ProcPtOwn.proc_pt], inside [ProcInv.proc_priv], inside
   [usertrap_res]) while the kernel runs, and that
   [UserPtTree.user_pt_inv] holds installed while user code runs.  A spec
   naming BOTH is claiming it twice, so its precondition is unsatisfiable
   and the lemma is vacuous -- green, and applicable by nobody.  An earlier
   draft of this file did exactly that and "proved" the 44-instruction walk
   through it; see claude-notes/projects/uservec.md.

   So this spec takes [SpecUsertrap.usertrap_res_bare pt vksp]: the kernel
   residue with NO address space in it.  The two borrows close in one order
   around the call into usertrap and reopen in the mirror order before
   userret --

     bare --[_pt_close]--> parked --[_tlb_close]--> usertrap_res

   -- and both pieces are produced by the ONE instruction that changes the
   view, the [csrw satp] of the exit switch: it converts the user table
   from [utlb_inv_pt] back to a [pt_frame] and roots satp at the kernel
   table.  The user PAGES do not move at all; [ProcPtOwn.proc_pt_own_udata]
   is the whole of that conversion.

   THE TRAPFRAME PAGE IS NOT PART OF THIS, and that is why the walks work.
   [ProcInv.tf_page] is at the PHYSICAL tier (native [tf_pa]/[↦ₚ₈] cells --
   the SAME tier uservec/userret's own 44/31-instruction walks use, so no
   phys<->mem crossing at this boundary) and its leaf has U = 0, so user
   mode cannot reach it and [user_pt_inv] never claims it.  It stays in the
   BARE residue, available in exactly the window the address space is not,
   which is why [usertrap_res_tf_open] is stated there: the proof opens it
   for the SAVE walk's cells, reseals before calling usertrap, and repeats
   the open/reseal around the call into userret.

   [uservec_post] therefore is NOT userret's own exit shape (which exposes
   raw [tf_pa] cells) -- it is that shape with the trapframe folded back
   into a fresh bare residue and the address space handed back in the USER
   view.  Folding THAT into the user-mode loop (the outer Löb that
   discharges [UserExec.stvec_handler_wp]) is future work, once USER is
   folded in too; the [Rut] it will need is
   [fun p => ∃ ksp, usertrap_res_bare p ksp].

   THE TWO GAPS THIS CONTRACT USED TO TAKE AS PREMISES, AND NO LONGER DOES
   (2026-08-21).  [user_trap_frame]'s pure content used to be only
   [trap_mstatus_ok ms_v], and nothing tied the trapframe's four kernel
   words to a root / [KernelSyms.usertrap] / [cid_word]; so this spec took
   "trap_mstatus_ok -> sconf_ms_facts /\ SPIE = 1" and "every 36-word list
   is tf_kernel_words_ok" as bare premises.  BOTH WERE UNSATISFIABLE (see
   claude-notes/projects/forkret-park.md §4), which made everything above
   uservec vacuous.  Now:

   * [UserExec.trap_mstatus_ok] carries FS/VS/XS/SD/MPP and SPIE = 1 --
     the user tier never writes mstatus, so it preserves from userret's sret
     what [user_mstatus_ok] now records -- and
     [SpecUsertrap.usertrap_entry_ms_of_trap] derives the rest;
   * the residue carries [UsertrapRes.ut_tfk]: the four kernel words are
     [ProcGeom.tf_kernel_words_ok] at an existential root whose [kpt_inv]
     rides beside the fact.  prepare_return establishes it at the hart the
     process resumes on (usertrap's exit and forkret's tail seal it), and
     the openers hand it back -- which is also where the proof gets the
     kernel root it switches to, so this contract names no [kroot]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile WpNext.
Require Import MinstretInv InstrBytes.
Require Import WpGpr.
Require Import KernelText.
Require Import RiscvExtras.
Require Import TrampPt UptTree KptShare UserretDefs.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import MstatusBits.
Require Import ProcGeom.
Require Import ProcInv ProcPtOwn.   (* [proc_pt] / [ud_pas] / [ud_norm] -- the address-space split *)
(* [usertrap_res]'s own signature (SpecUsertrap.v/USERTRAP_RES) is stated
   over these fourteen classes; unqualified [lockG]/[fdslotG]/... below
   only resolve to the CONCRETE classes (rather than each getting silently
   auto-generalized as a fresh, unrelated abstract variable of type
   [gFunctors -> Type] -- the same one-`Require`-isn't-enough trap as
   everywhere else in this project) if their defining modules are directly
   imported here too, not just transitively pulled in via SpecUsertrap. *)
Require Import FdSlots.
Require Import FileInvDefs.
Require Import IrefSlots.
Require Import SpecUsertrap.
Require Import UsertrapRes.  (* [USERTRAP_RES_PARK] -- the residue plus its producer *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* the register file uservec leaves for usertrap (insert order = execution
   order): a0 := TRAPFRAME (the li), t0 := the saved user a0 (csrr
   sscratch, later overwritten), sp := kernel_sp, tp := kernel_hartid,
   t0 := usertrap pointer, t1 := kernel_satp, ra := uva 0x9c (the c.jalr
   link -- usertrap returns straight into userret). *)
Definition uservec_gpr (g : regfile) (vksp vkhart vktr vksat : bv 64) : regfile :=
  <[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]>
  (<[Regidx (mword_of_int 6) := regval_into_reg vksat]>
  (<[Regidx (mword_of_int 5) := regval_into_reg vktr]>
  (<[Regidx (mword_of_int 4) := regval_into_reg vkhart]>
  (<[Regidx (mword_of_int 2) := regval_into_reg vksp]>
  (<[Regidx (mword_of_int 5) := regval_into_reg (g !!! Regidx (mword_of_int 10) : mword 64)]>
  (<[Regidx (mword_of_int 10) := mword_of_int TRAPFRAME]> g)))))).

(* THE CONTINUATION, NAMED for the same reason the old one was: a
   whole-function WP carries its continuation as a spatial hypothesis
   across every instruction step, so a spelled-out ~40-wand type would be
   re-embedded in the proof term at every one of uservec's own steps.
   [Typeclasses Opaque] stops instance search from descending into it; the
   proof unfolds it exactly once, at the very end, after chaining through
   usertrap and userret.  See claude-notes/optimization.md. *)
(* Only [riscvGS]/[sieG]: this never opens [usertrap_res]'s own internals,
   just holds [URes pt' vksp] opaquely -- the other twelve classes
   [usertrap_res] itself needs are for its holder ([Module Type USERVEC]'s
   [wp_uservec_pt], via [Include USERTRAP_RES]) to supply, not for this
   definition to re-demand. *)
Definition uservec_post `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (URes : uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd) (vksp : mword 64) : iProp Σ :=
  ( ∀ (pt' : uptd) (mf : regfile) (ms' usatp uepc sc' stval' mdv0 : mword 64),
    ⌜ud_tfp pt' = ud_tfp pt⌝ -∗
    ⌜upt_map_wf (ud_um pt')⌝ -∗
    ⌜satp_rooted usatp (ud_root pt')⌝ -∗
    (* THE DESCRIPTOR COMES BACK RENORMALISED -- see the entry premise of
       [wp_uservec_pt_body].  Handed over so the next round's entry premise
       is discharged by this round's exit, which is what makes the loop
       closed under it. *)
    ⌜ud_data pt' = ud_pas pt'⌝ -∗
    ⌜proc_pt_wf pt'⌝ -∗
    ⌜and_vec MIE_S (not_vec mdv0) = zeros' 64⌝ -∗
    (* THE EXIT mstatus FACTS, straight off [usertrap_post].  Without them a
       caller holds [mstatus ↦ᵣ sret_ms5 ms'] at a wholly abstract [ms'] and
       cannot re-establish [UserExec.user_mstatus_ok] -- so it cannot rebuild
       [user_inv] for the next round, which is the whole point of the post.
       [usertrap_ret_ms] carries exactly the six pins
       [user_mstatus_ok_sret_ms5] consumes (SXL / MXR / FS / VS / TVM / TSR),
       plus the two the sret itself needs. *)
    ⌜usertrap_ret_ms ms'⌝ -∗
    ⌜upt_acc_wf (ud_um pt')⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ sret_ms5 ms' -∗
    mie ↦ᵣ MIE_S -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    (* THE VECTOR, and it is a ROUND TRIP rather than a parked cell.  [stvec]
       is not free: while the kernel runs it must point at kernelvec to take
       interrupts, so it is owned there by [IntrDefs.sie_cap] (inside
       [intr_res], which usertrap's [csrw stvec,kernelvec] at +0x1e folds and
       prepare_return's [csrci] unfolds).  uservec therefore may NOT hold the
       cell back across its call -- usertrap NEEDS it, loose, and takes it as
       its own premise -- so what comes back here is what [usertrap_post]
       hands over at the resuming hart, at [TRAMPOLINE] again.  From there
       the trap loop puts it into the next round's [UserExec.user_cfg]. *)
    stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
    senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    (* usertrap never touches these after its own return -- held loose,
       framed the whole way through userret, and handed back unchanged *)
    scause ↦ᵣ sc' -∗
    stval ↦ᵣ stval' -∗
    sepc ↦ᵣ uepc -∗
    (* THE WHOLE ADDRESS SPACE, back in the USER view -- not just the
       translation invariant.  The pages come with it: they are the same
       resource [proc_pt_own] holds page-indexed while the kernel runs
       ([ProcPtOwn.user_pt_inv_close] is the conversion), and if this post
       handed back only [utlb_inv_pt] while the residue below still carried
       [proc_pt], the two together would claim the tree and the pages twice
       over -- the vacuity this whole boundary was restated to avoid. *)
    user_pt_any pt' -∗
    pc_is (ret_pc uepc) -∗
    gpr_file mf -∗
    (* the leftover: usertrap's OWN kernel-internal BARE bundle (no address
       space -- that is the conjunct above), RESEALED with
       userret's own restored trapframe words folded back in (the proof's
       tail does this fold once, right before userret's own return) -- at
       the SAME [ksp] uservec loaded and handed in.  No raw [tf_pa] cells
       here: [usertrap_res] is the ONE owner of the trapframe page
       (UsertrapRes.v), so exposing them here TOO would double-claim it,
       same as at entry -- see the header and
       claude-notes/completed/usertrap.md.  Folding this bundle into the
       user-mode loop is USER-module work, not this spec's. *)
    URes pt' vksp -∗
    (* THE TWO AMBIENT-HART PERSISTENT BUNDLES, AT THE RESUMING HART.  Both
       are per-hart -- [hw_config]'s cells and the body of [minstret_inv]'s
       invariant are this hart's -- so a caller's pre-crossing copy is a
       DIFFERENT resource from the one it needs after usertrap's park, and
       the two print identically.  [usertrap_post] hands them back for
       exactly this reason (see its own note); passing them on costs nothing
       to prove and is what lets the next round of the trap loop reach
       [SpecUser.wp_user_exec_closed], which takes both.  [wire_inv] needs no
       such treatment: it is all-harts (WireInv.v) and rides for free. *)
    hw_config -∗
    minstret_inv -∗
    WP (Loop : expr riscv_lang)).
Global Typeclasses Opaque uservec_post.

(* Same as [uservec_post]: only [riscvGS]/[sieG] -- [usertrap_res] is held
   opaquely through [URes], never opened. *)
Definition wp_uservec_pt_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (* A FAMILY, not one predicate: uservec calls usertrap, usertrap PARKS
       (SpecUsertrap.v's own [wp_next true pj] crossing), so everything
       after that call -- the residue included -- is a resource AT WHATEVER
       HART RESUMED.  Same shape, same reason, as [wp_usertrap_body]'s [R]. *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
    (j : nat) (vksp : mword 64) :=
  (* stvec points at the trampoline base *)
  uc_stvec C = mword_of_int TRAMPOLINE ->
  (* the kernel owns the config cells outright at this join (same fact the
     userret-side bridge [userret_to_user_inv] requires): the step leaves
     drive all six machine/config cells at ONE dfrac, and the trap frame
     holds hart_state/cur_privilege/mstatus at full *)
  uc_dqc C = DfracOwn 1 ->
  (* [user_cfg]'s [mie] is a caller-chosen field of [C]; [sconf] (hence
     usertrap's own borrowed-loose [mie]) pins it to the architectural
     constant -- see UsertrapRes.v's header on the mie/mideleg/menvcfg
     borrow. *)
  uc_mie C = MIE_S ->
  (* the process index usertrap needs, purely to prove [proc_addr j <>
     zero_reg] via [j < NPROC] -- see UsertrapRes.v's note that usertrap's
     OWN internal walk is not tied to it otherwise *)
  (j < NPROC)%nat ->
  (* THE DESCRIPTOR IS RENORMALISED.  [user_pt_inv] owns the user pages at
     the descriptor's [ud_data] field; the kernel tier owns the same pages
     page-indexed, i.e. at the DERIVED footprint [ProcPtOwn.ud_pas], and
     [proc_pt] says nothing about [ud_data] at all ([proc_pt_data_irrel]).
     The satp switch converts between the two views, so it needs the two
     footprints to be the same set.  This is not a restriction on which
     tables can trap: [uservec_post] hands the descriptor back already
     renormalised, so the loop is closed under it, and a first round can
     normalise for free ([ProcPtOwn.ud_norm], [user_pt_inv]'s only reader
     of the field). *)
  ud_data pt = ud_pas pt ->
  (* THE TABLE IS A KERNEL-TIER WELL-FORMED ONE.  [user_pt_inv] records only
     two of [proc_pt_wf]'s five conjuncts ([upt_map_wf] inside
     [utlb_inv_pt], [upt_acc_wf] beside it); the other three -- every user
     page is a kalloc page, distinct vpns map distinct pages, and the
     trapframe page is a kalloc page -- are facts the user-execution tier
     never needs and so never carries.  The satp switch needs them, because
     what it rebuilds is [proc_pt], and [proc_pt] is where a kernel that
     will later free those pages reads them.  Like the renormalisation
     above this is loop-closed: [uservec_post] hands it back for [pt'],
     read straight out of the residue's own [proc_pt]. *)
  proc_pt_wf pt ->
  (* THE TRAPFRAME'S KERNEL WORDS -- [vksat]/[vktr]/[vkhart] and the kernel
     root they name -- are NOT parameters: they live inside [usertrap_res]
     together with the fact that ties them to a root and to [vksp]
     ([UsertrapRes.ut_tfk]), and the proof discovers both by OPENING the
     residue.  The kernel root is therefore existential here too, with its
     [kpt_inv] coming out of the same open -- which is why this contract
     names no [kroot] and takes no [kpt_inv]. *)
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  (* the trampoline claim, threaded to the exit switch (persistent; the
     caller holds it from kvminithart's postcondition -- same premise
     [wp_userret_pt] takes) *)
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  (* the machine, exactly as the trap delivers it *)
  user_trap_frame C pt Rut -∗
  (* the kernel-side resources parked while user code ran.  [sscratch] is
     NOT among them: it lives in [IntrDefs.hart_csrs], inside the residue
     below, and the proof borrows it from there ([usertrap_res_tf_csrs_open])
     -- a separate premise would be BOTH unsatisfiable (the residue owns the
     cell, so a caller cannot hold a second one) and unmintable. *)
  (* usertrap's own kernel-internal bundle, for THIS trap round -- the ONE
     owner of the trapframe (SpecUsertrap.v's header), opened once at the
     top of the proof for the 44-instruction walk's own [tf_pa] cells and
     resealed before the call into usertrap.  An ordinary premise,
     unrelated to [Rut] (which stays fully abstract: uservec's own proof
     never opens it, exactly like [mie]/[mideleg]/[menvcfg] ride through
     [user_cfg] untouched). *)
  URes CID pt vksp -∗
  (* THE CONTINUATION, ACROSS THE CROSSING.  userret's own exit shape plus
     the leftover bare residue -- but at whatever hart usertrap resumed on,
     not the one uservec entered at.  Everything in [uservec_post] is
     hart-indexed (every [↦ᵣ] cell, the [satp]/[tlb] inside [user_pt_inv],
     the residue), so a continuation stated at the entry hart alone would
     be unusable at the point the proof actually needs it -- and would be
     silently so, since the two print identically.  Same [wp_next true
     (proc_addr j)] wrapper as [wp_usertrap_body]'s post, for the same
     reason and with the same escape: at a REAL proc ([j < NPROC], hence
     [proc_addr j <> zero_reg]) the pinning condition is vacuous, so the
     caller owes the post at every hart. *)
  wp_next true (proc_addr j) (fun CID' : CpuId =>
    uservec_post (CID := CID') (URes CID') C pt vksp) -∗
  WP (Loop : expr riscv_lang).

Module Type USERVEC.
  (* ...AND THE PARK'S ONE PRODUCER-SIDE ENTRY, threaded with the rest.
     [UsertrapRes.USERTRAP_RES_PARK] is [USERTRAP_RES] plus
     [usertrap_res_bare_park]: the residue stays opaque to every CONSUMER,
     and the one party that has to BUILD one -- whoever parks a process that
     has never trapped -- gets a closer instead.  See that file's "THE
     PARK'S CHANNEL THROUGH THE MODULE TYPES". *)
  Include UsertrapRes.USERTRAP_RES_PARK.
  Parameter wp_uservec_pt :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (j : nat) (vksp : mword 64),
      (* THE BARE RESIDUE, not [usertrap_res] and not even the parked form.
         [usertrap_res] and this spec's own [user_trap_frame] premise claim
         THE SAME FOUR RESOURCES -- satp/tlb, the user page-table tree, the
         user data pages, and (in the first draft of this file) the
         trapframe page -- so taking either of the fuller forms here makes
         the precondition unsatisfiable and this whole lemma vacuous.  The
         bare form owns none of the address space; uservec's exit switch
         produces both missing pieces at once (it converts the user table
         back to a [pt_frame] and writes the kernel root into satp), which
         [usertrap_res_pt_close] then [usertrap_res_tlb_close] fold back in
         just before the call into usertrap.  userret's entry switch runs
         the same two moves in reverse.  See
         claude-notes/projects/uservec.md. *)
      wp_uservec_pt_body (fun h : CpuId => usertrap_res_bare (CID := h))
        C pt Rut j vksp.
End USERVEC.
