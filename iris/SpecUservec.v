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

   THE TRAPFRAME IS OWNED THE SAME WAY THROUGHOUT.  [usertrap_res] is the
   ONE owner of the trapframe page (UsertrapRes.v), stated at the PHYSICAL
   tier ([ProcInv.tf_page], native [tf_pa]/[↦ₚ₈] cells -- the SAME tier
   uservec/userret's own 44/31-instruction walks already use, so there is
   no phys<->mem crossing at this boundary at all).  Consequently this
   spec takes [usertrap_res pt vksp] as ITS OWN precondition (not raw
   [tf_pa] cells): the proof opens it once (via
   [SpecUsertrap.usertrap_res_tf_open]) for the SAVE walk's own cells,
   reseals it before calling usertrap, and repeats the open/reseal once
   more around the call into userret.  [uservec_post] therefore is NOT
   userret's own exit shape (which exposes raw [tf_pa] cells) -- it is
   that shape with the trapframe folded back into a fresh [usertrap_res
   pt' vksp] instead, the ONE thing left over once userret's entry
   consumes everything else, and nothing downstream of THIS spec asks for
   more: folding THAT into the user-mode loop (the outer Löb that
   discharges [UserExec.stvec_handler_wp]) is future work, once USER is
   folded in too.

   THE MSTATUS GAP.  [user_trap_frame]'s own pure content is only
   [trap_mstatus_ok ms_v] (UserExec.v); [usertrap_entry_ms] additionally
   needs [sconf_ms_facts ms_v] (IntrDefs.v: XS/FS/VS/SD/MPP pins) and
   [SPIE = 1]. Neither is derivable from what a trap frame already carries
   -- [SPIE = 1] in particular is a genuine cross-round historical fact
   ("userret's sret set it, so it survived to this trap") that needs ghost
   tracking through the full user-mode loop, out of scope here. So this
   spec takes the gap as a BARE, EXPLICIT, undischarged premise instead of
   silently assuming it -- a real proof obligation for whoever eventually
   closes the loop, not a hole.

   THE TRAPFRAME KERNEL-WORDS GAP is the SAME shape.  Nothing ties the
   trapframe's four kernel words (inside [usertrap_res], opaque to this
   spec) to [kroot]/[KernelSyms.usertrap]/[cid_word] -- that connection IS
   established, but only at [prepare_return]'s own exit
   (SpecPrepareReturn.v), one round before uservec next opens
   [usertrap_res]; threading it forward is the same full-loop ghost
   tracking the SPIE=1 gap needs.  See [ProcGeom.tf_kernel_words_ok] and
   [usertrap_res_tf_open]'s own premise. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile HartTp.
Require Import MinstretInv InstrBytes.
Require Import WpGpr.
Require Import KernelText.
Require Import SmodeCore.
Require Import PtTree.
Require Import TrampPt KptTree UptTree TransPt KptShare UserretDefs.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import MstatusBits.
Require Import ProcGeom.
(* [usertrap_res]'s own signature (SpecUsertrap.v/USERTRAP_RES) is stated
   over these fourteen classes; unqualified [lockG]/[fdslotG]/... below
   only resolve to the CONCRETE classes (rather than each getting silently
   auto-generalized as a fresh, unrelated abstract variable of type
   [gFunctors -> Type] -- the same one-`Require`-isn't-enough trap as
   everywhere else in this project) if their defining modules are directly
   imported here too, not just transitively pulled in via SpecUsertrap. *)
Require Import WpLock.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import BioInv.
Require Import DiskPtsto.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import KallocInv.
Require Import IrefSlots InodeRegion.
Require Import SpecUsertrap.
Require Import SpecUserret.
From Kernel Require KernelSyms.
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
Definition uservec_post `{!riscvGS Σ, !sieG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (URes : uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd) (vksp : mword 64) : iProp Σ :=
  ( ∀ (pt' : uptd) (mf : regfile) (ms' usatp uepc sc' stval' mdv0 : mword 64),
    ⌜ud_tfp pt' = ud_tfp pt⌝ -∗
    ⌜upt_map_wf (ud_um pt')⌝ -∗
    ⌜satp_rooted usatp (ud_root pt')⌝ -∗
    ⌜and_vec MIE_S (not_vec mdv0) = zeros' 64⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ sret_ms5 ms' -∗
    mie ↦ᵣ MIE_S -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ MENVCFG_S -∗
    senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    (* usertrap never touches these after its own return -- held loose,
       framed the whole way through userret, and handed back unchanged *)
    scause ↦ᵣ sc' -∗
    stval ↦ᵣ stval' -∗
    sepc ↦ᵣ uepc -∗
    utlb_inv_pt (ud_root pt') (ud_tfp pt') (ud_um pt') -∗
    pc_is (ret_pc uepc) -∗
    gpr_file mf -∗
    (* the leftover: usertrap's OWN kernel-internal bundle, RESEALED with
       userret's own restored trapframe words folded back in (the proof's
       tail does this fold once, right before userret's own return) -- at
       the SAME [ksp] uservec loaded and handed in.  No raw [tf_pa] cells
       here: [usertrap_res] is the ONE owner of the trapframe page
       (UsertrapRes.v), so exposing them here TOO would double-claim it,
       same as at entry -- see the header and
       claude-notes/completed/usertrap.md.  Folding this bundle into the
       user-mode loop is USER-module work, not this spec's. *)
    URes pt' vksp -∗
    WP (Loop : expr riscv_lang)).
Global Typeclasses Opaque uservec_post.

(* Same as [uservec_post]: only [riscvGS]/[sieG] -- [usertrap_res] is held
   opaquely through [URes], never opened. *)
Definition wp_uservec_pt_body `{!riscvGS Σ, !sieG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (URes : uptd -> mword 64 -> iProp Σ)
    (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (kroot : mword 44)
    (j : nat) (sscr0 : mword 64) (vksp : mword 64) :=
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
  (* THE MSTATUS GAP, stated as a bare, undischarged premise -- see the
     header. *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (* THE TRAPFRAME KERNEL-WORDS GAP, the same shape -- see
     [ProcGeom.tf_kernel_words_ok]'s own header.  [vksat]/[vktr]/[vkhart]
     are no longer named parameters here: the four kernel words live
     entirely inside [usertrap_res] now (this spec's own header), so their
     values are discovered by OPENING it, not chosen by the caller -- this
     premise is what the proof's tail uses to justify the switch/jalr once
     it does.  HART-GENERIC: usertrap may PARK and resume on a different
     hart (SpecUsertrap.v's [wp_next] crossing), and the proof opens
     [usertrap_res] a second time there, at whichever hart that turns out
     to be -- so this premise must hold at ALL of them, not just the one
     uservec itself started on. *)
  (forall (CID' : CpuId) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := CID') kroot vksp ws) ->
  kernel_text -∗
  hw_config -∗
  minstret_inv -∗
  (* the trampoline claim, threaded to the exit switch (persistent; the
     caller holds it from kvminithart's postcondition -- same premise
     [wp_userret_pt] takes) *)
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  (* the machine, exactly as the trap delivers it *)
  user_trap_frame C pt Rut -∗
  (* the kernel-side resources parked while user code ran *)
  sscratch ↦ᵣ sscr0 -∗
  kpt_inv kroot -∗
  (* usertrap's own kernel-internal bundle, for THIS trap round -- the ONE
     owner of the trapframe (SpecUsertrap.v's header), opened once at the
     top of the proof for the 44-instruction walk's own [tf_pa] cells and
     resealed before the call into usertrap.  An ordinary premise,
     unrelated to [Rut] (which stays fully abstract: uservec's own proof
     never opens it, exactly like [mie]/[mideleg]/[menvcfg] ride through
     [user_cfg] untouched). *)
  URes pt vksp -∗
  (* the continuation: userret's own exit shape, plus the leftover
     [usertrap_res] -- see the header. *)
  uservec_post URes C pt vksp -∗
  WP (Loop : expr riscv_lang).

Module Type USERVEC.
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_uservec_pt :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (kroot : mword 44) (j : nat) (sscr0 : mword 64) (vksp : mword 64),
      (* THE PARKED RESIDUE, not [usertrap_res] itself: the latter owns
         [satp] (its [strans_inv] sits in the KPT arm), and this spec's own
         [user_trap_frame] premise owns [satp] too, at the USER root -- so
         taking the complete form here would make the precondition
         unsatisfiable and this whole lemma vacuous.  uservec's exit switch
         produces the [tlb_res_pt] that completes it
         ([usertrap_res_tlb_close]) just before it calls usertrap. *)
      wp_uservec_pt_body usertrap_res_parked C pt Rut kroot j sscr0 vksp.
End USERVEC.
