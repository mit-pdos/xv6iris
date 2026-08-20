(* UserExec.v -- the WP for ARBITRARY user-mode execution: the abstract
   invariant of a valid user-mode machine, the trapped-to-kernel frame, and
   the Löb capstone [wp_user_exec].

   This is the WP that belongs in [wp_userret]'s continuation (WpUserretAll.v):
   once userret sret's to User with the user page table live, the machine may
   keep executing WHATEVER user code the mapped pages hold, forever, with the
   only exit a synchronous trap into the kernel's handler at stvec (uservec).

     [user_inv]        the loop invariant: privilege User, an ARBITRARY pc,
                       ARBITRARY registers, arbitrary trap CSRs, over the
                       user page table bundle [user_pt_any] (UserPtTree.v --
                       owns the PT slots and the process's whole memory
                       [umem_own P M]; [M] -- the abstract state -- is
                       QUANTIFIED here, since arbitrary user code may write
                       arbitrary bytes into its own pages, while its DOMAIN
                       is pinned by the table) and the config [user_cfg].
     [user_trap_frame] the frame handed to the kernel re-entry continuation:
                       privilege Supervisor, pc at stvec's direct base, the
                       trap CSRs written, everything else as in [user_inv].
     [stvec_handler_wp] the assumed kernel re-entry contract: from
                       [user_trap_frame], the kernel handler runs safely.
     [user_step_obligation] ONE machine step from [user_inv] either retires
                       (re-establishing [user_inv]) or traps (producing
                       [user_trap_frame]), both continuations under a later.
     [wp_user_exec]    the Löb induction: step obligation + invariant +
                       handler contract ⊢ WP Loop.

   The step obligation is where all the real work lands; it is discharged by
   the per-step case analysis (interrupt dispatch x fetch trichotomy x decode
   totality [DecodeTotalU/DecodeSetU] x per-family execute outcomes).
   Everything a step can do falls in one of the two continuations:
     - retire: compute/branch/jump (register file changes), loads/stores/AMOs
       to mapped pages (the memory [M] is quantified in [user_pt_any], so a
       store re-establishes it at a new [M]), TLB fills and Svadu A/D write-backs (absorbed by [utlb_inv_pt]);
     - trap TO STVEC: a pending delegated INTERRUPT (see below), ecall/ebreak,
       illegal (incl. all privileged instructions), fetch/load/store page
       faults (unmapped or permission-denied or A/D-update-needed pages),
       misaligned accesses.
   INTERRUPTS CAN PREEMPT ANY STEP: at User privilege the effective SIE is
   architecturally true (unmaskable), and the wire thread (PlicLoop's wire
   step) may raise the external-interrupt wire [sig_seip] concurrently at
   any time.  So the user frame does NOT own the wire cells -- and under
   per-node semantics it does not have to BORROW them either: the dispatch
   reads [sig_meip]/[sig_seip] as forall-BOUND reads
   ([WpMmodeCsrSwp.swp_read_reg_any], which needs no ownership at all), so
   the wire value simply lives in the payload of the dispatch's answer.
   THE TWO PLIC WIRES ARE THE ONLY REGISTERS A USER CYCLE READS THAT THE
   HART DOES NOT OWN (the enumeration is section 1.4 of the port plan);
   everything else -- mip, mcycle, mtime and minstret included -- is owned
   outright by [user_regs] through [MinstretInv.clock_res]/[minstret_res].
   Consequently the user tier needs NEITHER [WireInv.wire_inv] NOR
   [MinstretInv.clock_inv], and every invariant borrow this file used to
   carry is gone.  Each step case-splits on the dispatch decision
   ([u_dispatch], UserStep.v): pending-and-enabled delegated interrupt ->
   the interrupt trap to stvec (Supervisor), which is just another producer
   of [user_trap_frame]; none -> fetch/execute.  [uc_mm] (mie & ~mideleg =
   0, a boot constant) only rules out M-DESTINED interrupts, so every
   dispatched interrupt goes to Supervisor.                                *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpGpr.
Require Import RegFile.
Require Import WpIntrCore.
Require Import UserFrame.
Require Import UserPtTree.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The synchronous exceptions user-mode execution can raise.            *)
(* ===================================================================== *)

Definition user_exc (e : ExceptionType) : bool :=
  match e with
  | E_Fetch_Addr_Align _ | E_Fetch_Access_Fault _ | E_Illegal_Instr _
  | E_Breakpoint _
  | E_Load_Addr_Align _ | E_Load_Access_Fault _
  | E_SAMO_Addr_Align _ | E_SAMO_Access_Fault _
  | E_U_EnvCall _
  | E_Fetch_Page_Fault _ | E_Load_Page_Fault _ | E_SAMO_Page_Fault _ => true
  | _ => false
  end.

(* ===================================================================== *)
(* §2 The loop-constant boot configuration.  ONE record so every lemma in  *)
(* the user-execution development closes over a single parameter [C].      *)
(* ===================================================================== *)

Record ucfg := UCfg {
  uc_stvec   : mword 64;    (* the kernel trap handler (uservec), DIRECT mode *)
  uc_mie     : mword 64;
  uc_mideleg : mword 64;
  uc_medeleg : mword 64;
  (* THERE IS STILL NO [uc_mip] FIELD, BUT NO LONGER FOR THE OLD REASON.
     [mip] is written by the CLOCK TICK ([tick_clock] sets MTIP/STIP from
     mtimecmp/stimecmp -- the Sstc branch is live), so a hart cannot pin a
     VALUE for it across a cycle.  Under per-node semantics the hart OWNS
     the cell (it rides inside [user_regs] via [MinstretInv.clock_res],
     together with mcycle and mtime), so the old exclusivity clash with
     [clock_inv] -- which is what used to make a [mip ↦ᵣ{dqc}] conjunct of
     [user_cfg] contradict [minstret_inv] and render every user-tier
     theorem vacuous -- is simply gone, and with it the [clock_mip_acc]
     borrow this file used to carry.  What survives is the WEAKER reason
     for the same conclusion: the value is EXISTENTIAL per step, which is
     exactly what [clock_res] already says, so there is nothing for a
     loop-CONSTANT record to hold. *)
  uc_dqc     : dfrac;       (* config-cell fraction *)
  (* stvec is DIRECT-mode: traps land exactly at its base *)
  uc_tvd : trapVectorMode_forwards (_get_Mtvec_Mode uc_stvec) = TV_Direct;
  (* no M-level interrupt is enabled-but-undelegated: every dispatched
     interrupt is S-destined (goes to stvec, not an M-mode handler).  The
     S-destined pending set is NOT constrained -- the device raises the
     sig_seip wire concurrently, and a pending delegated interrupt simply
     traps to stvec (the interrupt arm of the step obligation). *)
  uc_mm  : and_vec uc_mie (not_vec uc_mideleg) = zeros' 64;
  (* every exception user execution can raise is delegated to S-mode *)
  uc_del : forall e : ExceptionType, user_exc e = true ->
             bit_to_bool (access_vec_dec uc_medeleg
               (uint (exceptionType_bits_forwards e))) = true
}.

(* ===================================================================== *)
(* §3 hart-state and mstatus pins.                                         *)
(* ===================================================================== *)

(* the hart states user execution can put the core in: ACTIVE, or -- via
   the Zawrs WRS.STO / WRS.NTO instructions, which are user-executable and
   are NOT nops in this build -- WAITING.  (WFI in U-mode traps illegal
   before entering the wait, so WAIT_WFI is unreachable from user code.)
   The waiting-state step [run_hart_waiting] wakes when the raw
   [mip & mie ≠ 0] ([shouldWakeForInterrupt] -- NOTE: the raw mip register
   only, NOT the sig_* wires) or when the reservation is invalid; the
   latter scrutinizes the OPAQUE platform axiom [valid_reservation], so
   the wait-step arm of the step obligation case-splits on it -- BOTH
   branches step (wake-and-retire vs stay-waiting), and both re-establish
   [user_inv]. *)
Definition user_hart_ok (hs : HartState) : Prop :=
  match hs with
  | HART_ACTIVE _ => True
  | HART_WAITING (wr, _) => wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO
  end.

(* mstatus pins: user execution never writes mstatus (only traps do, and
   they exit the loop), so these ride through every retired step. *)

(* in the user phase: SXL fixed 64-bit, no M-mode memory-privilege override,
   MXR off (so a load's permission check is a pure function of the leaf's
   R bit -- no executable-implies-readable special case to track).
   TVM/TSR = 0 ride along even though user execution never consults them:
   they are M-mode bits xv6 never sets and sstatus writes cannot touch, and
   the kernel needs them across the round trip -- uservec's sfence.vma /
   csrw satp demand TVM=0, and userret's sret demands TSR=0.  Without the
   pins the values would be existentially lost inside [user_inv]. *)
Definition user_mstatus_ok (ms : mword 64) : Prop :=
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_FS ms) ('b"00") = true /\
  eq_vec (_get_Mstatus_VS ms) ('b"00") = true /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false.

(* after the trap: same pins, plus what the trap transform wrote --
   SPP = User (we trapped FROM user) and SIE = 0 (interrupts masked,
   exactly the state the kernel's S-mode leaves require) *)
(* THE per-step pure precondition every classification obligation takes:
   the machine (at the post-minstret-increment state the arms instantiate
   it at) is a no-pending-interrupt User machine at pc [va] with the
   mstatus pins.  ONE premise instead of four in every obligation. *)
Definition u_step_pre (σ : mstate) (va : mword 64) : Prop :=
  exec (dispatchInterrupt User) σ = Some (None, σ) /\
  register_lookup cur_privilege σ.(sregs) = User /\
  register_lookup PC σ.(sregs) = va /\
  user_mstatus_ok (register_lookup mstatus σ.(sregs)).

(* a register lookup survives the minstret_increment write *)
Lemma lookup_set_mi (σ : mstate) (b : bool) (r : register) (v : type_of_register r) :
  register_lookup r σ.(sregs) = v ->
  register_beq r (R_bool minstret_increment) = false ->
  register_lookup r (set_reg σ (R_bool minstret_increment) b).(sregs) = v.
Proof.
  intros Hv Hne. rewrite ?sregs_set_reg.
  rewrite irrelevant_register_set; [exact Hv | exact Hne].
Qed.

(* the arms build [u_step_pre] at the post-increment state from the
   σ-level frame facts + the wrapper's ∀-b dispatch fact *)
Lemma u_step_pre_intro (σ : mstate) (va ms_v : mword 64) (b : bool) :
  user_mstatus_ok ms_v ->
  register_lookup cur_privilege σ.(sregs) = User ->
  register_lookup mstatus σ.(sregs) = ms_v ->
  register_lookup PC σ.(sregs) = va ->
  exec (dispatchInterrupt User) (set_reg σ (R_bool minstret_increment) b)
    = Some (None, set_reg σ (R_bool minstret_increment) b) ->
  u_step_pre (set_reg σ (R_bool minstret_increment) b) va.
Proof.
  intros Hmsok Lpriv Lms Lpc Hdisp.
  split; [ exact Hdisp | ].
  split; [ exact (lookup_set_mi σ b cur_privilege _ Lpriv eq_refl) | ].
  split; [ exact (lookup_set_mi σ b PC _ Lpc eq_refl) | ].
  rewrite (lookup_set_mi σ b mstatus _ Lms eq_refl). exact Hmsok.
Qed.

Definition trap_mstatus_ok (ms : mword 64) : Prop :=
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_SPP ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false.

(* The post-fetch config facts an execute totality assumes at the fetched
   state [σf].  Relocated here from the pruned UserExecProducer.v and EXTENDED:
   the mstatus conjunct is now the full [user_mstatus_ok] (SXL + MPRV=0 + MXR=0
   + FS/VS=Off, enabling the memory + CSR arms), and [is_aligned_vaddr va 2]
   is threaded (the producers already hold it) so jump_to's target-bit0
   premise is dischargeable for JAL/BTYPE/C_J/C_BEQZ/C_BNEZ. *)
Definition post_fetch_cfg (σf : mstate) (va : mword 64) (miσ : bool) : Prop :=
  register_lookup PC σf.(sregs) = va /\
  register_lookup cur_privilege σf.(sregs) = User /\
  user_mstatus_ok (register_lookup mstatus σf.(sregs)) /\
  register_lookup menvcfg σf.(sregs) = MENVCFG_S /\
  is_aligned_vaddr (Virtaddr va) 2 = true /\
  register_lookup (R_bool minstret_increment) σf.(sregs) = miσ.


(* ===================================================================== *)
(* §4 The frames and the capstone.                                         *)
(* ===================================================================== *)
(* ---------------------------------------------------------------------- *)
(* THE TWO FROZEN COUNTER CELLS, OUT OF [hw_config].                        *)
(*                                                                          *)
(* [RiscvFetchExec] defines [counter_caps] and appends it to [hw_config] but *)
(* has no proofmode import, so the accessor lives here -- the U tier is its  *)
(* only consumer.  [mcounteren] is NOT among them: timerinit writes it after *)
(* [hw_config] is frozen, so its persistent form is [TimerCap.sstc_enabled], *)
(* which the trap loop takes out of the residue instead.                     *)
(* ---------------------------------------------------------------------- *)
Section HwCounters.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma hw_config_counters : hw_config -∗ counter_caps.
  Proof.
    iIntros "H". rewrite /hw_config.
    iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & $)".
  Qed.
End HwCounters.

Section UserExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* The exclusive [usertrap_res]-shaped residue that must survive
     UNCHANGED across arbitrary user-mode execution: usertrap's proof
     (SpecUsertrap.v) hands it to the loop on trap entry and gets it back
     unchanged on the next trap, so it rides inside [user_inv]/
     [user_trap_frame] as one more conjunct, opaque to everything in this
     file.  Concretely instantiated (by whoever closes the loop, e.g.
     [UservecProof]) as [fun pt => ∃ ksp, UT.usertrap_res pt ksp]. *)
  Context (Rut : uptd -> iProp Σ).

  Local Notation dqc := (uc_dqc C).

  (* the loop-constant config cells (fraction [dqc]: never written during
     user execution; the complementary fraction stays with the kernel).
     satp / tlb / pmp cells live inside [user_pt_any] (UserPtTree.v).  The
     external-interrupt WIRES sig_meip / sig_seip are deliberately ABSENT
     and no bundle in this file holds them: the device loop writes them
     concurrently, and the dispatch reads them forall-bound, off-frame.
     [mip] IS ABSENT FOR A DIFFERENT REASON: the clock tick writes it every
     cycle, so it has no loop-constant value -- but the hart does OWN the
     cell, inside [user_regs]'s [clock_res] rider.  See the note in [ucfg]
     where its field used to be. *)
  Definition user_cfg : iProp Σ :=
    (stvec ↦ᵣ{ dqc } uc_stvec C ∗
     mie ↦ᵣ{ dqc } uc_mie C ∗
     mideleg ↦ᵣ{ dqc } uc_mideleg C ∗
     (* [medeleg] and the two state-enable pins below are [↦ᵣ□] for the
        same reason [senvcfg] is, plus one more: nothing writes them after
        M-mode boot, AND [IntrDefs.hart_csrs] -- inside the kernel residue
        that [wp_uservec_pt] takes BESIDE the trap frame -- holds them too.
        At an owned fraction the two bundles would claim the same cells and
        uservec's precondition would be unsatisfiable. *)
     medeleg ↦ᵣ□ uc_medeleg C ∗
     menvcfg ↦ᵣ{ dqc } MENVCFG_S ∗
     (* [senvcfg] is NEVER WRITTEN -- no [wp_csrw]-style lemma for it exists
        anywhere in the tree -- so unlike its neighbors above it needs no
        fraction split with the kernel at all: state it directly at
        [DfracDiscarded], decoupled from [dqc]. A discarded fraction is
        freely duplicable, so this costs nothing to hold alongside every
        other read of it (e.g. [hw_config]'s own copy, RiscvFetchExec.v). *)
     senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
     mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) ∗
     sstateen0 ↦ᵣ□ (mword_of_int 0 : mword 32) ∗
     (* THE COUNTER-PERMISSION CELLS, and they are not optional.  A U-mode
        [csrr] of cycle / time / instret / hpmcounterN runs [counter_enabled],
        which reads mcounteren and scounteren UNCONDITIONALLY (UserCsr's
        [exec_counter_enabled_U_total]), and the hpm path reads mhpmcounter.
        Under whole-cycle stepping the interpreter answered those reads off
        [gen_heap_interp] and no bundle had to hold them; under per-node
        stepping every read the cycle makes must be ANSWERABLE, so the hart
        owns them.  Their VALUES are existential -- the U-mode CSR arm is
        total whatever the permission bits say (denied reads are
        Illegal_Instruction, which is a [u_result_ok] outcome) -- so they are
        [box] like [medeleg] and cost the kernel nothing to hand over. *)
     (∃ mcenv scenv : mword 32,
        (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv ∗
        (R_bitvector_32 scounteren) ↦ᵣ□ scenv) ∗
     (∃ hpm : type_of_register mhpmcounter, mhpmcounter ↦ᵣ□ hpm))%I.

  (* ------------------------------------------------------------------- *)
  (* The loop invariant: A VALID USER-MODE EXECUTION STATE.  Everything an *)
  (* instruction can change is existential: the hart state (ACTIVE, or     *)
  (* WAITING after a user WRS -- entering/leaving the wait WRITES the      *)
  (* cell, so it is owned at full fraction), the pc (ANY value -- fetching *)
  (* from a non-canonical or unmapped address page-faults safely), the     *)
  (* register file, the trap CSRs (stale until the next trap writes them), *)
  (* mstatus up to its pins, and -- inside [user_pt_any] -- the TLB and the    *)
  (* mapped pages' contents.                                               *)
  (*                                                                       *)
  (* PC vs nextPC: while ACTIVE the two are in lock-step ([pc_is]-shaped:  *)
  (* the previous step's epilogue ticked PC := nextPC).  While WAITING     *)
  (* they are DECOUPLED -- the enter-wait step skips the tick (the model's *)
  (* epilogue only ticks when the hart ends the step ACTIVE), so PC still  *)
  (* points at the WRS and nextPC at the instruction after it; the wake    *)
  (* step retires and ticks, restoring lock-step at [va'].                 *)
  (* ------------------------------------------------------------------- *)
  (* the per-step mutable register cells, as one bundle (shared between
     [user_inv] and the unpacked step obligations).  IT IS [UserFrame.u_regs]
     -- the same eight cells as before plus THREE RIDERS, [minstret_res],
     [clock_res] and [resv_any cpu_id].  They are here because the user hart
     now owns minstret/minstret_increment/mcycle/mtime/mip outright: there is
     no clock invariant left to borrow mip from, and the reservation frag is
     what [HartMemRun.swp_hmrun_of_exec] consumes and hands back at every
     model call.  Their values are existential per step, which is exactly
     what [clock_res]/[minstret_res] say, so nothing in this file's
     statements has to name them.
     WHY NOT [pc_is]: [InstrBytes.pc_is x] bundles the same three riders but
     FORCES PC = nextPC, and the WAITING hart decouples them (the enter-wait
     step skips the tick).  [UserFrame.u_regs_pc_is] is the bridge back for
     the two boundaries that still speak [pc_is]. *)
  Definition user_regs (hs : HartState)
      (ms_v sc_v stval_v sepc_v va va' : mword 64)
      (g : regfile) : iProp Σ :=
    u_regs hs ms_v sc_v stval_v sepc_v va va' g.

  Definition user_inv : iProp Σ :=
    (∃ (hs : HartState) (ms_v sc_v stval_v sepc_v va va' : mword 64)
       (g : regfile),
      ⌜user_hart_ok hs⌝ ∗
      ⌜user_mstatus_ok ms_v⌝ ∗
      ⌜forall u, hs = HART_ACTIVE u -> va' = va⌝ ∗
      user_regs hs ms_v sc_v stval_v sepc_v va va' g ∗
      user_pt_any pt ∗
      user_cfg ∗
      Rut pt)%I.

  (* ------------------------------------------------------------------- *)
  (* The trapped frame: what a synchronous trap out of user mode hands the *)
  (* kernel's stvec handler.  Supervisor privilege, pc at the handler, the *)
  (* trap CSRs freshly written (their exact values -- cause, tval, the     *)
  (* faulting pc in sepc -- are existential at this JOIN; the per-cause    *)
  (* step lemmas that produce this frame know them precisely, and a caller *)
  (* needing them can consume those lemmas directly).                      *)
  (* ------------------------------------------------------------------- *)
  Definition user_trap_frame : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v : mword 64)
       (g : regfile),
      ⌜trap_mstatus_ok ms_v⌝ ∗
      hart_state ↦ᵣ HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ Supervisor ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      pc_is (stvec_base (uc_stvec C)) ∗
      gpr_file g ∗
      user_pt_any pt ∗
      user_cfg ∗
      Rut pt)%I.

  (* assemble the trapped frame from the delivered cells (shared by every
     trap arm -- the values differ, the shape never does) *)
  (* IT TAKES [pc_is], NOT THE TWO CELLS.  Post-port every producer of a trap
     frame stands on a [u_regs]-shaped bundle whose PC/nextPC come back
     together with the three riders [user_trap_frame] needs, and [pc_is] is
     exactly that package ([UserFrame.u_regs_pc_is] is the one-line bridge).
     Handing the cells separately would owe the caller three more arguments
     for resources it already holds bundled. *)
  Lemma user_trap_frame_intro (ms' sc' stv' sep' : mword 64)
      (g : regfile) :
    trap_mstatus_ok ms' ->
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms' -∗ scause ↦ᵣ sc' -∗ stval ↦ᵣ stv' -∗ sepc ↦ᵣ sep' -∗
    pc_is (stvec_base (uc_stvec C)) -∗
    gpr_file g -∗ user_pt_any pt -∗ user_cfg -∗ Rut pt -∗
    user_trap_frame.
  Proof.
    iIntros (Hok) "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr Hupt Hcfg Hrut".
    iExists ms', sc', stv', sep', g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hupt Hcfg Hrut".
    iSplitR; [ iPureIntro; exact Hok | ].
    iFrame "Hpc".
  Qed.

  (* the assumed kernel re-entry contract: the handler at stvec (uservec)
     handles ANY trapped-out-of-user machine *)
  Definition stvec_handler_wp  : iProp Σ :=
    (user_trap_frame -∗ WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (* The step obligation: ONE machine step from the invariant, with both   *)
  (* continuations under a later (exactly what the step engines provide    *)
  (* after consuming one physical step).  The conjunction is ADDITIVE: the *)
  (* prover case-analyzes the machine first and selects exactly one arm.   *)
  (* ------------------------------------------------------------------- *)
  Definition user_step_obligation  : iProp Σ :=
    (□ (user_inv -∗
        ▷ ((user_inv -∗ WP (Loop : expr riscv_lang)) ∧
           (user_trap_frame -∗ WP (Loop : expr riscv_lang))) -∗
        WP (Loop : expr riscv_lang)))%I.

  (* the ACTIVE-hart residue of the step obligation: same contract, but the
     machine is handed over UNPACKED, with the hart pinned ACTIVE and the
     pc in lock-step ([user_step_obligation_holds], UserStep.v, discharges
     the WAITING case -- the WRS stay/wake steps -- so this is all that is
     left to prove) *)
  Definition user_step_obligation_active  : iProp Σ :=
    (□ (∀ (ms_v sc_v stval_v sepc_v va : mword 64)
          (g : regfile),
        ⌜user_mstatus_ok ms_v⌝ -∗
        user_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
        user_pt_any pt -∗
        user_cfg -∗
        Rut pt -∗
        ▷ ((user_inv -∗ WP (Loop : expr riscv_lang)) ∧
           (user_trap_frame -∗ WP (Loop : expr riscv_lang))) -∗
        WP (Loop : expr riscv_lang)))%I.

  (* ------------------------------------------------------------------- *)
  (* The capstone: safety of arbitrary user-mode execution, by Löb.        *)
  (* ------------------------------------------------------------------- *)
  (* THE HANDLER CONTRACT IS TAKEN UNDER A LATER, and it costs nothing to
     prove: the trap frame only ever reaches the handler THROUGH the step
     obligation, whose two continuations are both under a `▷` (at least one
     user instruction executes before any trap), so `Htrap` is used only
     after that `▷` is stripped.  Taking `▷ stvec_handler_wp` is therefore
     the strictly stronger statement, and it is what lets a caller close the
     userret -> user -> uservec -> usertrap -> userret cycle: the Löb
     hypothesis for the next trap round is available only under a later, and
     this is the premise it feeds. *)
  Theorem wp_user_exec  :
    user_step_obligation -∗
    user_inv -∗
    ▷ stvec_handler_wp -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hstep".
    iLöb as "IH".
    iIntros "HP Htrap".
    iApply ("Hstep" with "HP").
    iNext. iSplit.
    - iIntros "HP". iApply ("IH" with "HP [$Htrap]").
    - iExact "Htrap".
  Qed.

End UserExec.
