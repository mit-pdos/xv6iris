(* UserExec.v -- the WP for ARBITRARY user-mode execution: the abstract
   invariant of a valid user-mode machine, the trapped-to-kernel frame, and
   the Löb capstone [wp_user_exec].

   This is the WP that belongs in [wp_userret]'s continuation (WpUserretAll.v):
   once userret sret's to User with the user page table live, the machine may
   keep executing WHATEVER user code the mapped pages hold, forever, with the
   only exit a synchronous trap into the kernel's handler at stvec (uservec).

     [user_inv]        the loop invariant: privilege User, an ARBITRARY pc,
                       ARBITRARY registers, arbitrary trap CSRs, over the
                       user page table invariant [upt_inv] (UserPt.v -- owns
                       the PT slots and every mapped page, contents
                       existential) and the loop-constant config [user_cfg].
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
   the fetch/decode/execute case analysis (fetch trichotomy x decode totality
   [DecodeTotalU/DecodeSetU] x per-family execute outcomes).  Everything an
   instruction can do falls in one of the two continuations:
     - retire: compute/branch/jump (register file changes), loads/stores/AMOs
       to mapped pages (the page contents are existential in [upt_inv], so a
       store trivially re-establishes it), TLB fills ([upt_tlb_ok_fill]);
     - trap: ecall/ebreak, illegal (incl. all privileged instructions),
       fetch/load/store page faults (unmapped or permission-denied or
       A/D-update-needed pages), misaligned accesses.
   Interrupts never preempt: [uc_mm]/[uc_s0] say no interrupt is both
   pending and enabled-for-dispatch, so the hart never enters the interrupt
   path during user execution (the device wires are pinned by [user_cfg]). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpIntrCore.
Require Import UserPt.
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
  uc_mip     : mword 64;
  uc_meip    : mword 1;     (* the M/S external-interrupt wire pins *)
  uc_seip    : mword 1;
  uc_dq      : dfrac;       (* hart_state fraction *)
  uc_dqc     : dfrac;       (* config-cell fraction *)
  (* stvec is DIRECT-mode: traps land exactly at its base *)
  uc_tvd : trapVectorMode_forwards (_get_Mtvec_Mode uc_stvec) = TV_Direct;
  (* no M-level interrupt is enabled-but-undelegated ... *)
  uc_mm  : and_vec uc_mie (not_vec uc_mideleg) = zeros' 64;
  (* ... and no delegated S-level interrupt is pending-and-enabled: the
     interrupt dispatcher never fires during user execution *)
  uc_s0  : and_vec (s_mip_bits uc_mip uc_meip uc_seip)
             (and_vec uc_mie uc_mideleg) = zeros' 64;
  (* every exception user execution can raise is delegated to S-mode *)
  uc_del : forall e : ExceptionType, user_exc e = true ->
             bit_to_bool (access_vec_dec uc_medeleg
               (uint (exceptionType_bits_forwards e))) = true
}.

(* ===================================================================== *)
(* §3 mstatus pins.  User execution never writes mstatus (only traps do,   *)
(* and they exit the loop), so these ride through every retired step.      *)
(* ===================================================================== *)

(* in the user phase: SXL fixed 64-bit, no M-mode memory-privilege override,
   MXR off (so a load's permission check is a pure function of the leaf's
   R bit -- no executable-implies-readable special case to track) *)
Definition user_mstatus_ok (ms : mword 64) : Prop :=
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true.

(* after the trap: same pins, plus what the trap transform wrote --
   SPP = User (we trapped FROM user) and SIE = 0 (interrupts masked,
   exactly the state the kernel's S-mode leaves require) *)
Definition trap_mstatus_ok (ms : mword 64) : Prop :=
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_SPP ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false.

(* ===================================================================== *)
(* §4 The frames and the capstone.                                         *)
(* ===================================================================== *)
Section UserExec.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  Local Notation dq := (uc_dq C).
  Local Notation dqc := (uc_dqc C).

  (* the loop-constant config cells (fraction [dqc]: never written during
     user execution; the complementary fraction stays with the kernel).
     satp / tlb / pmp cells live inside [upt_inv] (UserPt.v). *)
  Definition user_cfg : iProp Σ :=
    (stvec ↦ᵣ{ dqc } uc_stvec C ∗
     mie ↦ᵣ{ dqc } uc_mie C ∗
     mideleg ↦ᵣ{ dqc } uc_mideleg C ∗
     medeleg ↦ᵣ{ dqc } uc_medeleg C ∗
     mip ↦ᵣ{ dqc } uc_mip C ∗
     sig_meip ↦ᵣ{ dqc } uc_meip C ∗
     sig_seip ↦ᵣ{ dqc } uc_seip C ∗
     menvcfg ↦ᵣ{ dqc } MENVCFG_S ∗
     senvcfg ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     mstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 64) ∗
     sstateen0 ↦ᵣ{ dqc } (mword_of_int 0 : mword 32))%I.

  (* ------------------------------------------------------------------- *)
  (* The loop invariant: A VALID USER-MODE EXECUTION STATE.  Everything an *)
  (* instruction can change is existential: the pc (ANY value -- fetching  *)
  (* from a non-canonical or unmapped address page-faults safely), the     *)
  (* register file, the trap CSRs (stale until the next trap writes them), *)
  (* mstatus up to its pins, and -- inside [upt_inv] -- the TLB and the    *)
  (* mapped pages' contents.                                               *)
  (* ------------------------------------------------------------------- *)
  Definition user_inv : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v va : mword 64)
       (g : gmap regidx (mword 64)),
      ⌜user_mstatus_ok ms_v⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ User ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      pc_is va ∗
      gpr_file g ∗
      upt_inv pt ∗
      user_cfg)%I.

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
       (g : gmap regidx (mword 64)),
      ⌜trap_mstatus_ok ms_v⌝ ∗
      hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
      cur_privilege ↦ᵣ Supervisor ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      pc_is (stvec_base (uc_stvec C)) ∗
      gpr_file g ∗
      upt_inv pt ∗
      user_cfg)%I.

  (* the assumed kernel re-entry contract: the handler at stvec (uservec)
     handles ANY trapped-out-of-user machine *)
  Definition stvec_handler_wp E (Φ : mval -> iProp Σ) : iProp Σ :=
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})%I.

  (* ------------------------------------------------------------------- *)
  (* The step obligation: ONE machine step from the invariant, with both   *)
  (* continuations under a later (exactly what the step engines provide    *)
  (* after consuming one physical step).  The conjunction is ADDITIVE: the *)
  (* prover case-analyzes the machine first and selects exactly one arm.   *)
  (* ------------------------------------------------------------------- *)
  Definition user_step_obligation E (Φ : mval -> iProp Σ) : iProp Σ :=
    (□ (user_inv -∗
        ▷ ((user_inv -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
           (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}))%I.

  (* ------------------------------------------------------------------- *)
  (* The capstone: safety of arbitrary user-mode execution, by Löb.        *)
  (* ------------------------------------------------------------------- *)
  Theorem wp_user_exec E (Φ : mval -> iProp Σ) :
    user_step_obligation E Φ -∗
    user_inv -∗
    stvec_handler_wp E Φ -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros "#Hstep".
    iLöb as "IH".
    iIntros "HP Htrap".
    iApply ("Hstep" with "HP").
    iNext. iSplit.
    - iIntros "HP". iApply ("IH" with "HP Htrap").
    - iExact "Htrap".
  Qed.

End UserExec.
