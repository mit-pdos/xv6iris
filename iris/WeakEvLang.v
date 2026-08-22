(** * WeakEvLang.v — the EVENT-GRANULAR weak-memory language (spike S1)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    2026-08-14 "expression-resident monad" section); worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S1).

    [WeakLang.wprim_step]'s hart arm runs a WHOLE INSTRUCTION
    ([WeakInterp.wrun (riscv_step tick)]) in one language step.  THIS
    language's hart arm runs ONE EVENT of the Sail interaction monad — the
    same case analysis [WeakSailLTS.sail_mstep] performs, but WITHOUT the two
    oracles ([psail]'s [sp_dev] stream/fabric and [sp_irq]), because the
    device fabric is σ's and the residual monad is the EXPRESSION's.

    ------------------------------------------------------------------------
    THE PLACEMENT RULE (design doc, revised).  Control state goes in the
    EXPRESSION exactly where control flow is MODEL-DEFINED, and in σ where it
    is MEMORY-DEFINED.  INTER-instruction control flow is memory-defined (the
    next instruction comes from a fetch through a page table into mutable
    memory), so the boundary stays a boring token [ELoop].  INTRA-instruction
    control flow is model-defined (the continuation IS the Sail monad value
    [riscv_step tick] hands out), so it rides in [ECycle], is consumed
    monotonically, and WP-of-an-instruction becomes proof by SYNTACTIC
    DESCENT on that argument.  Devices have neither a fetch nor a preemption
    problem, so [EDisk] carries its whole operation state — which, since M5,
    is a RESIDUAL MONAD exactly as a hart's is ([VirtioProg.DM]).

      σ           = [WeakLang.wgstate] VERBATIM (no new fields, no new
                    ghosts, [WeakGhost.weak_state_interp] unchanged);
      [ELoop g c] = hart [c] at an instruction boundary;
      [ECycle g c m fn] = hart [c] executing one instruction, [m] the
                    residual monad and [fn] the parked second fence;
      [EDisk g dp dws] = the disk agent: the RESIDUAL DEVICE PROGRAM (M5 —
                    [VirtioProg.virtio_prog], [None] between bursts) and its
                    own view — the pf [PDisk] agent field for field;
      [EUart g] / [EPlic g] / [EPower] = as in [WeakLang].

    ------------------------------------------------------------------------
    DESIGN DELTAS AND RECORDED DECISIONS (read before extending).

    (D1) THE DEVICE ACCESSORS ARE THE **PARTIAL** ONES.
         [DevModel.dev_read]/[dev_write] decline a bad width or an undecoded
         offset inside a device window, and this language is STUCK there —
         it does NOT use [WeakSailLTS]'s totalized [dev_read_t]/[dev_write_t].
         Justified by the design's "stuck-is-fine": nothing in this tower ever
         has to know that an instruction COMPLETES (there is no [sail_live],
         no [sail_shaped], no reconstruction), so a stuck node costs nothing.

    (D2) THE STORE ARM **COMPUTES** THE MESSAGE CLASS
         ([WeakInterp.wm_class_of ak ws] at the storing hart's own [wstate]),
         so there is no free class binder and [cls_canonical]/the retag die by
         construction (design doc, decision 2 of three).  The CONDITIONAL
         write computes it the same way, and gets [WCexcl] — [wm_class_of]
         returns [WCexcl] exactly at [ak_latest], which is what an exclusive
         access kind sets.

    (D3) THE RMW IS SPLIT (design [weak-memory-rmw-split.md], slice S3): an
         exclusive read is ONE event ([LExLoad], ordinary read semantics plus
         the agent-local reservation) and a conditional write is ANOTHER
         ([LExStore], ordinary write semantics plus the per-byte window
         check at the reservation).  The window's intervening nodes take the
         ordinary node rules; a dangling exclusive read is a LEGAL trace; and
         the conditional-write node carries §5's silent RETRY self-loop so
         that a dirtied window is not a stuck node.

    (D4) INTERRUPT DELIVERY IS **ONLY** THE PLIC THREAD'S ARM
         ([RiscvLang.plic_step]'s wire write, spelled here as [eplic_step]).
         There is NO hart-side delivery event: delivery is an asynchronous
         cross-thread register write and fires whatever expression the hart
         is sitting at.  (The pre-revision draft had it twice; the redundancy
         is gone.)

    (D5) THE PARKED FENCE GATES EVERYTHING: while [fn] is [Some _] the ONLY
         move [ECycle g c m fn] has is to fire it.  So the two halves of a
         [fence.tso] cannot be separated by any other event of that hart, and
         the whole park/fire discipline is local to one instruction's cycle —
         which is why [ECycle _ _ (Ret _) fn] pops to [ELoop] only at
         [fn = None]. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
(* THE DEVICE PROGRAM (M5).  Required BEFORE [WeakInterpProj] on purpose:
   [VirtioProg] has its own [wbytes] (the device's little-endian field
   bytes), and every [wbytes] in THIS file is the hart-side
   [WeakInterpProj.wbytes], so the later [Require] must be the one that
   wins. *)
Require Import VirtioProg.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The expressions

    [RiscvLang.mexpr] with the hart's boundary token SPLIT ([ELoop] /
    [ECycle]) and the disk's token carrying its operation state.  The
    generation index and the corpse discipline are unchanged, so the whole
    power/crash machinery transfers: [ECycle] simply gets the corpse arm
    [ELoop] already had. *)

Inductive eexpr :=
  | Sail   (gen : nat) (cpu : CPU) (m : M unit)
           (fn : option (bool * bool * bool * bool))
  | EUart  (gen : nat)
  | EDisk  (gen : nat) (dp : option (DM dres)) (dws : wstate)
  | EPlic  (gen : nat)
  | EPower.

(** THE BOUNDARY VALUE, and the mid-instruction one.  [ELoop] is not a
    constructor any more: the boundary IS the hart sitting at the monad's
    own terminal value, which is unique because the result type is [unit].
    Both are kept as (transparent) DEFINITIONS so that every statement of
    the spike files keeps elaborating verbatim, and so that [ELoop gen] may
    still be applied to one argument ([epower_fork]'s [<$>]). *)
Definition ELoop (gen : nat) (cpu : CPU) : eexpr :=
  Sail gen cpu (Interface.Ret tt) None.
Definition ECycle (gen : nat) (cpu : CPU) (m : M unit)
    (fn : option (bool * bool * bool * bool)) : eexpr := Sail gen cpu m fn.

Definition eval := Empty_set.
Definition eobs := Empty_set.
Definition eof_val (v : eval) : eexpr := match v with end.
Definition eto_val (_ : eexpr) : option eval := None.

(** The thread pool a fresh era forks: one hart thread per CPU, the two
    device threads and the PLIC.  The disk's expression carries the EMPTY
    burst and a FRESH view — the two clauses the pre-revision [eboot_facts]
    had to put on σ. *)
Definition epower_fork (gen : nat) : list eexpr :=
  (ELoop gen <$> enum CPU) ++ [EUart gen; EDisk gen None ws_init; EPlic gen].

(* ====================================================================== *)
(** ** 2. σ-updates

    σ is [WeakLang.wgstate] verbatim, so an arm's effect is one of five
    named shapes.  Keeping them named (rather than writing [WGState …] at
    each arm) is what lets S4's lifting rules state ONE interpretation-closing
    lemma per shape. *)

Definition ewg_reg (σ : wgstate) (c : CPU) (rs : regstate) : wgstate :=
  WGState (<[c := rs]> (wgregs σ)) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
          (wggen σ) (wgpow σ) (wgib σ).

Definition ewg_dev (σ : wgstate) (d : dev_state) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) d (wggen σ) (wgpow σ) (wgib σ).

Definition ewg_ws (σ : wgstate) (c : CPU) (ws : wstate) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (<[c := ws]> (wgws σ)) (wgdev σ)
          (wggen σ) (wgpow σ) (wgib σ).

Definition ewg_store (σ : wgstate) (c : CPU) (ws : wstate) (lg : list wmsg)
    : wgstate :=
  WGState (wgregs σ) (wgimg σ) lg (<[c := ws]> (wgws σ)) (wgdev σ)
          (wggen σ) (wgpow σ) (wgib σ).

(** THE REGS + VIEW + LOG SHAPE.  It was called [ewg_rmw] while the FUSED
    RMW arm was its only producer; after the RMW SPLIT no arm has it (the
    conditional write is an ordinary [ewg_store]), but the hart-side
    state-interpretation accessor [WeakEvLift.weak_state_interp_rmw] still
    needs it: closing the interpretation after a silent stretch must let the
    register file, the view and the log all move at once. *)
Definition ewg_regwslog (σ : wgstate) (c : CPU) (rs : regstate) (ws : wstate)
    (lg : list wmsg) : wgstate :=
  WGState (<[c := rs]> (wgregs σ)) (wgimg σ) lg (<[c := ws]> (wgws σ))
          (wgdev σ) (wggen σ) (wgpow σ) (wgib σ).

Definition ewg_log (σ : wgstate) (lg : list wmsg) : wgstate :=
  WGState (wgregs σ) (wgimg σ) lg (wgws σ) (wgdev σ) (wggen σ) (wgpow σ) (wgib σ).

(** *** D3: THE INSTRUCTION-BITS FIELD

    The announce carries a [bvn] — 16 bits for an RVC halfword, 32 for a base
    word — and we ZERO-EXTEND it to [mword 32].  That is lossless and
    unambiguous, because an RVC halfword has [bits[1:0] <> 0b11]
    ([WeakDeps.ib_compressed] is exactly that test), so the decoder can tell
    the two apart from the 32-bit value alone. *)
Notation oib32 := WeakLang.ibch (only parsing).

Definition ib_of_bvn (o : bvn) : SailStdpp.Values.mword 32 :=
  Z_to_bv 32 (bvn_unsigned o).

(** The sixth named σ-shape: the hart's announced instruction bits move, and
    NOTHING ELSE does.  [WeakGhost.weak_state_interp] does not mention
    [wgib], so this shape is INVISIBLE to the state interpretation — which is
    what [WeakEvLift.weak_state_interp_ib] records and what lets the announce
    node stay silent for the reflective cursor (D3 acceptance test). *)
Definition ewg_ib (σ : wgstate) (c : CPU) (v : oib32) : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ) (wggen σ)
          (wgpow σ) (<[c := v]> (wgib σ)).

Lemma ewg_ib_regs σ c v : wgregs (ewg_ib σ c v) = wgregs σ.
Proof. reflexivity. Qed.
Lemma ewg_ib_log σ c v : wglog (ewg_ib σ c v) = wglog σ.
Proof. reflexivity. Qed.
Lemma ewg_ib_ws σ c v : wgws (ewg_ib σ c v) = wgws σ.
Proof. reflexivity. Qed.
Lemma ewg_ib_dev σ c v : wgdev (ewg_ib σ c v) = wgdev σ.
Proof. reflexivity. Qed.
Lemma ewg_ib_img σ c v : wgimg (ewg_ib σ c v) = wgimg σ.
Proof. reflexivity. Qed.
Lemma ewg_ib_at σ c v : wgib (ewg_ib σ c v) c = v.
Proof. apply gib_insert_eq. Qed.
Lemma ewg_ib_ne σ c v c' : c' ≠ c -> wgib (ewg_ib σ c v) c' = wgib σ c'.
Proof. apply gib_insert_ne. Qed.

(** *** D3-2: the two COMBINED shapes the dependency labels need.

    A hart's register write may now ALSO move its view (PARM's
    [step_assign]: the destination register inherits the join of its
    sources' views), and the announce moves both the bits and the view (it
    RESETS [w_ldv], PARM's [res] bank, at every instruction start). *)
Definition ewg_regws (σ : wgstate) (c : CPU) (rs : regstate) (ws : wstate)
    : wgstate :=
  WGState (<[c := rs]> (wgregs σ)) (wgimg σ) (wglog σ) (<[c := ws]> (wgws σ))
          (wgdev σ) (wggen σ) (wgpow σ) (wgib σ).

Definition ewg_ibws (σ : wgstate) (c : CPU) (v : oib32) (ws : wstate)
    : wgstate :=
  WGState (wgregs σ) (wgimg σ) (wglog σ) (<[c := ws]> (wgws σ)) (wgdev σ)
          (wggen σ) (wgpow σ) (<[c := v]> (wgib σ)).

(* ====================================================================== *)
(** ** 2b. D3-2: WHICH REGISTER WRITE CARRIES A DEPENDENCY

    [WeakDeps.deps_of_bits] says which ARCHITECTURAL register the current
    instruction writes and which sources it inherits.  The Sail node stream
    says which SAIL register a [RegWrite] node targets.  This section is the
    join of the two, and it is the whole of the "which node emits [LRegW]"
    question.

    THREE KINDS, and the classification is TOTAL:
      [ERWreg rd srcs] — this node writes the instruction's architectural
        destination [rd]; the label is [LRegW rd srcs] and the view effect is
        PARM's [step_assign] ([regw_post], an OVERWRITE);
      [ERWctrl srcs] — this node writes [nextPC].  THE CONTROL VIEW GOES
        HERE, not at [BranchAnnounce] (which the taken arm alone emits) and
        not at the announce (which would need [LInstr] to carry an operand
        list, i.e. a Layer-1 label change).  [write_reg nextPC] is emitted by
        [riscv_step]'s decode preamble BEFORE [execute], unconditionally and
        on both arms of every branch, so it is exactly PARM's [step_if]
        position — and for a non-branch instruction [deps_ctrl] is [[]], so
        the arm is a no-op.  Recorded as deviation D-9.
      [ERWnone] — every other register write (CSRs, [PC], [minstret], and a
        GPR write that is not the architectural [rd], e.g. the walker's or a
        trap's): [LSilent], the safe under-approximation (D-4). *)
Inductive erw_kind :=
| ERWnone
| ERWreg (rd : wreg) (srcs : list dsrc)
| ERWctrl (srcs : list dsrc).

(** The Sail register name of an architectural GPR.  [x1 .. x31] are
    [num_of_register_bitvector_64] [16 .. 46] — the model has NO [x0]
    register (it is hardwired), which is exactly why [x0] can never be a
    dependency destination. *)
Definition ereg_gpr_num (r : register) : option wreg :=
  match r with
  | R_bitvector_64 rb =>
      let n := num_of_register_bitvector_64 rb in
      if decide (16 <= n /\ n <= 46)%Z then Some (Z.to_nat (n - 15)) else None
  | _ => None
  end.

(** ... AND THE NON-GPR DESTINATIONS THE DEPENDENCY TRACK KNOWS: the CSRs of
    [WeakDeps]' table, as its pseudo-registers [32 .. 52] (DEC-6, generalising
    DEC-5's [satp] / route-b §4e).  A CSR is not an RVWMO register, but a
    value that reaches one decides something the hart later does — the
    translation context ([satp], via the [sfence.vma] discipline), the
    [sret]/[mret] resumption PC ([sepc]/[mepc]), the trapframe pointer
    ([sscratch]) — so each gets provenance and [WeakRvwmoConf] draws the
    edges.  This is the SAIL-SIDE half of the table: the model has no
    [sstatus]/[sie]/[sip] register (they are views of [mstatus]/[mie]/[mip],
    and a [csrw sstatus,a5] emits [RegWrite mstatus]), which is exactly why
    [WeakDeps.csr_reg] gives each S/M pair ONE pseudo-register; [pmpaddr0]
    and [pmpcfg0] are elements of the model's [pmpaddr_n]/[pmpcfg_n] vector
    registers, whose whole-vector write is the node that fires.

    The arm fires only where the decoder ALSO named that pseudo-register as
    a destination ([erw_of] compares the two), so every CSR write of an
    instruction that has no CSR role is still [ERWnone] (D-4). *)
Definition ereg_csr_num (r : register) : option wreg :=
  match r with
  | R_bitvector_64 rb =>
      match rb with
      | satp     => Some (wcsr SATP)
      | sepc     => Some (wcsr SEPC)
      | mepc     => Some (wcsr MEPC)
      | sscratch => Some (wcsr SSCRATCH)
      | mscratch => Some (wcsr MSCRATCH)
      | stvec    => Some (wcsr STVEC)
      | mtvec    => Some (wcsr MTVEC)
      | mstatus  => Some (wcsr MSTATUS)   (* [sstatus] is a view of it *)
      | mie      => Some (wcsr MIE)       (* [sie]     is a view of it *)
      | mip      => Some (wcsr MIP)       (* [sip]     is a view of it *)
      | medeleg  => Some (wcsr MEDELEG)
      | mideleg  => Some (wcsr MIDELEG)
      | menvcfg  => Some (wcsr MENVCFG)
      | mhartid  => Some (wcsr MHARTID)
      | mtime    => Some (wcsr TIME)      (* the [time] CSR's backing store *)
      | scause   => Some (wcsr SCAUSE)
      | stval    => Some (wcsr STVAL)
      | stimecmp => Some (wcsr STIMECMP)
      | _ => None
      end
  | R_bitvector_32 rb =>
      match rb with mcounteren => Some (wcsr MCOUNTEREN) | _ => None end
  | R_vector_64_bitvector_64 _ => Some (wcsr PMPADDR0)  (* [pmpaddr_n] *)
  | R_vector_64_bitvector_8  _ => Some (wcsr PMPCFG0)   (* [pmpcfg_n]  *)
  | _ => None
  end.

Definition ereg_num (r : register) : option wreg :=
  match ereg_csr_num r with Some n => Some n | None => ereg_gpr_num r end.

(** *** DEC-7 (B2e-3b slice 2a): THE SOURCES ARE DYNAMIC

    [WeakDeps.deps_of_bits] decodes RVWMO's SYNTACTIC operand roles from the
    instruction word, and that is still the oracle for the DESTINATIONS (which
    node is [rd], DEC-4's join) and for the node CLASSIFICATION (is this a
    control node? does the result carry [DLdRes]?).  It is NO LONGER the
    oracle for the SOURCE lists.

    WHY.  Provenance soundness — "two runs of the same instruction from
    regstates that agree on the named sources emit the same label" — needs
    the named sources to COVER the registers the Sail semantics actually
    reads, and the decoder cannot see those: a memory access consults [satp]
    and [mstatus] for translation and permissions, [sret] consults [sepc],
    and no encoding field names them.  So the sources are taken from the
    per-instruction READ SET the machine accumulates ([WeakLang.ibch]'s
    [ib_rds], appended to at every [RegRead] of a carrier register and reset
    at the two instruction boundaries), and coverage holds BY CONSTRUCTION.

    HONESTY.  The dynamic set is a SUPERSET of the decoded one on the image's
    forms (the tests below), so every RVWMO syntactic dependency is still
    drawn; the extra ones are CSR-mediated chains, and an edge from a CSR
    exists only when that CSR's own provenance is non-empty — a chain real
    hardware also orders (CSR writes serialize; the [sfence.vma] discipline).
    The decoder's source lists stay in [WeakDeps] as the syntactic reference
    and as the [vm_compute] cross-checks of this section.

    TWO THINGS THE DECODER STILL DECIDES.
      - [DLdRes]: whether the instruction's result carries the LOAD RESULT
        (PARM's [res]) is a role question (DEC-2/DEC-4), not a register one,
        so it is read off the decoded list and prepended unchanged.
      - The CONTROL GATE: [nextPC] is written by EVERY instruction, so
        handing every instruction's read set to [ERWctrl] would make each of
        them a control-dependency point — far beyond RVWMO and beyond
        hardware.  The decoder says which instructions are control nodes
        (its [deps_ctrl] is non-empty exactly at a conditional branch and an
        indirect jump, [sret]/[mret] included since DEC-6), and only there is
        the read set used. *)

(** Does the decoded source list carry the load result? *)
Fixpoint has_ldres (l : list dsrc) : bool :=
  match l with
  | [] => false
  | DLdRes :: _ => true
  | _ :: t => has_ldres t
  end.

Lemma has_ldres_intro l : DLdRes ∈ l -> has_ldres l = true.
Proof.
  induction l as [|a l IH]; [by intros ?%elem_of_nil|].
  intros [Heq|Hin]%elem_of_cons.
  - subst a. reflexivity.
  - destruct a; [by apply IH|reflexivity].
Qed.

(** THE DYNAMIC SOURCE LIST: the decoded list's [DLdRes] flag, then one
    [DReg] per DISTINCT register the instruction has read so far. *)
Definition erw_srcs (dec : list dsrc) (rds : list wreg) : list dsrc :=
  (if has_ldres dec then [DLdRes] else []) ++ (DReg <$> remove_dups rds).

Lemma erw_srcs_ldres dec rds : DLdRes ∈ dec -> DLdRes ∈ erw_srcs dec rds.
Proof.
  intros Hin. rewrite /erw_srcs (has_ldres_intro _ Hin).
  apply elem_of_app. left. apply elem_of_list_singleton. reflexivity.
Qed.

Lemma erw_srcs_reg dec rds (r : wreg) :
  r ∈ rds -> DReg r ∈ erw_srcs dec rds.
Proof.
  intros Hin. rewrite /erw_srcs. apply elem_of_app. right.
  apply elem_of_list_fmap. exists r. split; [reflexivity|].
  by apply (proj2 (elem_of_remove_dups rds r)).
Qed.

(** THE COVERAGE TEST, once and for all: every DECODED source is a DYNAMIC
    source as soon as the run has read the register it names.  This is the
    general form of the [vm_compute] witnesses below. *)
Lemma erw_srcs_covers dec rds (s : dsrc) :
  s ∈ dec -> (forall r : wreg, s = DReg r -> r ∈ rds) ->
  s ∈ erw_srcs dec rds.
Proof.
  intros Hin Hr. destruct s as [r|].
  - apply erw_srcs_reg, Hr. reflexivity.
  - by apply erw_srcs_ldres.
Qed.

(** ... and the read set only ever grows, so neither does the source list
    shrink. *)
Lemma erw_srcs_mono dec rds rds' (s : dsrc) :
  rds ⊆ rds' -> s ∈ erw_srcs dec rds -> s ∈ erw_srcs dec rds'.
Proof.
  intros Hsub [Hs|Hs]%elem_of_app.
  - apply elem_of_app. by left.
  - apply elem_of_list_fmap in Hs as (r & Hseq & Hr).
    apply (proj1 (elem_of_remove_dups rds r)) in Hr. subst s.
    apply erw_srcs_reg. unfold subseteq, list_subseteq in Hsub.
    exact (Hsub r Hr).
Qed.

(** THE ACCUMULATOR at a [RegRead] node: the register is appended when it is
    a dependency CARRIER — a GPR [x1..x31] or one of [WeakDeps]' CSR
    pseudo-registers.  Everything else the Sail model reads (PC, [nextPC],
    [cur_privilege], [misa], the counters, …) is NOT a carrier: no value
    flows through it that RVWMO or the privileged spec would order on, and
    the soundness lemma quantifies over regstates that AGREE on all of them
    ([WeakEvProv.dreg_agree]'s non-carrier clause). *)
Definition ib_rd (i : oib32) (r : register) : oib32 := ib_read i (ereg_num r).

Lemma ib_rd_bits i r : ib_bits (ib_rd i r) = ib_bits i.
Proof. apply ib_read_bits. Qed.

(** One node, one candidate destination: does this [RegWrite]'s register
    match the one the decoded role names, and with which sources? *)
Definition erw_dest (rds : list wreg) (r : register)
    (d : option (wreg * list dsrc)) : erw_kind :=
  match d with
  | Some (rd, srcs) =>
      match ereg_num r with
      | Some n => if decide (n = rd) then ERWreg rd (erw_srcs srcs rds) else ERWnone
      | None => ERWnone
      end
  | None => ERWnone
  end.

(** DEC-6: A ZICSR ACCESS HAS TWO DESTINATIONS — the CSR ([deps_rd]) and,
    when [rd <> x0], the GPR that receives the CSR's OLD value
    ([deps_rd2]).  They are distinct registers, so trying the second only
    where the first did not match is exactly right, and for every
    non-[ORcsr] role [deps_rd2] is [None] and nothing changes. *)
Definition erw_of (role : op_roles) (rds : list wreg) (r : register)
    : erw_kind :=
  if register_beq r (R_bitvector_64 nextPC)
  then ERWctrl (match deps_ctrl role with
                | [] => []              (* DEC-7: not a control node *)
                | dec => erw_srcs dec rds
                end)
  else
    match erw_dest rds r (deps_rd role) with
    | ERWnone => erw_dest rds r (deps_rd2 role)
    | k => k
    end.

(** The label and the view effect of a classified register write — one
    function each, shared by the language and the instance. *)
Definition erw_label (k : erw_kind) : wlabel :=
  match k with
  | ERWnone => LSilent
  | ERWreg rd srcs => LRegW rd srcs
  | ERWctrl srcs => LCtrl srcs
  end.

Definition erw_ws (ws : wstate) (k : erw_kind) : wstate :=
  match k with
  | ERWnone => ws
  | ERWreg rd srcs => regw_post ws rd (srcs_view ws srcs)
  | ERWctrl srcs => ctrl_post ws (srcs_view ws srcs)
  end.

Lemma erw_ws_depmove ws k : ws_depmove ws (erw_ws ws k).
Proof.
  destruct k; simpl;
    [reflexivity|apply regw_post_depmove|apply ctrl_post_depmove].
Qed.

(** THE σ-EFFECT of a register write.  [ERWnone] must NOT go through
    [ewg_regws] with an unchanged view: [<[c := wgws σ c]> (wgws σ) = wgws σ]
    is pointwise, not syntactic, and this tree assumes no functional
    extensionality — hence the explicit split. *)
Definition ewg_rw (σ : wgstate) (c : CPU) (rs : regstate) (k : erw_kind)
    : wgstate :=
  match k with
  | ERWnone => ewg_reg σ c rs
  | _ => ewg_regws σ c rs (erw_ws (wgws σ c) k)
  end.

Lemma ewg_rw_img σ c rs k : wgimg (ewg_rw σ c rs k) = wgimg σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_log σ c rs k : wglog (ewg_rw σ c rs k) = wglog σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_dev σ c rs k : wgdev (ewg_rw σ c rs k) = wgdev σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_pow σ c rs k : wgpow (ewg_rw σ c rs k) = wgpow σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_gen σ c rs k : wggen (ewg_rw σ c rs k) = wggen σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_ib σ c rs k : wgib (ewg_rw σ c rs k) = wgib σ.
Proof. by destruct k. Qed.
Lemma ewg_rw_ws σ c rs k : wgws (ewg_rw σ c rs k) c = erw_ws (wgws σ c) k.
Proof. destruct k; simpl; [reflexivity|by rewrite gws_insert_eq..]. Qed.
Lemma ewg_rw_ws_ne σ c rs k c' :
  c' <> c -> wgws (ewg_rw σ c rs k) c' = wgws σ c'.
Proof.
  intros Hne. destruct k; simpl; [reflexivity|by rewrite gws_insert_ne..].
Qed.
Lemma ewg_rw_regs σ c rs k : wgregs (ewg_rw σ c rs k) = <[c := rs]> (wgregs σ).
Proof. by destruct k. Qed.

(** *** NON-VACUITY, by [vm_compute] on real encodings.

    These are the join in action: the decoder's architectural [rd] against
    the Sail register the node targets.  Without them a silent regression
    (a wrong bit field, a wrong [num_of_register_bitvector_64] window) would
    turn every [LRegW] back into [LSilent] and the whole dependency track
    into a no-op that still builds. *)

(* [lw a5,0(a5)] = 0x0007a783: the write of x15 IS the destination, and it
   inherits the LOAD RESULT (PARM's [res]) AND the load's ADDRESS SOURCES
   (F5' / DEC-4 — rules 9 and 10 composed) — this is the ppo 9/10/11 chain's
   first link.  Here rs1 = rd = x15; [ld a4,0(a5)] below separates them. *)
Example erw_of_lw_rd :
  erw_of (deps_of_bits (dbits 0x0007a783)) [15%nat] (R_bitvector_64 x15)
  = ERWreg 15 [DLdRes; DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

Example erw_of_ld_rd :
  erw_of (deps_of_bits (dbits 0x0007b703)) [15%nat] (R_bitvector_64 x14)
  = ERWreg 14 [DLdRes; DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* ... and a write of any OTHER GPR in the same instruction is silent *)
Example erw_of_lw_other :
  erw_of (deps_of_bits (dbits 0x0007a783)) [15%nat] (R_bitvector_64 x14) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* a CSR write is silent, whatever the instruction (deviation D-4) *)
Example erw_of_csr :
  erw_of (deps_of_bits (dbits 0x0007a783)) [15%nat] (R_bitvector_64 mstatus) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* DEC-5 — THE SATP-PROVENANCE EDGE's emission half.  [csrw satp,a5]
   = 0x18079073: the model's [RegWrite satp] node IS the destination, and it
   inherits [a5]'s provenance. *)
Example erw_of_csrw_satp :
  erw_of (deps_of_bits (dbits 0x18079073)) [15%nat] (R_bitvector_64 satp)
  = ERWreg wsatp [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* [csrr a4,satp] = 0x18002773: the transfer back out, into [a4]. *)
Example erw_of_csrr_satp :
  erw_of (deps_of_bits (dbits 0x18002773)) [wsatp] (R_bitvector_64 x14)
  = ERWreg 14 [DReg wsatp].
Proof. vm_compute. reflexivity. Qed.

(* ... and the [satp] node of an instruction that is NOT a satp write stays
   silent, as does a satp write's own GPR node. *)
Example erw_of_satp_other_instr :
  erw_of (deps_of_bits (dbits 0x0007a783)) [15%nat] (R_bitvector_64 satp) = ERWnone.
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrw_satp_gpr :
  erw_of (deps_of_bits (dbits 0x18079073)) [15%nat] (R_bitvector_64 x15) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* DEC-6 — THE REST OF THE TABLE.  [csrw sstatus,a5] = 0x10079073 writes the
   model's [mstatus] node ([sstatus] is a VIEW of it), and the decoder named
   the same shared pseudo-register, so the two meet. *)
Example erw_of_csrw_sstatus :
  erw_of (deps_of_bits (dbits 0x10079073)) [15%nat] (R_bitvector_64 mstatus)
  = ERWreg (wcsr MSTATUS) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* [csrw sepc,a5] = 0x14179073 and [csrw mepc,a5] = 0x34179073 — the two
   resumption-PC CSRs, whose provenance [sret]/[mret] turn into control. *)
Example erw_of_csrw_sepc :
  erw_of (deps_of_bits (dbits 0x14179073)) [15%nat] (R_bitvector_64 sepc)
  = ERWreg (wcsr SEPC) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrw_mepc :
  erw_of (deps_of_bits (dbits 0x34179073)) [15%nat] (R_bitvector_64 mepc)
  = ERWreg (wcsr MEPC) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* [csrw sscratch,a0] = 0x14051073 — [uservec]'s first instruction. *)
Example erw_of_csrw_sscratch :
  erw_of (deps_of_bits (dbits 0x14051073)) [10%nat] (R_bitvector_64 sscratch)
  = ERWreg (wcsr SSCRATCH) [DReg 10%nat].
Proof. vm_compute. reflexivity. Qed.

(* [csrw stvec,a5] = 0x10579073, [csrw stimecmp,a5] = 0x14d79073, and the
   two VECTOR-REGISTER CSRs [csrw pmpaddr0,a5] = 0x3b079073 /
   [csrw pmpcfg0,a5] = 0x3a079073, whose model nodes are the whole-vector
   writes [pmpaddr_n] / [pmpcfg_n]. *)
Example erw_of_csrw_stvec :
  erw_of (deps_of_bits (dbits 0x10579073)) [15%nat] (R_bitvector_64 stvec)
  = ERWreg (wcsr STVEC) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrw_stimecmp :
  erw_of (deps_of_bits (dbits 0x14d79073)) [15%nat] (R_bitvector_64 stimecmp)
  = ERWreg (wcsr STIMECMP) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrw_pmpaddr0 :
  erw_of (deps_of_bits (dbits 0x3b079073)) [15%nat] (R_vector_64_bitvector_64 pmpaddr_n)
  = ERWreg (wcsr PMPADDR0) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrw_pmpcfg0 :
  erw_of (deps_of_bits (dbits 0x3a079073)) [15%nat] (R_vector_64_bitvector_8 pmpcfg_n)
  = ERWreg (wcsr PMPCFG0) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* [csrw mcounteren,a5] = 0x30679073 — a 32-bit model register. *)
Example erw_of_csrw_mcounteren :
  erw_of (deps_of_bits (dbits 0x30679073)) [15%nat] (R_bitvector_32 mcounteren)
  = ERWreg (wcsr MCOUNTEREN) [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* A PURE READ transfers the CSR's provenance into the GPR: [csrr a4,sepc]
   = 0x14102773; the [sepc] node of that instruction stays silent (it writes
   no CSR). *)
Example erw_of_csrr_sepc :
  erw_of (deps_of_bits (dbits 0x14102773)) [wcsr SEPC] (R_bitvector_64 x14)
  = ERWreg 14 [DReg (wcsr SEPC)].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrr_sepc_csrnode :
  erw_of (deps_of_bits (dbits 0x14102773)) [wcsr SEPC] (R_bitvector_64 sepc) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* THE TWO-DESTINATION FORM (DEC-6): [csrrci a5,sstatus,2] = 0x100177f3.
   BOTH nodes fire — the CSR from [deps_rd], [a5] from [deps_rd2]. *)
Example erw_of_csrrci_sstatus_csr :
  erw_of (deps_of_bits (dbits 0x100177f3)) [wcsr MSTATUS] (R_bitvector_64 mstatus)
  = ERWreg (wcsr MSTATUS) [DReg (wcsr MSTATUS)].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_csrrci_sstatus_gpr :
  erw_of (deps_of_bits (dbits 0x100177f3)) [wcsr MSTATUS] (R_bitvector_64 x15)
  = ERWreg 15 [DReg (wcsr MSTATUS)].
Proof. vm_compute. reflexivity. Qed.
(* ... and an unrelated node of the same instruction is still silent. *)
Example erw_of_csrrci_sstatus_other :
  erw_of (deps_of_bits (dbits 0x100177f3)) [wcsr MSTATUS] (R_bitvector_64 x14) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* [sret] = 0x10200073 / [mret] = 0x30200073: the CONTROL node carries the
   resumption-PC CSR's provenance (this is what reaches [ds_ctl]), and the
   instruction writes no destination at all. *)
Example erw_of_sret_nextpc :
  erw_of (deps_of_bits (dbits 0x10200073)) [wcsr SEPC] (R_bitvector_64 nextPC)
  = ERWctrl [DReg (wcsr SEPC)].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_mret_nextpc :
  erw_of (deps_of_bits (dbits 0x30200073)) [wcsr MEPC] (R_bitvector_64 nextPC)
  = ERWctrl [DReg (wcsr MEPC)].
Proof. vm_compute. reflexivity. Qed.
Example erw_of_sret_sepc :
  erw_of (deps_of_bits (dbits 0x10200073)) [wcsr SEPC] (R_bitvector_64 sepc) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* D-4 SURVIVES OUTSIDE THE TABLE: [csrw fcsr,a5] = 0x00379073 has no role,
   so its [fcsr] node is silent. *)
Example erw_of_csrw_fcsr :
  erw_of (deps_of_bits (dbits 0x00379073)) [15%nat] (R_bitvector_32 fcsr) = ERWnone.
Proof. vm_compute. reflexivity. Qed.

(* [beq a5,zero,.] = 0x00078063: [nextPC] carries the CONTROL view — PARM's
   [step_if], on the taken and the not-taken arm alike (deviation D-9) *)
Example erw_of_beq_nextpc :
  erw_of (deps_of_bits (dbits 0x00078063)) [15%nat] (R_bitvector_64 nextPC)
  = ERWctrl [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* an ALU instruction's [nextPC] write carries NO control source *)
Example erw_of_addi_nextpc :
  erw_of (deps_of_bits (dbits 0x00178793)) [15%nat] (R_bitvector_64 nextPC)
  = ERWctrl [].
Proof. vm_compute. reflexivity. Qed.

(* [addi a5,a5,1]: the destination inherits its ALU source *)
Example erw_of_addi_rd :
  erw_of (deps_of_bits (dbits 0x00178793)) [15%nat] (R_bitvector_64 x15)
  = ERWreg 15 [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(** *** DEC-7's OWN WITNESSES: where the dynamic set is STRICTLY LARGER, and
    where the read set does NOT reach.

    Every [Example] above supplies the read set the DECODED role names and
    gets the decoded answer back, which is the "dynamic = decoded on the
    syntactic operands" half.  These three are the other half. *)

(* THE HONEST STRICT SUPERSET.  The same [ld a4,0(a5)] whose run consulted
   the translation context ([satp]) and the permission bits ([sstatus], i.e.
   the model's [mstatus]) — as EVERY translated access does.  The decoded
   answer was [[DLdRes; DReg 15]]; the dynamic one keeps it and adds the two
   pseudo-registers, so a value that reached [satp] now reaches this
   register's provenance. *)
Example erw_of_ld_rd_dynamic :
  erw_of (deps_of_bits (dbits 0x0007b703)) [15%nat; wsatp; wcsr MSTATUS]
    (R_bitvector_64 x14)
  = ERWreg 14 [DLdRes; DReg 15%nat; DReg wsatp; DReg (wcsr MSTATUS)].
Proof. vm_compute. reflexivity. Qed.

(* ... and it really is a superset of the decoded answer, mechanically. *)
Example erw_of_ld_rd_superset :
  forall s : dsrc,
    s ∈ [DLdRes; DReg 15%nat] ->
    match erw_of (deps_of_bits (dbits 0x0007b703))
            [15%nat; wsatp; wcsr MSTATUS] (R_bitvector_64 x14) with
    | ERWreg _ srcs => s ∈ srcs
    | _ => False
    end.
Proof.
  intros s Hs. rewrite erw_of_ld_rd_dynamic.
  apply elem_of_cons in Hs as [->|Hs]; [by apply elem_of_cons; left|].
  apply elem_of_cons in Hs as [->|Hs%elem_of_nil]; [|done].
  apply elem_of_cons; right. by apply elem_of_cons; left.
Qed.

(* A REPEATED READ COSTS NOTHING: the set is deduplicated. *)
Example erw_of_addi_rd_dedup :
  erw_of (deps_of_bits (dbits 0x00178793)) [15%nat; 15%nat; 15%nat]
    (R_bitvector_64 x15)
  = ERWreg 15 [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* THE CONTROL GATE (DEC-7).  An [addi] reads [a5] and writes [nextPC] like
   every instruction, and its [nextPC] node is STILL source-free: the
   decoder says it is not a control node. *)
Example erw_of_addi_nextpc_gated :
  erw_of (deps_of_bits (dbits 0x00178793)) [15%nat; wsatp; wcsr MSTATUS]
    (R_bitvector_64 nextPC)
  = ERWctrl [].
Proof. vm_compute. reflexivity. Qed.

(* ... whereas a [beq]'s IS, and picks up whatever the branch consulted. *)
Example erw_of_beq_nextpc_dynamic :
  erw_of (deps_of_bits (dbits 0x00078063)) [15%nat; wcsr MSTATUS]
    (R_bitvector_64 nextPC)
  = ERWctrl [DReg 15%nat; DReg (wcsr MSTATUS)].
Proof. vm_compute. reflexivity. Qed.

(** THE OPERAND LISTS a memory node carries, from the announced bits.

    D-8: A PLAIN LOAD CARRIES NO ADDRESS SOURCES.  The walker's PTE read and
    a load's data read are indistinguishable at the node (both [AK_explicit]
    plain with [va = None]; the model emits no
    [TranslationStart]/[TranslationEnd]), so attaching [rs1] to a read would
    also attach it to a PTE read, which is a STRENGTHENING beyond RVWMO's
    syntactic dependencies — the wrong polarity.  Stores and the fused RMW
    are unambiguous (the walker's A/D update is itself the fused arm), so
    they carry theirs. *)
Definition edeps (σ : wgstate) (c : CPU) : op_roles :=
  deps_of_ib (ib_bits (wgib σ c)).

(** DEC-7: ... and the DYNAMIC half of the same channel — the registers this
    hart's current instruction has read so far. *)
Definition erds (σ : wgstate) (c : CPU) : list wreg := ib_rds (wgib σ c).

(* ====================================================================== *)
(** ** 3. The barrier table

    (The fused-RMW ingredients [esilent1]/[esilent_run]/[ewr_node] lived
    here until the RMW SPLIT (S3): an exclusive read and a conditional
    write are SEPARATE events now, so there is no silent window inside an
    event and nothing to restate from [WeakSailLTS].) *)

(** The barrier table, split into what fires NOW and what is PARKED. *)
Definition ebar_now (b : barrier_kind) : option (bool * bool * bool * bool) :=
  match b with
  | Barrier_RISCV_rw_rw => Some (true , true , true , true )
  | Barrier_RISCV_r_rw  => Some (true , false, true , true )
  | Barrier_RISCV_r_r   => Some (true , false, true , false)
  | Barrier_RISCV_rw_w  => Some (true , true , false, true )
  | Barrier_RISCV_w_w   => Some (false, true , false, true )
  | Barrier_RISCV_w_rw  => Some (false, true , true , true )
  | Barrier_RISCV_rw_r  => Some (true , true , true , false)
  | Barrier_RISCV_r_w   => Some (true , false, false, true )
  | Barrier_RISCV_w_r   => Some (false, true , true , false)
  | Barrier_RISCV_tso   => Some (true , false, true , false)
  | Barrier_RISCV_i     => None
  end.

Definition ebar_park (b : barrier_kind) : option (bool * bool * bool * bool) :=
  match b with
  | Barrier_RISCV_tso => Some (true, true, false, true)
  | _ => None
  end.

Definition efence_apply (ws : wstate) (o : option (bool * bool * bool * bool))
    : wstate :=
  match o with
  | Some (pr, pw, sr, sw) => fence_post ws pr pw sr sw
  | None => ws
  end.

Lemma efence_barrier_post ws b :
  efence_apply (efence_apply ws (ebar_now b)) (ebar_park b) = barrier_post ws b.
Proof. by destruct b. Qed.

Lemma efence_apply_le ws o : ws_le ws (efence_apply ws o).
Proof.
  destruct o as [[[[pr pw] sr] sw]|]; [apply fence_post_le|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 4. The hart's per-event step

    One arm per event kind, per the design's table, ON THE EXPRESSION: the
    successor names the residual monad, so the WP rules of S4 are syntactic
    descent and not a ghost protocol. *)

Section hart.
  Context (gen : nat) (σ : wgstate) (c : CPU).

  Local Notation rs0 := (wgregs σ c).
  Local Notation ws0 := (wgws σ c).
  Local Notation d0  := (wgdev σ).
  Local Notation lg0 := (wglog σ).

  (** The monad-node dispatch.  Mirrors [WeakSailLTS.sail_mstep] arm for arm,
      minus the labels and the oracles; the device arms use the PARTIAL
      accessors (delta (D1)).

      RAM READ is LABEL-FREE: the timestamps/values it takes are chosen here
      and constrained by [WeakPromise.read_ok] against the SHARED log and
      this hart's own view.  The EXCLUSIVE READ (delta (D3)) is the second
      disjunct of the same arm.  RAM WRITE COMPUTES its class (delta (D2))
      and splits the same way, the conditional half carrying §4's window and
      §5's retry self-loop. *)
  Definition emonad_step (m : M unit) (e' : eexpr) (σ' : wgstate) : Prop :=
    match m with
    | Interface.Ret _ =>
        (* THE RESTART (the merged boundary rule): the hart is at the
           terminal value, i.e. AT an instruction boundary, and fetches a
           fresh instruction.  The old two-step "pop to [ELoop], then
           fetch" is one step now — [Ret tt] IS the boundary token. *)
        exists tick : bool, e' = Sail gen c (riscv_step tick) None /\
          (* D3: THE INSTRUCTION BOUNDARY CLEARS THE ANNOUNCED BITS.  A hart
             sitting at [Ret tt] is between instructions, so it has no
             current instruction and no dependency roles — which is exactly
             [WeakDeps.deps_of_ib None = ORnone].

             W2b CONDITION 1: IT IS ALSO THE RESET POINT, i.e. the boundary
             emits [LInstr] and applies [instr_post].  It must be HERE and
             not only at [InstrAnnounce], because the Sail model announces
             AFTER the fetch: with the reset riding the announce alone the
             fetch would consume the PREVIOUS instruction's data-read bank
             through [w_tbank], which is a blanket load → later-store edge
             RVWMO does not have (it forbids LB).  The announce KEEPS its
             own [LInstr] — see [WeakEvInst.pnode_step]'s boundary arm for
             why both resets stay. *)
          σ' = ewg_ibws σ c ib_none (instr_post ws0)
    | Interface.Next oc k =>
        (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
         (* DEC-7: THE READ SET ACCUMULATES HERE.  The node is still silent
            for the log, the views and the register file — the σ-write is
            [wgib] alone, which [WeakEvLift.weak_state_interp_ib] makes
            invisible to the interpretation by conversion. *)
         | Interface.RegRead r _ => fun k =>
             e' = ECycle gen c (k (register_lookup r rs0)) None /\
             σ' = ewg_ib σ c (ib_rd (wgib σ c) r)
         (* D3-2: a register write MAY carry a dependency — PARM's
            [step_assign] for the instruction's architectural [rd], and
            PARM's [step_if] (the control view) at [nextPC]; every other
            register write is silent (D-4). *)
         | Interface.RegWrite r _ v => fun k =>
             e' = ECycle gen c (k tt) None /\
             σ' = ewg_rw σ c (register_set r v rs0)
                    (erw_of (edeps σ c) (erds σ c) r)
         | Interface.MemRead n req => fun k =>
             if dev_addr (Interface.ReadReq.pa req)
             then (* MMIO: the SHARED fabric answers, partially (D1) *)
               exists (w : bv (8 * n)) (d' : dev_state),
                 dev_read d0 (Interface.ReadReq.pa req) n = Some (w, d') /\
                 e' = ECycle gen c (k (inl (w, None))) None /\
                 σ' = ewg_dev σ d'
             else
               ak_coh (classify (Interface.ReadReq.access_kind req)) = false /\
               ((* THE PLAIN RAM READ.  The guard is EXCLUSIVITY (design §6:
                   [ak_latest] is extensionally [ak_excl] today — [classify]
                   sets it exactly at [AV_exclusive]/[AV_atomic_rmw], and
                   ifetch/ttw are excluded by [ak_coh] one line up). *)
                (ak_latest (classify (Interface.ReadReq.access_kind req)) = false /\
                 exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (wgimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   e' = ECycle gen c (k (inl (w, None))) None /\
                   σ' = ewg_ws σ c
                          (load_post_run ws0
                             (ak_sync (classify (Interface.ReadReq.access_kind req)))
                             (pa_z (Interface.ReadReq.pa req)) tvs.*1))
                \/
                (* THE EXCLUSIVE READ (RMW split §2/§6).  ONE step, and its
                   read semantics are the plain arm's with [lat := false]
                   hardwired — at the PLAIN read floor since D-2r: the
                   address view is no longer an admissibility condition nor
                   a byte-fold floor (see [WeakMem.exload_post_run_d]'s
                   header for the rationale and the re-upgrade coupling); it
                   is still PASSED to the σ-effect, where it survives in
                   [w_vcap] (the [ctrl_post] join) and nowhere else.  The
                   RESERVATION is machine-side state: the language only names
                   the σ-effect [exload_post_run_d], which is the plain
                   run-level read plus [w_res := Some (base, tvs.*1,
                   ldv_of …)], SUPERSEDING whatever [w_res] held.

                   THE F6 GUARD IS GONE with the fusion: a bare exclusive
                   read is no longer stuck, and a DANGLING one (the walker's
                   A/D re-read race, [check_leaf_pte]'s Err arm, an AMOCAS
                   mismatch) is a legal trace — superseded at the next
                   exclusive read, cleared at [LInstr] by [instr_post]. *)
                (ak_latest (classify (Interface.ReadReq.access_kind req)) = true /\
                 exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
                   length tvs = N.to_nat n /\
                   (forall j : nat, (j < N.to_nat n)%nat ->
                      tvs.*2 !! j = Some (nth_byte w j)) /\
                   read_ok (img_z (wgimg σ)) lg0 ws0
                     (ak_sync (classify (Interface.ReadReq.access_kind req)))
                     false (pa_z (Interface.ReadReq.pa req)) tvs /\
                   e' = ECycle gen c (k (inl (w, None))) None /\
                   σ' = ewg_ws σ c
                          (exload_post_run_d ws0
                             (ak_sync (classify (Interface.ReadReq.access_kind req)))
                             (srcs_view ws0 (deps_asrc (edeps σ c)))
                             (pa_z (Interface.ReadReq.pa req)) tvs.*1)))
         | Interface.MemWrite n req => fun k =>
             if dev_addr (Interface.WriteReq.pa req)
             then
               exists d' : dev_state,
                 dev_write d0 (Interface.WriteReq.pa req) n
                   (Interface.WriteReq.value req) = Some d' /\
                 e' = ECycle gen c (k (inl None)) None /\ σ' = ewg_dev σ d'
             else
               n <> 0%N /\
               ((* THE PLAIN RAM WRITE, guarded by exclusivity exactly as the
                   read is: a CONDITIONAL write must not also be able to
                   take the unconditional arm, or the window check of §4 —
                   i.e. atomicity — could simply be bypassed. *)
                (ak_latest (classify (Interface.WriteReq.access_kind req)) = false /\
                 e' = ECycle gen c (k (inl None)) None /\
                 σ' = ewg_store σ c
                        (store_post_run_d ws0
                           (ak_sync (classify (Interface.WriteReq.access_kind req)))
                           (srcs_view ws0 (deps_asrc (edeps σ c)))
                           (srcs_view ws0 (deps_vsrc (edeps σ c)))
                           (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
                           (S (length lg0)))
                        (lg0 ++ [WMsg (pa_z (Interface.WriteReq.pa req))
                                   (wbytes n (Interface.WriteReq.value req))
                                   (Some (fin_to_nat c))
                                   (wm_class_of
                                      (classify (Interface.WriteReq.access_kind req))
                                      ws0)]))
                \/
                (ak_latest (classify (Interface.WriteReq.access_kind req)) = true /\
                 ((* THE CONDITIONAL WRITE (RMW split §4): the ordinary write
                     semantics, PLUS the reservation the matching exclusive
                     read left and the per-byte window still being clean.
                     There is NO plain-store fallback — a partnerless
                     [LExStore] has no arm at all. *)
                  (exwin_ok lg0 (fin_to_nat c)
                     ws0 (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
                     (S (length lg0)) /\
                   e' = ECycle gen c (k (inl None)) None /\
                   σ' = ewg_store σ c
                          (store_post_run_d ws0
                             (ak_sync (classify (Interface.WriteReq.access_kind req)))
                             (srcs_view ws0 (deps_asrc (edeps σ c)))
                             (srcs_view ws0 (deps_vsrc (edeps σ c)))
                             (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
                             (S (length lg0)))
                          (lg0 ++ [WMsg (pa_z (Interface.WriteReq.pa req))
                                     (wbytes n (Interface.WriteReq.value req))
                                     (Some (fin_to_nat c))
                                     (wm_class_of
                                        (classify
                                           (Interface.WriteReq.access_kind req))
                                        ws0)]))
                  \/
                  (* THE RETRY SELF-LOOP (design §5).  [WeakEvAdequacy] runs
                     at [NotStuck], and after the split a foreign append
                     during the window can make the conditional write's
                     [excl_ok_ts] fail — a stuck node.  So the node keeps a
                     SILENT self-loop: same monad, same σ, label [LSilent].

                     IT IS UNGUARDED, and that is forced twice over.  (i) The
                     FACTORIZATION: the guard would have to be "the window is
                     dirty", a MEMORY fact, and [WeakEvInst.pnode_step] — the
                     program half the factorization theorem is an iff against
                     — sees no memory at all.  (ii) The WP RULE: the retry is
                     absorbed by Löb, so the caller's callback must survive a
                     retry unconsumed; a guarded arm would have to be decided
                     before the mask moves ⊤→∅, i.e. before the step, and the
                     clean branch would then still have to dispose of an
                     already-fired callback.  The cost is a silent, σ-preserving
                     stutter that the robustness tower sees as one more
                     [LSilent] — which is exactly what §5 budgets. *)
                  (e' = ECycle gen c (Interface.Next (Interface.MemWrite n req) k)
                          None /\
                   σ' = σ))))
         | Interface.Barrier b => fun k =>
             e' = ECycle gen c (k tt) (ebar_park b) /\
             σ' = ewg_ws σ c (efence_apply ws0 (ebar_now b))
         (* D3: THE ANNOUNCE NODE RECORDS THE INSTRUCTION BITS.  This is the
            one place the machine learns which registers the current
            instruction reads and writes (deps design §2.4); everything
            downstream is [WeakDeps.deps_of_bits] of this word.  The node is
            otherwise silent: no log, no view, no register. *)
         | Interface.InstrAnnounce ob => fun k =>
             e' = ECycle gen c (k tt) None /\
             (* D3-2: the announce is ALSO the instruction start, so it
                RESETS the load-result bank ([LInstr] / PARM's [res]). *)
             σ' = ewg_ibws σ c (ib_ann (ib_of_bvn ob)) (instr_post ws0)
         (* [BranchAnnounce] STAYS SILENT: it fires only on the TAKEN arm of a
            redirect, whereas RVWMO ppo 11 (and PARM's [step_if]) order after
            a branch whether or not it is taken.  The control view is raised
            at the ANNOUNCE instead, from [deps_ctrl] of the bits. *)
         | Interface.BranchAnnounce _ _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.CacheOp _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TlbOp _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TakeException _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.ReturnException _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TranslationStart _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.TranslationEnd _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.CycleCount => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.Message _ => fun k =>
             e' = ECycle gen c (k tt) None /\ σ' = σ
         | Interface.GetCycleCount => fun k =>
             e' = ECycle gen c (k 0%Z) None /\ σ' = σ
         | Interface.Choose _ => fun k =>
             exists ch, e' = ECycle gen c (k ch) None /\ σ' = σ
         (* GenericFail / Discard / a raised Sail exception: STUCK. *)
         | _ => fun _ => False
         end) k
    end.

  (** THE CYCLE EVENT.  The parked fence gates everything (delta (D5)). *)
  Definition ecycle_step (m : M unit) (fn : option (bool * bool * bool * bool))
      (e' : eexpr) (σ' : wgstate) : Prop :=
    match fn with
    | Some (pr, pw, sr, sw) =>
        e' = ECycle gen c m None /\
        σ' = ewg_ws σ c (fence_post ws0 pr pw sr sw)
    | None => emonad_step m e' σ'
    end.

End hart.

(* ====================================================================== *)
(** ** 5. The device threads

    [WeakLang]'s three arms.  The UART and PLIC arms are literally
    [RiscvLang.uart_step]/[plic_step]; the disk arm is [WeakLang.wdisk_step]
    SPLIT into a burst and one emit per message — which is what makes it 1:1
    with the pf disk agent — with the burst buffer and the disk's own view in
    the EXPRESSION. *)

Definition euart_step (σ σ' : wgstate) : Prop :=
  exists d', uart_step (wgdev σ) d' /\ σ' = ewg_dev σ d'.

(** THE PLIC THREAD delivers ONE interrupt, to a hart it chooses: exactly
    [RiscvLang.plic_step]'s [PlicStepWire], and (delta (D4)) the ONLY
    interrupt-delivery arm in the language. *)
Definition eplic_step (σ σ' : wgstate) : Prop :=
  exists c : CPU,
    σ' = ewg_reg σ c
           (register_set sig_seip
              (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c))) (wgregs σ c)).

(** THE DISK THREAD (M5 — [claude-notes/design/weak-memory-m5.md]).

    The disk is a WEAK-MEMORY AGENT, not a flat-memory oracle: it runs
    [VirtioProg.virtio_prog] NODE BY NODE at its OWN [wstate], with exactly
    the events a hart has — a plain/acquire RAM read, a plain RAM write, a
    fence — plus fabric-touching silent steps for the three points where it
    reads or moves the device state itself (start, commit, PLIC latch).
    [WeakLang.wflat] / [wdisk_step] / [wmsgs_of_map] are GONE from the event
    language (they stay in [WeakLang] for the archived instruction-atomic
    tier), and with them the burst buffer and its canonicity invariant.

    THE CLASS THE DEVICE'S STORES CARRY.  The device has no access-kind
    annotations, so each of its stores is a PLAIN EXPLICIT store: [ddev_ak]
    is [AkInfo] with no coherence requirement, no exclusivity and no
    release/acquire annotation — literally
    [WeakInterp.classify (AK_explicit (Explicit_access_kind AV_plain
    AS_normal))].  [WeakInterp.wm_class_of] then computes [WCrel] exactly
    when the disk's own [w_relp] is armed (i.e. right after its [DFence])
    and [WCplain] otherwise — the same rule a hart's plain [sd] gets, which
    is the point: the used-index store the driver polls IS the device's
    release. *)
Definition ddev_ak : akinfo := AkInfo false false false.

Definition ddev_class (ws : wstate) : wm_class := wm_class_of ddev_ak ws.

Lemma ddev_class_eq ws : ddev_class ws = if w_relp ws then WCrel else WCplain.
Proof. rewrite /ddev_class /wm_class_of /=. by destruct (w_relp ws). Qed.

(** ... and it is the class of a plain explicit store, spelled through the
    model's own access kind rather than by hand. *)
Lemma ddev_ak_plain :
  ddev_ak =
  classify (AK_explicit (Build_Explicit_access_kind AV_plain AS_normal)).
Proof. reflexivity. Qed.

(** THE MALFORMED-CHAIN RESIDUE (assumption 4).  A request whose descriptor
    chain does not parse lets the device write ANYTHING ANYWHERE; at event
    granularity that is a chain of ordinary store events, chosen at the
    [DWild] step. *)
Inductive dm_wild_chain : DM dres -> Prop :=
  | dm_wild_ret : dm_wild_chain (DRet DIdle)
  | dm_wild_write pa bs k :
      bs <> [] -> dm_wild_chain k -> dm_wild_chain (DWrite pa bs k).

Lemma dm_wild_chain_wf p : dm_wild_chain p -> dm_wf p.
Proof.
  induction 1 as [|pa bs k Hne _ IH]; [apply dm_wf_ret|by apply dm_wf_write].
Qed.

(** THE DISK'S STEP: one arm per node of the residual program, plus the
    three fabric arms.  Each fabric-touching arm is its own disjunct — that
    is what [WeakEvInst]'s [LDev] marking keys on. *)
Definition edisk_step (gen : nat) (dp : option (DM dres)) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  (* START: read the fabric's virtio state and elaborate the program.  No
     log, no view; FABRIC-TOUCHING. *)
  (dp = None /\ e' = EDisk gen (Some (virtio_prog (dvirtio (wgdev σ)))) dws
   /\ σ' = σ)
  \/
  (* DRead: EXACTLY the hart's plain RAM-read arm, at [dws].  The
     continuation receives the byte LIST the label carries. *)
  (exists pa n aq k tvs,
     dp = Some (DRead pa n aq k) /\
     length tvs = n /\
     read_ok (img_z (wgimg σ)) (wglog σ) dws aq false (pa_z pa) tvs /\
     e' = EDisk gen (Some (k tvs.*2))
            (load_post_run dws aq (pa_z pa) tvs.*1) /\
     σ' = σ)
  \/
  (* DWrite: EXACTLY the hart's RAM-write arm, at [dws], tid [Some n_disk],
     class [ddev_class] (computed, no free binder). *)
  (exists pa bs k,
     dp = Some (DWrite pa bs k) /\ bs <> [] /\
     e' = EDisk gen (Some k)
            (store_post_run dws false (pa_z pa) (length bs)
               (S (length (wglog σ)))) /\
     σ' = ewg_log σ
            (wglog σ ++ [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)]))
  \/
  (* DFence: the device-side write barrier, [fence rw,rw]. *)
  (exists k,
     dp = Some (DFence k) /\
     e' = EDisk gen (Some k) (fence_post dws true true true true) /\ σ' = σ)
  \/
  (* COMMIT: apply the burst's delta to the CURRENT fabric state.
     FABRIC-TOUCHING. *)
  (exists delta,
     dp = Some (DRet (DDone delta)) /\ e' = EDisk gen None dws /\
     σ' = ewg_dev σ (set_dvirtio (wgdev σ) (delta (dvirtio (wgdev σ)))))
  \/
  (* DWild: the malformed chain becomes an arbitrary store chain. *)
  (exists prog',
     dp = Some (DRet DWild) /\ dm_wild_chain prog' /\
     e' = EDisk gen (Some prog') dws /\ σ' = σ)
  \/
  (* nothing pending. *)
  (dp = Some (DRet DIdle) /\ e' = EDisk gen None dws /\ σ' = σ)
  \/
  (* THE PLIC LATCH ([WeakLang.WDiskStepLatch]), at any time.
     FABRIC-TOUCHING. *)
  (exists p',
     dev_irq_level (wgdev σ) virtio_irq_id = true /\
     plic_latch (dplic (wgdev σ)) virtio_irq_id = Some p' /\
     e' = EDisk gen dp dws /\
     σ' = ewg_dev σ (set_dplic (wgdev σ) p')).

(** THE RESIDUAL PROGRAM'S WELL-FORMEDNESS, the invariant that replaces
    [epend_canon]: every read is of at least one byte and every store
    carries at least one byte, so the store arm's log message is never
    empty.  [VirtioProg.virtio_prog_wf] establishes it at every start. *)
Definition edp_wf (dp : option (DM dres)) : Prop :=
  match dp with Some p => dm_wf p | None => True end.

Lemma edp_wf_none : edp_wf None.
Proof. done. Qed.

(* ====================================================================== *)
(** ** 6. Boot / crash reset

    [WeakLang.wboot_facts] UNCHANGED — the four clauses the pre-revision
    version added (every hart at a boundary, no parked fence, empty burst
    buffer, fresh disk view) are now facts about [epower_fork]'s
    expressions, so σ owes nothing. *)
Definition eboot_shape (σ σ' : wgstate) : Prop :=
  wggen σ' = wggen σ
  /\ (wgdev σ').(dvirtio) = virtio_reset (wgdev σ).(dvirtio)
  /\ wboot_facts σ'.

(* ====================================================================== *)
(** ** 7. [eprim_step]: the six arms

    [WeakLang.wprim_step]'s shape — same live/corpse gating, same PowerOff
    generation bump, same PowerOn fork — with the hart's single instruction
    arm split into the boundary arm and the cycle arm. *)

Definition ethread_live (σ : wgstate) (gen : nat) : Prop :=
  wgpow σ = true /\ wggen σ = gen.

Lemma ethread_live_wthread_live σ gen :
  ethread_live σ gen <-> wthread_live σ gen.
Proof. reflexivity. Qed.

Definition eprim_step
    (e : eexpr) (σ : wgstate) (κ : list eobs)
    (e' : eexpr) (σ' : wgstate) (efs : list eexpr) : Prop :=
  (* THE HART, one arm (G5c): one event of the instruction, where the
     instruction BOUNDARY is the [Ret tt] node and its event is the fetch.
     One corpse arm, and one bookkeeping step per instruction fewer. *)
  (exists gen cpu m fn, e = Sail gen cpu m fn /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ ecycle_step gen σ cpu m fn e' σ')
     \/ (~ ethread_live σ gen /\ e' = e /\ σ' = σ)))
  \/
  (exists gen, e = EUart gen /\ e' = EUart gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ euart_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (exists gen dp dws, e = EDisk gen dp dws /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ edisk_step gen dp dws σ e' σ')
     \/ (~ ethread_live σ gen /\ e' = e /\ σ' = σ)))
  \/
  (exists gen, e = EPlic gen /\ e' = EPlic gen /\ κ = [] /\ efs = [] /\
    ((ethread_live σ gen /\ eplic_step σ σ')
     \/ (~ ethread_live σ gen /\ σ' = σ)))
  \/
  (e = EPower /\ e' = EPower /\ κ = [] /\
    ((wgpow σ = true /\ efs = [] /\
       σ' = WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
                    (S (wggen σ)) false (wgib σ))
     \/
     (wgpow σ = false /\ efs = epower_fork (wggen σ) /\ eboot_shape σ σ'))).

Lemma weak_ev_lang_mixin : LanguageMixin eof_val eto_val eprim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs _. reflexivity.
Qed.

Definition weak_ev_lang : language := Language weak_ev_lang_mixin.

(* ====================================================================== *)
(** ** 8. Per-arm inversion *)

Lemma eprim_step_loop_inv gen cpu σ κ e' σ' efs :
  eprim_step (ELoop gen cpu) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\
    σ' = ewg_ibws σ cpu ib_none (instr_post (wgws σ cpu)) /\
    exists tick : bool, e' = ECycle gen cpu (riscv_step tick) None)
   \/ (~ ethread_live σ gen /\ e' = ELoop gen cpu /\ σ' = σ)).
Proof.
  intros [(gen0 & cpu0 & m0 & fn0 & Heq & Hk & Hf & Harm)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]];
    rewrite /ELoop in Heq; try discriminate Heq.
  injection Heq as <- <- <- <-.
  split_and!; [exact Hk|exact Hf|].
  destruct Harm as [(Hl & Hcy)|(Hd & Hee & Hss)].
  - rewrite /ecycle_step /emonad_step /= in Hcy.
    destruct Hcy as (tick & -> & ->).
    left. split_and!; [exact Hl|reflexivity|by exists tick].
  - right. by split_and!.
Qed.

Lemma eprim_step_cycle_inv gen cpu m fn σ κ e' σ' efs :
  eprim_step (ECycle gen cpu m fn) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ ecycle_step gen σ cpu m fn e' σ')
   \/ (~ ethread_live σ gen /\ e' = ECycle gen cpu m fn /\ σ' = σ)).
Proof.
  intros [(gen0 & cpu0 & m0 & fn0 & Heq & ? & ? & Harm)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]];
    rewrite /ECycle in Heq; try discriminate Heq.
  injection Heq as <- <- <- <-. by split_and!.
Qed.

Lemma eprim_step_uart_inv gen σ κ e' σ' efs :
  eprim_step (EUart gen) σ κ e' σ' efs ->
  e' = EUart gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ euart_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & ? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_disk_inv gen dp dws σ κ e' σ' efs :
  eprim_step (EDisk gen dp dws) σ κ e' σ' efs ->
  κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ edisk_step gen dp dws σ e' σ')
   \/ (~ ethread_live σ gen /\ e' = EDisk gen dp dws /\ σ' = σ)).
Proof.
  intros [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _)
         | [(gen0 & p0 & d0 & Heq & ? & ? & Harm)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as -> -> ->. by split_and!.
Qed.

Lemma eprim_step_plic_inv gen σ κ e' σ' efs :
  eprim_step (EPlic gen) σ κ e' σ' efs ->
  e' = EPlic gen /\ κ = [] /\ efs = [] /\
  ((ethread_live σ gen /\ eplic_step σ σ')
   \/ (~ ethread_live σ gen /\ σ' = σ)).
Proof.
  intros [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma eprim_step_power_inv σ κ e' σ' efs :
  eprim_step EPower σ κ e' σ' efs ->
  e' = EPower /\ κ = [] /\
  ((wgpow σ = true /\ efs = [] /\
     σ' = WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
                  (S (wggen σ)) false (wgib σ))
   \/ (wgpow σ = false /\ efs = epower_fork (wggen σ) /\ eboot_shape σ σ')).
Proof.
  intros [(? & ? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | (_ & ? & ? & Harm)]]]];
    try discriminate Heq.
  by split_and!.
Qed.

(* ====================================================================== *)
(** ** 9. Cross-arm sanity lemmas (S3/S4's state-interpretation obligations) *)

Lemma ecycle_step_img gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> wgimg σ' = wgimg σ.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { by intros (_ & ->). }
  destruct m as [y|T oc k]; [by intros (? & _ & ->)|].
  destruct oc; simpl; try (by intros (_ & ->));
    try (intros (_ & ->); apply ewg_rw_img); try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(_ & w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & _ & _ & _ & _ & ->)]); reflexivity.
  - (* MemWrite *)
    destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + by intros (_ & [(_ & _ & ->)|(_ & [(_ & _ & ->)|(_ & ->)])]).
  - (* Choose *) by intros (ch & _ & ->).
Qed.

Lemma ecycle_step_era gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> wgpow σ' = wgpow σ /\ wggen σ' = wggen σ.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { by intros (_ & ->). }
  destruct m as [y|T oc k]; [by intros (? & _ & ->)|].
  destruct oc; simpl; try (by intros (_ & ->));
    try (intros (_ & ->); by rewrite ewg_rw_pow ewg_rw_gen);
    try (by intros []).
  - destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(_ & w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & _ & _ & _ & _ & ->)]); by split.
  - destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + by intros (_ & [(_ & _ & ->)|(_ & [(_ & _ & ->)|(_ & ->)])]).
  - by intros (ch & _ & ->).
Qed.

(** ... and its successor is always a hart expression of the SAME generation
    and hart: the cycle either advances or pops to the boundary. *)
Lemma ecycle_step_shape gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' ->
  e' = ELoop gen c \/ exists m' fn', e' = ECycle gen c m' fn'.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (-> & _). right. by do 2 eexists. }
  destruct m as [y|T oc k];
    [intros (tick & -> & _); right; by exists (riscv_step tick), None|].
  destruct oc; simpl;
    try (intros (-> & _); right; by do 2 eexists); try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & -> & _). right. by do 2 eexists.
    + intros (_ & [(_ & w & tvs & _ & _ & _ & -> & _)
                  |(_ & w & tvs & _ & _ & _ & -> & _)]);
        right; by do 2 eexists.
  - destruct (dev_addr _).
    + intros (d' & _ & -> & _). right. by do 2 eexists.
    + intros (_ & [(_ & -> & _)|(_ & [(_ & -> & _)|(-> & _)])]);
        right; by do 2 eexists.
  - intros (ch & -> & _). right. by do 2 eexists.
Qed.

Lemma ecycle_step_log_app gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> exists ms, wglog σ' = wglog σ ++ ms.
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). exists []. by rewrite app_nil_r. }
  destruct m as [y|T oc k];
    [intros (? & _ & ->); exists []; by rewrite app_nil_r|].
  destruct oc; simpl;
    try (intros (_ & ->); exists []; by rewrite app_nil_r);
    try (intros (_ & ->); exists []; by rewrite ewg_rw_log app_nil_r);
    try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & _ & ->). exists []. by rewrite app_nil_r.
    + intros (_ & [(_ & w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & _ & _ & _ & _ & ->)]);
        exists []; by rewrite app_nil_r.
  - destruct (dev_addr _).
    + intros (d' & _ & _ & ->). exists []. by rewrite app_nil_r.
    + intros (_ & [(_ & _ & ->)|(_ & [(_ & _ & ->)|(_ & ->)])]);
        [by eexists|by eexists|exists []; by rewrite app_nil_r].
  - intros (ch & _ & ->). exists []. by rewrite app_nil_r.
Qed.

Lemma ecycle_step_ws_other gen σ c m fn e' σ' c' :
  ecycle_step gen σ c m fn e' σ' -> c' <> c -> wgws σ' c' = wgws σ c'.
Proof.
  intros H Hne. revert H. rewrite /ecycle_step.
  destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). by rewrite /ewg_ws /= gws_insert_ne. }
  destruct m as [y|T oc k];
    [intros (? & _ & ->); rewrite /ewg_ibws /=; by rewrite gws_insert_ne|].
  destruct oc; simpl;
    try (by intros (_ & ->));
    try (intros (_ & ->); by apply ewg_rw_ws_ne);
    try (intros (_ & ->); rewrite /ewg_ibws /=; by rewrite gws_insert_ne);
    try (by intros []).
  - destruct (dev_addr _).
    + by intros (w & d' & _ & _ & ->).
    + intros (_ & [(_ & w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & _ & _ & _ & _ & ->)]);
        rewrite /ewg_ws /=; by rewrite gws_insert_ne.
  - destruct (dev_addr _).
    + by intros (d' & _ & _ & ->).
    + intros (_ & [(_ & _ & ->)|(_ & [(_ & _ & ->)|(_ & ->)])]);
        [rewrite /ewg_store /=; by rewrite gws_insert_ne
        |rewrite /ewg_store /=; by rewrite gws_insert_ne
        |reflexivity].
  (* the Barrier arm is now closed by the generic [ewg_ibws] branch above:
     its σ' is [ewg_ws], whose [gws_insert_ne] is the same one. *)
  - intros (ch & _ & ->). reflexivity.
Qed.

Lemma ecycle_step_ws_le gen σ c m fn e' σ' :
  ecycle_step gen σ c m fn e' σ' -> ws_le (wgws σ c) (wgws σ' c).
Proof.
  rewrite /ecycle_step. destruct fn as [[[[pr pw] sr] sw]|].
  { intros (_ & ->). rewrite /ewg_ws /= gws_insert_eq. apply fence_post_le. }
  destruct m as [y|T oc k];
    [intros (? & _ & ->); rewrite /ewg_ibws /= gws_insert_eq;
     by apply instr_post_le|].
  destruct oc; simpl; try (by intros (_ & ->));
    try (intros (_ & ->); rewrite ewg_rw_ws;
         by apply ws_depmove_le, erw_ws_depmove);
    try (intros (_ & ->); rewrite /ewg_ibws /= gws_insert_eq;
         by apply instr_post_le);
    try (by intros []).
  - destruct (dev_addr _).
    + intros (w & d' & _ & _ & ->). reflexivity.
    + intros (_ & [(_ & w & tvs & _ & _ & _ & _ & ->)
                  |(_ & w & tvs & _ & _ & _ & _ & ->)]);
        rewrite /ewg_ws /= gws_insert_eq;
        [apply load_post_run_le|apply exload_post_run_d_le].
  - destruct (dev_addr _).
    + intros (d' & _ & _ & ->). reflexivity.
    + intros (_ & [(_ & _ & ->)|(_ & [(_ & _ & ->)|(_ & ->)])]);
        [rewrite /ewg_store /= gws_insert_eq; apply store_post_run_d_le
        |rewrite /ewg_store /= gws_insert_eq; apply store_post_run_d_le
        |reflexivity].
  - (* Barrier *) intros (_ & ->). rewrite /ewg_ws /= gws_insert_eq.
    apply efence_apply_le.
  - intros (ch & _ & ->). reflexivity.
Qed.

(** The device threads move NO hart's view. *)
Lemma euart_step_ws σ σ' : euart_step σ σ' -> wgws σ' = wgws σ.
Proof. by intros (d' & _ & ->). Qed.
Lemma eplic_step_ws σ σ' : eplic_step σ σ' -> wgws σ' = wgws σ.
Proof. by intros (c0 & ->). Qed.
Lemma edisk_step_ws gen dp dws σ e' σ' :
  edisk_step gen dp dws σ e' σ' -> wgws σ' = wgws σ.
Proof.
  intros [(_ & _ & ->)
         |[(pa & n & aq & k & tvs & _ & _ & _ & _ & ->)
         |[(pa & bs & k & _ & _ & _ & ->)
         |[(k & _ & _ & ->)
         |[(delta & _ & _ & ->)
         |[(prog' & _ & _ & _ & ->)
         |[(_ & _ & ->)
         |(p' & _ & _ & _ & ->)]]]]]]]; reflexivity.
Qed.

(* ====================================================================== *)
(** ** 10. Reducibility helpers

    A CORPSE always steps; a live boundary always steps (the fetch arm needs
    nothing); the live device threads always step; the power thread steps
    while the power is on.  A live CYCLE steps iff its node is not stuck —
    which is the ONE place the language is honestly partial (delta (D1) and
    the design's "stuck-is-fine"). *)

Lemma eprim_step_loop_dead gen cpu σ :
  ~ ethread_live σ gen -> eprim_step (ELoop gen cpu) σ [] (ELoop gen cpu) σ [].
Proof.
  intros Hd. left. exists gen, cpu, (Interface.Ret tt), None.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_loop_live gen cpu σ (tick : bool) :
  ethread_live σ gen ->
  eprim_step (ELoop gen cpu) σ [] (ECycle gen cpu (riscv_step tick) None)
    (ewg_ibws σ cpu ib_none (instr_post (wgws σ cpu))) [].
Proof.
  intros Hl. left. exists gen, cpu, (Interface.Ret tt), None.
  split_and!; try reflexivity. left. split; [exact Hl|].
  rewrite /ecycle_step /emonad_step /=. by exists tick.
Qed.

Lemma eprim_step_cycle_dead gen cpu m fn σ :
  ~ ethread_live σ gen ->
  eprim_step (ECycle gen cpu m fn) σ [] (ECycle gen cpu m fn) σ [].
Proof.
  intros Hd. left. exists gen, cpu, m, fn.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_uart_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (EUart gen) σ [] (EUart gen) σ [].
Proof.
  intros Hd. right; left. exists gen. split_and!; try reflexivity.
  by right.
Qed.

Lemma eprim_step_disk_dead gen dp dws σ :
  ~ ethread_live σ gen ->
  eprim_step (EDisk gen dp dws) σ [] (EDisk gen dp dws) σ [].
Proof.
  intros Hd. right; right; left. exists gen, dp, dws.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_plic_dead gen σ :
  ~ ethread_live σ gen -> eprim_step (EPlic gen) σ [] (EPlic gen) σ [].
Proof.
  intros Hd. right; right; right; left. exists gen.
  split_and!; try reflexivity. by right.
Qed.

Lemma eprim_step_power_off σ :
  wgpow σ = true ->
  eprim_step EPower σ [] EPower
    (WGState (wgregs σ) (wgimg σ) (wglog σ) (wgws σ) (wgdev σ)
             (S (wggen σ)) false (wgib σ)) [].
Proof.
  intros Hon. right; right; right; right. split_and!; try reflexivity.
  left. by split_and!.
Qed.

Lemma eprim_step_uart_idle gen σ :
  ethread_live σ gen -> eprim_step (EUart gen) σ [] (EUart gen) σ [].
Proof.
  intros Hl. right; left. exists gen. split_and!; try reflexivity.
  left. split; [exact Hl|]. exists (wgdev σ). split; [apply UartStepIdle|].
  by destruct σ.
Qed.

Lemma eprim_step_plic_wire gen σ (c : CPU) :
  ethread_live σ gen ->
  eprim_step (EPlic gen) σ [] (EPlic gen)
    (ewg_reg σ c
       (register_set sig_seip
          (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c))) (wgregs σ c))) [].
Proof.
  intros Hl. right; right; right; left. exists gen.
  split_and!; try reflexivity. left. split; [exact Hl|]. by exists c.
Qed.

(** THE RESIDUAL-PROGRAM INVARIANT, in the shape [epend_canon] had: the
    disk's step preserves [edp_wf], because [dm_wf] is closed under
    continuations at ANY answers, [virtio_prog] is well formed
    ([VirtioProg.virtio_prog_wf]) and a wild chain is well formed by
    construction. *)
Lemma edisk_step_wf gen dp dws σ e' σ' :
  edp_wf dp -> edisk_step gen dp dws σ e' σ' ->
  exists dp' dws', e' = EDisk gen dp' dws' /\ edp_wf dp'.
Proof.
  intros Hwf
    [(_ & -> & _)
    |[(pa & n & aq & k & tvs & Hdp & _ & _ & -> & _)
    |[(pa & bs & k & Hdp & _ & -> & _)
    |[(k & Hdp & -> & _)
    |[(delta & _ & -> & _)
    |[(prog' & _ & Hch & -> & _)
    |[(_ & -> & _)
    |(p' & _ & _ & -> & _)]]]]]]];
    rewrite /edp_wf in Hwf |- *.
  - do 2 eexists. split; [reflexivity|apply virtio_prog_wf].
  - rewrite Hdp in Hwf.
    inversion Hwf as [|pa0 n0 aq0 k0 Hn Hk| |]; simplify_eq.
    do 2 eexists. split; [reflexivity|apply Hk].
  - rewrite Hdp in Hwf.
    inversion Hwf as [| |pa0 bs0 k0 Hne Hk|]; simplify_eq.
    do 2 eexists. split; [reflexivity|apply Hk].
  - rewrite Hdp in Hwf.
    inversion Hwf as [| | |k0 Hk]; simplify_eq.
    do 2 eexists. split; [reflexivity|apply Hk].
  - by do 2 eexists.
  - do 2 eexists. split; [reflexivity|by apply dm_wild_chain_wf].
  - by do 2 eexists.
  - by do 2 eexists.
Qed.

(** THE DISK IS REDUCIBLE except at a [DRead] — and a [DRead] whose address
    has no admissible timestamp assignment is LEGITIMATELY STUCK: that a
    device read is answerable is the DRIVER's proof obligation (the WP
    side), not a property of the language.  Every other node — start, a
    write of a well-formed program, a fence, a commit, a wild chain, idle —
    always steps. *)
Lemma eprim_step_disk_reducible gen dp dws σ :
  ethread_live σ gen -> edp_wf dp ->
  (forall pa n aq k, dp <> Some (DRead pa n aq k)) ->
  exists e' σ', eprim_step (EDisk gen dp dws) σ [] e' σ' [].
Proof.
  intros Hl Hwf Hnr.
  have Hstep : forall e' σ', edisk_step gen dp dws σ e' σ' ->
    exists e0 σ0, eprim_step (EDisk gen dp dws) σ [] e0 σ0 [].
  { intros e' σ' Hs. exists e', σ'. right; right; left.
    exists gen, dp, dws. split_and!; try reflexivity. left. by split. }
  destruct dp as [pgm|].
  2:{ eapply Hstep. left. by split_and!. }
  destruct pgm as [a|pa n aq k|pa bs k|k].
  - destruct a as [delta| |].
    + eapply Hstep. right; right; right; right; left. by exists delta.
    + eapply Hstep. right; right; right; right; right; left.
      exists (DRet DIdle). split_and!; try reflexivity. apply dm_wild_ret.
    + eapply Hstep. right; right; right; right; right; right; left.
      by split_and!.
  - by destruct (Hnr pa n aq k).
  - rewrite /edp_wf in Hwf. inversion Hwf as [| |pa0 bs0 k0 Hne Hk|]; subst.
    eapply Hstep. right; right; left. exists pa, bs, k. by split_and!.
  - eapply Hstep. right; right; right; left. by exists k.
Qed.
