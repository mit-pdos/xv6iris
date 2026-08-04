(* ============================================================== *)
(* RiscvAddTryStep.v -- consolidated Iris-over-Sail development.   *)
(* An Iris weakest-precondition for `add a2,a0,a1` executed by the *)
(* real Sail RISC-V `try_step`.  Self-contained except for:        *)
(*   - the generated model    : Riscv.rv64d / rv64d_types          *)
(*   - a small iris-FREE bv-arithmetic prelude : RiscvModelBytes    *)
(*     (kept separate ONLY because it uses vanilla `rewrite .. by`, *)
(*      which ssreflect -- pulled in by iris -- forbids).           *)
(* ============================================================== *)

From stdpp Require Import gmap finite bitvector.definitions.
From iris.program_logic Require Import language.
(* NOTE: SailStdpp.Base/Values/TypeCasts are imported LATER (before the         *)
(* ExecClose section), NOT here: they make the model's [mword] Countable        *)
(* (Countable_mword) canonical, but the Lang/Iris/Exec sections + the iris-free  *)
(* RiscvModelBytes must agree on stdpp's bv_countable for [gmap Arch.pa (bv 8)]  *)
(* (= the [mstate.mem] type).  Importing them here would retype mstate.mem and   *)
(* clash with read_bytes.  See the import line just above RiscvModelExecClose.    *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Export DevModel.
(* NB: deliberately NO `Set Default Proof Using "Type"` — some merged sections   *)
(* use bare `Proof.` and rely on Coq's default (generalize over the section      *)
(* Hypotheses actually used), as in their original (Set-free) files.             *)
Local Open Scope Z_scope.


(* ===== RiscvModelLang ===== *)
(* ====================================================================== *)
(* RiscvModelLang.v                                                        *)
(*                                                                         *)
(* Re-architecture of RiscvIrisFetch.v to run the *real* Sail model's      *)
(* [try_step] as the loop body, instead of the hand-written                *)
(* fetch-decode-execute [riscv_step].                                      *)
(*                                                                         *)
(* LAYER 1 (this file): the operational semantics.                         *)
(*   - state  = the model's own [regstate] + a byte memory                 *)
(*   - run    = interpreter over the real monad [M] / [Interface.outcome]  *)
(*   - step   = [try_step 0 false] (one fetch-decode-execute cycle),       *)
(*              optionally followed by [tick_clock] (see [riscv_step])     *)
(*   - language instance (argument-free, like RiscvIrisFetch).             *)
(* The Iris program-logic layer (gen_heap points-to over registers,        *)
(* state_interp, WP) is deliberately deferred to a follow-up file.         *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 1. Operational state: the model's register record + byte memory +       *)
(*    the memory-mapped device fabric (UART + PLIC, see DevModel.v).       *)
(*    Memory is keyed by the model's physical-address type [Arch.pa]       *)
(*    (= mword 64), values are individual bytes.  [mdev] is one hart's     *)
(*    view of the SHARED device state, exactly like [mem] is its view of   *)
(*    the shared byte memory.                                              *)
(* ---------------------------------------------------------------------- *)

Record mstate := MState {
  sregs : regstate;
  mem   : gmap Arch.pa (bv 8);
  mdev  : dev_state;
}.

Definition set_reg (s : mstate) (r : register) (v : type_of_register r) : mstate :=
  MState (register_set r v s.(sregs)) s.(mem) s.(mdev).


(* Byte address [a + j] (model's own mword arithmetic) and byte [j] of a value. *)

(* ---------------------------------------------------------------------- *)
(* 2. Interpreter over the real monad [M X = Interface.iMon (const exc) X].*)
(*    A relation (big-step), defined as a dependent Fixpoint to avoid the  *)
(*    UIP axiom that GADT inversion of [Next] would otherwise require.     *)
(*                                                                         *)
(*    Register effects use the model's own [register_lookup]/[register_set]*)
(*    (total, no dependent gmap needed at the operational level).          *)
(*    Memory reads/writes are byte-addressed.  Pure "announce"/trace       *)
(*    outcomes are state no-ops; failure/discard outcomes are stuck.       *)
(* ---------------------------------------------------------------------- *)

Fixpoint run {X} (m : M X) (s : mstate) (x : X) (s' : mstate) {struct m} : Prop :=
  match m with
  | Interface.Ret y => x = y /\ s' = s
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       (* registers *)
       | Interface.RegRead r _ =>
           fun k => run (k (register_lookup r s.(sregs))) s x s'
       | Interface.RegWrite r _ v =>
           fun k => run (k tt) (set_reg s r v) x s'
       (* memory: the bus routes each access by physical address.  Addresses
          below the DRAM bank ([dev_addr]) are memory-mapped I/O: the READ is
          serviced directly by the device (whose state may change, e.g. RHR
          pops the receive FIFO), and the WRITE is delivered to the device as
          an individual transaction.  A RAM read returns the value [w] whose
          every byte [j] is the memory byte at [pa + j] (little-endian,
          faithful), so the full word is pinned by [(mem, pa, n)] -- not just
          the low byte. *)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
               | Some (w, d') =>
                   run (k (inl (w, None))) (MState s.(sregs) s.(mem) d') x s'
               | None => False
               end
             else
               exists w : bv (8 * n),
                 (forall j : nat, (N.of_nat j < n)%N ->
                    s.(mem) !! (pa_add (Interface.ReadReq.pa req) j) = Some (nth_byte w j))
                 /\ run (k (inl (w, None))) s x s'
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) with
               | Some d' =>
                   run (k (inl None)) (MState s.(sregs) s.(mem) d') x s'
               | None => False
               end
             else
               run (k (inl None))
                   (MState s.(sregs)
                      (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req)) s.(mdev)) x s'
       (* trace / announce outcomes: state no-ops *)
       | Interface.InstrAnnounce _   => fun k => run (k tt) s x s'
       | Interface.BranchAnnounce _ _=> fun k => run (k tt) s x s'
       | Interface.Barrier _         => fun k => run (k tt) s x s'
       | Interface.CacheOp _         => fun k => run (k tt) s x s'
       | Interface.TlbOp _           => fun k => run (k tt) s x s'
       | Interface.TakeException _   => fun k => run (k tt) s x s'
       | Interface.ReturnException _ => fun k => run (k tt) s x s'
       | Interface.TranslationStart _=> fun k => run (k tt) s x s'
       | Interface.TranslationEnd _  => fun k => run (k tt) s x s'
       | Interface.CycleCount        => fun k => run (k tt) s x s'
       | Interface.Message _         => fun k => run (k tt) s x s'
       | Interface.GetCycleCount     => fun k => run (k 0%Z) s x s'
       (* nondeterminism: branch over every choice *)
       | Interface.Choose _          => fun k => exists c, run (k c) s x s'
       (* failure / discard / injected exception: stuck *)
       | _ => fun _ => False
       end) k
  end.

(* A CPU step never moves the disk IMAGE (crash.md): register effects and
   RAM accesses do not touch the device fabric at all, and an MMIO
   transaction goes through [dev_read]/[dev_write], which preserve
   [v_disk] ([DevModel.dev_read_v_disk]/[dev_write_v_disk]).  This is what
   lets the hart base rule FRAME [state_interp]'s durable disk conjunct;
   only the DISK's own DMA step moves the image. *)
Lemma run_v_disk {X} (m : M X) :
  forall s x s', run m s x s' ->
    v_disk (dvirtio (mdev s')) = v_disk (dvirtio (mdev s)).
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hrun.
  - destruct Hrun as [_ ->]. reflexivity.
  - destruct oc; simpl in Hrun;
      try (exact (IH _ _ _ _ Hrun));
      try (exfalso; exact Hrun);
      try (destruct Hrun as (c & Hrun); exact (IH _ _ _ _ Hrun));
      (destruct (dev_addr _) eqn:Hd;
       [ (destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr;
          [ etransitivity; [exact (IH _ _ _ _ Hrun)|];
            cbn; exact (dev_read_v_disk _ _ _ _ _ Hdr)
          | exfalso; exact Hrun ])
         ||
         (destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw;
          [ etransitivity; [exact (IH _ _ _ _ Hrun)|];
            cbn; exact (dev_write_v_disk _ _ _ _ _ Hdw)
          | exfalso; exact Hrun ])
       | try (destruct Hrun as (w & _ & Hrun)); exact (IH _ _ _ _ Hrun) ]).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The fixed loop body: ONE real fetch-decode-execute cycle.            *)
(*    The model's [loop] additionally runs [tick_clock tt] after the step  *)
(*    every [plat_insns_per_tick] retired instructions (advancing mtime    *)
(*    and re-dispatching the CLINT).  [riscv_step] has no instruction      *)
(*    counter, so the tick is a per-step parameter: [prim_step] chooses    *)
(*    [tick] nondeterministically, the sound weakening of [loop]'s         *)
(*    deterministic every-Nth tick.                                        *)
(* ---------------------------------------------------------------------- *)

Definition riscv_step (tick : bool) : M unit :=
  Defs.bind (try_step 0%Z false)
    (fun _ : bool => if tick then tick_clock tt else Defs.returnm tt).

(* ---------------------------------------------------------------------- *)
(* 3b. Multi-hart global state.                                             *)
(*                                                                          *)
(*   [CPU] is the FINITE type of valid HART ids -- every element is a real   *)
(*   hart that is always present.  [gstate] stores one [regstate] per hart   *)
(*   as a TOTAL function [CPU -> regstate] (no partiality, so no membership  *)
(*   side conditions ever arise) together with the single shared byte        *)
(*   memory.  An [mstate] is one hart's view: its own registers paired with  *)
(*   the shared memory.                                                       *)
(* ---------------------------------------------------------------------- *)

Definition NCPU : nat := 8.
Definition CPU : Type := fin NCPU.

Record gstate := GState {
  gregs : CPU -> regstate;
  gmem  : gmap Arch.pa (bv 8);
  gdev  : dev_state;
  (* the power/crash layer (claude-notes/design/crash.md): the current
     GENERATION and the POWER bit.  INERT until the power thread lands:
     every arm below PRESERVES both fields and none reads them, so the
     semantics is still generation- and power-blind. *)
  ggen : nat;
  gpow : bool;
}.

(* pointwise update of a single hart's register file *)
Global Instance greg_insert : Insert CPU regstate (CPU -> regstate) :=
  fun cpu rs gr c => if decide (c = cpu) then rs else gr c.

(* ---------------------------------------------------------------------- *)
(* 3c. The device execution contexts -- THREE of them, one per device.      *)
(*                                                                          *)
(*   The devices run CONCURRENTLY with the harts AND with each other:        *)
(*   between any two CPU instructions the UART may transmit or receive a     *)
(*   byte, the virtio disk may complete a queued request, either device's    *)
(*   PLIC gateway may latch its (level) interrupt output, and the PLIC may   *)
(*   propagate its per-hart EIP level onto a hart's external S-interrupt     *)
(*   pin -- the [sig_seip] register, which is exactly the model's external   *)
(*   interrupt WIRE: [read_mip IncludePlatformInterrupts] ORs it into mip,   *)
(*   so [dispatchInterrupt] sees it on the next instruction boundary.        *)
(*                                                                          *)
(*   THE FACTORING.  Each device latches its OWN interrupt source into the   *)
(*   PLIC, as part of that device's own step relation, and no relation ever  *)
(*   reads another device's state.  The three are therefore pairwise         *)
(*   decoupled over the [dev_state] fields:                                  *)
(*                                                                          *)
(*     uart_step  reads/writes  duart, dplic                                 *)
(*     disk_step  reads/writes  dvirtio, dplic, and the byte memory          *)
(*     plic_step  reads         dplic,  writes a hart's registers            *)
(*                                                                          *)
(*   so each gets its own execution context, its own lifting rule and its    *)
(*   own Iris invariant, and a proof about one device never has to reason     *)
(*   about the others' transitions.  ([dev_state] itself stays ONE object:   *)
(*   the fields are what is partitioned, not the record.)                    *)
(*                                                                          *)
(*   The disk is a BUS MASTER, so unlike the UART and the PLIC its step is   *)
(*   not confined to the device fabric: [disk_step] therefore carries the    *)
(*   byte memory, and [DiskStepDma] overrides it with the write set the DMA  *)
(*   produced ([w ∪ m], VirtioModel.virtio_req_step).  Every other device    *)
(*   transition returns the memory untouched.  The disk is also the only     *)
(*   device that steps NONDETERMINISTICALLY, in two ways: the bus view it    *)
(*   reads is unconstrained off the byte map, and a malformed queue lets it  *)
(*   write anything anywhere ([DiskStepWild]).                               *)
(*                                                                          *)
(*   TOTALITY (the [Idle] arms).  The old single relation was total for free, *)
(*   because [DevStepWire] had no premise -- there was always at least one    *)
(*   enabled transition.  A STANDALONE UART or disk thread has no such arm:  *)
(*   it can reach a state where no real transition is enabled (rx FIFO full   *)
(*   and tx FIFO empty; no request pending; the interrupt line already        *)
(*   latched or low), and then [wp_uart_loop]/[wp_disk_loop] could not prove  *)
(*   not-stuck.  Hence an explicit stutter in each.  It is ONLY a stutter and *)
(*   it excuses nothing: the wild arm below and the obligation to refute it   *)
(*   are untouched, so "the device did nothing" is never an admissible        *)
(*   explanation of a step the hardware would really have taken.              *)
(*                                                                          *)
(*   Note the wire is updated by its OWN step ([PlicStepWire]), not          *)
(*   synchronously with the MMIO write that caused the level change: the     *)
(*   interrupt line has propagation delay, which is both realistic and the   *)
(*   weaker (hence safer) modelling choice.                                  *)
(* ---------------------------------------------------------------------- *)

(* The UART: drain a byte, accept a byte, latch ITS OWN interrupt source
   ([dev_irq_level d uart_irq_id] reduces to [uart_irq d.(duart)]), or
   stutter.  Reads and writes [duart] and [dplic] and nothing else. *)
Inductive uart_step (d : dev_state) : dev_state -> Prop :=
  | UartStepTx b u' :
      uart_tx_pop d.(duart) = Some (b, u') ->
      uart_step d (set_duart d u')
  | UartStepRx b u' :
      uart_rx_push d.(duart) b = Some u' ->
      uart_step d (set_duart d u')
  | UartStepLatch p' :
      dev_irq_level d uart_irq_id = true ->
      plic_latch d.(dplic) uart_irq_id = Some p' ->
      uart_step d (set_dplic d p')
  (* the totality stutter -- see TOTALITY above *)
  | UartStepIdle : uart_step d d.

(* The disk: complete a queued request by DMA, scribble anywhere if the queue
   the driver published is malformed, latch its own interrupt source, or
   stutter.  This is the only relation that carries the byte memory. *)
Inductive disk_step (d : dev_state) (m : gmap Arch.pa (bv 8))
    : dev_state -> gmap Arch.pa (bv 8) -> Prop :=
  (* The disk masters the bus.  It does not read the byte MAP -- it reads a
     total VIEW of the bus that agrees with the map wherever the map is
     defined and is UNCONSTRAINED everywhere else (VirtioModel section 4), and
     the view is quantified here, existentially.  So a DMA read of an address
     nobody has accounted for returns an arbitrary byte, which is what a real
     bus does, and what forces a driver proof to account for every address it
     hands the device. *)
  | DiskStepDma (mv : vmem) v' w :
      mem_view m mv ->
      virtio_req_step d.(dvirtio) mv = Some (v', w) ->
      disk_step d m (set_dvirtio d v') (w ∪ m)
  (* ... and when the queue the driver published is MALFORMED, the device may
     do anything at all: [w] is arbitrary, so this constructor lets the disk
     scribble over any address in the machine.  That is the honest reading of
     a driver-must-not obligation.  An earlier model instead had the device
     quietly do NOTHING, which let a driver that misconfigured the queue
     satisfy its DMA obligation vacuously and be verified anyway.
     [wp_disk_loop] can only be proven by REFUTING this case from the disk
     invariant, so queue well-formedness becomes a standing obligation on the
     driver rather than a gift from the model. *)
  | DiskStepWild (mv : vmem) (w : gmap Arch.pa (bv 8)) :
      mem_view m mv ->
      virtio_stalled d.(dvirtio) mv = true ->
      disk_step d m d (w ∪ m)
  | DiskStepLatch p' :
      dev_irq_level d virtio_irq_id = true ->
      plic_latch d.(dplic) virtio_irq_id = Some p' ->
      disk_step d m (set_dplic d p') m
  (* the totality stutter -- see TOTALITY above.  It does NOT weaken the wild
     arm: a malformed queue still admits [DiskStepWild], which the invariant
     must still refute. *)
  | DiskStepIdle : disk_step d m d m.

(* The wire: propagate the PLIC's per-hart EIP level onto that hart's
   external S-interrupt pin.  Reads [dplic] (through [dev_seip], which is
   [plic_eip (dplic d)]) and writes one hart's register file; it needs no
   stutter, since the arm has no premise and any hart may be chosen. *)
Inductive plic_step (d : dev_state) (gr : CPU -> regstate)
    : (CPU -> regstate) -> Prop :=
  | PlicStepWire (c : CPU) :
      plic_step d gr
        (<[c := register_set sig_seip
                  (bool_to_bit (dev_seip d (fin_to_nat c))) (gr c)]> gr).

(* ---------------------------------------------------------------------- *)
(* 4. The language.  The program [Loop] steps ONE hart forever; which hart   *)
(*    is selected AMBIENTLY: the constructor [LoopE] carries the hart id and  *)
(*    the [Loop] notation fills it in from the surrounding [CpuId] instance.  *)
(*    Every WP therefore keeps the argument-free spelling [WP Loop {{...}}],  *)
(*    while [prim_step] over [gstate] reads the selected hart's registers,    *)
(*    pairs them with [gmem]/[gdev] to reconstruct that hart's [mstate], runs *)
(*    one [riscv_step], and writes the resulting registers, memory and        *)
(*    device state back.  [UartLoopE]/[DiskLoopE]/[PlicLoopE] are the THREE   *)
(*    device execution contexts: each steps its own relation forever,          *)
(*    interleaved with the harts and with each other.                         *)
(* ---------------------------------------------------------------------- *)

Class CpuId := cpu_id : CPU.

(* The GENERATION a thread belongs to (claude-notes/design/crash.md).
   Ambient, like [CpuId], and deliberately SEPARATE from it: parking /
   [wp_next] contracts quantify their continuations over the RESUMING
   CpuId, and that quantifier must range over harts of the SAME
   generation -- a parked proc's payload is era resources and dies with
   its generation.  Until the power thread lands, the semantics is
   GENERATION-BLIND: no [prim_step] arm reads or constrains the index
   (every arm preserves it), so a WP is provable at any fixed ambient
   generation and the tree is exactly as strong as before. *)
Class GenId := gen_id : nat.

Inductive mexpr :=
  | LoopE (gen : nat) (cpu : CPU)
  | UartLoopE (gen : nat)
  | DiskLoopE (gen : nat)
  | PlicLoopE (gen : nat)
  | PowerLoopE.

(* the machine state a PowerOn hands over (claude-notes/design/crash.md):
   same generation (PowerOff already bumped it), power up, a RAM-shaped
   memory, and the disk device RESET -- [virtio_reset] keeps [v_disk], the
   ONE crash-surviving component.  Deliberately MINIMAL so far: the
   UART/PLIC reset facts and the harts' reset registers join when their
   consumers (the device corollary, the M6 boot composition) land;
   tightening this predicate later only shrinks the PowerOn arm (the one
   proof it touches is [wp_power_loop]'s reducibility witness). *)
Definition boot_shape (g g' : gstate) : Prop :=
  g'.(ggen) = g.(ggen) /\ g'.(gpow) = true /\
  (forall a b, g'.(gmem) !! a = Some b ->
     (0x80000000 <= SailStdpp.Operators_mwords.uint a
        < 0x80000000 + 0x8000000)%Z) /\
  g'.(gdev).(dvirtio) = virtio_reset g.(gdev).(dvirtio).

(* what a PowerOn forks: the new generation's whole thread complement *)
Definition power_fork (gen : nat) : list mexpr :=
  (LoopE gen <$> enum CPU) ++ [UartLoopE gen; DiskLoopE gen; PlicLoopE gen].

(* a generation-indexed thread is LIVE iff the power is on and its
   generation is current; its real arms are gated on exactly that, and the
   CORPSE arm -- a pure self-loop -- is the complement.  A dead
   generation's thread can only take the corpse step, which needs no
   resources (RiscvExec.wp_dead). *)
Definition thread_live (g : gstate) (gen : nat) : Prop :=
  g.(gpow) = true /\ g.(ggen) = gen.
Definition mval := Empty_set.
Definition mobs := Empty_set.
Definition of_val (v : mval) : mexpr := match v with end.
Definition to_val (_ : mexpr) : option mval := None.

Notation Loop := (LoopE gen_id cpu_id).
Notation UartLoop := (UartLoopE gen_id).
Notation DiskLoop := (DiskLoopE gen_id).
Notation PlicLoop := (PlicLoopE gen_id).
Notation PowerLoop := PowerLoopE.

Definition prim_step
    (e : mexpr) (g : gstate) (κ : list mobs)
    (e' : mexpr) (g' : gstate) (efs : list mexpr) : Prop :=
  (exists gen cpu, e = LoopE gen cpu /\ e' = LoopE gen cpu /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists (tick : bool) (u : unit) (s' : mstate),
        run (riscv_step tick) (MState (g.(gregs) cpu) g.(gmem) g.(gdev)) u s' /\
        g' = GState (<[cpu := s'.(sregs)]> g.(gregs)) s'.(mem) s'.(mdev) g.(ggen) g.(gpow))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (exists gen, e = UartLoopE gen /\ e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists d',
        uart_step g.(gdev) d' /\
        g' = GState g.(gregs) g.(gmem) d' g.(ggen) g.(gpow))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (exists gen, e = DiskLoopE gen /\ e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists d' m',
        disk_step g.(gdev) g.(gmem) d' m' /\
        g' = GState g.(gregs) m' d' g.(ggen) g.(gpow))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (exists gen, e = PlicLoopE gen /\ e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists gr',
        plic_step g.(gdev) g.(gregs) gr' /\
        g' = GState gr' g.(gmem) g.(gdev) g.(ggen) g.(gpow))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (e = PowerLoopE /\ e' = PowerLoopE /\ κ = [] /\
    ((g.(gpow) = true /\ efs = [] /\
       (* PowerOff: kill the running generation INSTANTLY -- the bump is
          what makes [ggen > gen] the one stable death certificate *)
       g' = GState g.(gregs) g.(gmem) g.(gdev) (S g.(ggen)) false)
     \/
     (g.(gpow) = false /\ efs = power_fork g.(ggen) /\
       boot_shape g g'))).

Lemma riscv_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs
      [(gen & cpu & -> & _) | [(gen & -> & _) | [(gen & -> & _)
       | [(gen & -> & _) | (-> & _)]]]];
      reflexivity.
Qed.

Definition riscv_lang : language := Language riscv_lang_mixin.

