(* ============================================================== *)
(* RiscvAddTryStep.v -- consolidated Iris-over-Sail development.   *)
(* An Iris weakest-precondition for `add a2,a0,a1` executed by the *)
(* real Sail RISC-V `try_step`.  Self-contained except for:        *)
(*   - the generated model    : Riscv.rv64d / rv64d_types          *)
(*   - a small iris-FREE bv-arithmetic prelude : RiscvModelBytes    *)
(*     (kept separate ONLY because it uses vanilla `rewrite .. by`, *)
(*      which ssreflect -- pulled in by iris -- forbids).           *)
(* ============================================================== *)

From stdpp Require Import gmap finite relations bitvector.definitions.
From iris.program_logic Require Import language.
(* NOTE: SailStdpp.Base/Values/TypeCasts are imported LATER (before the         *)
(* ExecClose section), NOT here: they make the model's [mword] Countable        *)
(* (Countable_mword) canonical, but the Lang/Iris/Exec sections + the iris-free  *)
(* RiscvModelBytes must agree on stdpp's bv_countable for [gmap Arch.pa (bv 8)]  *)
(* (= the [mstate.mem] type).  Importing them here would retype mstate.mem and   *)
(* clash with read_bytes.  See the import line just above RiscvModelExecClose.    *)
Require Import Riscv.rv64d_types Riscv.rv64d.
(* THE PROGRAM A POWER-ON RUNS -- [boot_facts]' register clause names it, so it
   has to live below this file.  [Require] without [Import] on purpose:
   ArchReset.v imports SailStdpp.Base, and importing that HERE would make
   [Countable_mword] canonical and retype [mstate.mem] (see the note above).
   Import is not transitive, so requiring it changes nothing. *)
Require ArchReset.
Require Import RiscvModelBytes.
Require Export DevModel.
(* The LOADED KERNEL IMAGE, as the loader/firmware leaves it at a boot
   (claude-notes/design/crash.md): [boot_shape] below pins RAM to it, so the
   image has to be nameable HERE, in the language.  Both files are
   auto-generated per-byte [gmap Z (bv 8)] literals over stdpp only -- no
   Sail, no iris -- so importing them costs ~0.03 s per file and pulls in
   nothing that could shift a typeclass instance. *)
From Kernel Require KernelInstrs KernelData.

(* ---- the tree-wide [set_solver] override (see FastSetSolver.v) ----      *)
(* This file is here as a PROPAGATION HUB, not because it uses sets: it is  *)
(* [Require Import]ed DIRECTLY by 796 of the tree's 1090 files, and         *)
(* [Require Export] only reaches a file that imports THIS one directly (or  *)
(* through an unbroken chain of Exports, which this tree does not have).    *)
(* Without a hub like this, a new proof would silently get stdpp's slow     *)
(* [set_solver] -- which is exactly the trap the override exists to remove. *)
(* EXPORT, not Import, and deliberately "dead": the nightly dead-import     *)
(* sweep skips [Require Export] lines.                                     *)
Require Export FastSetSolver.

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

(* ---------------------------------------------------------------------- *)
(* PEEL A STATE CHAIN WITH THESE, NEVER WITH [unfold set_reg; cbn [...]].  *)
(*                                                                         *)
(* [set_reg]'s body mentions [s] THREE times (once per field), so          *)
(* [unfold set_reg] over an N-deep chain writes out a 3^N TREE -- the      *)
(* result is a small DAG, but every kernel pass at [Qed] that walks the    *)
(* term as a tree (HConstr.of_constr, sort_and_universes_of_constr) pays   *)
(* the unfolded size.  [utrap_state] alone is a 12-deep chain (3^12 = 531k)*)
(* and each subsequent [rewrite] copies that into an [eq_ind_r] motive.    *)
(* Measured on [UserClassify.active_step_branch]: the [unfold] spelling    *)
(* built a 24,508,005-node proof term for an 11,511-node DAG; the three    *)
(* rewrites below build 1,062,390 nodes for the SAME proof (23x smaller),  *)
(* taking the file from 23.4 s / 1832 MB to 8.7 s / 722 MB.                *)
(*                                                                         *)
(* They are goal-identical drop-ins: on the [sregs] projection             *)
(* [rewrite ?sregs_set_reg] leaves exactly what [unfold set_reg;           *)
(* cbn [sregs]] leaves, so whatever tactic followed still applies          *)
(* ([irrelevant_register_set], [register_lookup_set], [iFrame], ...).      *)
(* ---------------------------------------------------------------------- *)
Lemma sregs_set_reg (s : mstate) (r : register) (v : type_of_register r) :
  (set_reg s r v).(sregs) = register_set r v s.(sregs).
Proof. reflexivity. Qed.

Lemma mem_set_reg (s : mstate) (r : register) (v : type_of_register r) :
  (set_reg s r v).(mem) = s.(mem).
Proof. reflexivity. Qed.

Lemma mdev_set_reg (s : mstate) (r : register) (v : type_of_register r) :
  (set_reg s r v).(mdev) = s.(mdev).
Proof. reflexivity. Qed.


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

(* ---------------------------------------------------------------------- *)
(* A RESERVATION (claude-notes/design/main-cycle-port.md §3a): what a hart's *)
(* exclusive RAM read leaves behind -- the bytes it read, keyed by address.  *)
(* [dom r] is the reserved FOOTPRINT; the values are the SNAPSHOT.  While a  *)
(* hart holds one, no OTHER thread may write those bytes (it self-loops),   *)
(* so the language keeps [r ⊆ gmem] as a step invariant ([resv_ok]) -- the  *)
(* fact the conditional-write rule needs to know its RMW is atomic.  Every   *)
(* [MemWrite] event of the hart and the cycle boundary clear it; a new       *)
(* exclusive read overwrites it, so a dangling one never outlives its cycle. *)
(* ---------------------------------------------------------------------- *)
Definition resv : Type := gmap Arch.pa (bv 8).

(* the byte footprint of an [n]-byte access at [pa] *)
Definition footprint (pa : Arch.pa) (n : N) : gset Arch.pa :=
  list_to_set (pa_add pa <$> seq 0 (N.to_nat n)).

(* the snapshot an exclusive read of value [w] records: [dom] = [footprint] *)
Definition snap_of {w : N} (pa : Arch.pa) (n : N) (v : bv w) : resv :=
  write_bytes ∅ pa n v.

Record gstate := GState {
  gregs : CPU -> regstate;
  gmem  : gmap Arch.pa (bv 8);
  gdev  : dev_state;
  (* the power/crash layer (claude-notes/design/crash.md): the current
     GENERATION and the POWER bit.  LIVE: every hart and device arm below is
     gated on [thread_live g gen] ([gpow] set and [ggen] equal to the
     thread's own generation), with a pure self-loop on the COMPLEMENT, and
     the power thread's own arms clear [gpow] while bumping [ggen].  The
     gating partitions, so the relation stays total without a stutter arm --
     and [ggen > gen] is the one stable death certificate. *)
  ggen : nat;
  gpow : bool;
  (* each hart's outstanding reservation, if any (§3a) *)
  gresv : CPU -> option resv;
}.

(* pointwise update of a single hart's register file *)
Global Instance greg_insert : Insert CPU regstate (CPU -> regstate) :=
  fun cpu rs gr c => if decide (c = cpu) then rs else gr c.

(* ... and of a single hart's reservation slot *)
Global Instance gresv_insert : Insert CPU (option resv) (CPU -> option resv) :=
  fun cpu r gr c => if decide (c = cpu) then r else gr c.

(* the bytes reserved by every hart OTHER than [cpu] -- what blocks [cpu]'s
   stores and exclusive reads -- and by every hart at all -- what blocks the
   disk's DMA. *)
Definition resv_dom (gr : CPU -> option resv) (c : CPU) : gset Arch.pa :=
  match gr c with Some r => dom r | None => ∅ end.

Definition others_resv (gr : CPU -> option resv) (cpu : CPU) : gset Arch.pa :=
  ⋃ ((fun c => if decide (c = cpu) then ∅ else resv_dom gr c) <$> enum CPU).

Definition all_resv (gr : CPU -> option resv) : gset Arch.pa :=
  ⋃ (resv_dom gr <$> enum CPU).

(* THE STEP INVARIANT the reservation guards buy: every outstanding snapshot
   still agrees with memory.  Held as a pure conjunct of the state
   interpretation; re-established by every memory-writing arm below. *)
Definition resv_ok (g : gstate) : Prop :=
  forall c r, g.(gresv) c = Some r -> r ⊆ g.(gmem).

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

(* A UART step never moves the disk IMAGE either (crash.md): each arm
   rebuilds the fabric through [set_duart]/[set_dplic], which keep
   [dvirtio] verbatim.  This is what lets [wp_uart_step] FRAME
   [state_interp]'s durable disk conjunct.  ([plic_step] and the disk's own
   latch/idle arms need no lemma: their [d'] is syntactically [d] or
   [set_dplic d _], so the framing is by conversion.) *)
Lemma uart_step_v_disk (d d' : dev_state) :
  uart_step d d' -> v_disk (dvirtio d') = v_disk (dvirtio d).
Proof. intros H. destruct H; reflexivity. Qed.

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
   its generation.  The semantics READS this index: a thread's real arms
   are gated on [thread_live], so a WP at a fixed ambient generation is
   provable only while that generation is current -- a dead one can take
   only the corpse self-loop. *)
Class GenId := gen_id : nat.

(* ---------------------------------------------------------------------- *)
(* THE HART EXPRESSION CARRIES THE IN-FLIGHT SAIL MONAD                     *)
(* (claude-notes/design/main-cycle-port.md).                                *)
(*                                                                          *)
(* THE PLACEMENT RULE.  Control state lives in the EXPRESSION exactly where  *)
(* control flow is MODEL-defined, and in [gstate] where it is MEMORY-        *)
(* defined.  INTER-instruction control flow is memory-defined -- the next    *)
(* instruction is fetched through a page table out of mutable memory, which  *)
(* has to be PROVEN -- so the instruction boundary is a boring token and the *)
(* registers/PC stay in σ.  INTRA-instruction control flow is model-defined: *)
(* the continuation IS the Sail monad value, syntactically known and         *)
(* consumed monotonically.  So [HartE gen cpu m] is: hart [cpu] of           *)
(* generation [gen], with [m] left to run of the current cycle -- and        *)
(* WP-of-an-instruction becomes proof by syntactic descent on [m].           *)
(*                                                                          *)
(* [LoopE] is a DEFINITION, not a constructor: the boundary is the unique    *)
(* end-of-cycle value [Ret tt] (the cycle's result type is [unit]).  Every   *)
(* statement in the tree that mentions [LoopE gen cpu] therefore keeps       *)
(* elaborating unchanged; only proofs that unfold the hart step break.       *)
(*                                                                          *)
(* THE LOOP LIVES IN THE STEP RELATION, and that is the only place it can:   *)
(* [M] is an inductive type, so there is no in-monad loop value (the         *)
(* immediate-subterm relation on [M] is well-founded).  [hart_node_step]     *)
(* unfolds it at the boundary, choosing the tick nondeterministically        *)
(* exactly as the old whole-instruction arm did.                             *)
(* ---------------------------------------------------------------------- *)

Inductive mexpr :=
  | HartE (gen : nat) (cpu : CPU) (m : M unit)
  | UartLoopE (gen : nat)
  | DiskLoopE (gen : nat)
  | PlicLoopE (gen : nat)
  | PowerLoopE.

(* THE INSTRUCTION BOUNDARY.  [Ret tt] is the unique value of [M unit], so
   this is exactly "hart [cpu] has nothing left to run of its cycle". *)
Definition LoopE (gen : nat) (cpu : CPU) : mexpr :=
  HartE gen cpu (Interface.Ret tt).

(* ---------------------------------------------------------------------- *)
(* IS THIS ACCESS EXCLUSIVE (the read/write halves of an atomic RMW)?       *)
(*                                                                          *)
(* Read off the ACCESS KIND alone.  [AK_ifetch]/[AK_ttw] are never emitted  *)
(* by this model (fetch goes through [mem_read (InstructionFetch tt) …] and  *)
(* the walker through [mem_read_priv (Load PageTableEntry) …], both landing  *)
(* in [Read_plain]), so those arms are faithful but dead; they are spelled   *)
(* out anyway so a model regeneration that starts emitting them is a         *)
(* semantics change rather than a silent reclassification.                   *)
(* [AV_atomic_rmw] is never emitted either -- AMOs use the CONDITIONAL       *)
(* (exclusive) kinds -- and both are treated the same here, so nothing is    *)
(* lost by the merge.                                                        *)
(* ---------------------------------------------------------------------- *)
(* Spelled with QUALIFIED names: RiscvLang must not [Import]
   SailStdpp.ConcurrencyInterfaceTypes -- see the header note on
   [Countable_mword] and the type of [mstate.mem]. *)
Definition av_excl (v : SailStdpp.ConcurrencyInterfaceTypes.Access_variety)
    : bool :=
  match v with
  | SailStdpp.ConcurrencyInterfaceTypes.AV_plain => false
  | SailStdpp.ConcurrencyInterfaceTypes.AV_exclusive => true
  | SailStdpp.ConcurrencyInterfaceTypes.AV_atomic_rmw => true
  end.

Definition ak_excl (ak : Interface.accessKind) : bool :=
  match ak with
  | SailStdpp.ConcurrencyInterfaceTypes.AK_explicit eak =>
      av_excl (SailStdpp.ConcurrencyInterfaceTypes.Explicit_access_kind_variety eak)
  | SailStdpp.ConcurrencyInterfaceTypes.AK_ifetch _ => false
  | SailStdpp.ConcurrencyInterfaceTypes.AK_ttw _ => false
  | SailStdpp.ConcurrencyInterfaceTypes.AK_arch a =>
      av_excl (RISCV_strong_access_variety a)
  end.

(* ---------------------------------------------------------------------- *)
(* THE HART'S PER-NODE STEP.                                                *)
(*                                                                          *)
(* One arm per [Interface.outcome] node, transcribing what [run]'s          *)
(* interpreter does at that node -- registers against [gregs cpu], RAM       *)
(* against [gmem], MMIO against [gdev] through [dev_read]/[dev_write].       *)
(* Alignment/PMA/permission logic stays INSIDE the monad, where the model    *)
(* put it.  Fences are semantically inert at SC, so [Barrier] is silent.     *)
(*                                                                          *)
(* EXCLUSIVE ACCESSES (design §3a) are NOT fused: an exclusive RAM read is   *)
(* an ordinary read that also RECORDS its snapshot as this hart's            *)
(* reservation; the window that follows it is ordinary nodes; the paired     *)
(* conditional write is an ordinary RAM write.  Atomicity is mutual          *)
(* exclusion on the reserved bytes: while ANOTHER hart's reservation         *)
(* overlaps, a RAM write or an exclusive read SELF-LOOPS ([m' = m], state    *)
(* unchanged) -- a step, not a stuck state, so nobody's reducibility          *)
(* depends on it.  Every [MemWrite] event clears the hart's own reservation  *)
(* (so it never outlives the silent stretch it protects) and so does the     *)
(* boundary; a fresh exclusive read overwrites it, blocked or not (the       *)
(* region begins at the LAST exclusive read).  A BLOCKED WRITE KEEPS its     *)
(* reservation: releasing there would let the write's own arm run            *)
(* unguarded, and then [resv_ok] is inductive only together with pairwise    *)
(* disjointness of all reservations -- a second invariant nobody wants to    *)
(* carry.  Plain reads are never blocked and never reserve.                  *)
(*                                                                          *)
(* STUCK IS FINE.  [GenericFail]/[Discard]/[ExtraOutcome] have no arm, and   *)
(* there is deliberately NO shape or liveness predicate about the monad --   *)
(* a shape predicate is a promise about an instruction's FUTURE, and no rule *)
(* here mentions the future.                                                 *)
(*                                                                          *)
(* SEMANTIC DELTA, stated honestly: mid-instruction interleaving is now      *)
(* REAL.  Another hart's or a device's step can land between two events of   *)
(* one instruction.  At SC this admits strictly more runs than the old       *)
(* whole-instruction machine, whose runs embed as the contiguous-block       *)
(* special case (see the solo-block bracket in RiscvExec.v).                 *)
(* ---------------------------------------------------------------------- *)

(* THE HART-LOCAL NODE STEP, on ONE HART'S VIEW [mstate] -- the same
   currency [run] works in, and the same currency the lifting layer's
   σ-callback hands the caller ([mstate_interp]) -- PLUS the reservation
   context: [oth] is the byte set reserved by every OTHER hart (read-only
   here), [r]/[r'] this hart's own reservation before and after.
   [hart_node_step] below is then literally "focus this hart, take one local
   node, write back", exactly the shape the old whole-instruction arm had
   with [run] in place of [mnode_step]. *)
Definition mnode_step (oth : gset Arch.pa) (s : mstate) (r : option resv)
    (m : M unit) (m' : M unit) (s' : mstate) (r' : option resv) : Prop :=
  match m with
  (* THE BOUNDARY / RESTART RULE.  The cycle is over; begin the next one.
     [tick] is chosen nondeterministically here exactly as the old
     whole-instruction arm chose it -- the sound weakening of the model
     [loop]'s deterministic every-[plat_insns_per_tick] tick.  A dangling
     reservation is dropped here: it never crosses an instruction. *)
  | Interface.Ret _ =>
      exists tick : bool, m' = riscv_step tick /\ s' = s /\ r' = None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> Prop with
       (* registers *)
       | Interface.RegRead rg _ => fun k =>
           m' = k (register_lookup rg s.(sregs)) /\ s' = s /\ r' = r
       | Interface.RegWrite rg _ v => fun k =>
           m' = k tt /\ s' = set_reg s rg v /\ r' = r
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             (* MMIO: the device answers, and its state may move (an RHR read
                pops the receive FIFO).  The accessor is the PARTIAL one -- a
                bad width or an undecoded offset inside a device window is
                stuck, which costs nothing: nothing in this tower ever has to
                know that an instruction COMPLETES. *)
             exists (w : bv (8 * n)) (d' : dev_state),
               dev_read s.(mdev) (Interface.ReadReq.pa req) n = Some (w, d') /\
               m' = k (inl (w, None)) /\ s' = MState s.(sregs) s.(mem) d' /\
               r' = r
           else
             (* THE PLAIN RAM READ: never blocked, never reserves. *)
             (ak_excl (Interface.ReadReq.access_kind req) = false /\
              exists w : bv (8 * n),
                (forall j : nat, (N.of_nat j < n)%N ->
                   s.(mem) !! (pa_add (Interface.ReadReq.pa req) j)
                   = Some (nth_byte w j)) /\
                m' = k (inl (w, None)) /\ s' = s /\ r' = r)
             \/
             (* THE EXCLUSIVE RAM READ: blocked (self-loop) while another
                hart reserves any of its bytes -- and a hart that has reached
                a NEW exclusive read has abandoned whatever it reserved before,
                so the wait releases it (a waiting hart holds nothing, hence
                no wait-for cycle through exclusive reads); otherwise the same
                read, and its snapshot becomes this hart's reservation,
                replacing any stale one. *)
             (ak_excl (Interface.ReadReq.access_kind req) = true /\
              ((~ (footprint (Interface.ReadReq.pa req) n ## oth) /\
                m' = Interface.Next (Interface.MemRead n req) k /\
                s' = s /\ r' = None)
               \/
               (footprint (Interface.ReadReq.pa req) n ## oth /\
                exists w : bv (8 * n),
                  (forall j : nat, (N.of_nat j < n)%N ->
                     s.(mem) !! (pa_add (Interface.ReadReq.pa req) j)
                     = Some (nth_byte w j)) /\
                  m' = k (inl (w, None)) /\ s' = s /\
                  r' = Some (snap_of (Interface.ReadReq.pa req) n w))))
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             (* MMIO write: a [MemWrite] event, so it clears the reservation *)
             exists d' : dev_state,
               dev_write s.(mdev) (Interface.WriteReq.pa req) n
                 (Interface.WriteReq.value req) = Some d' /\
               m' = k (inl None) /\ s' = MState s.(sregs) s.(mem) d' /\
               r' = None
           else
             (* THE RAM WRITE, conditional or plain alike (the access kind
                plays no role): blocked (self-loop) while another hart
                reserves any of its bytes; otherwise written, and this hart's
                own reservation is cleared.  A conditional write on the
                hart's own reservation is never blocked -- no other hart can
                hold an overlapping one -- but the arm does not need to know
                that: the rule absorbs the self-loop by Löb either way. *)
             (~ (footprint (Interface.WriteReq.pa req) n ## oth) /\
              m' = Interface.Next (Interface.MemWrite n req) k /\
              s' = s /\ r' = r)
             \/
             (footprint (Interface.WriteReq.pa req) n ## oth /\
              m' = k (inl None) /\
              s' = MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                        (Interface.WriteReq.value req)) s.(mdev) /\
              r' = None)
       (* trace / announce / fence outcomes: state no-ops, exactly as [run].
          At SC a fence is semantically inert, so [Barrier] is silent and
          nothing is parked. *)
       | Interface.InstrAnnounce _    => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.BranchAnnounce _ _ => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.Barrier _          => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.CacheOp _          => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.TlbOp _            => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.TakeException _    => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.ReturnException _  => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.TranslationStart _ => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.TranslationEnd _   => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.CycleCount         => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.Message _          => fun k => m' = k tt /\ s' = s /\ r' = r
       | Interface.GetCycleCount      => fun k => m' = k 0%Z /\ s' = s /\ r' = r
       (* nondeterminism: branch over every choice *)
       | Interface.Choose _           => fun k => exists ch, m' = k ch /\ s' = s /\ r' = r
       (* failure / discard / injected exception: stuck *)
       | _ => fun _ => False
       end) k
  end.

(* ... and the global arm: focus the hart, take one local node, write back.
   Compare the OLD hart arm, which was this with [run (riscv_step tick)] in
   place of [mnode_step] -- the write-back is character-for-character the
   same, which is why the lifting rule's proof structure survives. *)
Definition hart_node_step (gen : nat) (g : gstate) (cpu : CPU) (m : M unit)
    (e' : mexpr) (g' : gstate) : Prop :=
  exists (m' : M unit) (s' : mstate) (r' : option resv),
    mnode_step (others_resv g.(gresv) cpu)
      (MState (g.(gregs) cpu) g.(gmem) g.(gdev)) (g.(gresv) cpu) m m' s' r' /\
    e' = HartE gen cpu m' /\
    g' = GState (<[cpu := s'.(sregs)]> g.(gregs)) s'.(mem) s'.(mdev)
           g.(ggen) g.(gpow) (<[cpu := r']> g.(gresv)).

(* ---------------------------------------------------------------------- *)
(* THE RESET MACHINE (claude-notes/design/crash.md): what the loader and    *)
(* the hardware leave behind at a PowerOn.  Everything a boot proof needs   *)
(* to READ off the fresh machine is pinned here, and nothing else is: every *)
(* register [SpecEntry.wp_entry_boot] quantifies over (mepc/satp/medeleg/   *)
(* mideleg/mie/mcounteren/stimecmp/pmpaddr_n) is deliberately left          *)
(* arbitrary, so this predicate stays as weak as the hardware.              *)
(* ---------------------------------------------------------------------- *)

(* RAM as the platform wires it.  [RiscvPtsto.addr_is_ram] is exactly
   [ram_lo <= uint a < ram_hi] (its [ram_base]/[ram_size] live ABOVE this
   file, so the constants are spelled here; keep the two in sync). *)
Definition ram_lo : Z := 0x80000000.
Definition ram_hi : Z := 0x88000000.

(* THE LOADED IMAGE.  The ELF's loadable bytes -- text ([kernel_bytes]) and
   data ([kernel_data]) -- RESTRICTED to the file image [ram_lo, img_end).
   The restriction is what makes ".bss is zero-filled" a SYMBOLIC fact: at
   or above [img_end] the filter yields [None], so [boot_byte] is [byte0]
   with no lookup into either 20k-entry literal.  [img_end] is the single
   PT_LOAD's vaddr + filesz, and [.bss] runs from there up to
   [KernelData.kernelMemEnd].

   IT IS COMPUTED FROM THE DUMP, not transcribed from it: the dumper already
   emits the program headers as [KernelData.kernel_segments], so a literal
   here was pure duplication -- and a stale one surfaced as an unhelpful
   [lia] "Cannot find witness" deep inside BootCarve.v rather than at this
   line.  The [ltac:(eval vm_compute)] form is durable-notes.md's "compute
   the result ONCE into its own Definition" idiom: the body is a plain [Z]
   literal by the time anything downstream sees it, so [unfold img_end; lia]
   reduces exactly as it did before. *)
Definition img_end : Z :=
  ltac:(let x := eval vm_compute in
          (match KernelData.kernel_segments with
           | (va, filesz, _, _) :: _ => (va + filesz)%Z
           | [] => 0%Z
           end) in exact x).

(* THE READ-ONLY/WRITABLE BOUNDARY inside the loaded image -- one past the
   last byte the kernel can never store to.  The PT_LOAD [img_end] is built
   from is a SINGLE RWX segment, so it says nothing about this; only the
   ELF's SECTION flags do, and [KernelData.kernelRodataEnd] is the dumper's
   reading of them (the lowest writable allocated section's address).  So the
   image splits THREE ways, not two:

     [ram_lo, rodata_end)   .text / .rodata / .eh_frame -- read-only image
                            material, immutable for the life of the image;
     [rodata_end, img_end)  .data / .got / .got.plt -- INITIALIZED but
                            WRITABLE (xv6's `first` and `nextpid` live here);
     [img_end, kernelMemEnd)  .bss -- zero-filled and writable.

   Only the first range may be resided at [DfracDiscarded]: a persistent
   points-to at an address the kernel stores to is an INCONSISTENT premise,
   not a failed proof, and it makes every contract that carries it vacuous.
   Computed from the dump by the same [ltac:(eval vm_compute)] idiom as
   [img_end], so [unfold rodata_end; lia] sees a plain [Z] literal. *)
Definition rodata_end : Z :=
  ltac:(let x := eval vm_compute in KernelData.kernelRodataEnd in exact x).

Definition boot_image : gmap Z (bv 8) :=
  base.filter (fun ab : Z * bv 8 => (ab.1 < img_end)%Z)
    (KernelInstrs.kernel_bytes ∪ KernelData.kernel_data).

(* the byte the loader leaves at [a]: the image's where it has one, zero
   everywhere else in RAM (.bss and the free pages) *)
Definition boot_byte (a : Z) : bv 8 := default byte0 (boot_image !! a).

(* a 64-bit reset value, spelled once (the model's [mword_of_int] is not
   imported unqualified here -- see the header note) *)
Definition boot_w64 (z : Z) : SailStdpp.Values.mword 64 :=
  SailStdpp.Values.mword_of_int z.

(* THE PLATFORM'S PMA TABLE -- THE MODEL'S OWN, three regions and the holes
   between them.  [sail_model_init] ends with one [write_reg pma_regions] of
   exactly this list (the values come from the memory map in
   model-xv6iris/sail-config-rv64d.json).  It is the BOARD's table -- written by
   [ArchReset.board_init], since the anchored boot program does not run the
   model's initializers (see that file's header) -- and it is kernel-checked
   against them anyway by [ColdBoot.board_regs_after_sim], which RUNS
   [sail_model_init] and shows this write is a no-op after it.  So a config or
   model move that changes a base, a size or an attribute breaks the build
   rather than silently making this transcription a fiction (the discipline
   [RiscvFetchExec.MISA_C] / [ColdBoot.cold_boot_misa] follow).

   WHAT THE THREE REGIONS ARE.  The boot ROM at 0x1000 is IOMemory, read-only
   and NOT executable; nothing the proofs touch lives there, and it matters
   only because it is FIRST in the list and so has to be shown NOT to match a
   RAM or a device access.  The MMIO band at 0x2000000 (size 0x10000000) is
   IOMemory R/W with no atomics and no PTE access, and every device window sits
   inside it (CLINT, PLIC, UART, virtio-mmio -- [RiscvPtsto.mmio_base]).  The
   DRAM bank at 0x80000000 (size [ram_hi - ram_lo]) is MainMemory R/W/X with
   AMOCASQ atomics -- so every AMO the decoder can produce is permitted there,
   at every width up to 16 -- and PTE reads/writes, and its range is EXACTLY
   [RiscvPtsto.addr_is_ram]'s.  It also carries a 16-byte MISALIGNED ATOMICITY
   GRANULE (the two [..._granule_size_exp] fields = 4, per Zama16b), which the
   two IOMemory regions do not (= 0, i.e. absent): that granule is what
   [pmaCheck] consults to decide whether a misaligned access is split, and it
   is irrelevant to every access these proofs perform, all of which are
   naturally aligned and therefore never split.  BETWEEN AND OUTSIDE THEM THERE ARE HOLES,
   which is why the tower's obligation is per address class
   ([RiscvFetchExec.pma_allows_ram] / [pma_allows_io]) and why an
   all-addresses one could only ever have held of an idealization. *)
Definition pma_boot_rom_attrs : PMA := {|
  PMA_mem_type := IOMemory;
  PMA_cacheable := true;
  PMA_coherent := false;
  PMA_executable := false;
  PMA_readable := true;
  PMA_writable := false;
  PMA_read_idempotent := true;
  PMA_write_idempotent := true;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMONone;
  PMA_reservability := RsrvNone;
  PMA_supports_cbo_zero := false;
  PMA_supports_pte_read := false;
  PMA_supports_pte_write := false;
  PMA_misaligned_atomicity_granule_size_exp := 0;
  PMA_vector_misaligned_atomicity_granule_size_exp := 0 |}.

Definition pma_boot_io_attrs : PMA := {|
  PMA_mem_type := IOMemory;
  PMA_cacheable := false;
  PMA_coherent := true;
  PMA_executable := false;
  PMA_readable := true;
  PMA_writable := true;
  PMA_read_idempotent := false;
  PMA_write_idempotent := false;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMONone;
  PMA_reservability := RsrvNone;
  PMA_supports_cbo_zero := false;
  PMA_supports_pte_read := false;
  PMA_supports_pte_write := false;
  PMA_misaligned_atomicity_granule_size_exp := 0;
  PMA_vector_misaligned_atomicity_granule_size_exp := 0 |}.

Definition pma_boot_ram_attrs : PMA := {|
  PMA_mem_type := MainMemory;
  PMA_cacheable := true;
  PMA_coherent := true;
  PMA_executable := true;
  PMA_readable := true;
  PMA_writable := true;
  PMA_read_idempotent := true;
  PMA_write_idempotent := true;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMOCASQ;
  PMA_reservability := RsrvEventual;
  PMA_supports_cbo_zero := true;
  PMA_supports_pte_read := true;
  PMA_supports_pte_write := true;
  PMA_misaligned_atomicity_granule_size_exp := 4;
  PMA_vector_misaligned_atomicity_granule_size_exp := 4 |}.

Definition pma_boot : list PMA_Region :=
  [ {| PMA_Region_base := boot_w64 0x1000;
       PMA_Region_size := boot_w64 0x1000;
       PMA_Region_attributes := pma_boot_rom_attrs;
       PMA_Region_include_in_device_tree := false |};
    {| PMA_Region_base := boot_w64 0x2000000;
       PMA_Region_size := boot_w64 0x10000000;
       PMA_Region_attributes := pma_boot_io_attrs;
       PMA_Region_include_in_device_tree := false |};
    {| PMA_Region_base := boot_w64 ram_lo;
       PMA_Region_size := boot_w64 (ram_hi - ram_lo);
       PMA_Region_attributes := pma_boot_ram_attrs;
       PMA_Region_include_in_device_tree := true |} ].

(* ====================================================================== *)
(* THE PMP CONFIGURATION A BOOT CONSUMER CONSUMES: every entry OFF         *)
(* (disabled) AND unlocked.  With no entry ever matching, M-mode grants     *)
(* accesses of ANY width -- in particular the 8-byte loads/stores, whose    *)
(* pmpCheck cannot be discharged from unlocked-ness alone: an 8-byte access *)
(* can PARTIALLY overlap a TOR/NA4 region boundary (any multiple of 4) at   *)
(* an unfortunate pmpaddr value, and a partial match faults even in M-mode. *)
(* The 8-byte data-access WPs therefore take [pmp_all_off]; it implies       *)
(* [RiscvFetchExec.pmp_allows_all] (for their instruction fetches) by        *)
(* projection ([pmp_all_off_allows_all], which lives with that weaker        *)
(* predicate).                                                              *)
(*                                                                        *)
(* IT LIVES HERE, not with the WPs that consume it, because [reset_regs]    *)
(* below states the reset machine's PMP obligation AS THIS PREDICATE rather *)
(* than as a pinned register value -- the spec-design rule that a           *)
(* hardware-attribute obligation says what the consumer consumes.  The      *)
(* architecture gives only A = OFF and L = 0 per entry (that is all         *)
(* [reset_pmp] establishes), and that is exactly what this asks for.        *)
(* ====================================================================== *)
Definition pmp_all_off (cfg : type_of_register pmpcfg_n) : Prop :=
  forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (SailStdpp.Values.vec_access_dec cfg i)) = OFF
         /\ pmpLocked (SailStdpp.Values.vec_access_dec cfg i) = false.

(* pmpcfg with every entry OFF and unlocked -- the all-zero vector the
   model's [reset_pmp] leaves behind when it clears A and L in all 64 entries
   of a power-on-zero register file.  This is a WITNESS, not an obligation:
   [reset_regs] asks only for [pmp_all_off], and this value is what
   [PowerBoot.boot_regs] writes and what the closed cold-boot run computes
   ([ColdBoot.cold_boot_pmpcfg]).  All-zero bytes: A = bits[4:3] = 0 decodes
   to OFF and L = bit 7 is clear, and the out-of-range default of
   [vec_access_dec] is the [Inhabited] zero as well, so the property holds
   at EVERY index. *)
Definition pmpcfg_boot
    : SailStdpp.Values.vec (SailStdpp.Values.mword 8) 64 :=
  SailStdpp.Values.vector_init 64 (SailStdpp.Values.mword_of_int 0).

(* [pmpcfg_boot] is [vector_init 64 0], and [pmp_all_off] quantifies over a
   [Z] index with no range premise -- so the OUT-OF-RANGE reads matter, and
   they are what makes the fact hold at every index: [vec_access_dec] falls
   back on the [Inhabited] default, which for [mword 8] is the same zero byte
   the vector is filled with.  Below the index range the fallback is taken by
   [access_list_inc]'s own guard; above it, by [nth] running off the list. *)
Local Lemma nth_pmp_zero (k : nat) :
  nth k (SailStdpp.Values.repeat
           [(SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8)] 64)
      inhabitant
  = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8).
Proof.
  vm_compute (SailStdpp.Values.repeat _ 64).
  do 64 (destruct k as [|k]; [reflexivity |]).
  destruct k; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pmpcfg_boot_entry (i : Z) :
  SailStdpp.Values.vec_access_dec pmpcfg_boot i
  = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8).
Proof.
  unfold pmpcfg_boot, SailStdpp.Values.vec_access_dec,
         SailStdpp.Values.vector_init.
  destruct (sumbool_of_bool (64 >=? 0)) as [GE | NGE]; [| discriminate NGE].
  cbn [projT1].
  unfold SailStdpp.Values.access_list_dec, SailStdpp.Values.access_list_inc.
  destruct (_ <? 0); [ apply bv_eq; vm_compute; reflexivity | apply nth_pmp_zero ].
Qed.

Lemma pmp_all_off_pmpcfg_boot : pmp_all_off pmpcfg_boot.
Proof.
  intro i. rewrite pmpcfg_boot_entry. split; vm_compute; reflexivity.
Qed.

(* THE PER-HART RESET REGISTERS.  Every value here is either the model's own
   reset ([sail_model_init]/[reset]) or the platform's configuration; the
   remaining PREDICATES the boot proof needs of them ([pma_allows_all
   pma_boot], the MISA bit facts, mstatus's MIE/MPRV/SXL, menvcfg's LPE) are
   consequences, proved where those predicates live (they are above this file).
   ONE conjunct is stated AS THE PREDICATE ITS CONSUMER CONSUMES rather than as
   a value -- pmpcfg's [pmp_all_off] (above): the architecture gives A = OFF
   and L = 0 per entry and nothing more, so a pinned [pmpcfg_boot] would claim
   the other five bits of all 64 entries for no consumer.  Prefer that shape for
   any future hardware-attribute conjunct.
   NO VALUE BELOW IS TAKEN ON TRUST.  [ColdBoot.reset_regs_cold_boot] runs the
   Sail model's OWN cold-boot chain ([sail_model_init]; the board's reset vector
   and hart id; [init_model]; [init_boot_requirements]) with [RiscvExec.exec]
   and proves this predicate of the register file it produces -- so the
   justification of each value is a compiled theorem, not a table, and a model
   regeneration that changes one breaks the build.  NO conjunct is an explicit
   [register_set] patch in that theorem any more.  Read ColdBoot.v's header for
   the one platform hook the interpreter cannot step and for the COLD-vs-warm
   caveat. *)
Definition reset_regs (c : CPU) (rs : regstate) : Prop :=
  (* the pc a hart comes out of reset at.  [KernelSyms._entry] is 0x80000000
     but KernelSyms is above this file, so the literal is spelled here and
     the M6 bridge equates the two. *)
  register_lookup PC rs = boot_w64 0x80000000
  (* ... and nextPC AT THE SAME VALUE.  [InstrBytes.pc_is x] is
     [PC ↦ᵣ x ∗ nextPC ↦ᵣ x] -- one [x] pinning BOTH cells -- so owning the
     nextPC cell is necessary but not sufficient: without this clause a boot
     client gets the cell at an arbitrary value and cannot build [pc_is] at
     [_entry] at all.  The model keeps the two in lock-step during
     straight-line execution (a tick sets PC := nextPC), and a reset hart is
     at the start of such a run. *)
  /\ register_lookup nextPC rs = boot_w64 0x80000000
  /\ register_lookup cur_privilege rs = Machine
  /\ register_lookup hart_state rs = HART_ACTIVE tt
  (* mhartid IS the hart index: this is what makes [_entry]'s per-hart stack
     carve and SpecMain's arm choice (cid_word = zero_reg for hart 0) line up
     with the CPU the thread runs on. *)
  /\ register_lookup mhartid rs = boot_w64 (Z.of_nat (fin_to_nat c))
  (* SXL = UXL = 2 (64-bit), MIE = MPRV = 0 -- the model's own
     [sail_model_init], and [BootBridge.mstatus_reset] *)
  /\ register_lookup mstatus rs = boot_w64 0xA00000000
  (* = [RiscvFetchExec.MISA_C]: MXL = 2 with A/C/D/F/I/M/S/U set -- exactly the
     bits [reset_misa] writes from [hartSupports], now that B and V are
     disabled in the model's config ([ColdBoot.cold_boot_misa] proves the tie).
     Run-derived, not assumed. *)
  /\ register_lookup misa rs = boot_w64 0x800000000014112D
  /\ register_lookup mseccfg rs = boot_w64 0
  /\ register_lookup menvcfg rs = boot_w64 0
  /\ register_lookup htif_tohost_base rs = None
  (* the model's [reset_elp]: no landing pad expected *)
  /\ register_lookup elp rs = landing_pad_bits_backwards NO_LP_EXPECTED
  /\ register_lookup pma_regions rs = pma_boot
  (* PMP: A = OFF and L = 0 in every entry, and NOT a pinned register value --
     [pmp_all_off] is exactly what [SpecEntry.wp_entry_boot] /
     [BootBridge.boot_bridge] take (at a quantified [pmpcfg0]), and it is all
     the architecture's [reset_pmp] gives.  The closed cold-boot run makes it a
     COMPUTED fact ([ColdBoot.cold_boot_pmp_all_off]); deriving it from
     [reset_pmp]'s per-entry RMW over an OPEN power-on register file is the
     ∀-garbage anchoring task's business (claude-notes/completed/crash.md). *)
  /\ pmp_all_off (register_lookup pmpcfg_n rs)
  (* mie AND mideleg CLEAR: every interrupt disabled, nothing delegated.  Like
     the [nextPC] pin above these are necessary-and-not-obvious, and for the
     same reason -- the S-mode side's [IntrDefs.sconf] requires that every
     enabled interrupt be delegated, and start()'s [csrs sie] does not clear
     an M-mode enable it finds already set while [legalize_mideleg] forces the
     matching delegation bit to 0.  So at a nonzero entry [mie] the boot
     chain's bridge is not provable at all (M6c (3)).  Justification: the
     model's own cold-boot path leaves them at the [regstate]'s initial value
     ([sail_model_init] writes neither, and [reset] does not either), so this
     is a PLATFORM assumption exactly like [pc_reset_address] and [mhartid]
     above -- one the model's own initial register file happens to agree with,
     which is what makes [ColdBoot.reset_regs_cold_boot] able to close these
     two conjuncts along with the rest. *)
  /\ register_lookup mie rs = boot_w64 0
  /\ register_lookup mideleg rs = boot_w64 0
  (* senvcfg = 0: like mseccfg/menvcfg, [reset_sys] never writes it and the
     kernel never writes it either, so it is a board obligation
     ([ArchReset.board_regs]'s ninth write) -- see that file's bullet.  This
     is what lets [hw_config] (RiscvFetchExec.v) hold it as a sixth frozen,
     persistently-shareable cell alongside misa/mseccfg/pma_regions/
     htif_tohost_base/elp. *)
  /\ register_lookup senvcfg rs = boot_w64 0
  (* THE TWO STATE-ENABLE PINS, and they come from DIFFERENT places.  The
     U-mode decode gates read both, so the user-execution tier needs the
     zeros, and [IntrDefs.hart_csrs] parks the two cells at these values.
     [mstateen0] is DERIVED over arbitrary garbage: [reset_sys] calls the
     spec's own [reset_stateen], which zeroes mstateen0..3.  [sstateen0] is
     NOT written by any line of the reset chain -- [reset_stateen] stops at
     the M-mode four -- so it is a BOARD obligation, [ArchReset.board_regs]'
     tenth write, exactly like mie / mideleg / senvcfg. *)
  /\ register_lookup mstateen0 rs = boot_w64 0
  /\ register_lookup sstateen0 rs = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32).

(* NAMED PROJECTIONS of the three clauses consumers ask for one at a time
   (pmpcfg, mie, mideleg).  [reset_regs] is a sixteen-way
   conjunction and positional destructuring of it in a consumer is exactly the
   brittleness that adding a conjunct exposes, so anything that wants ONE fact
   asks by name. *)
Lemma reset_regs_pmpcfg (c : CPU) (rs : regstate) :
  reset_regs c rs -> pmp_all_off (register_lookup pmpcfg_n rs).
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _ & _). exact H. Qed.

Lemma reset_regs_mie (c : CPU) (rs : regstate) :
  reset_regs c rs -> register_lookup mie rs = boot_w64 0.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma reset_regs_mideleg (c : CPU) (rs : regstate) :
  reset_regs c rs -> register_lookup mideleg rs = boot_w64 0.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma reset_regs_senvcfg (c : CPU) (rs : regstate) :
  reset_regs c rs -> register_lookup senvcfg rs = boot_w64 0.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma reset_regs_mstateen0 (c : CPU) (rs : regstate) :
  reset_regs c rs -> register_lookup mstateen0 rs = boot_w64 0.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma reset_regs_sstateen0 (c : CPU) (rs : regstate) :
  reset_regs c rs ->
  register_lookup sstateen0 rs = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32).
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* WHAT A BOOTED MACHINE LOOKS LIKE, with no reference to the machine it
   replaces: this is the fact set the power thread hands the boot client
   ([RiscvAdequacy.power_boot_res]'s [Hboot] premise). *)
Definition boot_facts (g' : gstate) : Prop :=
  g'.(gpow) = true
  (* nothing outside RAM exists ... *)
  /\ (forall a b, g'.(gmem) !! a = Some b ->
        (ram_lo <= SailStdpp.Operators_mwords.uint a < ram_hi)%Z)
  (* ... and ALL of RAM does, holding the loaded image (zero off it).  The
     totality is what lets a client carve main's memory precondition, and the
     content is what lets it read the kernel text back out. *)
  /\ (forall a : Z, (ram_lo <= a < ram_hi)%Z ->
        g'.(gmem) !! (SailStdpp.Values.mword_of_int a : Arch.pa)
        = Some (boot_byte a))
  (* THE REGISTER SIDE, ANCHORED ON A RUN rather than on a table of values: for
     each hart there are a power-on file [rs0] and a landing file [rs1] such that
     the boot program RAN from the one to the other, and this hart's registers
     ARE [rs1] -- no patch layer, nothing written over the run's output at all.
     THE POWER-ON MODEL IS THEREFORE
     "arbitrary garbage in every register, plus [ArchReset.board_init]'s short
     list of explicit board-guaranteed writes, plus the privileged spec's own
     [reset] with its configuration validation" -- deliberately NOT "whatever the
     simulator's initializers leave behind", which would narrow the modeled
     power-ons to the simulator's own and put real hardware with garbage in an
     unreset register outside the theorem.  Read [ArchReset.board_init]'s comment
     for the write list; it IS the platform assumption list.
     [rs0] is arbitrary garbage, which is the point: [BootReset.reset_regs_of_run]
     derives [reset_regs] -- the sixteen-way fact set every consumer still asks
     for by name -- from this clause for EVERY [rs0], and
     [PowerBoot.boot_shape_boot_gstate] satisfies it with one convenient
     instance ([init_regstate], where ColdBoot computes the whole run with the
     VM).  Memory and the device fabric are pinned on both sides because the
     chain touches neither. *)
  /\ (forall c : CPU, exists rs0 rs1 : regstate,
        run (ArchReset.boot_prog (boot_w64 (Z.of_nat (fin_to_nat c))) pma_boot)
            (MState rs0 ∅ dev0_state) tt (MState rs1 ∅ dev0_state)
        /\ g'.(gregs) c = rs1)
  (* the devices are reset: FIFOs empty, no interrupt enabled or pending,
     the disk's queue not live (its IMAGE survives -- see [boot_shape]) *)
  /\ g'.(gdev).(duart) = uart0_state
  /\ g'.(gdev).(dplic) = plic0_state
  /\ (exists v0, g'.(gdev).(dvirtio) = virtio_reset v0)
  (* no reservation survives a power cycle *)
  /\ (forall c : CPU, g'.(gresv) c = None).

(* the machine state a PowerOn hands over (claude-notes/design/crash.md):
   same generation (PowerOff already bumped it), the reset machine above,
   and the disk device reset FROM THIS MACHINE's disk -- [virtio_reset]
   keeps [v_disk], the ONE crash-surviving component. *)
Definition boot_shape (g g' : gstate) : Prop :=
  g'.(ggen) = g.(ggen)
  /\ g'.(gdev).(dvirtio) = virtio_reset g.(gdev).(dvirtio)
  /\ boot_facts g'.

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
  (* THE HART ARM, one Sail-monad NODE at a time.  [LoopE] is a [HartE], so
     the corpse arm covers the instruction boundary uniformly -- one arm. *)
  (exists gen cpu m, e = HartE gen cpu m /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\ hart_node_step gen g cpu m e' g')
     \/ (~ thread_live g gen /\ e' = e /\ g' = g)))
  \/
  (exists gen, e = UartLoopE gen /\ e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists d',
        uart_step g.(gdev) d' /\
        g' = GState g.(gregs) g.(gmem) d' g.(ggen) g.(gpow) g.(gresv))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (exists gen, e = DiskLoopE gen /\ e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists d' m',
        disk_step g.(gdev) g.(gmem) d' m' /\
        (* the DMA may not touch a byte any hart has reserved (§3a); the
           device's own [Idle] arm is what it does instead *)
        (forall a, a ∈ all_resv g.(gresv) -> m' !! a = g.(gmem) !! a) /\
        g' = GState g.(gregs) m' d' g.(ggen) g.(gpow) g.(gresv))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (exists gen, e = PlicLoopE gen /\ e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
    ((thread_live g gen /\
      exists gr',
        plic_step g.(gdev) g.(gregs) gr' /\
        g' = GState gr' g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv))
     \/ (~ thread_live g gen /\ g' = g)))
  \/
  (e = PowerLoopE /\ e' = PowerLoopE /\ κ = [] /\
    ((g.(gpow) = true /\ efs = [] /\
       (* PowerOff: kill the running generation INSTANTLY -- the bump is
          what makes [ggen > gen] the one stable death certificate *)
       g' = GState g.(gregs) g.(gmem) g.(gdev) (S g.(ggen)) false g.(gresv))
     \/
     (g.(gpow) = false /\ efs = power_fork g.(ggen) /\
       boot_shape g g'))).

Lemma riscv_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs _. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* PER-ARM INVERSION.  Every consumer of [prim_step] destructs the five-way *)
(* disjunction; doing it by name here keeps the ~200-character destruct     *)
(* patterns out of the lifting rules and makes an added arm one edit.       *)
(* ---------------------------------------------------------------------- *)

Lemma prim_step_hart_inv gen cpu m g κ e' g' efs :
  prim_step (HartE gen cpu m) g κ e' g' efs ->
  κ = [] /\ efs = [] /\
  ((thread_live g gen /\ hart_node_step gen g cpu m e' g')
   \/ (~ thread_live g gen /\ e' = HartE gen cpu m /\ g' = g)).
Proof.
  intros [(gen0 & cpu0 & m0 & Heq & ? & ? & Harm)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as -> -> ->. by split_and!.
Qed.

Lemma prim_step_uart_inv gen g κ e' g' efs :
  prim_step (UartLoopE gen) g κ e' g' efs ->
  e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
  ((thread_live g gen /\
    exists d', uart_step g.(gdev) d' /\
      g' = GState g.(gregs) g.(gmem) d' g.(ggen) g.(gpow) g.(gresv))
   \/ (~ thread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | [(? & Heq & _)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma prim_step_disk_inv gen g κ e' g' efs :
  prim_step (DiskLoopE gen) g κ e' g' efs ->
  e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
  ((thread_live g gen /\
    exists d' m', disk_step g.(gdev) g.(gmem) d' m' /\
      (forall a, a ∈ all_resv g.(gresv) -> m' !! a = g.(gmem) !! a) /\
      g' = GState g.(gregs) m' d' g.(ggen) g.(gpow) g.(gresv))
   \/ (~ thread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(gen0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma prim_step_plic_inv gen g κ e' g' efs :
  prim_step (PlicLoopE gen) g κ e' g' efs ->
  e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
  ((thread_live g gen /\
    exists gr', plic_step g.(gdev) g.(gregs) gr' /\
      g' = GState gr' g.(gmem) g.(gdev) g.(ggen) g.(gpow) g.(gresv))
   \/ (~ thread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma prim_step_power_inv g κ e' g' efs :
  prim_step PowerLoopE g κ e' g' efs ->
  e' = PowerLoopE /\ κ = [] /\
  ((g.(gpow) = true /\ efs = [] /\
     g' = GState g.(gregs) g.(gmem) g.(gdev) (S g.(ggen)) false g.(gresv))
   \/ (g.(gpow) = false /\ efs = power_fork g.(ggen) /\ boot_shape g g')).
Proof.
  intros [(? & ? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (_ & ? & ? & Harm)]]]];
    try discriminate Heq.
  by split_and!.
Qed.

(* ---------------------------------------------------------------------- *)
(* SHAPE FACTS a hart step preserves: the successor is the SAME hart of the *)
(* SAME generation, and the era fields never move.  Both are needed by      *)
(* every lifting rule, and both are one [destruct] away -- but that         *)
(* [destruct] is over ~20 outcome arms, so it is done ONCE here.            *)
(* ---------------------------------------------------------------------- *)

Lemma hart_node_step_shape gen g cpu m e' g' :
  hart_node_step gen g cpu m e' g' -> exists m', e' = HartE gen cpu m'.
Proof. intros (m' & s' & r' & _ & -> & _). by eexists. Qed.

Lemma hart_node_step_era gen g cpu m e' g' :
  hart_node_step gen g cpu m e' g' ->
  g'.(ggen) = g.(ggen) /\ g'.(gpow) = g.(gpow).
Proof. by intros (m' & s' & r' & _ & _ & ->). Qed.

(* A hart node never moves the disk IMAGE (crash.md): register effects and
   RAM accesses do not touch the device fabric at all, and an MMIO
   transaction goes through [dev_read]/[dev_write], which preserve [v_disk].
   The per-NODE twin of [run_v_disk], and what lets the hart lifting rule
   FRAME [state_interp]'s durable disk conjunct. *)
Lemma mnode_step_v_disk oth s r m m' s' r' :
  mnode_step oth s r m m' s' r' ->
  v_disk (dvirtio (mdev s')) = v_disk (dvirtio (mdev s)).
Proof.
  rewrite /mnode_step. destruct m as [y|T oc k].
  { by intros (tick & _ & -> & _). }
  destruct oc; simpl;
    try (by intros (_ & -> & _)); try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + intros (w & d' & Hdr & _ & -> & _). cbn.
      exact (dev_read_v_disk _ _ _ _ _ Hdr).
    + by intros [(_ & w & _ & _ & -> & _)
                |(_ & [(_ & _ & -> & _) | (_ & w & _ & _ & -> & _)])].
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros (d' & Hdw & _ & -> & _). cbn.
      exact (dev_write_v_disk _ _ _ _ _ Hdw).
    + by intros [(_ & _ & -> & _) | (_ & _ & -> & _)].
  - (* Choose *) by intros (ch & _ & -> & _).
Qed.

Lemma hart_node_step_v_disk gen g cpu m e' g' :
  hart_node_step gen g cpu m e' g' ->
  v_disk (dvirtio g'.(gdev)) = v_disk (dvirtio g.(gdev)).
Proof.
  intros (m' & s' & r' & Hn & _ & ->). cbn.
  exact (mnode_step_v_disk _ _ _ _ _ _ _ Hn).
Qed.

(* THE BATCHING LICENCE (claude-notes/design/main-cycle-port.md §5): apart
   from hart [c]'s own steps and a PowerOn's whole-machine reset, the ONLY
   thing any step of any other thread can do to hart [c]'s register file is
   [plic_step]'s [sig_seip] wire write.  This is the meta-level soundness of
   every batched register rule: a stretch of nodes whose registers the
   caller owns (and [sig_seip] is not ownable -- it lives in [WireInv])
   cannot be invalidated by interference. *)
Lemma prim_step_hart_regs_frame e g κ e' g' efs (c : CPU) :
  prim_step e g κ e' g' efs ->
  (forall gen m, e <> HartE gen c m) ->
  e <> PowerLoopE ->
  g'.(gregs) c = g.(gregs) c \/
  g'.(gregs) c = register_set sig_seip
      (bool_to_bit (dev_seip g.(gdev) (fin_to_nat c))) (g.(gregs) c).
Proof.
  intros Hstep Hnot Hnp.
  destruct Hstep as
    [ (gen & cpu & m & -> & _ & _ & [ (_ & (m' & s' & r' & _ & _ & ->)) | (_ & _ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & d' & _ & ->) | (_ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & d' & m' & _ & _ & ->) | (_ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & gr' & Hp & ->) | (_ & ->) ])
    | (-> & _) ] ] ] ];
    try (by left).
  - (* another hart's node: [c] is not [cpu], so the insert misses [c] *)
    left. cbn. rewrite /insert /greg_insert.
    case_decide as Hc; [exfalso; subst c; exact (Hnot gen m eq_refl)|done].
  - (* the wire: [sig_seip] on whichever hart the PLIC chose *)
    destruct Hp as [c0]. cbn. rewrite /insert /greg_insert.
    case_decide as Hc; [subst c0; by right|by left].
Qed.

(* THE CORPSE STEP is always available, at every expression that carries a
   generation -- which is what makes [wp_dead] provable uniformly. *)
Lemma prim_step_hart_dead gen cpu m g :
  ~ thread_live g gen -> prim_step (HartE gen cpu m) g [] (HartE gen cpu m) g [].
Proof.
  intros Hd. left. exists gen, cpu, m. split_and!; try reflexivity. by right.
Qed.

(* THE BOUNDARY always steps when live: the restart arm needs no resources
   and no facts about memory -- the fetch is a LATER node.  The successor
   state is written with the arm's own (identity) register write-back rather
   than as [g]: the two are only EXTENSIONALLY equal, and collapsing them
   would cost this file [functional_extensionality] for a reducibility
   witness that does not need it. *)
Lemma prim_step_hart_restart gen cpu g (tick : bool) :
  thread_live g gen ->
  prim_step (LoopE gen cpu) g [] (HartE gen cpu (riscv_step tick))
    (GState (<[cpu := g.(gregs) cpu]> g.(gregs)) g.(gmem) g.(gdev)
       g.(ggen) g.(gpow) (<[cpu := None]> g.(gresv))) [].
Proof.
  intros Hl. left. exists gen, cpu, (Interface.Ret tt).
  split_and!; try reflexivity. left. split; [exact Hl|].
  exists (riscv_step tick), (MState (g.(gregs) cpu) g.(gmem) g.(gdev)), None.
  split_and!; [by exists tick|reflexivity|reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* THE RESERVATION INVARIANT [resv_ok] IS PRESERVED BY EVERY STEP           *)
(* (design §3a).  This is the meta-level fact the state interpretation's     *)
(* pure [resv_ok] conjunct rests on; the per-arm lemmas are what the node    *)
(* rules discharge it with.                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma elem_of_footprint (pa : Arch.pa) (n : N) (a : Arch.pa) :
  a ∈ footprint pa n <-> exists j : nat, (N.of_nat j < n)%N /\ a = pa_add pa j.
Proof.
  unfold footprint. rewrite elem_of_list_to_set elem_of_list_fmap.
  split.
  - intros (j & -> & Hj). apply elem_of_seq in Hj. exists j. split; [lia|done].
  - intros (j & Hj & ->). exists j. split; [done|]. apply elem_of_seq. lia.
Qed.

(* the generic foldr-insert facts the byte primitives reduce to *)
Local Lemma foldr_ins_lookup_out (l : list nat) (pa : Arch.pa)
    (f : nat -> bv 8) (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) :
  (forall j, j ∈ l -> pa_add pa j ≠ a) ->
  foldr (fun j acc => <[pa_add pa j := f j]> acc) mm l !! a = mm !! a.
Proof.
  induction l as [|j l IH]; intros Hne; [reflexivity|].
  cbn [foldr]. rewrite lookup_insert_ne.
  - apply IH. intros i Hi. apply Hne, elem_of_list_further, Hi.
  - apply Hne, elem_of_list_here.
Qed.

Local Lemma foldr_ins_lookup_Some (l : list nat) (pa : Arch.pa)
    (f : nat -> bv 8) (a : Arch.pa) (b : bv 8) :
  foldr (fun j acc => <[pa_add pa j := f j]> acc) (∅ : gmap Arch.pa (bv 8)) l
    !! a = Some b ->
  exists j, j ∈ l /\ a = pa_add pa j /\ b = f j.
Proof.
  induction l as [|j l IH]; intros H.
  { rewrite lookup_empty in H. discriminate H. }
  cbn [foldr] in H. destruct (decide (pa_add pa j = a)) as [<-|Hne].
  - rewrite lookup_insert in H. injection H as <-.
    exists j. split_and!; [apply elem_of_list_here|done|done].
  - rewrite lookup_insert_ne in H; [|exact Hne].
    destruct (IH H) as (i & Hi & -> & ->).
    exists i. split_and!; [apply elem_of_list_further, Hi|done|done].
Qed.

Local Lemma foldr_ins_dom (l : list nat) (pa : Arch.pa) (f : nat -> bv 8)
    (mm : gmap Arch.pa (bv 8)) :
  dom (foldr (fun j acc => <[pa_add pa j := f j]> acc) mm l)
  = list_to_set (pa_add pa <$> l) ∪ dom mm.
Proof.
  induction l as [|j l IH].
  - cbn [foldr fmap list_fmap list_to_set]. set_solver.
  - cbn [foldr fmap list_fmap list_to_set]. rewrite dom_insert_L IH. set_solver.
Qed.

(* a store leaves every byte OUTSIDE its footprint alone *)
Lemma write_bytes_lookup_notin {w : N} (mm : gmap Arch.pa (bv 8))
    (pa : Arch.pa) (n : N) (v : bv w) (a : Arch.pa) :
  a ∉ footprint pa n -> write_bytes mm pa n v !! a = mm !! a.
Proof.
  intros Ha. unfold write_bytes. apply foldr_ins_lookup_out.
  intros j Hj Heq. apply Ha, elem_of_footprint. exists j.
  apply elem_of_seq in Hj. split; [lia|done].
Qed.

Lemma dom_snap_of {w : N} (pa : Arch.pa) (n : N) (v : bv w) :
  dom (snap_of pa n v) = footprint pa n.
Proof.
  unfold snap_of, write_bytes, footprint. rewrite foldr_ins_dom dom_empty_L.
  set_solver.
Qed.

Lemma snap_of_lookup_Some {w : N} (pa : Arch.pa) (n : N) (v : bv w)
    (a : Arch.pa) (b : bv 8) :
  snap_of pa n v !! a = Some b ->
  exists j : nat, (N.of_nat j < n)%N /\ a = pa_add pa j /\ b = nth_byte v j.
Proof.
  unfold snap_of, write_bytes. intros H.
  destruct (foldr_ins_lookup_Some _ _ _ _ _ H) as (j & Hj & -> & ->).
  apply elem_of_seq in Hj. exists j. split_and!; [lia|done|done].
Qed.

(* the snapshot an exclusive read records agrees with the memory it read *)
Lemma snap_of_sub (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> mm !! pa_add pa j = Some (nth_byte w j)) ->
  snap_of pa n w ⊆ mm.
Proof.
  intros Hrd. apply map_subseteq_spec. intros a b Hab.
  destruct (snap_of_lookup_Some _ _ _ _ _ Hab) as (j & Hj & -> & ->). exact (Hrd j Hj).
Qed.

Lemma elem_of_others_resv (gr : CPU -> option resv) (cpu c : CPU)
    (rr : resv) (a : Arch.pa) :
  c <> cpu -> gr c = Some rr -> a ∈ dom rr -> a ∈ others_resv gr cpu.
Proof.
  intros Hne Hc Ha. unfold others_resv. apply elem_of_union_list.
  exists (resv_dom gr c). split.
  - apply elem_of_list_fmap. exists c. split; [|apply elem_of_enum].
    by case_decide.
  - unfold resv_dom. by rewrite Hc.
Qed.

Lemma elem_of_all_resv (gr : CPU -> option resv) (c : CPU) (rr : resv)
    (a : Arch.pa) :
  gr c = Some rr -> a ∈ dom rr -> a ∈ all_resv gr.
Proof.
  intros Hc Ha. unfold all_resv. apply elem_of_union_list.
  exists (resv_dom gr c). split.
  - apply elem_of_list_fmap. exists c. split; [done|apply elem_of_enum].
  - unfold resv_dom. by rewrite Hc.
Qed.

(* one hart node: its own reservation (if any) still agrees with memory
   afterwards, and no byte another hart has reserved moved *)
Lemma mnode_step_resv oth s r m m' s' r' :
  mnode_step oth s r m m' s' r' ->
  (forall rr, r = Some rr -> rr ⊆ s.(mem)) ->
  (forall rr, r' = Some rr -> rr ⊆ s'.(mem)) /\
  (forall a, a ∈ oth -> s'.(mem) !! a = s.(mem) !! a).
Proof.
  rewrite /mnode_step. destruct m as [y|T oc k].
  { intros (tick & _ & -> & ->) _. split; [discriminate|done]. }
  destruct oc; simpl;
    try (by intros (_ & -> & ->) Hr; split; [exact Hr|done]);
    try (by intros []).
  - (* MemRead *)
    destruct (dev_addr _).
    + intros (w & d' & _ & _ & -> & ->) Hr. split; [exact Hr|done].
    + intros [(_ & w & _ & _ & -> & ->)
             |(_ & [(_ & _ & -> & ->) | (Hdisj & w & Hrd & _ & -> & ->)])] Hr;
        try (by split; [exact Hr|done]); [by split; [discriminate|done]|].
      split; [|done]. intros rr [= <-]. exact (snap_of_sub _ _ _ _ Hrd).
  - (* MemWrite *)
    destruct (dev_addr _).
    + intros (d' & _ & _ & -> & ->) Hr. split; [discriminate|done].
    + intros [(_ & _ & -> & ->) | (Hdisj & _ & -> & ->)] Hr;
        [by split; [exact Hr|done]|].
      split; [discriminate|]. intros a Ha. cbn.
      apply write_bytes_lookup_notin. intros Hfp.
      exact (Hdisj a Hfp Ha).
  - (* Choose *) intros (ch & _ & -> & ->) Hr. split; [exact Hr|done].
Qed.

Lemma hart_node_step_resv_ok gen g cpu m e' g' :
  hart_node_step gen g cpu m e' g' -> resv_ok g -> resv_ok g'.
Proof.
  intros (m' & s' & r' & Hn & _ & ->) Hok c rr. cbn.
  rewrite /insert /gresv_insert. case_decide as Hc.
  - (* the stepping hart: its new reservation *)
    subst c. intros Hr'.
    destruct (mnode_step_resv _ _ _ _ _ _ _ Hn (Hok cpu)) as (Hown & _).
    exact (Hown rr Hr').
  - (* another hart: its bytes did not move *)
    intros Hc'. pose proof (Hok c rr Hc') as Hsub.
    destruct (mnode_step_resv _ _ _ _ _ _ _ Hn (Hok cpu)) as (_ & Hoth).
    apply map_subseteq_spec. intros a b Hab.
    rewrite Hoth; [by eapply map_subseteq_spec in Hsub|].
    eapply elem_of_others_resv; [exact Hc|exact Hc'|].
    apply elem_of_dom. by eexists.
Qed.

Lemma prim_step_resv_ok e g κ e' g' efs :
  prim_step e g κ e' g' efs -> resv_ok g -> resv_ok g'.
Proof.
  intros Hstep Hok.
  destruct Hstep as
    [ (gen & cpu & m & -> & _ & _ & [ (_ & Hn) | (_ & _ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & d' & _ & ->) | (_ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & d' & m' & _ & Hkeep & ->) | (_ & ->) ])
    | [ (gen & -> & _ & _ & _ & [ (_ & gr' & _ & ->) | (_ & ->) ])
    | (-> & _ & _ & [ (_ & _ & ->) | (_ & _ & Hboot) ]) ] ] ] ];
    try exact Hok;
    try (by intros c rr Hc; exact (Hok c rr Hc)).
  - exact (hart_node_step_resv_ok _ _ _ _ _ _ Hn Hok).
  - (* the disk: it left every reserved byte alone *)
    intros c rr Hc. cbn. pose proof (Hok c rr Hc) as Hsub.
    apply map_subseteq_spec. intros a b Hab.
    rewrite Hkeep; [by eapply map_subseteq_spec in Hsub|].
    eapply elem_of_all_resv; [exact Hc|]. apply elem_of_dom. by eexists.
  - (* PowerOn: no reservation survives *)
    intros c rr Hc. destruct Hboot as (_ & _ & Hbf).
    destruct Hbf as (_ & _ & _ & _ & _ & _ & _ & Hnone).
    rewrite Hnone in Hc. discriminate Hc.
Qed.

Definition riscv_lang : language := Language riscv_lang_mixin.
