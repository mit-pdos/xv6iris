(* ============================================================== *)
(* RiscvAddTryStep.v -- consolidated Iris-over-Sail development.   *)
(* An Iris weakest-precondition for `add a2,a0,a1` executed by the *)
(* real Sail RISC-V `try_step`.  Self-contained except for:        *)
(*   - the generated model    : Riscv.rv64d / rv64d_types          *)
(*   - a small iris-FREE bv-arithmetic prelude : RiscvModelBytes    *)
(*     (kept separate ONLY because it uses vanilla `rewrite .. by`, *)
(*      which ssreflect -- pulled in by iris -- forbids).           *)
(* ============================================================== *)

From stdpp Require Import gmap bitvector.definitions.
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
}.

(* pointwise update of a single hart's register file *)
Global Instance greg_insert : Insert CPU regstate (CPU -> regstate) :=
  fun cpu rs gr c => if decide (c = cpu) then rs else gr c.

(* ---------------------------------------------------------------------- *)
(* 3c. The device execution context.                                        *)
(*                                                                          *)
(*   The devices run CONCURRENTLY with the harts: between any two CPU        *)
(*   instructions the UART may transmit or receive a byte, the virtio disk   *)
(*   may complete a queued request, the PLIC gateway may latch either        *)
(*   device's (level) interrupt output, and the PLIC may propagate its       *)
(*   per-hart EIP level onto a hart's external S-interrupt pin -- the        *)
(*   [sig_seip] register, which is exactly the model's external interrupt    *)
(*   WIRE: [read_mip IncludePlatformInterrupts] ORs it into mip, so          *)
(*   [dispatchInterrupt] sees it on the next instruction boundary.           *)
(*                                                                          *)
(*   The disk is a BUS MASTER, so unlike the UART and the PLIC its step is   *)
(*   not confined to the device fabric: [dev_step] therefore carries the     *)
(*   byte memory, and [DevStepDisk] overrides it with the write set the DMA  *)
(*   produced ([w ∪ m], VirtioModel.virtio_req_step).  Every other device    *)
(*   transition returns the memory untouched.  The disk is also the only     *)
(*   device that steps NONDETERMINISTICALLY, in two ways: the bus view it    *)
(*   reads is unconstrained off the byte map, and a malformed queue lets it  *)
(*   write anything anywhere ([DevStepDiskWild]).                            *)
(*                                                                          *)
(*   Note the wire is updated by its OWN step (DevStepWire), not             *)
(*   synchronously with the MMIO write that caused the level change: the     *)
(*   interrupt line has propagation delay, which is both realistic and the   *)
(*   weaker (hence safer) modelling choice.                                  *)
(* ---------------------------------------------------------------------- *)

Inductive dev_step (d : dev_state) (m : gmap Arch.pa (bv 8)) (gr : CPU -> regstate)
    : dev_state -> gmap Arch.pa (bv 8) -> (CPU -> regstate) -> Prop :=
  | DevStepTx b u' :
      uart_tx_pop d.(duart) = Some (b, u') ->
      dev_step d m gr (set_duart d u') m gr
  | DevStepRx b u' :
      uart_rx_push d.(duart) b = Some u' ->
      dev_step d m gr (set_duart d u') m gr
  | DevStepLatch (i : N) p' :
      dev_irq_level d i = true ->
      plic_latch d.(dplic) i = Some p' ->
      dev_step d m gr (set_dplic d p') m gr
  (* The disk masters the bus.  It does not read the byte MAP -- it reads a
     total VIEW of the bus that agrees with the map wherever the map is
     defined and is UNCONSTRAINED everywhere else (VirtioModel section 4), and
     the view is quantified here, existentially.  So a DMA read of an address
     nobody has accounted for returns an arbitrary byte, which is what a real
     bus does, and what forces a driver proof to account for every address it
     hands the device. *)
  | DevStepDisk (mv : vmem) v' w :
      mem_view m mv ->
      virtio_req_step d.(dvirtio) mv = Some (v', w) ->
      dev_step d m gr (set_dvirtio d v') (w ∪ m) gr
  (* ... and when the queue the driver published is MALFORMED, the device may
     do anything at all: [w] is arbitrary, so this constructor lets the disk
     scribble over any address in the machine.  That is the honest reading of
     a driver-must-not obligation.  An earlier model instead had the device
     quietly do NOTHING, which let a driver that misconfigured the queue
     satisfy its DMA obligation vacuously and be verified anyway.
     [wp_dev_loop] can only be proven by REFUTING this case from the device
     invariant, so queue well-formedness becomes a standing obligation on the
     driver rather than a gift from the model. *)
  | DevStepDiskWild (mv : vmem) (w : gmap Arch.pa (bv 8)) :
      mem_view m mv ->
      virtio_stalled d.(dvirtio) mv = true ->
      dev_step d m gr d (w ∪ m) gr
  | DevStepWire (c : CPU) :
      dev_step d m gr d m
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
(*    device state back.  [DevLoopE] is the device execution context: it      *)
(*    steps [dev_step] forever, interleaved with the harts.                   *)
(* ---------------------------------------------------------------------- *)

Class CpuId := cpu_id : CPU.

Inductive mexpr := LoopE (cpu : CPU) | DevLoopE.
Definition mval := Empty_set.
Definition mobs := Empty_set.
Definition of_val (v : mval) : mexpr := match v with end.
Definition to_val (_ : mexpr) : option mval := None.

Notation Loop := (LoopE cpu_id).
Notation DevLoop := DevLoopE.

Definition prim_step
    (e : mexpr) (g : gstate) (κ : list mobs)
    (e' : mexpr) (g' : gstate) (efs : list mexpr) : Prop :=
  (exists cpu, e = LoopE cpu /\ e' = LoopE cpu /\ κ = [] /\ efs = [] /\
    exists (tick : bool) (u : unit) (s' : mstate),
      run (riscv_step tick) (MState (g.(gregs) cpu) g.(gmem) g.(gdev)) u s' /\
      g' = GState (<[cpu := s'.(sregs)]> g.(gregs)) s'.(mem) s'.(mdev))
  \/
  (e = DevLoopE /\ e' = DevLoopE /\ κ = [] /\ efs = [] /\
    exists d' m' gr',
      dev_step g.(gdev) g.(gmem) g.(gregs) d' m' gr' /\
      g' = GState gr' m' d').

Lemma riscv_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs [(cpu & -> & _) | (-> & _)]; reflexivity.
Qed.

Definition riscv_lang : language := Language riscv_lang_mixin.

