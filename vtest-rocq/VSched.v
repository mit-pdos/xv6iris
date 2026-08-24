(* ====================================================================== *)
(* VSched.v -- the DEVICE SCHEDULE, executably.                            *)
(*                                                                         *)
(* [RiscvLang]'s device threads step RELATIONS: [uart_step], [disk_step]    *)
(* and [plic_step], each with several arms, and the disk's DMA arm          *)
(* quantifies the bus view EXISTENTIALLY.  A test has to EXHIBIT a run, so  *)
(* what it needs is the other side of that coin: a FUNCTION that, given a   *)
(* choice of arm, computes the successor.  That is [sapply] below, and a    *)
(* [sitem] is exactly "which arm, with which parameters".                   *)
(*                                                                         *)
(* SO A TEST'S WITNESS IS A SHORT LIST.  [SCpu 812; SDiskCapture;           *)
(* SDiskDrain 2; SDiskDma; SCpu 40] is a whole disk round trip.  Nothing    *)
(* materialises a list of machine states or of Sail monad terms: each item  *)
(* carries a COUNT or a CHOICE, and [srun] folds.                           *)
(*                                                                         *)
(* WHAT IS NOT HERE YET: the soundness lemma                                *)
(*   sapply i s = Some s' -> <one or more prim_steps from s to s'>.         *)
(* Each arm's proof is a two-line application of the corresponding          *)
(* constructor ([DevStepDisk], [UartStepTx], ...), and the CPU arm's is the *)
(* converse of [HartBlock] that its header defers to "the language's own    *)
(* functional interpreter".  Until those land, a green test is a fact about *)
(* the model as [exec] and these step functions compute it -- which is      *)
(* still a genuine differential test of [VirtioModel]/[DevModel], since     *)
(* every arm below calls straight into them -- and not yet a fact about     *)
(* [prim_step].  The [sitem] type is the interface that will not change     *)
(* when they do.                                                            *)
(*                                                                         *)
(* THE ARMS ARE THE MODEL'S, INCLUDING THE UGLY ONE.  [SDiskWild] is        *)
(* [DevStepDiskWild]: when the published queue is malformed the device may  *)
(* write ANYTHING ANYWHERE, and the model says so on purpose (an absent     *)
(* transition would silently excuse the driver that caused it).  A test     *)
(* that misconfigures the queue and then finds QEMU scribbling is matched   *)
(* by this arm and by nothing else, so it is here.                          *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel.
(* EXPORT what a test reasons about: the language ([mstate]), the device model
   ([virtio_state], [virtio_req_step] and their lemmas -- a test that records a
   FINDING states it against those, see DiskOrder.v) and the model's own types
   ([Arch.pa]).  [Require Import VTest] should be all a test file needs. *)
Require Export Riscv.rv64d_types RiscvLang VirtioModel.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The bus view.                                                        *)
(*                                                                         *)
(*    [disk_step]'s DMA and capture arms read a TOTAL view [vmem] that      *)
(*    agrees with the byte map wherever the map is defined and is           *)
(*    UNCONSTRAINED elsewhere -- a real bus returns something for an        *)
(*    address nobody accounted for.  A witness has to pick one; this picks  *)
(*    zero off the map, which is what QEMU's zero-initialised RAM gives.    *)
(*    [mem_view (mem s) (view_of (mem s))] holds by construction, which is  *)
(*    the premise the soundness lemma will discharge.                       *)
(* ---------------------------------------------------------------------- *)

Definition view_of (m : gmap Arch.pa (bv 8)) : vmem :=
  fun a => default byte_zero (m !! a).

Lemma view_of_ok (m : gmap Arch.pa (bv 8)) : mem_view m (view_of m).
Proof. intros a b Hb. unfold view_of. by rewrite Hb. Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. Seeding the disk.                                                   *)
(*                                                                         *)
(*     [set_vdisk] belongs beside [VirtioModel.set_vcfg]; it lives here     *)
(*     because adding a definition to VirtioModel.v rebuilds the 1286       *)
(*     files in its reverse-dependency closure.  Move it there the next     *)
(*     time that file is touched for another reason.                       *)
(*                                                                         *)
(*     Spelling the fields is what a setter does, and keeping it to ONE     *)
(*     place is the point: this is the only line in vtest-rocq that names   *)
(*     [VirtioState]'s constructor, so a new device field breaks here and   *)
(*     nowhere else.                                                       *)
(* ---------------------------------------------------------------------- *)

Definition set_vdisk (v : virtio_state) (dk : Z -> bv 8) : virtio_state :=
  VirtioState (v_cfg v) (v_isr v) (v_seen v) (v_ahead v) (v_used_idx v) dk
              (v_cache v) (v_taken v) (v_cap v).

(* the disk image as the device sees it: a TOTAL function over a finite
   description, zero off it -- the same shape [view_of] gives the bus. *)
Definition disk_of (img : gmap Z (bv 8)) : Z -> bv 8 :=
  fun a => default byte_zero (img !! a).

Definition dev_of (img : gmap Z (bv 8)) : dev_state :=
  DevState uart0_state plic0_state (set_vdisk virtio0_state (disk_of img)).

Lemma dev_of_empty : dev_of ∅ = dev0_state.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The schedule item: one arm of one thread.                            *)
(* ---------------------------------------------------------------------- *)

Inductive sitem : Type :=
  (* the hart: [n] whole instructions.  [SCpuTick] takes the clock tick,
     which [prim_step] chooses nondeterministically at each boundary. *)
  | SCpu (n : nat)
  | SCpuTick (n : nat)
  (* the UART ([uart_step]) *)
  | SUartTx                       (* drain one byte of the transmit FIFO *)
  | SUartRx (b : Z)               (* the host types a byte *)
  (* the disk ([disk_step]).  Three ordinary arms and the wild one. *)
  (* THE POSITION IS THE DEVICE'S CHOICE (VirtioModel section 5b): the ring
     is served in whatever order the device finishes, so a schedule has to
     say WHICH published request it is answering.  The nullary arms take the
     first one still outstanding, which is what every test that is not about
     ordering wants; [SDiskDmaAt]/[SDiskCaptureAt] name a position instead,
     and that is how a test exhibits a REORDERED completion. *)
  | SDiskDma                      (* complete the oldest outstanding request *)
  | SDiskCapture                  (* take its data into the cache *)
  | SDiskDmaAt (pos : Z)          (* ...complete THIS position instead *)
  | SDiskCaptureAt (pos : Z)      (* ...capture THIS position instead *)
  | SDiskDrain (sec : Z)          (* one cached sector reaches the durable image *)
  | SDiskWild (w : list (Z * Z))  (* a malformed queue: write anything, anywhere *)
  (* the PLIC gateway, per SOURCE -- an arm of the DEVICE that drives it *)
  | SLatch (src : N)
  (* the wire ([plic_step]): propagate the PLIC's EIP onto a hart's pin *)
  | SWire (h : nat).

(* THE OLDEST OUTSTANDING POSITION -- what the nullary disk arms serve. *)
Definition first_free (d : dev_state) (mv : vmem) : option (bv 16) :=
  let v := dvirtio d in
  head (vfree_list (v_seen v) (avail_idx_at (v_cfg v) mv) (v_ahead v)).

(* ---------------------------------------------------------------------- *)
(* 3. Applying one item.                                                   *)
(*                                                                         *)
(*    [None] means the chosen arm is NOT ENABLED at this state -- a bad     *)
(*    schedule, or a device that has nothing to do -- and it propagates, so *)
(*    a test with a wrong witness fails rather than silently doing less.    *)
(* ---------------------------------------------------------------------- *)

Definition with_dev (s : mstate) (d : dev_state) : mstate :=
  MState (sregs s) (mem s) d.

Fixpoint cpu_steps (tick : bool) (n : nat) (s : mstate) : option mstate :=
  match n with
  | 0%nat => Some s
  | S n' => match exec (riscv_step tick) s with
            | Some (_, s') => cpu_steps tick n' s'
            | None => None
            end
  end.

Definition writes_of (w : list (Z * Z)) : gmap Arch.pa (bv 8) :=
  list_to_map ((fun ab => (SailStdpp.Values.mword_of_int ab.1, Z_to_bv 8 ab.2)) <$> w).

Definition sapply (i : sitem) (s : mstate) : option mstate :=
  let d := mdev s in
  match i with
  | SCpu n => cpu_steps false n s
  | SCpuTick n => cpu_steps true n s
  | SUartTx =>
      match uart_tx_pop (duart d) with
      | Some (_, u') => Some (with_dev s (set_duart d u'))
      | None => None
      end
  | SUartRx b =>
      match uart_rx_push (duart d) (Z_to_bv 8 b) with
      | Some u' => Some (with_dev s (set_duart d u'))
      | None => None
      end
  | SDiskDma =>
      match first_free d (view_of (mem s)) with
      | None => None
      | Some i =>
          match virtio_req_step (dvirtio d) (view_of (mem s)) i with
          | Some (v', w) => Some (MState (sregs s) (w ∪ mem s) (set_dvirtio d v'))
          | None => None
          end
      end
  | SDiskCapture =>
      match first_free d (view_of (mem s)) with
      | None => None
      | Some i =>
          match virtio_capture_step (dvirtio d) (view_of (mem s)) i with
          | Some v' => Some (with_dev s (set_dvirtio d v'))
          | None => None
          end
      end
  | SDiskDmaAt pos =>
      match virtio_req_step (dvirtio d) (view_of (mem s)) (Z_to_bv 16 pos) with
      | Some (v', w) => Some (MState (sregs s) (w ∪ mem s) (set_dvirtio d v'))
      | None => None
      end
  | SDiskCaptureAt pos =>
      match virtio_capture_step (dvirtio d) (view_of (mem s)) (Z_to_bv 16 pos) with
      | Some v' => Some (with_dev s (set_dvirtio d v'))
      | None => None
      end
  | SDiskDrain sec =>
      match virtio_drain_step (dvirtio d) sec with
      | Some v' => Some (with_dev s (set_dvirtio d v'))
      | None => None
      end
  | SDiskWild w =>
      (* enabled ONLY when the queue really is malformed -- the model's own
         side condition, not a licence to scribble whenever convenient *)
      if virtio_stalled (dvirtio d) (view_of (mem s))
      then Some (MState (sregs s) (writes_of w ∪ mem s) d)
      else None
  | SLatch src =>
      if dev_irq_level d src then
        match plic_latch (dplic d) src with
        | Some p' => Some (with_dev s (set_dplic d p'))
        | None => None
        end
      else None
  | SWire h =>
      Some (MState (register_set sig_seip (bool_to_bit (dev_seip d h)) (sregs s))
                   (mem s) d)
  end.

Definition srun (sch : list sitem) (s : mstate) : option mstate :=
  foldl (fun o i => match o with Some s' => sapply i s' | None => None end)
        (Some s) sch.

(* ---------------------------------------------------------------------- *)
(* 4. The eager default schedule.                                          *)
(*                                                                         *)
(*    Most tests are not ABOUT interleaving: they publish a request and     *)
(*    want it served.  [settle] takes every enabled device action, in a     *)
(*    fixed priority, until none is.  A test that IS about interleaving     *)
(*    writes its [sitem] list by hand instead -- and the list then          *)
(*    DOCUMENTS what the test is about, which the eager default cannot.     *)
(*                                                                         *)
(*    Note what the priority means for the write path: capture before       *)
(*    drain before completion is the order a WRITETHROUGH device must use   *)
(*    ([virtio_complete_ok] gates completion on the request's sectors       *)
(*    having drained), so the eager schedule serves xv6-style writes        *)
(*    without a hand-written list.  It drains only sector [d_sec], the      *)
(*    lowest cached one, per round.                                         *)
(* ---------------------------------------------------------------------- *)

Definition lowest_cached (v : virtio_state) : option Z :=
  head (elements (dom (v_cache v))).

Definition drain_one (s : mstate) : option mstate :=
  match lowest_cached (dvirtio (mdev s)) with
  | Some sec => sapply (SDiskDrain sec) s
  | None => None
  end.

(* THE WIRE NEEDS A GUARD THAT THE OTHER ARMS DO NOT.  [plic_step] has no
   premise -- propagating the PLIC's EIP level onto a hart's pin is always a
   legal step, even when it writes the value already there -- so an eager
   scheduler that took it unconditionally would never terminate.  Fire it
   only when it actually moves the pin; that is the same set of reachable
   states, reached without spinning. *)
Definition wire_needed (s : mstate) (h : nat) : bool :=
  negb (bv_unsigned (register_lookup sig_seip (sregs s))
        =? bv_unsigned (bool_to_bit (dev_seip (mdev s) h))).

Definition settle_wire (s : mstate) : option mstate :=
  if wire_needed s 0 then sapply (SWire 0) s else None.

(* WHICH OUTSTANDING REQUEST THE EAGER SCHEDULE PICKS UP.  The device may
   serve any published position it has not served yet, so an eager schedule
   has to choose -- and the choice is a real degree of freedom, not a detail:
   [first_free] is the in-order run and [last_free] is the one where a later
   request OVERTAKES an earlier one, which is what a device with two requests
   in flight does (DiskOrder.v).  Everything else about the two schedules is
   identical. *)
Definition last_free (d : dev_state) (mv : vmem) : option (bv 16) :=
  let v := dvirtio d in
  last (vfree_list (v_seen v) (avail_idx_at (v_cfg v) mv) (v_ahead v)).

Definition pick_at (pick : dev_state -> vmem -> option (bv 16))
    (f : Z -> sitem) (s : mstate) : option mstate :=
  match pick (mdev s) (view_of (mem s)) with
  | Some i => sapply (f (bv_unsigned i)) s
  | None => None
  end.

(* first enabled arm wins.  Nested rather than a list, so a later arm is not
   even evaluated once an earlier one fires -- [settle] runs after EVERY
   instruction, so this is the harness's hot path. *)
Definition settle1_at (pick : dev_state -> vmem -> option (bv 16))
    (s : mstate) : option mstate :=
  match sapply SUartTx s with Some s' => Some s' | None =>
  match pick_at pick SDiskCaptureAt s with Some s' => Some s' | None =>
  match drain_one s with Some s' => Some s' | None =>
  match pick_at pick SDiskDmaAt s with Some s' => Some s' | None =>
  (* the two interrupt gateways, then the wire.  [plic_latch] is itself
     guarded -- a level source is forwarded only when it is neither already
     pending nor claimed -- so these stop on their own. *)
  match sapply (SLatch virtio_irq_id) s with Some s' => Some s' | None =>
  match sapply (SLatch uart_irq_id) s with Some s' => Some s' | None =>
  settle_wire s
  end end end end end end.

Definition settle1 (s : mstate) : option mstate := settle1_at first_free s.

Fixpoint settle_at (pick : dev_state -> vmem -> option (bv 16)) (fuel : nat)
    (s : mstate) : mstate :=
  match fuel with
  | 0%nat => s
  | S f => match settle1_at pick s with Some s' => settle_at pick f s' | None => s end
  end.

Definition settle (fuel : nat) (s : mstate) : mstate := settle_at first_free fuel s.
