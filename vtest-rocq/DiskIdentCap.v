(* DiskIdentCap.v -- ASKING THE DISK HOW BIG IT IS.  The model has no answer,
   and this is the one entry in the stuck matrix that should be FIXED rather
   than merely recorded.

   Source: tools/vtest/tests/disk_ident_cap.S.  Capture: DiskIdentCapGen.v.

   The virtio-blk CONFIG SPACE begins at offset 0x100 of the mmio window and
   its first eight bytes are [capacity], the size of the device in 512-byte
   sectors (virtio spec 5.2.4).  [VirtioModel.virtio_read] decodes nine
   offsets and 0x100 is not one of them, so it returns None, [DevModel.
   dev_read] returns None, and the load has NO TRANSITION: the machine is
   stuck.  QEMU answers with the real size of the backing file.

   CLASSIFICATION: INCOMPLETENESS, and the actionable kind.  A stuck state is
   not unsoundness -- the system theorem proves xv6 never gets stuck, so
   these states are never reached, and no proof can be wrong because of one.
   What it costs is COVERAGE: a driver that sizes its buffer cache, validates
   a block number, or refuses to mount a filesystem larger than the device
   cannot be verified in this development at all, because it has no model
   execution.  Reading the disk's size is a perfectly ordinary thing for a
   driver to do; xv6 gets away without it only because FSSIZE is a compile
   time constant. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentCapGen.
Local Open Scope Z_scope.

Definition cap_start : mstate := start disk_ident_cap_text.

(* ---------------------------------------------------------------------- *)
(* 1. The model: STUCK, and at exactly the load of 0x100.                   *)
(*                                                                         *)
(*    [stuck_pc] names the instruction, so this says WHICH access the model *)
(*    refuses rather than only that one of them did.  Cross-checked against *)
(*    riscv64-linux-gnu-objdump -d tools/vtest/build/disk_ident_cap.elf:    *)
(*                                                                         *)
(*      80000090:  10042283   lw  t0,256(s0)     # s0 = 0x10001000          *)
(*                                                                         *)
(*    Everything before it -- the reset, ACKNOWLEDGE, DRIVER, the feature   *)
(*    negotiation, FEATURES_OK -- the model executes happily, so this is    *)
(*    the config-space read and nothing else.  Every address the program   *)
(*    materialises comes from [li]/[lui] and never [la], whose GOT load     *)
(*    would be outside the [-j .text] image and would masquerade as a       *)
(*    device finding.                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma disk_ident_cap_model_stuck : run_status 50000 cap_start = VStuck.
Proof. solve_vtest VStuck. Qed.

Lemma disk_ident_cap_stuck_at : stuck_pc 50000 cap_start = 0x80000090.
Proof. solve_vtest (0x80000090 : Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. What the hardware said instead.                                      *)
(*                                                                         *)
(*    The backing file tools/vtest/vtest.py creates is 128 sectors of 512   *)
(*    bytes = 64 KB, and that is exactly what the config space reports:     *)
(*    capacity = 128, high word 0.  The two words after it are size_max and *)
(*    seg_max; size_max reads 0 because VIRTIO_BLK_F_SIZE_MAX was not       *)
(*    negotiated, and seg_max reads 254.                                    *)
(*                                                                         *)
(*    This is read off the CAPTURE, not off the model, so it costs nothing. *)
(* ---------------------------------------------------------------------- *)

Definition cap_qemu : list Z :=
  (fun o => cap_word disk_ident_cap_qemu_result o) <$> [8; 12; 16; 20]%nat.

Definition cap_qemu_expect : list Z := [128; 0; 0; 254].

Lemma disk_ident_cap_qemu_capacity : cap_qemu = cap_qemu_expect.
Proof. solve_vtest cap_qemu_expect. Qed.

(* ...and the model produced no result region at all, because it never got
   to the DONE handshake.  [result_of] of a [None] run is the empty list,
   which is what "there is no model execution here" looks like in this
   harness. *)
Lemma disk_ident_cap_model_no_result :
  result_of (run_until 50000 cap_start) = [].
Proof. solve_vtest (@nil Z). Qed.

(* ---------------------------------------------------------------------- *)
(* 3. WHAT THE FIX LOOKS LIKE.                                             *)
(*                                                                         *)
(*    Small, and local to VirtioModel.v.  The device needs one new derived  *)
(*    quantity -- how many sectors the image has -- and one new case in     *)
(*    [virtio_read].                                                       *)
(*                                                                         *)
(*    (a) The capacity itself.  [v_disk : Z -> bv 8] is TOTAL, so the image *)
(*        has no size today; the size has to become part of the device      *)
(*        state.  The cheapest honest way is a new [virtio_cfg]-sibling     *)
(*        field on [virtio_state],                                          *)
(*                                                                         *)
(*          v_cap : bv 64        (* capacity, in 512-byte sectors *)        *)
(*                                                                         *)
(*        set once at power-on ([virtio0_state], and [VSched.dev_of], which *)
(*        is where a test seeds an image) and never written again --        *)
(*        [virtio_reset] keeps it, exactly as it keeps [v_disk], because a  *)
(*        device does not change size when the driver resets it.  Making it *)
(*        a field rather than deriving it from [v_disk] is the point: a     *)
(*        total function has no size to derive.                            *)
(*                                                                         *)
(*    (b) The register offsets.  Add                                       *)
(*                                                                         *)
(*          Definition vio_off_config : Z := 0x100.                        *)
(*                                                                         *)
(*        and two cases at the end of [virtio_read], BEFORE the final None: *)
(*                                                                         *)
(*          else if off =? vio_off_config then                             *)
(*            Some (bv_extract 0 32 (v_cap v))                             *)
(*          else if off =? vio_off_config + 4 then                         *)
(*            Some (bv_extract 32 32 (v_cap v))                            *)
(*                                                                         *)
(*        Two 32-bit halves and not one 64-bit read, because [dev_read]     *)
(*        decodes the virtio window at width 4 only (see DiskIdentRd1.v);   *)
(*        a driver reads the capacity as two words, which is what QEMU      *)
(*        serves and what the test above records.                          *)
(*                                                                         *)
(*    (c) [vio_readable] gains the same two offsets, so a driver proof      *)
(*        under a contents-agnostic device invariant can conjure the result *)
(*        equation for them the way it does for the other nine.            *)
(*                                                                         *)
(*    NOT part of the fix, and worth saying: nothing should start CHECKING  *)
(*    requests against [v_cap].  A request past the end of the device is a  *)
(*    separate question (QEMU answers it with status IOERR = 1, which the   *)
(*    model has no constant for), and bundling it in would turn a two-case  *)
(*    addition into a change to the completion gate.                       *)
(*                                                                        *)
(*    What makes even this a decision rather than a drive-by edit is the    *)
(*    cost of touching VirtioModel.v at all: its reverse-dependency closure *)
(*    is 1286 files.  It wants to be done in the same pass as findings 4    *)
(*    and 5.                                                               *)
(* ---------------------------------------------------------------------- *)
