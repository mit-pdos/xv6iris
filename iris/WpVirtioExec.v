(* WpVirtioExec.v -- the width-4 device-access exec-layer facts for the
   virtio-mmio disk window [0x10001000, 0x10002000).

   NOTE ON SHAPE.  There is deliberately NO third copy of the width-4
   device STORE/LOAD exec tower here.  The towers in [WpPlicExec.v]
   (sections (A)-(D) and (F)-(H): [exec_write_dev_4],
   [exec_pmaCheck_dev_store_4], [exec_checked_mem_write_dev_4_S],
   [exec_mem_write_value_dev_4_S], [exec_vmem_write_addr_4_S_walk_dev_pt],
   [exec_vmem_write_4_gpr_S_walk_dev_pt],
   [exec_execute_STORE_4_gpr_S_walk_dev] and their LOAD twins) are already
   WINDOW-GENERIC: they take the bus decode and the transaction as the two
   abstract premises

     [dev_addr pa = true]  and  [dev_write s'.(mdev) pa 4 wv = Some d']
                           /   [dev_read  s'.(mdev) pa 4 = Some (v, d')]

   and never mention [in_plic] or [plic_write]/[plic_read].  So a new MMIO
   window needs only its own GEOMETRY -- the analogue of WpPlicExec's
   section (E) -- which is what this file adds.  It re-exports WpPlicExec so
   a client of the virtio window gets both halves from one [Require].

   The one structural difference from the PLIC: a virtio-mmio READ does NOT
   change the device.  [DevModel.dev_read]'s virtio arm returns [(w, d)] with
   the SAME [d], so [dev_read_virtio] below concludes at [d] rather than at a
   [set_dvirtio], and a LOAD leaf built on it leaves [state_interp]'s device
   half untouched.

   All lemmas here are pure exec-level (iris-free). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExec RiscvExtras.
Require Import DevModel.
Require Import WpMmodeLeafBase.
Require Export WpPlicExec.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* virtio-mmio window geometry (the mirror of WpPlicExec's section (E)).  *)
(* ===================================================================== *)

(* The window order inside [dev_read]/[dev_write] is uart -> plic -> virtio,
   so every virtio routing lemma has to step past the two earlier windows.
   Both are refuted by the UPPER bound of the earlier window:
     uart  = [0x10000000, 0x10000008)
     plic  = [0x0c000000, 0x10000000)
   and virtio starts at 0x10001000, above both. *)
Lemma in_uart_virtio_false (a : Z) :
  virtio_base <= a < virtio_base + virtio_size -> in_uart a = false.
Proof.
  intros Hrange. unfold in_uart. apply andb_false_intro2. apply Z.ltb_ge.
  unfold uart_base, uart_size, virtio_base, virtio_size in *. lia.
Qed.

Lemma in_plic_virtio_false (a : Z) :
  virtio_base <= a < virtio_base + virtio_size -> in_plic a = false.
Proof.
  intros Hrange. unfold in_plic. apply andb_false_intro2. apply Z.ltb_ge.
  unfold plic_base, plic_size, virtio_base, virtio_size in *. lia.
Qed.

Lemma in_virtio_true (a : Z) :
  virtio_base <= a < virtio_base + virtio_size -> in_virtio a = true.
Proof.
  intros Hrange. unfold in_virtio. apply andb_true_intro.
  split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

(* A virtio address is a device address (below the DRAM bank). *)
Lemma dev_addr_virtio (pa : mword 64) :
  virtio_base <= uint pa < virtio_base + virtio_size -> dev_addr pa = true.
Proof.
  intros Hrange. unfold dev_addr. apply Z.ltb_lt.
  unfold virtio_base, virtio_size, dev_bound in *. lia.
Qed.

(* a width-4 virtio MMIO write, at the fabric level, routes to virtio_write *)
Lemma dev_write_virtio (d : dev_state) (pa : mword 64) (w : bv 32) (v' : virtio_state) :
  virtio_base <= uint pa < virtio_base + virtio_size ->
  virtio_write (dvirtio d) (uint pa - virtio_base) w = Some v' ->
  dev_write d pa 4 w = Some (set_dvirtio d v').
Proof.
  intros Hrange Hwr. unfold dev_write.
  rewrite (in_uart_virtio_false _ Hrange).
  rewrite (in_plic_virtio_false _ Hrange).
  rewrite (in_virtio_true _ Hrange).
  rewrite Hwr. reflexivity.
Qed.

(* a width-4 virtio MMIO read routes to virtio_read AND LEAVES THE DEVICE
   ALONE -- unlike the UART (whose RHR read pops the rx FIFO) and the PLIC
   (whose claim clears a pending bit), no virtio-mmio register is
   read-sensitive.  Hence the post-state device is the SAME [d]. *)
Lemma dev_read_virtio (d : dev_state) (pa : mword 64) (w : bv 32) :
  virtio_base <= uint pa < virtio_base + virtio_size ->
  virtio_read (dvirtio d) (uint pa - virtio_base) = Some w ->
  dev_read d pa 4 = Some (w, d).
Proof.
  intros Hrange Hrd. unfold dev_read.
  rewrite (in_uart_virtio_false _ Hrange).
  rewrite (in_plic_virtio_false _ Hrange).
  rewrite (in_virtio_true _ Hrange).
  rewrite Hrd. reflexivity.
Qed.

(* a 4-byte virtio access matches the kernel's TOR entry 0 (the virtio window
   [0x10001000,0x10002000) sits well inside [0, pmpaddr0*4)) *)
Lemma virtio_pmp_match4 (pmpaddr0 : mword 64) (pa : mword 64) :
  virtio_base <= uint pa < virtio_base + virtio_size ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
Proof.
  intros Hrange Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (Hw4 : uint (to_bits 64 4 : mword 64) = 4) by (vm_compute; reflexivity).
  rewrite Hz Hw4. rewrite Z.mul_0_l.
  apply pmpRangeMatch_full; unfold ram_base, ram_size, virtio_base, virtio_size in *; lia.
Qed.

(* a virtio address sits above the CLINT window, so it is [not_in_clint] and
   the model's within_clint check reduces to false *)
Lemma virtio_pa_not_in_clint (pa : mword 64) :
  virtio_base <= uint pa < virtio_base + virtio_size -> not_in_clint pa.
Proof.
  intros Hrange. right.
  assert (uint plat_clint_base + uint plat_clint_size = 34340864) as ->
    by (vm_compute; reflexivity).
  unfold virtio_base, virtio_size in *. lia.
Qed.

Lemma within_clint_virtio (pa : mword 64) (w : Z) s :
  virtio_base <= uint pa < virtio_base + virtio_size -> 0 < w ->
  exec (within_clint (Physaddr pa) w) s = Some (false, s).
Proof.
  intros Hrange Hw.
  apply within_clint_false; [apply virtio_pa_not_in_clint; exact Hrange | exact Hw].
Qed.

(* the SIG test device is disabled (plat_have_sig = false), so within_sig is
   false at any address -- see the PLIC twin. *)
Lemma within_sig_virtio (pa : mword 64) (w : Z) s :
  exec (within_sig (Physaddr pa) w) s = Some (false, s).
Proof. apply within_sig_plic. Qed.
