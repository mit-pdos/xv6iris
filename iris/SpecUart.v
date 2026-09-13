(* SpecUart.v -- the public interface of Uart, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import DevModel RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import KptPt.
Require Import DiskPtsto WpUart WpSmodeUart.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.

(* ===================================================================== *)
(*  THE PORT-GENERIC UART PAGE'S Sv39 VPN                                 *)
(*                                                                        *)
(*  [WpSmodeUart.uart_vpn] is the CONSOLE port's page and nothing else;    *)
(*  the leaves below are stated at an arbitrary port, so their geometry    *)
(*  premise has to name a vpn derived from the BOARD FACT               *)
(*  [DevModel.uart_base] instead of from that constant.                   *)
(*                                                                        *)
(*  [kvmmake] maps both ports' pages, but in two DISJOINT bands of         *)
(*  [KptPt.kmap_class]: the contiguous PLIC/UART0/VIRTIO band              *)
(*  [kpt_dev_vpn] and UART1's own [kpt_uart1_vpn], eight pages above it.   *)
(*  So a port-generic leaf's mapping fact is the DISJUNCTION               *)
(*  [uart_vpn_of_mapped] -- and the two arms converge immediately, since   *)
(*  [kmap_class_rw] and [kmap_class_uart1] both conclude                   *)
(*  [kmap_class ... = Some KP_rw].                                        *)
(* ===================================================================== *)

Definition uart_vpn_of (i : uart_id) : mword 27 :=
  mword_of_int (Z.div (uart_base i) 4096).

(* the console port's page is exactly WpSmodeUart's constant, which is what
   lets the [Uart0] corollaries below keep their landed statements. *)
Lemma uart_vpn_of_console : uart_vpn_of Uart0 = uart_vpn.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma uart_vpn_of_mapped (i : uart_id) :
  kpt_dev_vpn (uart_vpn_of i) \/ kpt_uart1_vpn (uart_vpn_of i).
Proof.
  unfold kpt_dev_vpn, kpt_uart1_vpn. destruct i.
  - left. assert (bv_unsigned (uart_vpn_of Uart0) = 65536) as ->
      by (vm_compute; reflexivity). lia.
  - right. assert (bv_unsigned (uart_vpn_of Uart1) = 65546) as ->
      by (vm_compute; reflexivity). lia.
Qed.

(* ===================================================================== *)
(*  §1  THE PRIMITIVES: the S-mode device LOAD/STORE leaves at an          *)
(*      ARBITRARY port, over the BARE [uart_inv i] invariant.              *)
(*                                                                        *)
(*  [dev_inv] is the CONSOLE bundle -- it names the PLIC and the disk and  *)
(*  cannot even be STATED at the second port -- so the general form takes  *)
(*  the one invariant it opens.  The [Uart0] leaves in §2 are these two    *)
(*  instantiated, and keep their landed statements verbatim.               *)
(* ===================================================================== *)

Definition wp_lb_uart_uinv_s_sconf_at_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (i : uart_id) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) (b : bool) (p : mword 64) :=
let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
(* the vmem level hands back the value itself now, not the split accumulator *)
let ldval := fun (bt : mword (8*1)) => (extend_value is_unsigned bt : mword 64) in
(0 <= off < uart_size)%Z ->
uint rd <> 0 ->
rd_ok rd ->
(* geometry: [a8] is canonical, its Sv39 vpn is port [i]'s page, and the
   leaf ppn composes back to [uart_pa i off] = [a8] (the identity mapping
   [kvmmake] installs for BOTH ports) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn_of i ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa i off ->
sie_cap_gpr kt m n b p -∗
pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
uart_inv i γd -∗
R -∗
(* THE GHOST STEP, run with THIS PORT's UART invariant open.  The RECEIVE
   COLUMN travels beside the four ghosts as its own leg (WpUart.uart_colE i):
   a read at offset 0 with DLAB clear POPS the FIFO, and what the column
   carries -- one application tag per queued byte, aligned with [u_rx] --
   has to move with it.  Every other read leaves both alone. *)
(∀ u bt u', ⌜ uart_read u off = Some (bt, u') ⌝ -∗
   uart_ghosts γd u -∗ uart_colE i γd u -∗ R ==∗
   uart_ghosts γd u' ∗ uart_colE i γd u' ∗ S bt) -∗
wp_next b p (fun (CID : CpuId) =>
  ∀ bt : bv 8,
  sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ldval bt)]> m) n b p -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S bt -∗
  WP (Loop : expr riscv_lang)) -∗
WP (Loop : expr riscv_lang).

Definition wp_sb_uart_uinv_s_sconf_at_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (i : uart_id) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64) :=
let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 1 8) 1) 0) in
(0 <= off < uart_size)%Z ->
(* geometry: as in the load leaf above *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn_of i ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa i off ->
sie_cap_gpr kt m n b p -∗
pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
uart_inv i γd -∗
R -∗
(* the column travels here too: an FCR write may clear the receive FIFO *)
(∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
   uart_ghosts γd u -∗ uart_colE i γd u -∗ R ==∗
   uart_ghosts γd u' ∗ uart_colE i γd u' ∗ S) -∗
wp_next b p (fun (CID : CpuId) =>
  sie_cap_gpr kt m n b p -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S -∗
  WP (Loop : expr riscv_lang)) -∗
WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  §2  THE [Uart0] COROLLARIES, statements verbatim.                     *)
(*                                                                        *)
(*  Two of them take the CONSOLE BUNDLE [dev_inv γd γv] and are derived    *)
(*  through [WpUart.dev_inv_uart]; the third takes the bare console        *)
(*  invariant.  [dev_inv] keeps arity 2 -- ~140 specs name it -- so the    *)
(*  second port never appears in it.                                      *)
(* ===================================================================== *)

Definition wp_lb_uart_s_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γd : uart_names) (γv : disk_names) (off : Z) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) (b : bool) (p : mword 64) :=
let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
(* the vmem level hands back the value itself now, not the split accumulator *)
let ldval := fun (bt : mword (8*1)) => (extend_value is_unsigned bt : mword 64) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
uint rd <> 0 ->
rd_ok rd ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa Uart0 off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa Uart0 off ->
sie_cap_gpr kt m n b p -∗
pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
dev_inv γd γv -∗
R -∗
(* THE GHOST STEP, run with the UART invariant open.  The RECEIVE COLUMN
   travels beside the four ghosts as its own leg (WpUart.uart_colE Uart0): a read
   at offset 0 with DLAB clear POPS the FIFO, and what the column carries --
   one application tag per queued byte, aligned with [u_rx] -- has to move
   with it.  Every other read leaves both alone. *)
(∀ u bt u', ⌜ uart_read u off = Some (bt, u') ⌝ -∗
   uart_ghosts γd u -∗ uart_colE Uart0 γd u -∗ R ==∗
   uart_ghosts γd u' ∗ uart_colE Uart0 γd u' ∗ S bt) -∗
wp_next b p (fun (CID : CpuId) =>
  ∀ bt : bv 8,
  sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ldval bt)]> m) n b p -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S bt -∗
  WP (Loop : expr riscv_lang)) -∗
WP (Loop : expr riscv_lang).

Definition wp_sb_uart_s_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γd : uart_names) (γv : disk_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64) :=
let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 1 8) 1) 0) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa Uart0 off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa Uart0 off ->
sie_cap_gpr kt m n b p -∗
pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
dev_inv γd γv -∗
R -∗
(* the column travels here too: an FCR write may clear the receive FIFO *)
(∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
   uart_ghosts γd u -∗ uart_colE Uart0 γd u -∗ R ==∗
   uart_ghosts γd u' ∗ uart_colE Uart0 γd u' ∗ S) -∗
wp_next b p (fun (CID : CpuId) =>
  sie_cap_gpr kt m n b p -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S -∗
  WP (Loop : expr riscv_lang)) -∗
WP (Loop : expr riscv_lang).

(* The SAME accessor-form store leaf, taking the BARE [uart_inv Uart0] rather than
   the [dev_inv] bundle.  This is the general form -- the store touches no PLIC
   and no disk resource, and since the invariant split the proof only ever
   opened [uartN] -- so a function whose contract mentions only the UART
   ([uartinit], and everything downstream of it) can use it without being
   handed a disk ghost bundle it has no use for.  [wp_sb_uart_s_sconf] above is
   its bundle-taking restatement, kept verbatim for the existing consumers. *)
Definition wp_sb_uart_uinv_s_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64) :=
let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 1 8) 1) 0) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa Uart0 off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa Uart0 off ->
sie_cap_gpr kt m n b p -∗
pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
uart_inv Uart0 γd -∗
R -∗
(* the column travels here too: an FCR write may clear the receive FIFO *)
(∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
   uart_ghosts γd u -∗ uart_colE Uart0 γd u -∗ R ==∗
   uart_ghosts γd u' ∗ uart_colE Uart0 γd u' ∗ S) -∗
wp_next b p (fun (CID : CpuId) =>
  sie_cap_gpr kt m n b p -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S -∗
  WP (Loop : expr riscv_lang)) -∗
WP (Loop : expr riscv_lang).

Module Type UART.
  (* --- the port-generic primitives, over the bare per-port invariant --- *)
  Parameter wp_lb_uart_uinv_s_sconf_at :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (i : uart_id) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) (b : bool) (p : mword 64),
      wp_lb_uart_uinv_s_sconf_at_body kt i γd off pc is_rvc is_unsigned rd rs1 imm m n R S b p.
  Parameter wp_sb_uart_uinv_s_sconf_at :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (i : uart_id) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64),
      wp_sb_uart_uinv_s_sconf_at_body kt i γd off pc is_rvc rs2 rs1 imm m n R S b p.
  (* --- the [Uart0] corollaries, statements unchanged --- *)
  Parameter wp_lb_uart_s_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γd : uart_names) (γv : disk_names) (off : Z) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) (b : bool) (p : mword 64),
      wp_lb_uart_s_sconf_body kt γd γv off pc is_rvc is_unsigned rd rs1 imm m n R S b p.
  Parameter wp_sb_uart_s_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γd : uart_names) (γv : disk_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64),
      wp_sb_uart_s_sconf_body kt γd γv off pc is_rvc rs2 rs1 imm m n R S b p.
  Parameter wp_sb_uart_uinv_s_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γd : uart_names) (off : Z) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64),
      wp_sb_uart_uinv_s_sconf_body kt γd off pc is_rvc rs2 rs1 imm m n R S b p.
End UART.
