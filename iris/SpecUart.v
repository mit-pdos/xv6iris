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
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import KptPt.
Require Import SmodeCore.
Require Import DiskPtsto WpUart WpSmodeUart.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Import Defs.

Definition wp_lb_uart_s_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (γd : uart_names) (γv : disk_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) :=
let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let ldval := fun (b : bv 8) =>
      (extend_value is_unsigned (update_subrange_vec_dec (zeros' (1*1*8)) (1*(0+1)*8-1) (1*0*8) b) : mword 64) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
uint rd <> 0 ->
rd <> csp_rs1 ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
sie_cap_gpr γ m n -∗
pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) -∗
dev_inv γd γv -∗
R -∗
(∀ u b u', ⌜ uart_read u off = Some (b, u') ⌝ -∗
   uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S b) -∗
( ∀ b : bv 8,
  sie_cap_gpr γ (<[Regidx rd := regval_into_reg (ldval b)]> m) n -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S b -∗
  WP (Loop : expr riscv_lang) {{ Φ }}) -∗
WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_sb_uart_s_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ : gname) (γd : uart_names) (γv : disk_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) :=
let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
sie_cap_gpr γ m n -∗
pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
dev_inv γd γv -∗
R -∗
(∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
   uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S) -∗
( sie_cap_gpr γ m n -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S -∗
  WP (Loop : expr riscv_lang) {{ Φ }}) -∗
WP (Loop : expr riscv_lang) {{ Φ }}.

(* The SAME accessor-form store leaf, taking the BARE [uart_inv] rather than
   the [dev_inv] bundle.  This is the general form -- the store touches no PLIC
   and no disk resource, and since the invariant split the proof only ever
   opened [uartN] -- so a function whose contract mentions only the UART
   ([uartinit], and everything downstream of it) can use it without being
   handed a disk ghost bundle it has no use for.  [wp_sb_uart_s_sconf] above is
   its bundle-taking restatement, kept verbatim for the existing consumers. *)
Definition wp_sb_uart_uinv_s_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
    (γ : gname) (γd : uart_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ) :=
let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
let storebyte : mword 8 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) in
let lppn := kpt_leaf_ppn uart_vpn in
(0 <= off < uart_size)%Z ->
(* geometry: [a8] is canonical, its Sv39 vpn is [uart_vpn], and the leaf
   ppn composes back to [uart_pa off] = [a8] (the UART identity mapping) *)
neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = uart_vpn ->
zero_extend' 64 (add_vec_int a8 (0 * 1)) = uart_pa off ->
sie_cap_gpr γ m n -∗
pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
uart_inv γd -∗
R -∗
(∀ u u', ⌜ uart_write u off storebyte = Some u' ⌝ -∗
   uart_ghosts γd u -∗ R ==∗ uart_ghosts γd u' ∗ S) -∗
( sie_cap_gpr γ m n -∗
  pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
  S -∗
  WP (Loop : expr riscv_lang) {{ Φ }}) -∗
WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UART.
  Parameter wp_lb_uart_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (γv : disk_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ),
      wp_lb_uart_s_sconf_body γ γd γv off Φ pc is_rvc is_unsigned rd rs1 imm m n R S.
  Parameter wp_sb_uart_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (γv : disk_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ),
      wp_sb_uart_s_sconf_body γ γd γv off Φ pc is_rvc rs2 rs1 imm m n R S.
  Parameter wp_sb_uart_uinv_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (off : Z) (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12) (m : regfile) (n : nat) (R S : iProp Σ),
      wp_sb_uart_uinv_s_sconf_body γ γd off Φ pc is_rvc rs2 rs1 imm m n R S.
End UART.
