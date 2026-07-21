(* WpSconfPlicinithart.v: whole-function WP for xv6's plicinithart() in S-mode,
   over the SIE-agnostic sie_cap bundle.  plicinithart() @ 0x80005498 enables
   the UART + VIRTIO interrupts for THIS hart's S-mode PLIC context and drops
   that context's priority threshold to 0:

     0x80005498 <plicinithart>:
       +0x00  1141      c.addi   sp,sp,-16     frame alloc  (== cpuid/plicinit)
       +0x02  e406      c.sdsp   ra,8(sp)
       +0x04  e022      c.sdsp   s0,0(sp)
       +0x06  0800      c.addi4spn s0,sp,16
       +0x08  c30fc0ef  jal      ra,cpuid      a0 = hart id
       +0x0c  0085171b  slliw    a4,a0,0x8
       +0x10  0c0027b7  lui      a5,0xc002
       +0x14  97ba      c.add    a5,a5,a4      a5 = PLIC+0x2000 + hart*0x100
       +0x16  40200713  addi     a4,zero,1026
       +0x1a  08e7a023  sw       a4,128(a5)    *PLIC_SENABLE(hart)  = 1026
       +0x1e  00d5151b  slliw    a0,a0,0xd
       +0x22  0c2017b7  lui      a5,0xc201
       +0x26  97aa      c.add    a5,a5,a0      a5 = PLIC+0x201000 + hart*0x2000
       +0x28  0007a023  sw       zero,0(a5)    *PLIC_SPRIORITY(hart) = 0
       +0x2c  60a2      c.ldsp   ra,8(sp)      frame free   (== cpuid/plicinit)
       +0x2e  6402      c.ldsp   s0,0(sp)
       +0x30  0141      c.addi   sp,sp,16
       +0x32  8082      c.ret

   The 16-byte frame is byte-identical to cpuid/plicinit, so the prologue and
   epilogue reuse KernelRvcDecode's shared templates and the WpSconf{Mem,Ctl}
   frame leaves.  The two MMIO writes go through [wp_sw_plic_dev_s_sconf]
   (WpPlic.v), which opens the device invariant around each write: every hart
   runs this function concurrently, so none of them may own [plic_frag] across
   a step (see SpecPlicinithart.v).  Each write therefore has to preserve the
   kernel's PLIC plan [plic_ok] (PlicPlan.v) at EVERY state that plan admits.

   Unlike plicinit, both store addresses depend on the hart id, which is only
   bounded ([bv_unsigned tp < dev_ncpu]) rather than concrete.  Every fact that
   needs the address as a number is therefore proved by an eight-way case split
   on the hart id ([hart_cases]) followed by [vm_compute] -- see the geometry /
   write lemmas below, which are stated over an abstract [tp] so the main proof
   body stays single-copy and symbolic. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile WpGpr InstrBytes WpMmodeLeafBase WpMmodeShiftiop.
Require Import SmodeCore.
Require Import KptTree KptPt.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import WpDecode WpLeafCommon WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import DevModel PlicPlan WpUart WpPlic WpPlicExec SpecCpuid SpecPlicinithart.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* A closed [lo <= x < hi] bound over Z.  [lia] is unusable on these: the heavy
   bitvector.tactics import installs a zify hook that answers "Cannot find
   witness" even on ground literals (durable-notes), so decide each side
   through the boolean reflection lemmas instead. *)
Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.

(* One [callee_saved] conjunct for a register that plicinithart itself never
   writes: strip the local insert tower down to the callee's return map
   [base], hop the callee's own [callee_saved], then strip the prologue's
   tower.  Both strips are [reg_lookup] (a cheap vm-cast, never bare
   conversion -- see RegFile.v on the async-Qed hazard); the register is a
   MISS in both towers, so no symbolic value is ever reduced. *)
Ltac cs_through Hcs base :=
  match goal with
  | |- _ !!! Regidx ?c = _ =>
      transitivity (base !!! Regidx c);
      [ reg_lookup
      | rewrite (callee_saved_lookup Hcs c ltac:(vm_compute; reflexivity)); reg_lookup ]
  end.

(* plicinithart's balanced 16-byte frame: entry [addi sp,-16] and exit
   [addi sp,+16] cancel (identical to cpuid_frame_cancel / plicinit_frame_cancel). *)
Lemma plicinithart_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* ===================================================================== *)
(*  The hart id: eight concrete words, and what the code computes from it. *)
(* ===================================================================== *)

(* A legal hart id is one of the [dev_ncpu] = 8 concrete 64-bit words.  Every
   address fact below is proved by this case split + [vm_compute]. *)
(* [lia] cannot be used once a [bv] term is in the context (the
   bitvector.tactics zify hook answers "Cannot find witness"), so the pure Z
   case split is done here, where nothing bitvector-shaped is in scope. *)
Lemma z_lt8_cases (z : Z) :
  0 <= z -> z < 8 ->
  z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7.
Proof. lia. Qed.

Lemma hart_cases (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  tp = (mword_of_int 0 : mword 64) \/ tp = (mword_of_int 1 : mword 64) \/
  tp = (mword_of_int 2 : mword 64) \/ tp = (mword_of_int 3 : mword 64) \/
  tp = (mword_of_int 4 : mword 64) \/ tp = (mword_of_int 5 : mword 64) \/
  tp = (mword_of_int 6 : mword 64) \/ tp = (mword_of_int 7 : mword 64).
Proof.
  intro Hh.
  change (Z.of_nat dev_ncpu) with 8%Z in Hh.
  remember (bv_unsigned tp) as z eqn:Hz.
  assert (Hu : bv_unsigned tp = z) by (symmetry; exact Hz).
  assert (Hlo : 0 <= z).
  { rewrite <- Hu. apply (proj1 (bv_unsigned_in_range _ tp)). }
  destruct (z_lt8_cases z Hlo Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E in Hu;
    [ left | right; left | right; right; left | right; right; right; left
    | right; right; right; right; left | right; right; right; right; right; left
    | right; right; right; right; right; right; left
    | right; right; right; right; right; right; right ];
    apply bv_eq; rewrite Hu; vm_compute; reflexivity.
Qed.

(* the SLLIW the code applies to the hart id (shift the low 32 bits, sign-extend) *)
Definition ph_shl (tp : mword 64) (k : Z) : mword 64 :=
  sign_extend' 64 (shift_bits_left (subrange_vec_dec tp 31 0 : mword 32) (mword_of_int k : mword 5)).

(* the two [lui]+[add] bases, and the effective addresses of the two stores *)
Definition ph_senb (tp : mword 64) : mword 64 :=
  add_vec (mword_of_int 0x0c002000 : mword 64) (ph_shl tp 8).
Definition ph_sthb (tp : mword 64) : mword 64 :=
  add_vec (mword_of_int 0x0c201000 : mword 64) (ph_shl tp 13).

Definition ph_a8 (base : mword 64) (imm : mword 12) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec (add_vec base (sign_extend' 64 imm)) (xlen - 0 - 1) 0).

(* [cpuid] truncates its result to an [int]; for a legal hart id the top bits
   are clear, so the truncation is the identity. *)
Lemma cpuid_ret_hart (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu -> cpuid_ret tp = tp.
Proof.
  intro Hh. unfold cpuid_ret.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]];
    rewrite E; apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the geometry of the two PLIC context addresses ------------------ *)
(* Both bundles say: the address is inside the PLIC window, 4-aligned,
   canonical, on a [kpt_dev_vpn] page, and identity-mapped by the kernel page
   table -- exactly the five hypotheses [wp_sw_plic_s_sconf] takes. *)

Lemma ph_senable_geom (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  let a8 := ph_a8 (ph_senb tp) (mword_of_int 128 : mword 12) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z
  /\ is_aligned_vaddr (Virtaddr a8) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of a8)
  /\ zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8.
Proof.
  intro Hh. cbv zeta.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    (split; [ zrange_vm | ]); (split; [ vm_compute; reflexivity | ]);
    (split; [ vm_compute; reflexivity | ]);
    (split; [ unfold kpt_dev_vpn; zrange_vm | ]);
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ph_sthresh_geom (tp : mword 64) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  let a8 := ph_a8 (ph_sthb tp) (mword_of_int 0 : mword 12) in
  (plic_base <= uint a8 < plic_base + plic_size)%Z
  /\ is_aligned_vaddr (Virtaddr a8) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of a8)
  /\ zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8.
Proof.
  intro Hh. cbv zeta.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    (split; [ zrange_vm | ]); (split; [ vm_compute; reflexivity | ]);
    (split; [ vm_compute; reflexivity | ]);
    (split; [ unfold kpt_dev_vpn; zrange_vm | ]);
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- what the two writes do to the PLIC state ------------------------ *)

Lemma ph_senable_write (tp : mword 64) (p : plic_state) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_write p (uint (ph_a8 (ph_senb tp) (mword_of_int 128 : mword 12)) - plic_base)
    plic_senable_word
  = Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
            (hupd (p_enable p) (Z.to_nat (bv_unsigned tp)) plic_senable_word) (p_thresh p)).
Proof.
  intro Hh.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    vm_compute; reflexivity.
Qed.

Lemma ph_sthresh_write (tp : mword 64) (p : plic_state) :
  bv_unsigned tp < Z.of_nat dev_ncpu ->
  plic_write p (uint (ph_a8 (ph_sthb tp) (mword_of_int 0 : mword 12)) - plic_base)
    (Z_to_bv 32 0)
  = Some (PlicState (p_prio p) (p_pending p) (p_claimed p) (p_enable p)
            (hupd (p_thresh p) (Z.to_nat (bv_unsigned tp)) (Z_to_bv 32 0))).
Proof.
  intro Hh.
  destruct (hart_cases tp Hh) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  Decodes for the ten instructions not shared with the frame templates. *)
(* ===================================================================== *)

(* +0x08  c30fc0ef  jal ra,cpuid   (target = pc - 15312) *)
Lemma phdec_jal s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc30fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x0c  0085171b  slliw a4,a0,0x8 *)
Lemma phdec_slliw_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0085171b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* +0x10  0c0027b7  lui a5,0xc002 *)
Lemma phdec_lui_c002 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c0027b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* +0x14  97ba  c.add a5,a5,a4 *)
Lemma phdec_add_a5_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x16  40200713  addi a4,zero,1026 *)
Lemma phdec_li_1026 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40200713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  08e7a023  sw a4,128(a5) *)
Lemma phdec_sw_128 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08e7a023 : mword 32)) s
  = Some (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  00d5151b  slliw a0,a0,0xd *)
Lemma phdec_slliw_a0 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d5151b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* +0x22  0c2017b7  lui a5,0xc201 *)
Lemma phdec_lui_c201 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c2017b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* +0x26  97aa  c.add a5,a5,a0 *)
Lemma phdec_add_a5_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97aa : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x28  0007a023  sw zero,0(a5) *)
Lemma phdec_sw_zero s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

Module PlicinithartProof (Cpuid : CPUID) : PLICINITHART.

Section WpSconfPlicinithart.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ}.
  Context `{CID : CpuId}.

  Notation PH := KernelSyms.plicinithart.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the eighteen plicinithart instructions.            *)
  (* ------------------------------------------------------------------- *)
  Lemma phi_00 : kernel_text -∗ instr (mword_of_int (PH + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PH + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (PH + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma phi_02 : kernel_text -∗ instr (mword_of_int (PH + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PH + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PH + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma phi_04 : kernel_text -∗ instr (mword_of_int (PH + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PH + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PH + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma phi_06 : kernel_text -∗ instr (mword_of_int (PH + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PH + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PH + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma phi_08 : kernel_text -∗ instr (mword_of_int (PH + 0x08) : mword 64) false (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PH + 0x08)%Z (mword_of_int 0xc30fc0ef : mword 32)
    (mword_of_int (PH + 0x08) : mword 64) (JAL (mword_of_int 2081840 : mword 21, Regidx (mword_of_int 1))) phdec_jal. Qed.

  Lemma phi_0c : kernel_text -∗ instr (mword_of_int (PH + 0x0c) : mword 64) false (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW)).
  Proof. mk_base (PH + 0x0c)%Z (mword_of_int 0x0085171b : mword 32)
    (mword_of_int (PH + 0x0c) : mword 64) (SHIFTIWOP (mword_of_int 8 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLLIW)) phdec_slliw_a4. Qed.

  Lemma phi_10 : kernel_text -∗ instr (mword_of_int (PH + 0x10) : mword 64) false (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (PH + 0x10)%Z (mword_of_int 0x0c0027b7 : mword 32)
    (mword_of_int (PH + 0x10) : mword 64) (UTYPE (mword_of_int 0xc002 : mword 20, Regidx (mword_of_int 15), LUI)) phdec_lui_c002. Qed.

  Lemma phi_14 : kernel_text -∗ instr (mword_of_int (PH + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PH + 0x14)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (PH + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) phdec_add_a5_a4 exec_execute_C_ADD. Qed.

  Lemma phi_16 : kernel_text -∗ instr (mword_of_int (PH + 0x16) : mword 64) false (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PH + 0x16)%Z (mword_of_int 0x40200713 : mword 32)
    (mword_of_int (PH + 0x16) : mword 64) (ITYPE (mword_of_int 1026 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), ADDI)) phdec_li_1026. Qed.

  Lemma phi_1a : kernel_text -∗ instr (mword_of_int (PH + 0x1a) : mword 64) false (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (PH + 0x1a)%Z (mword_of_int 0x08e7a023 : mword 32)
    (mword_of_int (PH + 0x1a) : mword 64) (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) phdec_sw_128. Qed.

  Lemma phi_1e : kernel_text -∗ instr (mword_of_int (PH + 0x1e) : mword 64) false (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)).
  Proof. mk_base (PH + 0x1e)%Z (mword_of_int 0x00d5151b : mword 32)
    (mword_of_int (PH + 0x1e) : mword 64) (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 10), SLLIW)) phdec_slliw_a0. Qed.

  Lemma phi_22 : kernel_text -∗ instr (mword_of_int (PH + 0x22) : mword 64) false (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (PH + 0x22)%Z (mword_of_int 0x0c2017b7 : mword 32)
    (mword_of_int (PH + 0x22) : mword 64) (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI)) phdec_lui_c201. Qed.

  Lemma phi_26 : kernel_text -∗ instr (mword_of_int (PH + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PH + 0x26)%Z (mword_of_int 0x97aa : mword 16)
    (mword_of_int (PH + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) phdec_add_a5_a0 exec_execute_C_ADD. Qed.

  Lemma phi_28 : kernel_text -∗ instr (mword_of_int (PH + 0x28) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (PH + 0x28)%Z (mword_of_int 0x0007a023 : mword 32)
    (mword_of_int (PH + 0x28) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) phdec_sw_zero. Qed.

  Lemma phi_2c : kernel_text -∗ instr (mword_of_int (PH + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PH + 0x2c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PH + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma phi_2e : kernel_text -∗ instr (mword_of_int (PH + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PH + 0x2e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PH + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma phi_30 : kernel_text -∗ instr (mword_of_int (PH + 0x30) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PH + 0x30)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PH + 0x30) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma phi_32 : kernel_text -∗ instr (mword_of_int (PH + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PH + 0x32)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PH + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plicinithart(), entry to return.  *)
  (* =================================================================== *)
  Lemma wp_plicinithart_sconf (γ : gname) (root_ppn : mword 44) (γd : uart_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat)
    : wp_plicinithart_sconf_body γ root_ppn γd Φ m0 n.
  Proof.
    cbv beta delta [wp_plicinithart_sconf_body].
    intros ra_idx tp_idx pcE ra0 ret_tgt Hretok Hhart Hn.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (z_idx  := (mword_of_int 0 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc #Hdinv Hcont".
    iPoseProof (phi_00 with "Htext") as "Hi00".
    iPoseProof (phi_02 with "Htext") as "Hi02".
    iPoseProof (phi_04 with "Htext") as "Hi04".
    iPoseProof (phi_06 with "Htext") as "Hi06".
    iPoseProof (phi_08 with "Htext") as "Hi08".
    iPoseProof (phi_0c with "Htext") as "Hi0c".
    iPoseProof (phi_10 with "Htext") as "Hi10".
    iPoseProof (phi_14 with "Htext") as "Hi14".
    iPoseProof (phi_16 with "Htext") as "Hi16".
    iPoseProof (phi_1a with "Htext") as "Hi1a".
    iPoseProof (phi_1e with "Htext") as "Hi1e".
    iPoseProof (phi_22 with "Htext") as "Hi22".
    iPoseProof (phi_26 with "Htext") as "Hi26".
    iPoseProof (phi_28 with "Htext") as "Hi28".
    iPoseProof (phi_2c with "Htext") as "Hi2c".
    iPoseProof (phi_2e with "Htext") as "Hi2e".
    iPoseProof (phi_30 with "Htext") as "Hi30".
    iPoseProof (phi_32 with "Htext") as "Hi32".
    assert (Hn2 : (2 <= n)%nat) by lia.
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE imm_entry m0 n 2 Hn2 Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PH + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (PH + 0x02) : mword 64) 2 = mword_of_int (PH + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (PH + 0x04) : mword 64) 2 = mword_of_int (PH + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (PH + 0x06) : mword 64) 2 = mword_of_int (PH + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* the entry values still visible in m2 *)
    assert (Hm2sp : m2 !!! Regidx csp_rs1 = sp').
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate]. exact Hcsp1. }
    (* stated with the RAW index literal on the left: the [callee_saved] /
       cpuid facts below mention [mword_of_int 4], not the local [tp_idx]. *)
    assert (Hm2tp : m2 !!! Regidx (mword_of_int 4 : mword 5) = m0 !!! Regidx tp_idx).
    { unfold m2. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    (* ---- 0x08: jal ra,cpuid ---- *)
    iApply (Cpuid.wp_call_cpuid_sconf_cs γ root_ppn Φ (mword_of_int (PH + 0x08))
              (mword_of_int 2081840 : mword 21) m2 (n - 2)%nat
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite upd_eq; vm_compute; reflexivity)
              ltac:(lia)
              with "Hsc Hhs Hcg Htlbinv Htext Hpc Hi08 [-]").
    iIntros (mo) "Hhs Hsc Hcg Htlbinv Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc0c : update_vec_dec (add_vec (add_vec_int (mword_of_int (PH + 0x08) : mword 64) 4)
                       (sign_extend' 64 (zeros' 12))) 0 ('b"0") = (mword_of_int (PH + 0x0c) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* the register file's x0 slot, needed to read the [zero] source operands *)
    iDestruct (sie_cap_gpr_x0 γ root_ppn mo (n - 2)%nat z_idx ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
    (* what survived the call *)
    assert (Hmosp : mo !!! Regidx csp_rs1 = sp')
      by (rewrite (proj1 Hmo_cs); exact Hm2sp).
    assert (Hmoa0 : mo !!! Regidx a0_idx = m0 !!! Regidx tp_idx).
    { unfold a0_idx. rewrite Hmo_a0 Hm2tp. apply cpuid_ret_hart. exact Hhart. }
    (* ---- the post-call register-map chain ---- *)
    set (N2 := <[Regidx a4_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 8)]> mo).
    set (N3 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c002000 : mword 64)]> N2).
    set (N4 := <[Regidx a5_idx := regval_into_reg (add_vec (N3 !!! Regidx a5_idx) (N3 !!! Regidx a4_idx))]> N3).
    set (N5 := <[Regidx a4_idx := regval_into_reg (add_vec (N4 !!! Regidx z_idx) (sign_extend' 64 (mword_of_int 1026 : mword 12)))]> N4).
    set (N6 := <[Regidx a0_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 13)]> N5).
    set (N7 := <[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N6).
    set (N8 := <[Regidx a5_idx := regval_into_reg (add_vec (N7 !!! Regidx a5_idx) (N7 !!! Regidx a0_idx))]> N7).
    set (N9 := <[Regidx ra_idx := regval_into_reg ra0]> N8).
    set (N10 := <[Regidx s0_idx := regval_into_reg s00]> N9).
    set (N11 := <[Regidx csp_rs1 := regval_into_reg (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N10).
    (* ---- 0x0c: slliw a4,a0,8 ---- *)
    iApply (wp_slliw_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x0c)) a4_idx a0_idx
              (mword_of_int 8 : mword 5) (ph_shl (m0 !!! Regidx tp_idx) 8) mo (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmoa0; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (PH + 0x0c) : mword 64) 4 = mword_of_int (PH + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 8)]> mo) with N2.
    (* ---- 0x10: lui a5,0xc002 ---- *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x10)) a5_idx
              (mword_of_int 0xc002 : mword 20) (mword_of_int 0x0c002000 : mword 64) N2 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (PH + 0x10) : mword 64) 4 = mword_of_int (PH + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c002000 : mword 64)]> N2) with N3.
    (* ---- 0x14: c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x14)) a5_idx a4_idx N3 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp16 : add_vec_int (mword_of_int (PH + 0x14) : mword 64) 2 = mword_of_int (PH + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (N3 !!! Regidx a5_idx) (N3 !!! Regidx a4_idx))]> N3) with N4.
    (* ---- 0x16: addi a4,zero,1026 ---- *)
    iApply (wp_addi4_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x16)) a4_idx z_idx
              (mword_of_int 1026 : mword 12) N4 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp1a : add_vec_int (mword_of_int (PH + 0x16) : mword 64) 4 = mword_of_int (PH + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (add_vec (N4 !!! Regidx z_idx) (sign_extend' 64 (mword_of_int 1026 : mword 12)))]> N4) with N5.
    (* the two operands of the first store *)
    assert (HN3a5 : N3 !!! Regidx a5_idx = (mword_of_int 0x0c002000 : mword 64))
      by (unfold N3; apply upd_eq).
    assert (HN3a4 : N3 !!! Regidx a4_idx = ph_shl (m0 !!! Regidx tp_idx) 8).
    { unfold N3. rewrite upd_ne; [| vm_compute; discriminate]. unfold N2. apply upd_eq. }
    assert (HN4a5 : N4 !!! Regidx a5_idx = ph_senb (m0 !!! Regidx tp_idx)).
    { unfold N4. rewrite upd_eq. unfold regval_into_reg, ph_senb.
      rewrite HN3a5 HN3a4. reflexivity. }
    assert (HN5a5 : N5 !!! Regidx a5_idx = ph_senb (m0 !!! Regidx tp_idx)).
    { unfold N5. rewrite upd_ne; [| vm_compute; discriminate]. exact HN4a5. }
    assert (HN4z : N4 !!! Regidx z_idx = zero_reg).
    { unfold N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hz0. }
    assert (HN5a4 : N5 !!! Regidx a4_idx = (mword_of_int 1026 : mword 64)).
    { unfold N5. rewrite upd_eq. unfold regval_into_reg. rewrite HN4z.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HN5sw : (autocast (T := mword) (subrange_vec_dec (N5 !!! Regidx a4_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = plic_senable_word).
    { rewrite HN5a4. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x1a: sw a4,128(a5) -- PLIC_SENABLE(hart) = 1026 ---- *)
    iApply (wp_sw_plic_dev_s_sconf γ root_ppn γd Φ (mword_of_int (PH + 0x1a)) false a4_idx a5_idx
              (mword_of_int 128 : mword 12) N5 (n - 2)%nat
              ltac:(rewrite HN5a5; exact (proj1 (ph_senable_geom _ Hhart)))
              ltac:(rewrite HN5a5; exact (proj1 (proj2 (ph_senable_geom _ Hhart))))
              ltac:(rewrite HN5a5; exact (proj1 (proj2 (proj2 (ph_senable_geom _ Hhart)))))
              ltac:(rewrite HN5a5; exact (proj1 (proj2 (proj2 (proj2 (ph_senable_geom _ Hhart))))))
              ltac:(rewrite HN5a5; exact (proj2 (proj2 (proj2 (proj2 (ph_senable_geom _ Hhart))))))
              ltac:(rewrite HN5sw HN5a5; intros pq Hpq;
                    eexists; split;
                    [ exact (ph_senable_write _ pq Hhart)
                    | apply plic_ok_hupd_enable;
                      [ exact Hpq | exact plic_senable_ok_mask ] ])
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1a Hdinv").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp1e : add_vec_int (mword_of_int (PH + 0x1a) : mword 64) 4 = mword_of_int (PH + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* ---- 0x1e: slliw a0,a0,13 ---- *)
    assert (HN5a0 : N5 !!! Regidx a0_idx = m0 !!! Regidx tp_idx).
    { unfold N5, N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmoa0. }
    iApply (wp_slliw_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x1e)) a0_idx a0_idx
              (mword_of_int 13 : mword 5) (ph_shl (m0 !!! Regidx tp_idx) 13) N5 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HN5a0; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi1e [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp22 : add_vec_int (mword_of_int (PH + 0x1e) : mword 64) 4 = mword_of_int (PH + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 13)]> N5) with N6.
    (* ---- 0x22: lui a5,0xc201 ---- *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x22)) a5_idx
              (mword_of_int 0xc201 : mword 20) (mword_of_int 0x0c201000 : mword 64) N6 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi22 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (PH + 0x22) : mword 64) 4 = mword_of_int (PH + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N6) with N7.
    (* ---- 0x26: c.add a5,a5,a0 ---- *)
    iApply (wp_cadd_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x26)) a5_idx a0_idx N7 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi26 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp28 : add_vec_int (mword_of_int (PH + 0x26) : mword 64) 2 = mword_of_int (PH + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (N7 !!! Regidx a5_idx) (N7 !!! Regidx a0_idx))]> N7) with N8.
    (* the operands of the second store *)
    assert (HN7a5 : N7 !!! Regidx a5_idx = (mword_of_int 0x0c201000 : mword 64))
      by (unfold N7; apply upd_eq).
    assert (HN7a0 : N7 !!! Regidx a0_idx = ph_shl (m0 !!! Regidx tp_idx) 13).
    { unfold N7. rewrite upd_ne; [| vm_compute; discriminate].
      unfold N6. apply upd_eq. }
    assert (HN8a5 : N8 !!! Regidx a5_idx = ph_sthb (m0 !!! Regidx tp_idx)).
    { unfold N8. rewrite upd_eq. unfold regval_into_reg, ph_sthb.
      rewrite HN7a5 HN7a0. reflexivity. }
    assert (HN8z : N8 !!! Regidx z_idx = zero_reg).
    { unfold N8, N7, N6, N5, N4, N3, N2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hz0. }
    assert (HN8sw : (autocast (T := mword) (subrange_vec_dec (N8 !!! Regidx z_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = Z_to_bv 32 0).
    { rewrite HN8z. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x28: sw zero,0(a5) -- PLIC_SPRIORITY(hart) = 0 ---- *)
    iApply (wp_sw_plic_dev_s_sconf γ root_ppn γd Φ (mword_of_int (PH + 0x28)) false z_idx a5_idx
              (mword_of_int 0 : mword 12) N8 (n - 2)%nat
              ltac:(rewrite HN8a5; exact (proj1 (ph_sthresh_geom _ Hhart)))
              ltac:(rewrite HN8a5; exact (proj1 (proj2 (ph_sthresh_geom _ Hhart))))
              ltac:(rewrite HN8a5; exact (proj1 (proj2 (proj2 (ph_sthresh_geom _ Hhart)))))
              ltac:(rewrite HN8a5; exact (proj1 (proj2 (proj2 (proj2 (ph_sthresh_geom _ Hhart))))))
              ltac:(rewrite HN8a5; exact (proj2 (proj2 (proj2 (proj2 (ph_sthresh_geom _ Hhart))))))
              ltac:(rewrite HN8sw HN8a5; intros pq Hpq;
                    eexists; split;
                    [ exact (ph_sthresh_write _ pq Hhart)
                    | apply plic_ok_hupd_thresh; exact Hpq ])
              with "Hsc Hhs Hcg Htlbinv Hpc Hi28 Hdinv").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp2c : add_vec_int (mword_of_int (PH + 0x28) : mword 64) 4 = mword_of_int (PH + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- 0x2c: c.ldsp ra,8(sp) ---- *)
    assert (HN8sp : N8 !!! Regidx csp_rs1 = sp').
    { unfold N8, N7, N6, N5, N4, N3, N2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmosp. }
    assert (Hpa1' : add_vec (N8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HN8sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (N8 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HN8sp. rewrite -Hcsp1. exact Hpa2. }
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x2c)) (mword_of_int 1 : mword 6) ra_idx N8 (n - 2)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2c Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp2e : add_vec_int (mword_of_int (PH + 0x2c) : mword 64) 2 = mword_of_int (PH + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> N8) with N9.
    (* ---- 0x2e: c.ldsp s0,0(sp) ---- *)
    assert (HN9sp : N9 !!! Regidx csp_rs1 = N8 !!! Regidx csp_rs1)
      by (unfold N9; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -HN9sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x2e)) (mword_of_int 0 : mword 6) s0_idx N9 (n - 2)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi2e Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp30 : add_vec_int (mword_of_int (PH + 0x2e) : mword 64) 2 = mword_of_int (PH + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> N9) with N10.
    (* ---- 0x30: c.addi sp,16 -- the frame pop ---- *)
    assert (HN10sp : N10 !!! Regidx csp_rs1 = sp').
    { unfold N10, N9. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact HN8sp. }
    assert (Hwv : add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite HN10sp. unfold sp', imm_dealloc, imm_entry, sp0. apply plicinithart_frame_cancel. }
    assert (Hpop : N10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv HN10sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite HN9sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x30)) imm_dealloc N10
              (n - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi30 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp32 : add_vec_int (mword_of_int (PH + 0x30) : mword 64) 2 = mword_of_int (PH + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (N10 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> N10) with N11.
    (* ---- 0x32: c.ret ---- *)
    assert (HN11ra : N11 !!! Regidx ra_idx = ra0).
    { unfold N11, N10. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold N9. rewrite upd_eq. reflexivity. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (N11 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite HN11ra; exact Hretok).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (PH + 0x32)) ra_idx N11 n
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi32 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (N11 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite HN11ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! N11 with "Hhs Hsc Hcg Htlbinv Hpc [%]").
    split.
    - (* [callee_saved m0 N11].  The save/restore of sp and s0 SPANS the call
         (mid-call they hold the wrong values), so the fact does not factor
         through [callee_saved m0 m2] / [callee_saved mo N11] -- each conjunct
         is discharged on its own: sp and s0 by their epilogue restores, the
         other twelve by hopping cpuid's own [callee_saved]. *)
      unfold callee_saved.
      split.
      { unfold N11. rewrite upd_eq. unfold regval_into_reg. exact Hwv. }
      split; [ cs_through Hmo_cs mo | ].
      split.
      { unfold N11, N10, s0_idx, s00.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq. unfold regval_into_reg. reflexivity. }
      repeat split; cs_through Hmo_cs mo.
    - exact HN11ra.
  Qed.

End WpSconfPlicinithart.

End PlicinithartProof.
