(* ProofVirtioDiskInit.v -- the whole-function WP for xv6's virtio_disk_init()
   (kernel/virtio_disk.c) over the SIE-agnostic sconf world, against the
   interface in SpecVirtioDiskInit.v.

   ~127 instructions, straight-line apart from SIX refuted branches:

     - the four identification reads are constants of the device model
       ([virtio_read] at MAGIC/VERSION/DEVICE_ID/VENDOR_ID);
     - the FEATURES_OK re-read sticks (the status register reads back);
     - QUEUE_READY reads clear after the reset, QUEUE_NUM_MAX reads 8;
     - the three [kalloc]s cannot return null, because the caller supplies
       three pages ([page_valid] => non-null).

   The MMIO accesses go through the raw-[virtio_frag] width-4 leaves
   (WpVirtioMmio), wrapped here as [wp_vdi_sw]/[wp_vdi_lw] so a call site
   supplies only the effective address, the window geometry (a [vdi_geom]
   fact per concrete register address) and the device transaction.

   The three queue addresses are programmed as low/high halves; the halves
   are read back out of the [struct disk] cells (the DESC pair through a
   [word_pointsto_split4] of the 8-byte cell, the other two through an
   [ld] + [sext.w]/[srai]), and [set_lo_hi_id] reassembles them, which is
   what lets the spec's postcondition name [virtio_init_cfg pd pav pu]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes WpGpr RegFile WpMmodeLeafBase.
Require Import SmodeCore.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpAuipc.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import KernelDataInv.
Require Import ProcGeom.
Require Import KallocInv KvmSpec.
Require Import KptPt.
Require Import VirtioModel WpVirtioMmio.
Require Import VirtioModel.
Require Import WpMemsetPage.
Require Import WpVirtioDiskInitDecode.
Require Import SpecInitlock SpecKalloc SpecMemset SpecVirtioDiskInit.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 0.  mword-free arithmetic (the bitvector zify hook breaks [lia] on any  *)
(*     goal or context mentioning [bv_unsigned] -- claude-notes).          *)
(* ===================================================================== *)

Lemma vdi_cap_bounds (K : nat) : (18 <= K)%nat ->
  (4 <= K)%nat /\ (2 <= K - 4)%nat /\ (14 <= K - 4)%nat /\ ((K - 4) + 4 = K)%nat.
Proof. lia. Qed.

Lemma vdi_hi_byte_zero (x k : Z) : (0 <= x < 2 ^ 32)%Z -> (32 <= k)%Z -> (x ≫ k)%Z = 0%Z.
Proof.
  intros [H0 H1] Hk. rewrite Z.shiftr_div_pow2; [| lia].
  apply Z.div_small. split; [lia|].
  apply (Z.lt_le_trans _ (2 ^ 32)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma vdi_k_ge32 (j : nat) : (4 <= j)%nat -> (32 <= Z.of_N (8 * N.of_nat j))%Z.
Proof. lia. Qed.

Lemma vdi_j_lt4 (j : nat) : (N.of_nat j < 4)%N -> (j < 4)%nat.
Proof. lia. Qed.

Lemma vdi_j_lt8 (j : nat) : (N.of_nat j < 8)%N -> (j < 8)%nat.
Proof. lia. Qed.

Lemma vdi_lt32_of (z : Z) : (z < 0x88000000)%Z -> (z < 2 ^ 32)%Z.
Proof. intro. lia. Qed.

(* ===================================================================== *)
(* 1.  The low/high halves of a 64-bit queue address below 2^32.          *)
(* ===================================================================== *)

Lemma vdi_lo32_small (w : bv 64) : (bv_unsigned w < 2 ^ 32)%Z -> bv_unsigned (lo32 w) = bv_unsigned w.
Proof.
  intro H. pose proof (bv_unsigned_in_range _ w) as [Hl _].
  unfold lo32. rewrite bv_extract_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z. exact (conj Hl H).
Qed.

Lemma vdi_hi32_small (w : bv 64) : (bv_unsigned w < 2 ^ 32)%Z -> hi32 w = Z_to_bv 32 0.
Proof.
  intro H. pose proof (bv_unsigned_in_range _ w) as [Hl _].
  apply bv_eq. unfold hi32. rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned.
  f_equal. apply (vdi_hi_byte_zero (bv_unsigned w) (Z.of_N 32) (conj Hl H)).
  change (Z.of_N 32) with 32%Z. reflexivity.
Qed.

Lemma vdi_word_lo_small (w : bv 64) : (bv_unsigned w < 2 ^ 32)%Z -> word_lo w = lo32 w.
Proof.
  intro H. apply (bv_eq_of_bytes (n := 4)). intros j Hj.
  rewrite (nth_byte_word_lo w j (vdi_j_lt4 j Hj)).
  apply bv_eq. rewrite !nth_byte_unsigned. rewrite (vdi_lo32_small w H). reflexivity.
Qed.

Lemma vdi_word_hi_small (w : bv 64) : (bv_unsigned w < 2 ^ 32)%Z -> word_hi w = Z_to_bv 32 0.
Proof.
  intro H. pose proof (bv_unsigned_in_range _ w) as [Hl _].
  assert (Hz : forall j : nat, (4 <= j)%nat -> nth_byte w j = Z_to_bv 8 0).
  { intros j Hj. apply bv_eq. rewrite nth_byte_unsigned. rewrite Z_to_bv_unsigned.
    rewrite (vdi_hi_byte_zero (bv_unsigned w) _ (conj Hl H) (vdi_k_ge32 j Hj)).
    reflexivity. }
  unfold word_hi.
  rewrite (Hz 4%nat ltac:(lia)). rewrite (Hz 5%nat ltac:(lia)).
  rewrite (Hz 6%nat ltac:(lia)). rewrite (Hz 7%nat ltac:(lia)).
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma vdi_word_join (w : bv 64) : word_of_words (word_lo w) (word_hi w) = w.
Proof.
  apply (bv_eq_of_bytes (n := 8)). intros j Hj.
  pose proof (vdi_j_lt8 j Hj) as Hj8.
  destruct (decide (j < 4)%nat) as [Hlt|Hge].
  - rewrite (nth_byte_word_of_words_lo _ _ j Hlt).
    apply (nth_byte_word_lo w j Hlt).
  - replace j with (4 + (j - 4))%nat by lia.
    rewrite (nth_byte_word_of_words_hi _ _ (j - 4)%nat ltac:(lia)).
    apply (nth_byte_word_hi w (j - 4)%nat ltac:(lia)).
Qed.

(* the 4-byte store word IS [RiscvExtras.trunc32] *)
Lemma vdi_trunc32_lo32 (x : mword 64) : trunc32 x = lo32 x.
Proof.
  apply bv_eq. unfold trunc32. rewrite autocast_id.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  unfold lo32. rewrite !bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (MachineWord.MachineWord.Z_idx (Z.sub (Z.mul 4 8) 1 - 0 + 1)) with 32%N.
  reflexivity.
Qed.

Lemma vdi_bv_signed_small (x : mword 64) : (bv_unsigned x < 2 ^ 32)%Z -> bv_signed x = bv_unsigned x.
Proof.
  intro H. pose proof (bv_unsigned_in_range _ x) as [Hl _].
  unfold bv_signed. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z) by (vm_compute; reflexivity).
  rewrite Hhm. split; [lia|]. apply (Z.lt_trans _ (2 ^ 32)); [exact H | reflexivity].
Qed.

Lemma vdi_srai32 (x : mword 64) : (bv_unsigned x < 2 ^ 32)%Z ->
  shift_bits_right_arith x (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int 0 : mword 64).
Proof.
  intro H. pose proof (bv_unsigned_in_range _ x) as [Hl _].
  apply bv_eq.
  unfold shift_bits_right_arith, arith_shiftr, SailStdpp.Values.with_word, get_word,
         MachineWord.MachineWord.arith_shift_right.
  rewrite bv_ashiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
             (MachineWord.MachineWord.Z_idx (int_of_mword false
                (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))))) with 32%Z
    by (vm_compute; reflexivity).
  rewrite (vdi_bv_signed_small x H).
  rewrite Z.shiftr_div_pow2; [| lia].
  replace (bv_unsigned x / 2 ^ 32)%Z with 0%Z
    by (symmetry; apply Z.div_small; split; [lia | exact H]).
  vm_compute. reflexivity.
Qed.

Lemma vdi_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  apply bv_eq.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z.
  rewrite Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

(* the queue address the device ends up with IS the page the driver kalloc'd *)
Lemma vdi_reassemble (a : Arch.pa) : (bv_unsigned a < 2 ^ 32)%Z ->
  set_hi (set_lo zero64 (lo32 a)) (Z_to_bv 32 0) = a.
Proof. intro H. rewrite <- (vdi_hi32_small a H). apply set_lo_hi_id. Qed.

(* the 4-slot frame push/pop cancel *)
Lemma vdi_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64) = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64) = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* the [sext.w rd,rs] + [sw] pair commits exactly the low half of [rs] *)
Lemma vdi_addiw_sw (x : mword 64) :
  trunc32 (sign_extend' 64 (subrange_vec_dec
             (add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)) = lo32 x.
Proof.
  rewrite addv_sext0. rewrite trunc32_sext64.
  rewrite <- vdi_trunc32_lo32. unfold trunc32.
  change (Z.sub (Z.mul 4 8) 1) with 31%Z. symmetry. apply autocast_id.
Qed.

(* ===================================================================== *)
(* 2.  The virtio-mmio window geometry, per concrete register address.    *)
(* ===================================================================== *)

Definition vdi_geom (a : mword 64) : Prop :=
  (virtio_base <= uint a < virtio_base + virtio_size)%Z
  /\ is_aligned_vaddr (Virtaddr a) 4 = true
  /\ neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false
  /\ kpt_dev_vpn (svpn_of a).

Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.
Ltac vgeom := unfold vdi_geom; split; [zrange_vm|];
              split; [vm_compute; reflexivity|];
              split; [vm_compute; reflexivity|];
              unfold kpt_dev_vpn; zrange_vm.

Lemma vg_010 : vdi_geom (mword_of_int 0x10001010). Proof. vgeom. Qed.
Lemma vg_020 : vdi_geom (mword_of_int 0x10001020). Proof. vgeom. Qed.
Lemma vg_030 : vdi_geom (mword_of_int 0x10001030). Proof. vgeom. Qed.
Lemma vg_034 : vdi_geom (mword_of_int 0x10001034). Proof. vgeom. Qed.
Lemma vg_038 : vdi_geom (mword_of_int 0x10001038). Proof. vgeom. Qed.
Lemma vg_044 : vdi_geom (mword_of_int 0x10001044). Proof. vgeom. Qed.
Lemma vg_070 : vdi_geom (mword_of_int 0x10001070). Proof. vgeom. Qed.
Lemma vg_080 : vdi_geom (mword_of_int 0x10001080). Proof. vgeom. Qed.
Lemma vg_084 : vdi_geom (mword_of_int 0x10001084). Proof. vgeom. Qed.
Lemma vg_090 : vdi_geom (mword_of_int 0x10001090). Proof. vgeom. Qed.
Lemma vg_094 : vdi_geom (mword_of_int 0x10001094). Proof. vgeom. Qed.
Lemma vg_0a0 : vdi_geom (mword_of_int 0x100010a0). Proof. vgeom. Qed.
Lemma vg_0a4 : vdi_geom (mword_of_int 0x100010a4). Proof. vgeom. Qed.
Lemma vg_000 : vdi_geom (mword_of_int 0x10001000). Proof. vgeom. Qed.
Lemma vg_004 : vdi_geom (mword_of_int 0x10001004). Proof. vgeom. Qed.
Lemma vg_008 : vdi_geom (mword_of_int 0x10001008). Proof. vgeom. Qed.
Lemma vg_00c : vdi_geom (mword_of_int 0x1000100c). Proof. vgeom. Qed.

(* ===================================================================== *)
(* 3.  The device-state vocabulary this proof threads.                    *)
(* ===================================================================== *)

Definition vdi_v (st dfeat qsel qnum : Z) (rdy : bool) (d a u : Arch.pa)
                 (dk : Z -> bv 8) : virtio_state :=
  VirtioState (VirtioCfg (Z_to_bv 32 st) (Z_to_bv 32 dfeat) (Z_to_bv 32 qsel)
                         (Z_to_bv 32 qnum) rdy d a u)
              zero32 zero16 zero16 dk.

(* ===================================================================== *)
(* 4.  The two virtio-mmio leaves, at a CONCRETE effective address.       *)
(*     Everything else this function executes is a shared leaf            *)
(*     (WpSconfAlu / WpSconfMem / WpSconfBtype / WpSconfCtl).             *)
(* ===================================================================== *)

Section VdiLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_vdi_sw (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v v' : virtio_state)
      (a : mword 64) (off : Z) (sw : mword 32) :
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = a ->
    vdi_geom a ->
    (uint a - virtio_base)%Z = off ->
    trunc32 (m !!! Regidx rs2) = sw ->
    virtio_write v off sw = Some v' ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    virtio_frag v -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc (if rvc then 2 else 4)) -∗
      virtio_frag v' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hea Hg Hoff Hsw Hvw. destruct Hg as (Hr & Hal & Hcan & Hdv).
    assert (Hsw' : (autocast (T := mword)
                      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = sw)
      by exact Hsw.
    assert (Ha8 : sign_extend' 64 (subrange_vec_dec
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = a).
    { rewrite subrange_id. rewrite sign_extend'_id. exact Hea. }
    iIntros "Hcg Hpc Hinstr Hv Hcont".
    iApply (wp_sw_virtio_frag_s_sconf γ Φ pc rvc rs2 rs1 imm m n v v'
              ltac:(rewrite Ha8; exact Hr)
              ltac:(rewrite Ha8; exact Hal)
              ltac:(rewrite Ha8; exact Hcan)
              ltac:(rewrite Ha8; exact Hdv)
              ltac:(rewrite Ha8; rewrite Hoff; rewrite Hsw'; exact Hvw)
              with "Hcg Hpc Hinstr Hv Hcont").
  Qed.

  Lemma vdi_ldval (w : mword 32) :
    extend_value false (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) w)
    = sign_extend' 64 w.
  Proof. rewrite <- (data2_ext_4 w). rewrite autocast_id. reflexivity. Qed.

  Lemma wp_vdi_lw (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rvc : bool) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (v : virtio_state)
      (a : mword 64) (off : Z) (w : mword 32) :
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = a ->
    vdi_geom a ->
    (uint a - virtio_base)%Z = off ->
    uint rd <> 0 -> rd <> csp_rs1 ->
    virtio_read v off = Some w ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗ instr pc rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    virtio_frag v -∗
    ( sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 w)]> m) n -∗
      pc_is (add_vec_int pc (if rvc then 2 else 4)) -∗
      virtio_frag v -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hea Hg Hoff Hrd Hrdsp Hvr. destruct Hg as (Hr & Hal & Hcan & Hdv).
    assert (Ha8 : sign_extend' 64 (subrange_vec_dec
                    (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = a).
    { rewrite subrange_id. rewrite sign_extend'_id. exact Hea. }
    iIntros "Hcg Hpc Hinstr Hv Hcont".
    iApply (wp_lw_virtio_frag_s_sconf γ Φ pc rvc false rd rs1 imm m n v w
              ltac:(rewrite Ha8; exact Hr)
              ltac:(rewrite Ha8; exact Hal)
              ltac:(rewrite Ha8; exact Hcan)
              ltac:(rewrite Ha8; exact Hdv)
              Hrd Hrdsp
              ltac:(rewrite Ha8; rewrite Hoff; exact Hvr)
              with "Hcg Hpc Hinstr Hv [-]").
    iIntros "Hcg Hpc Hv". iEval (rewrite vdi_ldval) in "Hcg".
    iApply ("Hcont" with "Hcg Hpc Hv").
  Qed.

End VdiLeaves.

(* ===================================================================== *)
(* 5.  THE BODY.                                                          *)
(* ===================================================================== *)

Module VirtioDiskInitProof (IL : INITLOCK) (AK : KALLOC) (MS : MEMSET) : VIRTIODISKINIT.
Section ProofVirtioDiskInit.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation VDI := KernelSyms.virtio_disk_init.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Ltac peel :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac pcs := apply bv_eq; vm_compute; reflexivity.
  Ltac nzd := vm_compute; discriminate.
  Ltac bvc := apply bv_eq; vm_compute; reflexivity.

  (* NAMING THE REGISTER CHAIN: [pose], never [set].  Each leaf lemma is
     applied at its ENTRY map by name ([iApply (wp_… Bk …)]) and hands back
     [<[rd := v]> Bk], so the goal is never more than ONE insert deep and there
     is nothing for [set]'s whole-goal occurrence abstraction to buy — while
     paying for it means re-scanning this proof's Iris context (the device
     invariant, the disk resources, the whole-function continuation) once per
     instruction.  Measured on the 85 chain links here: [set] 1.7 s each,
     [pose] ~0.05 s — 305 s vs 177 s for the file.  The next [iApply] closes
     the gap with one delta step on the name.  Keep [set] only where the
     abstraction is the point ([sp0], [spr], [dk], [pd], [pav], [pu] — values
     that really do occur all over the goal). *)

  Lemma wp_virtio_disk_init_sconf (γ γa : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
      (v0 : virtio_state) (vlock : bv 32) (vname vcpu : bv 64)
      (pd0 pav0 pu0 : mword 64) (free0 : nat -> bv 8)
    : wp_virtio_disk_init_sconf_body γ γa Φ m K eb pp C on v0 vlock vname vcpu
                                     pd0 pav0 pu0 free0.
  Proof.
    cbv beta delta [wp_virtio_disk_init_sconf_body].
    intros pcE ret_tgt c_name c_cpu HK Hex Hcid.
    destruct Hex as (nb & Hon & Hnb). subst on.
    pose proof (vdi_cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hknk).
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (dk := v_disk v0).
    iIntros "Hcg Hcpu #Htext #Hkdata Hpc Henv Hv Hlk Hnm Hcp Hdesc Havail Hused Hfree Hcont".
    (* the "virtio_disk" string literal, read out of the data image *)
    pose (nmv := (mword_of_int 0x80007630 : mword 64)).
    assert (Hstrb : forall j b, cstring_bytes "virtio_disk"%string !! j = Some b ->
                    KernelData.kernel_data !! (0x80007630 + Z.of_nat j)%Z = Some b).
    { intros j b Hj.
      do 12 (destruct j as [|j];
             [vm_compute in Hj; injection Hj as <-; vm_compute; reflexivity |]);
      vm_compute in Hj; discriminate. }
    iPoseProof (kernel_data_string 0x80007630%Z "virtio_disk"%string nmv eq_refl
                  ltac:(unfold text_end; lia) Hstrb with "Hkdata") as "#Hstr".
    (* frame-cell address facts (4-slot frame: ra@24, s0@16, s1@8, s2@0) *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. bvc. }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try bvc. }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try bvc. }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try bvc. }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try bvc. }
    (* ===== PROLOGUE (0x000..0x00a) ===== *)
    iPoseProof (vdi_000 with "Htext") as "Hi".
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int VDI) (mword_of_int 32 : mword 6) m K 4
              Hc4 Hpush with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hframe Hpc". iClear "Hi".
    pose (W1 := <[Regidx csp_rs1 := regval_into_reg spr]> m).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (w1) "Hs1c". iDestruct "S2" as (w2) "Hs2c".
    iDestruct "S3" as (w3) "Hs3c". iDestruct "S4" as (w4) "Hs4c".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1 upd_eq; reflexivity).
    assert (Hp002 : add_vec_int (mword_of_int VDI : mword 64) 2 = mword_of_int (VDI + 0x002)) by pcs.
    iEval (rewrite Hp002) in "Hpc".
    (* +0x002 sd ra,24(sp) *)
    iPoseProof (vdi_002 with "Htext") as "Hi".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (VDI + 0x002)) (mword_of_int 3 : mword 6)
              (mword_of_int 1 : mword 5) W1 (K - 4)%nat w1 with "Hcg Hpc Hi [Hs1c] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hs1c". }
    iIntros "Hcg Hpc Hs1c". iEval (rewrite HspW1 Hb1) in "Hs1c". iClear "Hi".
    assert (HW1ra : W1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1ra) in "Hs1c".
    assert (Hp004 : add_vec_int (mword_of_int (VDI + 0x002) : mword 64) 2 = mword_of_int (VDI + 0x004)) by pcs.
    iEval (rewrite Hp004) in "Hpc".
    (* +0x004 sd s0,16(sp) *)
    iPoseProof (vdi_004 with "Htext") as "Hi".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (VDI + 0x004)) (mword_of_int 2 : mword 6)
              (mword_of_int 8 : mword 5) W1 (K - 4)%nat w2 with "Hcg Hpc Hi [Hs2c] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hs2c". }
    iIntros "Hcg Hpc Hs2c". iEval (rewrite HspW1 Hb2) in "Hs2c". iClear "Hi".
    assert (HW1s0 : W1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1s0) in "Hs2c".
    assert (Hp006 : add_vec_int (mword_of_int (VDI + 0x004) : mword 64) 2 = mword_of_int (VDI + 0x006)) by pcs.
    iEval (rewrite Hp006) in "Hpc".
    (* +0x006 sd s1,8(sp) *)
    iPoseProof (vdi_006 with "Htext") as "Hi".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (VDI + 0x006)) (mword_of_int 1 : mword 6)
              (mword_of_int 9 : mword 5) W1 (K - 4)%nat w3 with "Hcg Hpc Hi [Hs3c] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hs3c". }
    iIntros "Hcg Hpc Hs3c". iEval (rewrite HspW1 Hb3) in "Hs3c". iClear "Hi".
    assert (HW1s1 : W1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1s1) in "Hs3c".
    assert (Hp008 : add_vec_int (mword_of_int (VDI + 0x006) : mword 64) 2 = mword_of_int (VDI + 0x008)) by pcs.
    iEval (rewrite Hp008) in "Hpc".
    (* +0x008 sd s2,0(sp) *)
    iPoseProof (vdi_008 with "Htext") as "Hi".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (VDI + 0x008)) (mword_of_int 0 : mword 6)
              (mword_of_int 18 : mword 5) W1 (K - 4)%nat w4 with "Hcg Hpc Hi [Hs4c] [-]").
    { iEval (rewrite HspW1 Hb4). iExact "Hs4c". }
    iIntros "Hcg Hpc Hs4c". iEval (rewrite HspW1 Hb4) in "Hs4c". iClear "Hi".
    assert (HW1s2 : W1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /W1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1s2) in "Hs4c".
    assert (Hp00a : add_vec_int (mword_of_int (VDI + 0x008) : mword 64) 2 = mword_of_int (VDI + 0x00a)) by pcs.
    iEval (rewrite Hp00a) in "Hpc".
    (* +0x00a addi s0,sp,32 (value unused; s0 reloaded at the epilogue) *)
    iPoseProof (vdi_00a with "Htext") as "Hi".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (VDI + 0x00a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5) W1 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp00c : add_vec_int (mword_of_int (VDI + 0x00a) : mword 64) 2 = mword_of_int (VDI + 0x00c)) by pcs.
    iEval (rewrite Hp00c) in "Hpc".
    (* ===== initlock(&disk.vdisk_lock, "virtio_disk") (0x00c..0x01c) ===== *)
    (* +0x00c auipc a1,0x2 *)
    iPoseProof (vdi_00c with "Htext") as "Hi".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VDI + 0x00c)) (mword_of_int 11 : mword 5)
              (mword_of_int 2 : mword 20) W2 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (VDI + 0x00c) : mword 64) (auipc_off (mword_of_int 2 : mword 20)))]> W2).
    assert (Hp010 : add_vec_int (mword_of_int (VDI + 0x00c) : mword 64) 4 = mword_of_int (VDI + 0x010)) by pcs.
    iEval (rewrite Hp010) in "Hpc".
    (* +0x010 addi a1,a1,156 : a1 := &"virtio_disk" *)
    iPoseProof (vdi_010 with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x010)) (mword_of_int 11 : mword 5)
              (mword_of_int 11 : mword 5) (mword_of_int 156 : mword 12) W3 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg
        (add_vec (W3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 156 : mword 12)))]> W3).
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = nmv) by (peel; bvc).
    assert (Hp014 : add_vec_int (mword_of_int (VDI + 0x010) : mword 64) 4 = mword_of_int (VDI + 0x014)) by pcs.
    iEval (rewrite Hp014) in "Hpc".
    (* +0x014 auipc a0,0x1e *)
    iPoseProof (vdi_014 with "Htext") as "Hi".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VDI + 0x014)) (mword_of_int 10 : mword 5)
              (mword_of_int 30 : mword 20) W4 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (VDI + 0x014) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> W4).
    assert (Hp018 : add_vec_int (mword_of_int (VDI + 0x014) : mword 64) 4 = mword_of_int (VDI + 0x018)) by pcs.
    iEval (rewrite Hp018) in "Hpc".
    (* +0x018 addi a0,a0,-92 : a0 := &disk.vdisk_lock *)
    iPoseProof (vdi_018 with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x018)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 4004 : mword 12) W5 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (W5 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 4004 : mword 12)))]> W5).
    assert (HW6a0 : W6 !!! Regidx (mword_of_int 10 : mword 5) = disk_lock) by (peel; bvc).
    assert (Hp01c : add_vec_int (mword_of_int (VDI + 0x018) : mword 64) 4 = mword_of_int (VDI + 0x01c)) by pcs.
    iEval (rewrite Hp01c) in "Hpc".
    (* +0x01c jal initlock *)
    iPoseProof (vdi_01c with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x01c)) (mword_of_int 1 : mword 5)
              (mword_of_int 2078180 : mword 21) W6 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (W7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (VDI + 0x01c) : mword 64) 4)]> W6).
    assert (Htgtil : add_vec (mword_of_int (VDI + 0x01c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2078180 : mword 21))
                     = mword_of_int KernelSyms.initlock) by bvc.
    iEval (rewrite Htgtil) in "Hpc".
    assert (HW7a0 : W7 !!! Regidx (mword_of_int 10 : mword 5) = disk_lock)
      by (rewrite /W7 upd_ne; [exact HW6a0 | reg_neq]).
    assert (HW7a1 : W7 !!! Regidx (mword_of_int 11 : mword 5) = nmv).
    { rewrite /W7 upd_ne; [| reg_neq]. rewrite /W6 upd_ne; [| reg_neq].
      rewrite /W5 upd_ne; [exact HW4a1 | reg_neq]. }
    assert (HW7sp : W7 !!! Regidx csp_rs1 = spr).
    { rewrite /W7 upd_ne; [| reg_neq]. rewrite /W6 upd_ne; [| reg_neq].
      rewrite /W5 upd_ne; [| reg_neq]. rewrite /W4 upd_ne; [| reg_neq].
      rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq]. exact HspW1. }
    assert (HW7tp : W7 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /W7 upd_ne; [| reg_neq]. rewrite /W6 upd_ne; [| reg_neq].
      rewrite /W5 upd_ne; [| reg_neq]. rewrite /W4 upd_ne; [| reg_neq].
      rewrite /W3 upd_ne; [| reg_neq]. rewrite /W2 upd_ne; [| reg_neq].
      rewrite /W1 upd_ne; [reflexivity | reg_neq]. }
    iApply (IL.wp_initlock_sconf γ Φ W7 vlock vname vcpu "virtio_disk"%string (K - 4)%nat
              ltac:(lia) with "Hcg Htext Hpc [] [Hlk] [Hnm] [Hcp]").
    { iEval (rewrite HW7a1). iExact "Hstr". }
    { iEval (rewrite HW7a0). iExact "Hlk". }
    { iEval (rewrite HW7a0). iExact "Hnm". }
    { iEval (rewrite HW7a0). iExact "Hcp". }
    iIntros (mil) "Hcg Hpc %Hilcs Hlk Hnm Hcp".
    iEval (rewrite HW7a0) in "Hlk".
    iEval (rewrite HW7a0 HW7a1) in "Hnm".
    iEval (rewrite HW7a0) in "Hcp".
    iMod (lock_name_intro with "Hstr Hnm") as "#Hlnm".
    assert (Hretil : ret_pc (W7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x020)).
    { rewrite /W7 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hretil) in "Hpc".
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hilcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HW7sp. }
    assert (Hmiltp : mil !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite (callee_saved_lookup Hilcs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HW7tp. }
    (* ===== the four identification reads (0x020..0x05e), all refuted ===== *)
    (* +0x020 lui a5,0x10001 *)
    iPoseProof (vdi_020 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x020)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) mil (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> mil).
    assert (HB1a5 : B1 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp024 : add_vec_int (mword_of_int (VDI + 0x020) : mword 64) 4 = mword_of_int (VDI + 0x024)) by pcs.
    iEval (rewrite Hp024) in "Hpc".
    (* +0x024 lw a4,0(a5) : MAGIC *)
    iPoseProof (vdi_024 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x024)) true (mword_of_int 14 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 12) B1 (K - 4)%nat v0
              (mword_of_int 0x10001000) 0 (Z_to_bv 32 0x74726976)
              ltac:(rewrite HB1a5; bvc) vg_000 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 0x74726976 : mword 32))]> B1).
    assert (Hp026 : add_vec_int (mword_of_int (VDI + 0x024) : mword 64) 2 = mword_of_int (VDI + 0x026)) by pcs.
    iEval (rewrite Hp026) in "Hpc".
    (* +0x026 sext.w a4,a4 *)
    iPoseProof (vdi_026 with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x026)) (mword_of_int 14 : mword 5)
              (mword_of_int 0 : mword 6) B2 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B2 !!! Regidx (mword_of_int 14 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B2).
    assert (Hp028 : add_vec_int (mword_of_int (VDI + 0x026) : mword 64) 2 = mword_of_int (VDI + 0x028)) by pcs.
    iEval (rewrite Hp028) in "Hpc".
    (* +0x028 lui a5,0x74727 *)
    iPoseProof (vdi_028 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x028)) (mword_of_int 15 : mword 5)
              (mword_of_int 476967 : mword 20) (luival (mword_of_int 476967 : mword 20)) B3 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 476967 : mword 20))]> B3).
    assert (Hp02c : add_vec_int (mword_of_int (VDI + 0x028) : mword 64) 4 = mword_of_int (VDI + 0x02c)) by pcs.
    iEval (rewrite Hp02c) in "Hpc".
    (* +0x02c addi a5,a5,-1674 *)
    iPoseProof (vdi_02c with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x02c)) (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 2422 : mword 12) B4 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (B4 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 2422 : mword 12)))]> B4).
    assert (HB5a5 : B5 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x74726976) by (peel; bvc).
    assert (HB5a4 : B5 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x74726976) by (peel; bvc).
    assert (Hp030 : add_vec_int (mword_of_int (VDI + 0x02c) : mword 64) 4 = mword_of_int (VDI + 0x030)) by pcs.
    iEval (rewrite Hp030) in "Hpc".
    (* +0x030 bne a4,a5 -- NOT taken (magic value is a model constant) *)
    iPoseProof (vdi_030 with "Htext") as "Hi".
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (VDI + 0x030)) (mword_of_int 336 : mword 13)
              (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) B5 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(rewrite HB5a4 HB5a5; vm_compute; reflexivity)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp034 : add_vec_int (mword_of_int (VDI + 0x030) : mword 64) 4 = mword_of_int (VDI + 0x034)) by pcs.
    iEval (rewrite Hp034) in "Hpc".
    (* +0x034 lui a5,0x10001 *)
    iPoseProof (vdi_034 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x034)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B5 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B5).
    assert (HB6a5 : B6 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp038 : add_vec_int (mword_of_int (VDI + 0x034) : mword 64) 4 = mword_of_int (VDI + 0x038)) by pcs.
    iEval (rewrite Hp038) in "Hpc".
    (* +0x038 lw a5,4(a5) : VERSION *)
    iPoseProof (vdi_038 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x038)) true (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 4 : mword 12) B6 (K - 4)%nat v0
              (mword_of_int 0x10001004) 4 (Z_to_bv 32 2)
              ltac:(rewrite HB6a5; bvc) vg_004 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 2 : mword 32))]> B6).
    assert (Hp03a : add_vec_int (mword_of_int (VDI + 0x038) : mword 64) 2 = mword_of_int (VDI + 0x03a)) by pcs.
    iEval (rewrite Hp03a) in "Hpc".
    (* +0x03a sext.w a5,a5 *)
    iPoseProof (vdi_03a with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x03a)) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 6) B7 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B7 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B7).
    assert (Hp03c : add_vec_int (mword_of_int (VDI + 0x03a) : mword 64) 2 = mword_of_int (VDI + 0x03c)) by pcs.
    iEval (rewrite Hp03c) in "Hpc".
    (* +0x03c li a4,2 *)
    iPoseProof (vdi_03c with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x03c)) (mword_of_int 14 : mword 5)
              (mword_of_int 2 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) B8 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> B8).
    assert (HB9a5 : B9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 2) by (peel; bvc).
    assert (HB9a4 : B9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 2) by (peel; bvc).
    assert (Hp03e : add_vec_int (mword_of_int (VDI + 0x03c) : mword 64) 2 = mword_of_int (VDI + 0x03e)) by pcs.
    iEval (rewrite Hp03e) in "Hpc".
    (* +0x03e bne a5,a4 -- NOT taken *)
    iPoseProof (vdi_03e with "Htext") as "Hi".
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (VDI + 0x03e)) (mword_of_int 322 : mword 13)
              (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) B9 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(rewrite HB9a5 HB9a4; vm_compute; reflexivity)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp042 : add_vec_int (mword_of_int (VDI + 0x03e) : mword 64) 4 = mword_of_int (VDI + 0x042)) by pcs.
    iEval (rewrite Hp042) in "Hpc".
    (* +0x042 lui a5,0x10001 *)
    iPoseProof (vdi_042 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x042)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B9 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B9).
    assert (HB10a5 : B10 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp046 : add_vec_int (mword_of_int (VDI + 0x042) : mword 64) 4 = mword_of_int (VDI + 0x046)) by pcs.
    iEval (rewrite Hp046) in "Hpc".
    (* +0x046 lw a5,8(a5) : DEVICE_ID *)
    iPoseProof (vdi_046 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x046)) true (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 8 : mword 12) B10 (K - 4)%nat v0
              (mword_of_int 0x10001008) 8 (Z_to_bv 32 2)
              ltac:(rewrite HB10a5; bvc) vg_008 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 2 : mword 32))]> B10).
    assert (Hp048 : add_vec_int (mword_of_int (VDI + 0x046) : mword 64) 2 = mword_of_int (VDI + 0x048)) by pcs.
    iEval (rewrite Hp048) in "Hpc".
    (* +0x048 sext.w a5,a5 *)
    iPoseProof (vdi_048 with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x048)) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 6) B11 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B11 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B11).
    assert (HB12a5 : B12 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 2) by (peel; bvc).
    assert (HB12a4 : B12 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 2) by (peel; bvc).
    assert (Hp04a : add_vec_int (mword_of_int (VDI + 0x048) : mword 64) 2 = mword_of_int (VDI + 0x04a)) by pcs.
    iEval (rewrite Hp04a) in "Hpc".
    (* +0x04a bne a5,a4 -- NOT taken *)
    iPoseProof (vdi_04a with "Htext") as "Hi".
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (VDI + 0x04a)) (mword_of_int 310 : mword 13)
              (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) B12 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(rewrite HB12a5 HB12a4; vm_compute; reflexivity)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp04e : add_vec_int (mword_of_int (VDI + 0x04a) : mword 64) 4 = mword_of_int (VDI + 0x04e)) by pcs.
    iEval (rewrite Hp04e) in "Hpc".
    (* +0x04e lui a5,0x10001 *)
    iPoseProof (vdi_04e with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x04e)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B12 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B13 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B12).
    assert (HB13a5 : B13 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp052 : add_vec_int (mword_of_int (VDI + 0x04e) : mword 64) 4 = mword_of_int (VDI + 0x052)) by pcs.
    iEval (rewrite Hp052) in "Hpc".
    (* +0x052 lw a4,12(a5) : VENDOR_ID *)
    iPoseProof (vdi_052 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x052)) true (mword_of_int 14 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 12 : mword 12) B13 (K - 4)%nat v0
              (mword_of_int 0x1000100c) 12 (Z_to_bv 32 0x554d4551)
              ltac:(rewrite HB13a5; bvc) vg_00c ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 0x554d4551 : mword 32))]> B13).
    assert (Hp054 : add_vec_int (mword_of_int (VDI + 0x052) : mword 64) 2 = mword_of_int (VDI + 0x054)) by pcs.
    iEval (rewrite Hp054) in "Hpc".
    (* +0x054 sext.w a4,a4 *)
    iPoseProof (vdi_054 with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x054)) (mword_of_int 14 : mword 5)
              (mword_of_int 0 : mword 6) B14 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B15 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B14 !!! Regidx (mword_of_int 14 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B14).
    assert (Hp056 : add_vec_int (mword_of_int (VDI + 0x054) : mword 64) 2 = mword_of_int (VDI + 0x056)) by pcs.
    iEval (rewrite Hp056) in "Hpc".
    (* +0x056 lui a5,0x554d4 *)
    iPoseProof (vdi_056 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x056)) (mword_of_int 15 : mword 5)
              (mword_of_int 349396 : mword 20) (luival (mword_of_int 349396 : mword 20)) B15 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B16 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 349396 : mword 20))]> B15).
    assert (Hp05a : add_vec_int (mword_of_int (VDI + 0x056) : mword 64) 4 = mword_of_int (VDI + 0x05a)) by pcs.
    iEval (rewrite Hp05a) in "Hpc".
    (* +0x05a addi a5,a5,1361 *)
    iPoseProof (vdi_05a with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x05a)) (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 1361 : mword 12) B16 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B17 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (B16 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 1361 : mword 12)))]> B16).
    assert (HB17a5 : B17 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x554d4551) by (peel; bvc).
    assert (HB17a4 : B17 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x554d4551) by (peel; bvc).
    assert (Hp05e : add_vec_int (mword_of_int (VDI + 0x05a) : mword 64) 4 = mword_of_int (VDI + 0x05e)) by pcs.
    iEval (rewrite Hp05e) in "Hpc".
    (* +0x05e bne a4,a5 -- NOT taken *)
    iPoseProof (vdi_05e with "Htext") as "Hi".
    iApply (wp_bne_fall_s_sconf γ Φ (mword_of_int (VDI + 0x05e)) (mword_of_int 290 : mword 13)
              (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) B17 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(rewrite HB17a4 HB17a5; vm_compute; reflexivity)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp062 : add_vec_int (mword_of_int (VDI + 0x05e) : mword 64) 4 = mword_of_int (VDI + 0x062)) by pcs.
    iEval (rewrite Hp062) in "Hpc".
    (* ===== the reset / status / feature sequence (0x062..0x0ba) ===== *)
    pose (V1 := vdi_v 0 0 0 0 false zero64 zero64 zero64 dk).
    pose (V2 := vdi_v 1 0 0 0 false zero64 zero64 zero64 dk).
    pose (V3 := vdi_v 3 0 0 0 false zero64 zero64 zero64 dk).
    pose (V5 := vdi_v 11 0 0 0 false zero64 zero64 zero64 dk).
    (* +0x062 lui a5,0x10001 *)
    iPoseProof (vdi_062 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x062)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B17 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B18 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B17).
    assert (HB18a5 : B18 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp066 : add_vec_int (mword_of_int (VDI + 0x062) : mword 64) 4 = mword_of_int (VDI + 0x066)) by pcs.
    iEval (rewrite Hp066) in "Hpc".
    (* +0x066 sw zero,112(a5) : STATUS <- 0 (device reset) *)
    iDestruct (sie_cap_gpr_x0 γ B18 (K - 4)%nat (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx18 Hcg]".
    iPoseProof (vdi_066 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x066)) false (mword_of_int 0 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 112 : mword 12) B18 (K - 4)%nat v0 V1
              (mword_of_int 0x10001070) 112 (Z_to_bv 32 0 : mword 32)
              ltac:(rewrite HB18a5; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hx18; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp06a : add_vec_int (mword_of_int (VDI + 0x066) : mword 64) 4 = mword_of_int (VDI + 0x06a)) by pcs.
    iEval (rewrite Hp06a) in "Hpc".
    (* +0x06a li a4,1 *)
    iPoseProof (vdi_06a with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x06a)) (mword_of_int 14 : mword 5)
              (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) B18 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B19 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> B18).
    assert (HB19a5 : B19 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000)
      by (rewrite /B19 upd_ne; [exact HB18a5 | reg_neq]).
    assert (HB19a4 : B19 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 1) by (peel; bvc).
    assert (Hp06c : add_vec_int (mword_of_int (VDI + 0x06a) : mword 64) 2 = mword_of_int (VDI + 0x06c)) by pcs.
    iEval (rewrite Hp06c) in "Hpc".
    (* +0x06c sw a4,112(a5) : STATUS <- ACKNOWLEDGE *)
    iPoseProof (vdi_06c with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x06c)) true (mword_of_int 14 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 112 : mword 12) B19 (K - 4)%nat V1 V2
              (mword_of_int 0x10001070) 112 (Z_to_bv 32 1 : mword 32)
              ltac:(rewrite HB19a5; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HB19a4; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp06e : add_vec_int (mword_of_int (VDI + 0x06c) : mword 64) 2 = mword_of_int (VDI + 0x06e)) by pcs.
    iEval (rewrite Hp06e) in "Hpc".
    (* +0x06e li a4,3 *)
    iPoseProof (vdi_06e with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x06e)) (mword_of_int 14 : mword 5)
              (mword_of_int 3 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))) B19 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B20 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))]> B19).
    assert (HB20a5 : B20 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000)
      by (rewrite /B20 upd_ne; [exact HB19a5 | reg_neq]).
    assert (HB20a4 : B20 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 3) by (peel; bvc).
    assert (Hp070 : add_vec_int (mword_of_int (VDI + 0x06e) : mword 64) 2 = mword_of_int (VDI + 0x070)) by pcs.
    iEval (rewrite Hp070) in "Hpc".
    (* +0x070 sw a4,112(a5) : STATUS <- | DRIVER *)
    iPoseProof (vdi_070 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x070)) true (mword_of_int 14 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 112 : mword 12) B20 (K - 4)%nat V2 V3
              (mword_of_int 0x10001070) 112 (Z_to_bv 32 3 : mword 32)
              ltac:(rewrite HB20a5; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HB20a4; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp072 : add_vec_int (mword_of_int (VDI + 0x070) : mword 64) 2 = mword_of_int (VDI + 0x072)) by pcs.
    iEval (rewrite Hp072) in "Hpc".
    (* +0x072 lui a4,0x10001 *)
    iPoseProof (vdi_072 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x072)) (mword_of_int 14 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B20 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B21 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B20).
    assert (HB21a4 : B21 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp076 : add_vec_int (mword_of_int (VDI + 0x072) : mword 64) 4 = mword_of_int (VDI + 0x076)) by pcs.
    iEval (rewrite Hp076) in "Hpc".
    (* +0x076 lw a4,16(a4) : DEVICE_FEATURES *)
    iPoseProof (vdi_076 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x076)) true (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 16 : mword 12) B21 (K - 4)%nat V3
              (mword_of_int 0x10001010) 16 (Z_to_bv 32 0)
              ltac:(rewrite HB21a4; bvc) vg_010 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B22 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 0 : mword 32))]> B21).
    assert (Hp078 : add_vec_int (mword_of_int (VDI + 0x076) : mword 64) 2 = mword_of_int (VDI + 0x078)) by pcs.
    iEval (rewrite Hp078) in "Hpc".
    (* +0x078 lui a3,0xc7ffe *)
    iPoseProof (vdi_078 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x078)) (mword_of_int 13 : mword 5)
              (mword_of_int 819198 : mword 20) (luival (mword_of_int 819198 : mword 20)) B22 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B23 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (mword_of_int 819198 : mword 20))]> B22).
    assert (Hp07c : add_vec_int (mword_of_int (VDI + 0x078) : mword 64) 4 = mword_of_int (VDI + 0x07c)) by pcs.
    iEval (rewrite Hp07c) in "Hpc".
    (* +0x07c addi a3,a3,1887 *)
    iPoseProof (vdi_07c with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x07c)) (mword_of_int 13 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 1887 : mword 12) B23 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B24 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
        (add_vec (B23 !!! Regidx (mword_of_int 13 : mword 5)) (sign_extend' 64 (mword_of_int 1887 : mword 12)))]> B23).
    assert (Hp080 : add_vec_int (mword_of_int (VDI + 0x07c) : mword 64) 4 = mword_of_int (VDI + 0x080)) by pcs.
    iEval (rewrite Hp080) in "Hpc".
    (* +0x080 and a4,a4,a3 : mask off VIRTIO_RING_F_INDIRECT_DESC etc. *)
    iPoseProof (vdi_080 with "Htext") as "Hi".
    iApply (wp_cand_s_sconf γ Φ (mword_of_int (VDI + 0x080)) (mword_of_int 14 : mword 5)
              (mword_of_int 13 : mword 5) B24 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B25 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (and_vec (B24 !!! Regidx (mword_of_int 14 : mword 5)) (B24 !!! Regidx (mword_of_int 13 : mword 5)))]> B24).
    assert (Hp082 : add_vec_int (mword_of_int (VDI + 0x080) : mword 64) 2 = mword_of_int (VDI + 0x082)) by pcs.
    iEval (rewrite Hp082) in "Hpc".
    (* +0x082 lui a3,0x10001 *)
    iPoseProof (vdi_082 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x082)) (mword_of_int 13 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B25 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B26 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B25).
    assert (HB26a3 : B26 !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (HB26a4 : B26 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0) by (peel; bvc).
    assert (Hp086 : add_vec_int (mword_of_int (VDI + 0x082) : mword 64) 4 = mword_of_int (VDI + 0x086)) by pcs.
    iEval (rewrite Hp086) in "Hpc".
    (* +0x086 sw a4,32(a3) : DRIVER_FEATURES <- 0 *)
    iPoseProof (vdi_086 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x086)) true (mword_of_int 14 : mword 5)
              (mword_of_int 13 : mword 5) (mword_of_int 32 : mword 12) B26 (K - 4)%nat V3 V3
              (mword_of_int 0x10001020) 32 (Z_to_bv 32 0 : mword 32)
              ltac:(rewrite HB26a3; bvc) vg_020 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HB26a4; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp088 : add_vec_int (mword_of_int (VDI + 0x086) : mword 64) 2 = mword_of_int (VDI + 0x088)) by pcs.
    iEval (rewrite Hp088) in "Hpc".
    (* +0x088 li a4,11 *)
    iPoseProof (vdi_088 with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x088)) (mword_of_int 14 : mword 5)
              (mword_of_int 11 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 11 : mword 6)))) B26 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B27 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 11 : mword 6))))]> B26).
    assert (HB27a4 : B27 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 11) by (peel; bvc).
    assert (HB27a5 : B27 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp08a : add_vec_int (mword_of_int (VDI + 0x088) : mword 64) 2 = mword_of_int (VDI + 0x08a)) by pcs.
    iEval (rewrite Hp08a) in "Hpc".
    (* +0x08a sw a4,112(a5) : STATUS <- | FEATURES_OK *)
    iPoseProof (vdi_08a with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x08a)) true (mword_of_int 14 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 112 : mword 12) B27 (K - 4)%nat V3 V5
              (mword_of_int 0x10001070) 112 (Z_to_bv 32 11 : mword 32)
              ltac:(rewrite HB27a5; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HB27a4; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp08c : add_vec_int (mword_of_int (VDI + 0x08a) : mword 64) 2 = mword_of_int (VDI + 0x08c)) by pcs.
    iEval (rewrite Hp08c) in "Hpc".
    (* +0x08c addi a5,a5,112 *)
    iPoseProof (vdi_08c with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x08c)) (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 112 : mword 12) B27 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B28 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec (B27 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 112 : mword 12)))]> B27).
    assert (HB28a5 : B28 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001070) by (peel; bvc).
    assert (Hp090 : add_vec_int (mword_of_int (VDI + 0x08c) : mword 64) 4 = mword_of_int (VDI + 0x090)) by pcs.
    iEval (rewrite Hp090) in "Hpc".
    (* +0x090 lw a5,0(a5) : re-read STATUS -- FEATURES_OK is stuck *)
    iPoseProof (vdi_090 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x090)) true (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 12) B28 (K - 4)%nat V5
              (mword_of_int 0x10001070) 112 (Z_to_bv 32 11)
              ltac:(rewrite HB28a5; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B29 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 11 : mword 32))]> B28).
    assert (Hp092 : add_vec_int (mword_of_int (VDI + 0x090) : mword 64) 2 = mword_of_int (VDI + 0x092)) by pcs.
    iEval (rewrite Hp092) in "Hpc".
    (* +0x092 sext.w s2,a5 : remember the status word *)
    iPoseProof (vdi_092 with "Htext") as "Hi".
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (VDI + 0x092)) (mword_of_int 18 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 12) B29 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B30 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B29 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> B29).
    assert (HB30s2 : B30 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; bvc).
    assert (Hp096 : add_vec_int (mword_of_int (VDI + 0x092) : mword 64) 4 = mword_of_int (VDI + 0x096)) by pcs.
    iEval (rewrite Hp096) in "Hpc".
    (* +0x096 andi a5,a5,8 *)
    iPoseProof (vdi_096 with "Htext") as "Hi".
    iApply (wp_candi_s_sconf γ Φ (mword_of_int (VDI + 0x096)) (mword_of_int 15 : mword 5)
              (mword_of_int 8 : mword 6) B30 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B31 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (B30 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> B30).
    assert (HB31a5 : B31 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 8) by (peel; bvc).
    assert (Hp098 : add_vec_int (mword_of_int (VDI + 0x096) : mword 64) 2 = mword_of_int (VDI + 0x098)) by pcs.
    iEval (rewrite Hp098) in "Hpc".
    (* +0x098 beqz a5 -- NOT taken: FEATURES_OK stuck *)
    iPoseProof (vdi_098 with "Htext") as "Hi".
    iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (VDI + 0x098)) (mword_of_int 244 : mword 13)
              (mword_of_int 15 : mword 5) B31 (K - 4)%nat ltac:(nzd)
              ltac:(rewrite HB31a5; vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp09c : add_vec_int (mword_of_int (VDI + 0x098) : mword 64) 4 = mword_of_int (VDI + 0x09c)) by pcs.
    iEval (rewrite Hp09c) in "Hpc".
    (* +0x09c lui a5,0x10001 *)
    iPoseProof (vdi_09c with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x09c)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B31 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B32 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B31).
    assert (HB32a5 : B32 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp0a0 : add_vec_int (mword_of_int (VDI + 0x09c) : mword 64) 4 = mword_of_int (VDI + 0x0a0)) by pcs.
    iEval (rewrite Hp0a0) in "Hpc".
    (* +0x0a0 sw zero,48(a5) : QUEUE_SEL <- 0 *)
    iDestruct (sie_cap_gpr_x0 γ B32 (K - 4)%nat (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx32 Hcg]".
    iPoseProof (vdi_0a0 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x0a0)) false (mword_of_int 0 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 48 : mword 12) B32 (K - 4)%nat V5 V5
              (mword_of_int 0x10001030) 48 (Z_to_bv 32 0 : mword 32)
              ltac:(rewrite HB32a5; bvc) vg_030 ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hx32; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp0a4 : add_vec_int (mword_of_int (VDI + 0x0a0) : mword 64) 4 = mword_of_int (VDI + 0x0a4)) by pcs.
    iEval (rewrite Hp0a4) in "Hpc".
    (* +0x0a4 lw a5,68(a5) : QUEUE_READY -- clear after the reset *)
    iPoseProof (vdi_0a4 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x0a4)) true (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 68 : mword 12) B32 (K - 4)%nat V5
              (mword_of_int 0x10001044) 68 (Z_to_bv 32 0)
              ltac:(rewrite HB32a5; bvc) vg_044 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B33 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 0 : mword 32))]> B32).
    assert (Hp0a6 : add_vec_int (mword_of_int (VDI + 0x0a4) : mword 64) 2 = mword_of_int (VDI + 0x0a6)) by pcs.
    iEval (rewrite Hp0a6) in "Hpc".
    (* +0x0a6 sext.w a5,a5 *)
    iPoseProof (vdi_0a6 with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x0a6)) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 6) B33 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B34 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B33 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B33).
    assert (HB34a5 : B34 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0) by (peel; bvc).
    assert (Hp0a8 : add_vec_int (mword_of_int (VDI + 0x0a6) : mword 64) 2 = mword_of_int (VDI + 0x0a8)) by pcs.
    iEval (rewrite Hp0a8) in "Hpc".
    (* +0x0a8 bnez a5 -- NOT taken *)
    iPoseProof (vdi_0a8 with "Htext") as "Hi".
    iApply (wp_bnez_x0_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0a8)) (mword_of_int 240 : mword 13)
              (mword_of_int 15 : mword 5) B34 (K - 4)%nat
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HB34a5; vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0ac : add_vec_int (mword_of_int (VDI + 0x0a8) : mword 64) 4 = mword_of_int (VDI + 0x0ac)) by pcs.
    iEval (rewrite Hp0ac) in "Hpc".
    (* +0x0ac lui a5,0x10001 *)
    iPoseProof (vdi_0ac with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x0ac)) (mword_of_int 15 : mword 5)
              (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20)) B34 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B35 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> B34).
    assert (HB35a5 : B35 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (Hp0b0 : add_vec_int (mword_of_int (VDI + 0x0ac) : mword 64) 4 = mword_of_int (VDI + 0x0b0)) by pcs.
    iEval (rewrite Hp0b0) in "Hpc".
    (* +0x0b0 lw a5,52(a5) : QUEUE_NUM_MAX = 8 *)
    iPoseProof (vdi_0b0 with "Htext") as "Hi".
    iApply (wp_vdi_lw γ Φ (mword_of_int (VDI + 0x0b0)) true (mword_of_int 15 : mword 5)
              (mword_of_int 15 : mword 5) (mword_of_int 52 : mword 12) B35 (K - 4)%nat V5
              (mword_of_int 0x10001034) 52 (Z_to_bv 32 8)
              ltac:(rewrite HB35a5; bvc) vg_034 ltac:(vm_compute; reflexivity)
              ltac:(nzd) ltac:(nzd) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    pose (B36 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (Z_to_bv 32 8 : mword 32))]> B35).
    assert (Hp0b2 : add_vec_int (mword_of_int (VDI + 0x0b0) : mword 64) 2 = mword_of_int (VDI + 0x0b2)) by pcs.
    iEval (rewrite Hp0b2) in "Hpc".
    (* +0x0b2 sext.w a5,a5 *)
    iPoseProof (vdi_0b2 with "Htext") as "Hi".
    iApply (wp_caddiw_s_sconf γ Φ (mword_of_int (VDI + 0x0b2)) (mword_of_int 15 : mword 5)
              (mword_of_int 0 : mword 6) B36 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B37 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (B36 !!! Regidx (mword_of_int 15 : mword 5))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> B36).
    assert (HB37a5 : B37 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 8) by (peel; bvc).
    assert (Hp0b4 : add_vec_int (mword_of_int (VDI + 0x0b2) : mword 64) 2 = mword_of_int (VDI + 0x0b4)) by pcs.
    iEval (rewrite Hp0b4) in "Hpc".
    (* +0x0b4 beqz a5 -- NOT taken (max = 8) *)
    iPoseProof (vdi_0b4 with "Htext") as "Hi".
    iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0b4)) (mword_of_int 240 : mword 13)
              (mword_of_int 15 : mword 5) B37 (K - 4)%nat ltac:(nzd)
              ltac:(rewrite HB37a5; vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0b8 : add_vec_int (mword_of_int (VDI + 0x0b4) : mword 64) 4 = mword_of_int (VDI + 0x0b8)) by pcs.
    iEval (rewrite Hp0b8) in "Hpc".
    (* +0x0b8 li a4,7 *)
    iPoseProof (vdi_0b8 with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x0b8)) (mword_of_int 14 : mword 5)
              (mword_of_int 7 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6)))) B37 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B38 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6))))]> B37).
    assert (HB38a4 : B38 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 7) by (peel; bvc).
    assert (HB38a5 : B38 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 8)
      by (rewrite /B38 upd_ne; [exact HB37a5 | reg_neq]).
    assert (Hp0ba : add_vec_int (mword_of_int (VDI + 0x0b8) : mword 64) 2 = mword_of_int (VDI + 0x0ba)) by pcs.
    iEval (rewrite Hp0ba) in "Hpc".
    (* +0x0ba bgeu a4,a5 -- NOT taken (7 <u 8) *)
    iPoseProof (vdi_0ba with "Htext") as "Hi".
    iApply (wp_bgeu_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0ba)) (mword_of_int 246 : mword 13)
              (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) B38 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(rewrite HB38a4 HB38a5; vm_compute; reflexivity)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0be : add_vec_int (mword_of_int (VDI + 0x0ba) : mword 64) 4 = mword_of_int (VDI + 0x0be)) by pcs.
    iEval (rewrite Hp0be) in "Hpc".
    (* ===== disk.desc/avail/used = kalloc() x3 (0x0be..0x0d8) ===== *)
    iDestruct "Henv" as (γk) "(#Hklock & Havl & #Hpanic)".
    (* +0x0be jal kalloc *)
    iPoseProof (vdi_0be with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x0be)) (mword_of_int 1 : mword 5)
              (mword_of_int 2077928 : mword 21) B38 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (B39 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (VDI + 0x0be) : mword 64) 4)]> B38).
    assert (Htgk1 : add_vec (mword_of_int (VDI + 0x0be) : mword 64)
                      (sign_extend' 64 (mword_of_int 2077928 : mword 21))
                    = mword_of_int KernelSyms.kalloc) by bvc.
    iEval (rewrite Htgk1) in "Hpc".
    assert (HB39sp : B39 !!! Regidx csp_rs1 = spr) by (peel; exact Hmilsp).
    assert (HB39tp : B39 !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
      by (peel; try rewrite Hmiltp; exact Hcid).
    assert (HB39s2 : B39 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11)
      by (peel; exact HB30s2).
    iApply (AK.wp_kalloc_sconf γ Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              B39 (Some nb) 0%nat eb pp C (K - 4)%nat Hc14 HB39tp
              ltac:(reflexivity) ltac:(vm_compute; reflexivity)
              with "Hcg Hcpu Htext Hpc Hklock Havl Hpanic [-]").
    iIntros (mk1) "Hcg Hcpu Hpc %Hk1cs Hkpost".
    assert (Hr0c2 : ret_pc (B39 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x0c2)).
    { rewrite /B39 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr0c2) in "Hpc".
    assert (Hcnt1 : Some nb = Some (S (nb - 1))) by (f_equal; lia).
    iEval (rewrite Hcnt1) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpdv & Hpdpg & Havl)".
    set (pd := (mk1 !!! Regidx (mword_of_int 10 : mword 5) : mword 64)).
    assert (Hk1sp : mk1 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hk1cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB39sp. }
    assert (Hk1tp : mk1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hk1cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HB39tp. }
    assert (Hk1s2 : mk1 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hk1cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HB39s2. }
    (* +0x0c2 auipc s1,0x1e *)
    iPoseProof (vdi_0c2 with "Htext") as "Hi".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VDI + 0x0c2)) (mword_of_int 9 : mword 5)
              (mword_of_int 30 : mword 20) mk1 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (C1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (VDI + 0x0c2) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> mk1).
    assert (Hp0c6 : add_vec_int (mword_of_int (VDI + 0x0c2) : mword 64) 4 = mword_of_int (VDI + 0x0c6)) by pcs.
    iEval (rewrite Hp0c6) in "Hpc".
    (* +0x0c6 addi s1,s1,-562 : s1 := &disk *)
    iPoseProof (vdi_0c6 with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x0c6)) (mword_of_int 9 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 3534 : mword 12) C1 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (C2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (C1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 3534 : mword 12)))]> C1).
    assert (HC2s1 : C2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; bvc).
    assert (Hadesc : add_vec (C2 !!! Regidx (mword_of_int 9 : mword 5))
                       (sign_extend' 64 (mword_of_int 0 : mword 12)) = disk_desc)
      by (rewrite HC2s1; bvc).
    assert (HC2a0 : C2 !!! Regidx (mword_of_int 10 : mword 5) = pd) by (peel; reflexivity).
    assert (Hp0ca : add_vec_int (mword_of_int (VDI + 0x0c6) : mword 64) 4 = mword_of_int (VDI + 0x0ca)) by pcs.
    iEval (rewrite Hp0ca) in "Hpc".
    (* +0x0ca sd a0,0(s1) : disk.desc = kalloc() *)
    iPoseProof (vdi_0ca with "Htext") as "Hi".
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (VDI + 0x0ca)) (mword_of_int 10 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12) C2 (K - 4)%nat pd0
              with "Hcg Hpc Hi [Hdesc] [-]").
    { iEval (rewrite Hadesc). iExact "Hdesc". }
    iIntros "Hcg Hpc Hdesc". iClear "Hi".
    iEval (rewrite Hadesc HC2a0) in "Hdesc".
    assert (Hp0cc : add_vec_int (mword_of_int (VDI + 0x0ca) : mword 64) 2 = mword_of_int (VDI + 0x0cc)) by pcs.
    iEval (rewrite Hp0cc) in "Hpc".
    (* +0x0cc jal kalloc *)
    iPoseProof (vdi_0cc with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x0cc)) (mword_of_int 1 : mword 5)
              (mword_of_int 2077914 : mword 21) C2 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (C3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (VDI + 0x0cc) : mword 64) 4)]> C2).
    assert (Htgk2 : add_vec (mword_of_int (VDI + 0x0cc) : mword 64)
                      (sign_extend' 64 (mword_of_int 2077914 : mword 21))
                    = mword_of_int KernelSyms.kalloc) by bvc.
    iEval (rewrite Htgk2) in "Hpc".
    assert (HC3sp : C3 !!! Regidx csp_rs1 = spr) by (peel; exact Hk1sp).
    assert (HC3tp : C3 !!! Regidx (mword_of_int 4 : mword 5) = cid_word) by (peel; exact Hk1tp).
    assert (HC3s1 : C3 !!! Regidx (mword_of_int 9 : mword 5) = disk_base)
      by (rewrite /C3 upd_ne; [exact HC2s1 | reg_neq]).
    assert (HC3s2 : C3 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11)
      by (peel; exact Hk1s2).
    iApply (AK.wp_kalloc_sconf γ Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              C3 (Some (nb - 1)%nat) 0%nat eb pp C (K - 4)%nat Hc14 HC3tp
              ltac:(reflexivity) ltac:(vm_compute; reflexivity)
              with "Hcg Hcpu Htext Hpc Hklock Havl Hpanic [-]").
    iIntros (mk2) "Hcg Hcpu Hpc %Hk2cs Hkpost".
    assert (Hr0d0 : ret_pc (C3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x0d0)).
    { rewrite /C3 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr0d0) in "Hpc".
    assert (Hcnt2 : Some (nb - 1)%nat = Some (S (nb - 2))) by (f_equal; lia).
    iEval (rewrite Hcnt2) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpavv & Hpavpg & Havl)".
    set (pav := (mk2 !!! Regidx (mword_of_int 10 : mword 5) : mword 64)).
    assert (Hk2sp : mk2 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hk2cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HC3sp. }
    assert (Hk2tp : mk2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hk2cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HC3tp. }
    assert (Hk2s1 : mk2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base).
    { rewrite (callee_saved_lookup Hk2cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HC3s1. }
    assert (Hk2s2 : mk2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hk2cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HC3s2. }
    assert (Haavail : add_vec (mk2 !!! Regidx (mword_of_int 9 : mword 5))
                        (sign_extend' 64 (mword_of_int 8 : mword 12)) = disk_avail)
      by (rewrite Hk2s1; bvc).
    (* +0x0d0 sd a0,8(s1) : disk.avail = kalloc() *)
    iPoseProof (vdi_0d0 with "Htext") as "Hi".
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (VDI + 0x0d0)) (mword_of_int 10 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 8 : mword 12) mk2 (K - 4)%nat pav0
              with "Hcg Hpc Hi [Havail] [-]").
    { iEval (rewrite Haavail). iExact "Havail". }
    iIntros "Hcg Hpc Havail". iClear "Hi".
    iEval (rewrite Haavail) in "Havail".
    assert (Hp0d2 : add_vec_int (mword_of_int (VDI + 0x0d0) : mword 64) 2 = mword_of_int (VDI + 0x0d2)) by pcs.
    iEval (rewrite Hp0d2) in "Hpc".
    (* +0x0d2 jal kalloc *)
    iPoseProof (vdi_0d2 with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x0d2)) (mword_of_int 1 : mword 5)
              (mword_of_int 2077908 : mword 21) mk2 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (D2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (VDI + 0x0d2) : mword 64) 4)]> mk2).
    assert (Htgk3 : add_vec (mword_of_int (VDI + 0x0d2) : mword 64)
                      (sign_extend' 64 (mword_of_int 2077908 : mword 21))
                    = mword_of_int KernelSyms.kalloc) by bvc.
    iEval (rewrite Htgk3) in "Hpc".
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spr) by (peel; exact Hk2sp).
    assert (HD2tp : D2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word) by (peel; exact Hk2tp).
    assert (HD2s1 : D2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hk2s1).
    assert (HD2s2 : D2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; exact Hk2s2).
    iApply (AK.wp_kalloc_sconf γ Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              D2 (Some (nb - 2)%nat) 0%nat eb pp C (K - 4)%nat Hc14 HD2tp
              ltac:(reflexivity) ltac:(vm_compute; reflexivity)
              with "Hcg Hcpu Htext Hpc Hklock Havl Hpanic [-]").
    iIntros (mk3) "Hcg Hcpu Hpc %Hk3cs Hkpost".
    assert (Hr0d6 : ret_pc (D2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x0d6)).
    { rewrite /D2 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr0d6) in "Hpc".
    assert (Hcnt3 : Some (nb - 2)%nat = Some (S (nb - 3))) by (f_equal; lia).
    iEval (rewrite Hcnt3) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpuv & Hpupg & Havl)".
    set (pu := (mk3 !!! Regidx (mword_of_int 10 : mword 5) : mword 64)).
    assert (Hk3sp : mk3 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hk3cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HD2sp. }
    assert (Hk3tp : mk3 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hk3cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HD2tp. }
    assert (Hk3s1 : mk3 !!! Regidx (mword_of_int 9 : mword 5) = disk_base).
    { rewrite (callee_saved_lookup Hk3cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HD2s1. }
    assert (Hk3s2 : mk3 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hk3cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)).
      exact HD2s2. }
    (* +0x0d6 mv a5,a0 *)
    iPoseProof (vdi_0d6 with "Htext") as "Hi".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (VDI + 0x0d6)) (mword_of_int 15 : mword 5)
              (mword_of_int 10 : mword 5) mk3 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (add_vec zero_reg (mk3 !!! Regidx (mword_of_int 10 : mword 5)))]> mk3).
    assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hk3s1).
    assert (HE1a0 : E1 !!! Regidx (mword_of_int 10 : mword 5) = pu) by (peel; reflexivity).
    assert (Haused : add_vec (E1 !!! Regidx (mword_of_int 9 : mword 5))
                       (sign_extend' 64 (mword_of_int 16 : mword 12)) = disk_used)
      by (rewrite HE1s1; bvc).
    assert (Hp0d8 : add_vec_int (mword_of_int (VDI + 0x0d6) : mword 64) 2 = mword_of_int (VDI + 0x0d8)) by pcs.
    iEval (rewrite Hp0d8) in "Hpc".
    (* +0x0d8 sd a0,16(s1) : disk.used = kalloc() *)
    iPoseProof (vdi_0d8 with "Htext") as "Hi".
    iApply (wp_csd_s_sconf γ Φ (mword_of_int (VDI + 0x0d8)) (mword_of_int 10 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12) E1 (K - 4)%nat pu0
              with "Hcg Hpc Hi [Hused] [-]").
    { iEval (rewrite Haused). iExact "Hused". }
    iIntros "Hcg Hpc Hused". iClear "Hi".
    iEval (rewrite Haused HE1a0) in "Hused".
    assert (Hp0da : add_vec_int (mword_of_int (VDI + 0x0d8) : mword 64) 2 = mword_of_int (VDI + 0x0da)) by pcs.
    iEval (rewrite Hp0da) in "Hpc".
    (* ===== the three null tests, all refuted by [page_valid] ===== *)
    assert (Hnz : (zero_reg : mword 64) = nullp) by bvc.
    assert (Hadesc1 : add_vec (E1 !!! Regidx (mword_of_int 9 : mword 5))
                        (sign_extend' 64 (mword_of_int 0 : mword 12)) = disk_desc)
      by (rewrite HE1s1; bvc).
    (* +0x0da ld a0,0(s1) *)
    iPoseProof (vdi_0da with "Htext") as "Hi".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VDI + 0x0da)) (mword_of_int 10 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12) E1 (K - 4)%nat pd
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Hdesc] [-]").
    { iEval (rewrite Hadesc1). iExact "Hdesc". }
    iIntros "Hcg Hpc Hdesc". iClear "Hi".
    iEval (rewrite Hadesc1) in "Hdesc".
    pose (E2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg pd]> E1).
    assert (HE2a0 : E2 !!! Regidx (mword_of_int 10 : mword 5) = pd) by (peel; reflexivity).
    assert (Hp0dc : add_vec_int (mword_of_int (VDI + 0x0da) : mword 64) 2 = mword_of_int (VDI + 0x0dc)) by pcs.
    iEval (rewrite Hp0dc) in "Hpc".
    (* +0x0dc beqz a0 -- NOT taken *)
    iPoseProof (vdi_0dc with "Htext") as "Hi".
    iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0dc)) (mword_of_int 224 : mword 13)
              (mword_of_int 10 : mword 5) E2 (K - 4)%nat ltac:(nzd)
              ltac:(rewrite HE2a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpdv))
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0e0 : add_vec_int (mword_of_int (VDI + 0x0dc) : mword 64) 4 = mword_of_int (VDI + 0x0e0)) by pcs.
    iEval (rewrite Hp0e0) in "Hpc".
    (* +0x0e0 auipc a4,0x1e *)
    iPoseProof (vdi_0e0 with "Htext") as "Hi".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VDI + 0x0e0)) (mword_of_int 14 : mword 5)
              (mword_of_int 30 : mword 20) E2 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (E3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (VDI + 0x0e0) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> E2).
    assert (Havail2 : add_vec (E3 !!! Regidx (mword_of_int 14 : mword 5))
                        (sign_extend' 64 (mword_of_int 3512 : mword 12)) = disk_avail).
    { assert (HE3a4 : E3 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x80023668)
        by (peel; bvc). rewrite HE3a4. bvc. }
    assert (Hp0e4 : add_vec_int (mword_of_int (VDI + 0x0e0) : mword 64) 4 = mword_of_int (VDI + 0x0e4)) by pcs.
    iEval (rewrite Hp0e4) in "Hpc".
    (* +0x0e4 ld a4,-584(a4) : disk.avail *)
    iPoseProof (vdi_0e4 with "Htext") as "Hi".
    iApply (wp_ld_s_sconf γ Φ (mword_of_int (VDI + 0x0e4)) (mword_of_int 14 : mword 5)
              (mword_of_int 14 : mword 5) (mword_of_int 3512 : mword 12) E3 (K - 4)%nat pav
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Havail] [-]").
    { iEval (rewrite Havail2). iExact "Havail". }
    iIntros "Hcg Hpc Havail". iClear "Hi".
    iEval (rewrite Havail2) in "Havail".
    pose (E4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg pav]> E3).
    assert (HE4a4 : E4 !!! Regidx (mword_of_int 14 : mword 5) = pav) by (peel; reflexivity).
    assert (HE4a5 : E4 !!! Regidx (mword_of_int 15 : mword 5) = pu)
      by (peel; apply vdi_addv_zero_l).
    assert (Hp0e8 : add_vec_int (mword_of_int (VDI + 0x0e4) : mword 64) 4 = mword_of_int (VDI + 0x0e8)) by pcs.
    iEval (rewrite Hp0e8) in "Hpc".
    (* +0x0e8 beqz a4 -- NOT taken *)
    iPoseProof (vdi_0e8 with "Htext") as "Hi".
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0e8)) (mword_of_int 106 : mword 8)
              (Cregidx (mword_of_int 6)) (mword_of_int 14 : mword 5) E4 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(nzd)
              ltac:(rewrite HE4a4; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpavv))
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0ea : add_vec_int (mword_of_int (VDI + 0x0e8) : mword 64) 2 = mword_of_int (VDI + 0x0ea)) by pcs.
    iEval (rewrite Hp0ea) in "Hpc".
    (* +0x0ea beqz a5 -- NOT taken *)
    iPoseProof (vdi_0ea with "Htext") as "Hi".
    iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (VDI + 0x0ea)) (mword_of_int 105 : mword 8)
              (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) E4 (K - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(nzd)
              ltac:(rewrite HE4a5; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpuv))
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    assert (Hp0ec : add_vec_int (mword_of_int (VDI + 0x0ea) : mword 64) 2 = mword_of_int (VDI + 0x0ec)) by pcs.
    iEval (rewrite Hp0ec) in "Hpc".
    (* ===== memset(page,0,4096) x3 (0x0ec..0x10c) ===== *)
    iPoseProof (vdi_0ec with "Htext") as "Hi".
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (VDI + 0x0ec)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6))
              (luival (sign_extend' 20 (mword_of_int 1 : mword 6))) E4 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (E5 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> E4).
    assert (Hp0ee : add_vec_int (mword_of_int (VDI + 0x0ec) : mword 64) 2 = mword_of_int (VDI + 0x0ee)) by pcs.
    iEval (rewrite Hp0ee) in "Hpc".
    iPoseProof (vdi_0ee with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x0ee)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) E5 (K - 4)%nat ltac:(nzd) ltac:(nzd) ltac:(bvc)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (E6 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> E5).
    assert (Hp0f0 : add_vec_int (mword_of_int (VDI + 0x0ee) : mword 64) 2 = mword_of_int (VDI + 0x0f0)) by pcs.
    iEval (rewrite Hp0f0) in "Hpc".
    iPoseProof (vdi_0f0 with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x0f0)) (mword_of_int 1 : mword 5) (mword_of_int 2078288 : mword 21) E6 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (E7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (VDI + 0x0f0) : mword 64) 4)]> E6).
    assert (Htgm1 : add_vec (mword_of_int (VDI + 0x0f0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2078288 : mword 21))
                    = mword_of_int KernelSyms.memset) by bvc.
    iEval (rewrite Htgm1) in "Hpc".
    assert (HE7a0 : E7 !!! Regidx (mword_of_int 10 : mword 5) = pd) by (peel; reflexivity).
    assert (HE7sp : E7 !!! Regidx csp_rs1 = spr) by (peel; exact Hk3sp).
    assert (HE7tp : E7 !!! Regidx (mword_of_int 4 : mword 5) = cid_word) by (peel; exact Hk3tp).
    assert (HE7s1 : E7 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hk3s1).
    assert (HE7s2 : E7 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; exact Hk3s2).
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (mword_of_int 0 : mword 64)
                     (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = byte_zero) by bvc.
    iEval (rewrite /page_own /byte_any) in "Hpdpg".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add pd j) ↦ₘ b)%I) with "Hpdpg") as (opd) "Hbufd".
    iApply (MS.wp_memset_sconf γ Φ E7 (K - 4)%nat 4096%nat (mword_of_int 0 : mword 64) opd
              Hc2 ltac:(vm_compute; reflexivity) ltac:(peel; bvc) ltac:(peel; bvc)
              with "Hcg Htext Hpc [Hbufd] [-]").
    { iApply (big_sepL_impl with "Hbufd"). iIntros "!>" (k j _) "H". rewrite HE7a0. iExact "H". }
    iIntros (ms1) "Hcg Hpc Hbpd %Hms1cs".
    iEval (rewrite Hcb HE7a0) in "Hbpd".
    assert (Hr0f4 : ret_pc (E7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x0f4)).
    { rewrite /E7 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr0f4) in "Hpc".
    assert (Hms1sp : ms1 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hms1cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HE7sp. }
    assert (Hms1tp : ms1 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hms1cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact HE7tp. }
    assert (Hms1s1 : ms1 !!! Regidx (mword_of_int 9 : mword 5) = disk_base).
    { rewrite (callee_saved_lookup Hms1cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HE7s1. }
    assert (Hms1s2 : ms1 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hms1cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HE7s2. }
    iPoseProof (vdi_0f4 with "Htext") as "Hi".
    iApply (wp_auipc_s_sconf γ Φ (mword_of_int (VDI + 0x0f4)) (mword_of_int 9 : mword 5) (mword_of_int 30 : mword 20) ms1 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (F1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (VDI + 0x0f4) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> ms1).
    assert (Hp0f8 : add_vec_int (mword_of_int (VDI + 0x0f4) : mword 64) 4 = mword_of_int (VDI + 0x0f8)) by pcs.
    iEval (rewrite Hp0f8) in "Hpc".
    iPoseProof (vdi_0f8 with "Htext") as "Hi".
    iApply (wp_addi4_s_sconf γ Φ (mword_of_int (VDI + 0x0f8)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 3484 : mword 12) F1 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (F2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (F1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 3484 : mword 12)))]> F1).
    assert (HF2s1 : F2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; bvc).
    assert (Hp0fc : add_vec_int (mword_of_int (VDI + 0x0f8) : mword 64) 4 = mword_of_int (VDI + 0x0fc)) by pcs.
    iEval (rewrite Hp0fc) in "Hpc".
    iPoseProof (vdi_0fc with "Htext") as "Hi".
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (VDI + 0x0fc)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6))
              (luival (sign_extend' 20 (mword_of_int 1 : mword 6))) F2 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (F3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> F2).
    assert (Hp0fe : add_vec_int (mword_of_int (VDI + 0x0fc) : mword 64) 2 = mword_of_int (VDI + 0x0fe)) by pcs.
    iEval (rewrite Hp0fe) in "Hpc".
    iPoseProof (vdi_0fe with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x0fe)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) F3 (K - 4)%nat ltac:(nzd) ltac:(nzd) ltac:(bvc)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (F4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> F3).
    assert (Hp100 : add_vec_int (mword_of_int (VDI + 0x0fe) : mword 64) 2 = mword_of_int (VDI + 0x100)) by pcs.
    iEval (rewrite Hp100) in "Hpc".
    assert (HF4s1 : F4 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HF2s1).
    assert (Haavail2 : add_vec (F4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)) = disk_avail)
      by (rewrite HF4s1; bvc).
    iPoseProof (vdi_100 with "Htext") as "Hi".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VDI + 0x100)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 8 : mword 12) F4 (K - 4)%nat pav
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Havail] [-]").
    { iEval (rewrite Haavail2). iExact "Havail". }
    iIntros "Hcg Hpc Havail". iClear "Hi".
    iEval (rewrite Haavail2) in "Havail".
    pose (F5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg pav]> F4).
    assert (Hp102 : add_vec_int (mword_of_int (VDI + 0x100) : mword 64) 2 = mword_of_int (VDI + 0x102)) by pcs.
    iEval (rewrite Hp102) in "Hpc".
    iPoseProof (vdi_102 with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x102)) (mword_of_int 1 : mword 5) (mword_of_int 2078270 : mword 21) F5 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (F6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (VDI + 0x102) : mword 64) 4)]> F5).
    assert (Htgm2 : add_vec (mword_of_int (VDI + 0x102) : mword 64)
                      (sign_extend' 64 (mword_of_int 2078270 : mword 21))
                    = mword_of_int KernelSyms.memset) by bvc.
    iEval (rewrite Htgm2) in "Hpc".
    assert (HF6a0 : F6 !!! Regidx (mword_of_int 10 : mword 5) = pav) by (peel; reflexivity).
    assert (HF6sp : F6 !!! Regidx csp_rs1 = spr) by (peel; exact Hms1sp).
    assert (HF6tp : F6 !!! Regidx (mword_of_int 4 : mword 5) = cid_word) by (peel; exact Hms1tp).
    assert (HF6s1 : F6 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HF2s1).
    assert (HF6s2 : F6 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; exact Hms1s2).
    iEval (rewrite /page_own /byte_any) in "Hpavpg".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add pav j) ↦ₘ b)%I) with "Hpavpg") as (opav) "Hbufa".
    iApply (MS.wp_memset_sconf γ Φ F6 (K - 4)%nat 4096%nat (mword_of_int 0 : mword 64) opav
              Hc2 ltac:(vm_compute; reflexivity) ltac:(peel; bvc) ltac:(peel; bvc)
              with "Hcg Htext Hpc [Hbufa] [-]").
    { iApply (big_sepL_impl with "Hbufa"). iIntros "!>" (k j _) "H". rewrite HF6a0. iExact "H". }
    iIntros (ms2) "Hcg Hpc Hbpav %Hms2cs".
    iEval (rewrite Hcb HF6a0) in "Hbpav".
    assert (Hr106 : ret_pc (F6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x106)).
    { rewrite /F6 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr106) in "Hpc".
    assert (Hms2sp : ms2 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hms2cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF6sp. }
    assert (Hms2tp : ms2 !!! Regidx (mword_of_int 4 : mword 5) = cid_word).
    { rewrite (callee_saved_lookup Hms2cs (mword_of_int 4 : mword 5) ltac:(vm_compute; reflexivity)). exact HF6tp. }
    assert (Hms2s1 : ms2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base).
    { rewrite (callee_saved_lookup Hms2cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HF6s1. }
    assert (Hms2s2 : ms2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hms2cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HF6s2. }
    iPoseProof (vdi_106 with "Htext") as "Hi".
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (VDI + 0x106)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6))
              (luival (sign_extend' 20 (mword_of_int 1 : mword 6))) ms2 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) eq_refl with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (G1 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> ms2).
    assert (Hp108 : add_vec_int (mword_of_int (VDI + 0x106) : mword 64) 2 = mword_of_int (VDI + 0x108)) by pcs.
    iEval (rewrite Hp108) in "Hpc".
    iPoseProof (vdi_108 with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x108)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) G1 (K - 4)%nat ltac:(nzd) ltac:(nzd) ltac:(bvc)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (G2 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> G1).
    assert (Hp10a : add_vec_int (mword_of_int (VDI + 0x108) : mword 64) 2 = mword_of_int (VDI + 0x10a)) by pcs.
    iEval (rewrite Hp10a) in "Hpc".
    assert (HG2s1 : G2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hms2s1).
    assert (Haused2 : add_vec (G2 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = disk_used)
      by (rewrite HG2s1; bvc).
    iPoseProof (vdi_10a with "Htext") as "Hi".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VDI + 0x10a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12) G2 (K - 4)%nat pu
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Hused] [-]").
    { iEval (rewrite Haused2). iExact "Hused". }
    iIntros "Hcg Hpc Hused". iClear "Hi".
    iEval (rewrite Haused2) in "Hused".
    pose (G3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg pu]> G2).
    assert (Hp10c : add_vec_int (mword_of_int (VDI + 0x10a) : mword 64) 2 = mword_of_int (VDI + 0x10c)) by pcs.
    iEval (rewrite Hp10c) in "Hpc".
    iPoseProof (vdi_10c with "Htext") as "Hi".
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (VDI + 0x10c)) (mword_of_int 1 : mword 5) (mword_of_int 2078260 : mword 21) G3 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (G4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (VDI + 0x10c) : mword 64) 4)]> G3).
    assert (Htgm3 : add_vec (mword_of_int (VDI + 0x10c) : mword 64)
                      (sign_extend' 64 (mword_of_int 2078260 : mword 21))
                    = mword_of_int KernelSyms.memset) by bvc.
    iEval (rewrite Htgm3) in "Hpc".
    assert (HG4a0 : G4 !!! Regidx (mword_of_int 10 : mword 5) = pu) by (peel; reflexivity).
    assert (HG4sp : G4 !!! Regidx csp_rs1 = spr) by (peel; exact Hms2sp).
    assert (HG4s1 : G4 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hms2s1).
    assert (HG4s2 : G4 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; exact Hms2s2).
    iEval (rewrite /page_own /byte_any) in "Hpupg".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add pu j) ↦ₘ b)%I) with "Hpupg") as (opu) "Hbufu".
    iApply (MS.wp_memset_sconf γ Φ G4 (K - 4)%nat 4096%nat (mword_of_int 0 : mword 64) opu
              Hc2 ltac:(vm_compute; reflexivity) ltac:(peel; bvc) ltac:(peel; bvc)
              with "Hcg Htext Hpc [Hbufu] [-]").
    { iApply (big_sepL_impl with "Hbufu"). iIntros "!>" (k j _) "H". rewrite HG4a0. iExact "H". }
    iIntros (ms3) "Hcg Hpc Hbpu %Hms3cs".
    iEval (rewrite Hcb HG4a0) in "Hbpu".
    assert (Hr110 : ret_pc (G4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (VDI + 0x110)).
    { rewrite /G4 upd_eq. unfold ret_pc. bvc. }
    iEval (rewrite Hr110) in "Hpc".
    assert (Hms3sp : ms3 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hms3cs csp_rs1 ltac:(vm_compute; reflexivity)). exact HG4sp. }
    assert (Hms3s1 : ms3 !!! Regidx (mword_of_int 9 : mword 5) = disk_base).
    { rewrite (callee_saved_lookup Hms3cs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact HG4s1. }
    assert (Hms3s2 : ms3 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11).
    { rewrite (callee_saved_lookup Hms3cs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact HG4s2. }
    (* ===== program the queue (0x110..0x170) ===== *)
    assert (Hpdlt : (bv_unsigned pd < 2 ^ 32)%Z).
    { destruct Hpdv as [_ [_ Hhi]]. rewrite uint_unsigned in Hhi.
      unfold kmem_hi in Hhi. exact (vdi_lt32_of _ Hhi). }
    assert (Hpavlt : (bv_unsigned pav < 2 ^ 32)%Z).
    { destruct Hpavv as [_ [_ Hhi]]. rewrite uint_unsigned in Hhi.
      unfold kmem_hi in Hhi. exact (vdi_lt32_of _ Hhi). }
    assert (Hpult : (bv_unsigned pu < 2 ^ 32)%Z).
    { destruct Hpuv as [_ [_ Hhi]]. rewrite uint_unsigned in Hhi.
      unfold kmem_hi in Hhi. exact (vdi_lt32_of _ Hhi). }
    pose (V7 := vdi_v 11 0 0 8 false zero64 zero64 zero64 dk).
    pose (V8 := vdi_v 11 0 0 8 false (set_lo zero64 (word_lo pd)) zero64 zero64 dk).
    pose (V9 := vdi_v 11 0 0 8 false (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd)) zero64 zero64 dk).
    pose (V10 := vdi_v 11 0 0 8 false (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_lo zero64 (lo32 pav)) zero64 dk).
    pose (V11 := vdi_v 11 0 0 8 false (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0)) zero64 dk).
    pose (V12 := vdi_v 11 0 0 8 false (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0)) (set_lo zero64 (lo32 pu)) dk).
    pose (V13 := vdi_v 11 0 0 8 false (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0))
                       (set_hi (set_lo zero64 (lo32 pu)) (Z_to_bv 32 0)) dk).
    pose (V14 := vdi_v 11 0 0 8 true (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0))
                       (set_hi (set_lo zero64 (lo32 pu)) (Z_to_bv 32 0)) dk).
    pose (V15 := vdi_v 15 0 0 8 true (set_hi (set_lo zero64 (word_lo pd)) (word_hi pd))
                       (set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0))
                       (set_hi (set_lo zero64 (lo32 pu)) (Z_to_bv 32 0)) dk).
    iPoseProof (vdi_110 with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x110)) (mword_of_int 15 : mword 5) (mword_of_int 65537 : mword 20)
              (luival (mword_of_int 65537 : mword 20)) ms3 (K - 4)%nat ltac:(nzd) ltac:(nzd) eq_refl
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> ms3).
    assert (Hp114 : add_vec_int (mword_of_int (VDI + 0x110) : mword 64) 4 = mword_of_int (VDI + 0x114)) by pcs.
    iEval (rewrite Hp114) in "Hpc".
    iPoseProof (vdi_114 with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x114)) (mword_of_int 14 : mword 5) (mword_of_int 8 : mword 6)
              (mword_of_int 8 : mword 64) H1 (K - 4)%nat ltac:(nzd) ltac:(nzd) ltac:(bvc)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (mword_of_int 8 : mword 64)]> H1).
    assert (HH2a5 : H2 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (HH2a4 : H2 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 8) by (peel; reflexivity).
    assert (HH2s1 : H2 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact Hms3s1).
    assert (Hp116 : add_vec_int (mword_of_int (VDI + 0x114) : mword 64) 2 = mword_of_int (VDI + 0x116)) by pcs.
    iEval (rewrite Hp116) in "Hpc".
    iPoseProof (vdi_116 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x116)) true (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 56 : mword 12)
              H2 (K - 4)%nat V5 V7 (mword_of_int 0x10001038) 56 (Z_to_bv 32 8 : mword 32)
              ltac:(rewrite HH2a5; bvc) vg_038 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH2a4; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp118 : add_vec_int (mword_of_int (VDI + 0x116) : mword 64) 2 = mword_of_int (VDI + 0x118)) by pcs.
    iEval (rewrite Hp118) in "Hpc".
    iDestruct (word_pointsto_aligned_p with "Hdesc") as %Haldesc.
    iDestruct (word_pointsto_split4 with "Hdesc") as "[Hdlo Hdhi]".
    assert (Hdad0 : add_vec (H2 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = disk_desc)
      by (rewrite HH2s1; bvc).
    iPoseProof (vdi_118 with "Htext") as "Hi".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (VDI + 0x118)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0 : mword 12) H2 (K - 4)%nat (word_lo pd)
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Hdlo] [-]").
    { iEval (rewrite Hdad0). iExact "Hdlo". }
    iIntros "Hcg Hpc Hdlo". iClear "Hi".
    iEval (rewrite Hdad0) in "Hdlo".
    pose (H3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (word_lo pd : mword 32))]> H2).
    assert (HH3a4 : H3 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (word_lo pd : mword 32)) by (peel; reflexivity).
    assert (HH3a5 : H3 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH2a5).
    assert (HH3s1 : H3 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH2s1).
    assert (Hp11a : add_vec_int (mword_of_int (VDI + 0x118) : mword 64) 2 = mword_of_int (VDI + 0x11a)) by pcs.
    iEval (rewrite Hp11a) in "Hpc".
    iPoseProof (vdi_11a with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x11a)) false (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 128 : mword 12)
              H3 (K - 4)%nat V7 V8 (mword_of_int 0x10001080) 128 (word_lo pd)
              ltac:(rewrite HH3a5; bvc) vg_080 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH3a4; apply trunc32_sext64) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp11e : add_vec_int (mword_of_int (VDI + 0x11a) : mword 64) 4 = mword_of_int (VDI + 0x11e)) by pcs.
    iEval (rewrite Hp11e) in "Hpc".
    assert (Hdad4 : add_vec (H3 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 4 : mword 12)) = pa_add disk_desc 4%nat)
      by (rewrite HH3s1; bvc).
    iPoseProof (vdi_11e with "Htext") as "Hi".
    iApply (wp_clw_s_sconf γ Φ (mword_of_int (VDI + 0x11e)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 4 : mword 12) H3 (K - 4)%nat (word_hi pd)
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Hdhi] [-]").
    { iEval (rewrite Hdad4). iExact "Hdhi". }
    iIntros "Hcg Hpc Hdhi". iClear "Hi".
    iEval (rewrite Hdad4) in "Hdhi".
    pose (H4 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (sign_extend' 64 (word_hi pd : mword 32))]> H3).
    assert (HH4a4 : H4 !!! Regidx (mword_of_int 14 : mword 5) = sign_extend' 64 (word_hi pd : mword 32)) by (peel; reflexivity).
    assert (HH4a5 : H4 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH3a5).
    assert (HH4s1 : H4 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH3s1).
    iDestruct (word_pointsto_join4 _ _ _ _ Haldesc with "Hdlo Hdhi") as "Hdesc".
    iEval (rewrite vdi_word_join) in "Hdesc".
    assert (Hp120 : add_vec_int (mword_of_int (VDI + 0x11e) : mword 64) 2 = mword_of_int (VDI + 0x120)) by pcs.
    iEval (rewrite Hp120) in "Hpc".
    iPoseProof (vdi_120 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x120)) false (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 132 : mword 12)
              H4 (K - 4)%nat V8 V9 (mword_of_int 0x10001084) 132 (word_hi pd)
              ltac:(rewrite HH4a5; bvc) vg_084 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH4a4; apply trunc32_sext64) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp124 : add_vec_int (mword_of_int (VDI + 0x120) : mword 64) 4 = mword_of_int (VDI + 0x124)) by pcs.
    iEval (rewrite Hp124) in "Hpc".
    assert (Hava3 : add_vec (H4 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 8 : mword 12)) = disk_avail)
      by (rewrite HH4s1; bvc).
    iPoseProof (vdi_124 with "Htext") as "Hi".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VDI + 0x124)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 8 : mword 12) H4 (K - 4)%nat pav
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Havail] [-]").
    { iEval (rewrite Hava3). iExact "Havail". }
    iIntros "Hcg Hpc Havail". iClear "Hi".
    iEval (rewrite Hava3) in "Havail".
    pose (H5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg pav]> H4).
    assert (HH5a5 : H5 !!! Regidx (mword_of_int 15 : mword 5) = pav) by (peel; reflexivity).
    assert (HH5s1 : H5 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH4s1).
    assert (Hp126 : add_vec_int (mword_of_int (VDI + 0x124) : mword 64) 2 = mword_of_int (VDI + 0x126)) by pcs.
    iEval (rewrite Hp126) in "Hpc".
    iPoseProof (vdi_126 with "Htext") as "Hi".
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (VDI + 0x126)) (mword_of_int 13 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 12) H5 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H6 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (H5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> H5).
    assert (Hp12a : add_vec_int (mword_of_int (VDI + 0x126) : mword 64) 4 = mword_of_int (VDI + 0x12a)) by pcs.
    iEval (rewrite Hp12a) in "Hpc".
    iPoseProof (vdi_12a with "Htext") as "Hi".
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (VDI + 0x12a)) (mword_of_int 14 : mword 5) (mword_of_int 65537 : mword 20)
              (luival (mword_of_int 65537 : mword 20)) H6 (K - 4)%nat ltac:(nzd) ltac:(nzd) eq_refl
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H7 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> H6).
    assert (HH7a4 : H7 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; bvc).
    assert (HH7a5 : H7 !!! Regidx (mword_of_int 15 : mword 5) = pav) by (peel; exact HH5a5).
    assert (HH7a3 : H7 !!! Regidx (mword_of_int 13 : mword 5) = sign_extend' 64 (subrange_vec_dec
        (add_vec pav (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))
      by (peel; try rewrite HH5a5; reflexivity).
    assert (HH7s1 : H7 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH5s1).
    assert (Hp12e : add_vec_int (mword_of_int (VDI + 0x12a) : mword 64) 4 = mword_of_int (VDI + 0x12e)) by pcs.
    iEval (rewrite Hp12e) in "Hpc".
    iPoseProof (vdi_12e with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x12e)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 144 : mword 12)
              H7 (K - 4)%nat V9 V10 (mword_of_int 0x10001090) 144 (lo32 pav)
              ltac:(rewrite HH7a4; bvc) vg_090 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH7a3; apply vdi_addiw_sw) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp132 : add_vec_int (mword_of_int (VDI + 0x12e) : mword 64) 4 = mword_of_int (VDI + 0x132)) by pcs.
    iEval (rewrite Hp132) in "Hpc".
    iPoseProof (vdi_132 with "Htext") as "Hi".
    iApply (wp_srai_s_sconf γ Φ (mword_of_int (VDI + 0x132)) (mword_of_int 15 : mword 5) (mword_of_int 32 : mword 6) H7 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_right_arith (H7 !!! Regidx (mword_of_int 15 : mword 5))
        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> H7).
    assert (HH8a5 : H8 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int 0 : mword 64))
      by (peel; try rewrite HH7a5; exact (vdi_srai32 pav Hpavlt)).
    assert (HH8a4 : H8 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH7a4).
    assert (HH8s1 : H8 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH7s1).
    assert (Hp134 : add_vec_int (mword_of_int (VDI + 0x132) : mword 64) 2 = mword_of_int (VDI + 0x134)) by pcs.
    iEval (rewrite Hp134) in "Hpc".
    iPoseProof (vdi_134 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x134)) false (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 148 : mword 12)
              H8 (K - 4)%nat V10 V11 (mword_of_int 0x10001094) 148 (Z_to_bv 32 0 : mword 32)
              ltac:(rewrite HH8a4; bvc) vg_094 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH8a5; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp138 : add_vec_int (mword_of_int (VDI + 0x134) : mword 64) 4 = mword_of_int (VDI + 0x138)) by pcs.
    iEval (rewrite Hp138) in "Hpc".
    assert (Husa3 : add_vec (H8 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = disk_used)
      by (rewrite HH8s1; bvc).
    iPoseProof (vdi_138 with "Htext") as "Hi".
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (VDI + 0x138)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 16 : mword 12) H8 (K - 4)%nat pu
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [Hused] [-]").
    { iEval (rewrite Husa3). iExact "Hused". }
    iIntros "Hcg Hpc Hused". iClear "Hi".
    iEval (rewrite Husa3) in "Hused".
    pose (H9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg pu]> H8).
    assert (HH9a5 : H9 !!! Regidx (mword_of_int 15 : mword 5) = pu) by (peel; reflexivity).
    assert (HH9a4 : H9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH8a4).
    assert (HH9s1 : H9 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH8s1).
    assert (Hp13a : add_vec_int (mword_of_int (VDI + 0x138) : mword 64) 2 = mword_of_int (VDI + 0x13a)) by pcs.
    iEval (rewrite Hp13a) in "Hpc".
    iPoseProof (vdi_13a with "Htext") as "Hi".
    iApply (wp_addiw_s_sconf γ Φ (mword_of_int (VDI + 0x13a)) (mword_of_int 13 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 12) H9 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H10 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (sign_extend' 64 (subrange_vec_dec
        (add_vec (H9 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> H9).
    assert (HH10a3 : H10 !!! Regidx (mword_of_int 13 : mword 5) = sign_extend' 64 (subrange_vec_dec
        (add_vec pu (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))
      by (peel; try rewrite HH9a5; reflexivity).
    assert (HH10a4 : H10 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH9a4).
    assert (HH10a5 : H10 !!! Regidx (mword_of_int 15 : mword 5) = pu) by (peel; exact HH9a5).
    assert (HH10s1 : H10 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH9s1).
    assert (Hp13e : add_vec_int (mword_of_int (VDI + 0x13a) : mword 64) 4 = mword_of_int (VDI + 0x13e)) by pcs.
    iEval (rewrite Hp13e) in "Hpc".
    iPoseProof (vdi_13e with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x13e)) false (mword_of_int 13 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 160 : mword 12)
              H10 (K - 4)%nat V11 V12 (mword_of_int 0x100010a0) 160 (lo32 pu)
              ltac:(rewrite HH10a4; bvc) vg_0a0 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH10a3; apply vdi_addiw_sw) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp142 : add_vec_int (mword_of_int (VDI + 0x13e) : mword 64) 4 = mword_of_int (VDI + 0x142)) by pcs.
    iEval (rewrite Hp142) in "Hpc".
    iPoseProof (vdi_142 with "Htext") as "Hi".
    iApply (wp_srai_s_sconf γ Φ (mword_of_int (VDI + 0x142)) (mword_of_int 15 : mword 5) (mword_of_int 32 : mword 6) H10 (K - 4)%nat
              ltac:(nzd) ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_right_arith (H10 !!! Regidx (mword_of_int 15 : mword 5))
        (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> H10).
    assert (HH11a5 : H11 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int 0 : mword 64))
      by (peel; try rewrite HH10a5; exact (vdi_srai32 pu Hpult)).
    assert (HH11a4 : H11 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH10a4).
    assert (HH11s1 : H11 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH10s1).
    assert (Hp144 : add_vec_int (mword_of_int (VDI + 0x142) : mword 64) 2 = mword_of_int (VDI + 0x144)) by pcs.
    iEval (rewrite Hp144) in "Hpc".
    iPoseProof (vdi_144 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x144)) false (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 164 : mword 12)
              H11 (K - 4)%nat V12 V13 (mword_of_int 0x100010a4) 164 (Z_to_bv 32 0 : mword 32)
              ltac:(rewrite HH11a4; bvc) vg_0a4 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH11a5; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp148 : add_vec_int (mword_of_int (VDI + 0x144) : mword 64) 4 = mword_of_int (VDI + 0x148)) by pcs.
    iEval (rewrite Hp148) in "Hpc".
    iPoseProof (vdi_148 with "Htext") as "Hi".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (VDI + 0x148)) (mword_of_int 15 : mword 5) (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) H11 (K - 4)%nat ltac:(nzd) ltac:(nzd) ltac:(bvc)
              with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> H11).
    assert (HH12a5 : H12 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int 1 : mword 64)) by (peel; reflexivity).
    assert (HH12a4 : H12 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH11a4).
    assert (HH12s1 : H12 !!! Regidx (mword_of_int 9 : mword 5) = disk_base) by (peel; exact HH11s1).
    assert (HH12s2 : H12 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int 11) by (peel; exact Hms3s2).
    assert (Hp14a : add_vec_int (mword_of_int (VDI + 0x148) : mword 64) 2 = mword_of_int (VDI + 0x14a)) by pcs.
    iEval (rewrite Hp14a) in "Hpc".
    iPoseProof (vdi_14a with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x14a)) true (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 68 : mword 12)
              H12 (K - 4)%nat V13 V14 (mword_of_int 0x10001044) 68 (Z_to_bv 32 1 : mword 32)
              ltac:(rewrite HH12a4; bvc) vg_044 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH12a5; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp14c : add_vec_int (mword_of_int (VDI + 0x14a) : mword 64) 2 = mword_of_int (VDI + 0x14c)) by pcs.
    iEval (rewrite Hp14c) in "Hpc".
    (* disk.free[0..7] = 1 *)
    iEval (cbn [seq]) in "Hfree".
    iDestruct "Hfree" as "(Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & _)".
    assert (Hsb1 : trunc8 (H12 !!! Regidx (mword_of_int 15 : mword 5)) = Z_to_bv 8 1) by (rewrite HH12a5; bvc).
    assert (Hfa0 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 24 : mword 12)) = pa_add disk_free 0%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_14c with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x14c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12) H12 (K - 4)%nat (free0 0%nat)
              with "Hcg Hpc Hi [Hf0] [-]").
    { iEval (rewrite Hfa0). iExact "Hf0". }
    iIntros "Hcg Hpc Hf0". iClear "Hi".
    iEval (rewrite Hfa0 Hsb1) in "Hf0".
    assert (Hp150 : add_vec_int (mword_of_int (VDI + 0x14c) : mword 64) 4 = mword_of_int (VDI + 0x150)) by pcs.
    iEval (rewrite Hp150) in "Hpc".
    assert (Hfa1 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 25 : mword 12)) = pa_add disk_free 1%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_150 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x150)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 25 : mword 12) H12 (K - 4)%nat (free0 1%nat)
              with "Hcg Hpc Hi [Hf1] [-]").
    { iEval (rewrite Hfa1). iExact "Hf1". }
    iIntros "Hcg Hpc Hf1". iClear "Hi".
    iEval (rewrite Hfa1 Hsb1) in "Hf1".
    assert (Hp154 : add_vec_int (mword_of_int (VDI + 0x150) : mword 64) 4 = mword_of_int (VDI + 0x154)) by pcs.
    iEval (rewrite Hp154) in "Hpc".
    assert (Hfa2 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 26 : mword 12)) = pa_add disk_free 2%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_154 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x154)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 26 : mword 12) H12 (K - 4)%nat (free0 2%nat)
              with "Hcg Hpc Hi [Hf2] [-]").
    { iEval (rewrite Hfa2). iExact "Hf2". }
    iIntros "Hcg Hpc Hf2". iClear "Hi".
    iEval (rewrite Hfa2 Hsb1) in "Hf2".
    assert (Hp158 : add_vec_int (mword_of_int (VDI + 0x154) : mword 64) 4 = mword_of_int (VDI + 0x158)) by pcs.
    iEval (rewrite Hp158) in "Hpc".
    assert (Hfa3 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 27 : mword 12)) = pa_add disk_free 3%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_158 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x158)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 27 : mword 12) H12 (K - 4)%nat (free0 3%nat)
              with "Hcg Hpc Hi [Hf3] [-]").
    { iEval (rewrite Hfa3). iExact "Hf3". }
    iIntros "Hcg Hpc Hf3". iClear "Hi".
    iEval (rewrite Hfa3 Hsb1) in "Hf3".
    assert (Hp15c : add_vec_int (mword_of_int (VDI + 0x158) : mword 64) 4 = mword_of_int (VDI + 0x15c)) by pcs.
    iEval (rewrite Hp15c) in "Hpc".
    assert (Hfa4 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 28 : mword 12)) = pa_add disk_free 4%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_15c with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x15c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 28 : mword 12) H12 (K - 4)%nat (free0 4%nat)
              with "Hcg Hpc Hi [Hf4] [-]").
    { iEval (rewrite Hfa4). iExact "Hf4". }
    iIntros "Hcg Hpc Hf4". iClear "Hi".
    iEval (rewrite Hfa4 Hsb1) in "Hf4".
    assert (Hp160 : add_vec_int (mword_of_int (VDI + 0x15c) : mword 64) 4 = mword_of_int (VDI + 0x160)) by pcs.
    iEval (rewrite Hp160) in "Hpc".
    assert (Hfa5 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 29 : mword 12)) = pa_add disk_free 5%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_160 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x160)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 29 : mword 12) H12 (K - 4)%nat (free0 5%nat)
              with "Hcg Hpc Hi [Hf5] [-]").
    { iEval (rewrite Hfa5). iExact "Hf5". }
    iIntros "Hcg Hpc Hf5". iClear "Hi".
    iEval (rewrite Hfa5 Hsb1) in "Hf5".
    assert (Hp164 : add_vec_int (mword_of_int (VDI + 0x160) : mword 64) 4 = mword_of_int (VDI + 0x164)) by pcs.
    iEval (rewrite Hp164) in "Hpc".
    assert (Hfa6 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 30 : mword 12)) = pa_add disk_free 6%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_164 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x164)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 30 : mword 12) H12 (K - 4)%nat (free0 6%nat)
              with "Hcg Hpc Hi [Hf6] [-]").
    { iEval (rewrite Hfa6). iExact "Hf6". }
    iIntros "Hcg Hpc Hf6". iClear "Hi".
    iEval (rewrite Hfa6 Hsb1) in "Hf6".
    assert (Hp168 : add_vec_int (mword_of_int (VDI + 0x164) : mword 64) 4 = mword_of_int (VDI + 0x168)) by pcs.
    iEval (rewrite Hp168) in "Hpc".
    assert (Hfa7 : add_vec (H12 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 31 : mword 12)) = pa_add disk_free 7%nat)
      by (rewrite HH12s1; bvc).
    iPoseProof (vdi_168 with "Htext") as "Hi".
    iApply (wp_sb_s_sconf γ Φ (mword_of_int (VDI + 0x168)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 31 : mword 12) H12 (K - 4)%nat (free0 7%nat)
              with "Hcg Hpc Hi [Hf7] [-]").
    { iEval (rewrite Hfa7). iExact "Hf7". }
    iIntros "Hcg Hpc Hf7". iClear "Hi".
    iEval (rewrite Hfa7 Hsb1) in "Hf7".
    assert (Hp16c : add_vec_int (mword_of_int (VDI + 0x168) : mword 64) 4 = mword_of_int (VDI + 0x16c)) by pcs.
    iEval (rewrite Hp16c) in "Hpc".
    iAssert ([∗ list] j ∈ seq 0%nat 8%nat, (pa_add disk_free j) ↦ₘ (Z_to_bv 8 1))%I
      with "[Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7]" as "Hfree".
    { cbn [seq]. iFrame "Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7"; try done. }
    iPoseProof (vdi_16c with "Htext") as "Hi".
    iApply (wp_ori_s_sconf γ Φ (mword_of_int (VDI + 0x16c)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 4 : mword 12)
              (mword_of_int 15 : mword 64) H12 (K - 4)%nat ltac:(nzd) ltac:(nzd)
              ltac:(rewrite HH12s2; bvc) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (H13 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mword_of_int 15 : mword 64)]> H12).
    assert (HH13s2 : H13 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int 15 : mword 64)) by (peel; reflexivity).
    assert (HH13a4 : H13 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0x10001000) by (peel; exact HH12a4).
    assert (Hp170 : add_vec_int (mword_of_int (VDI + 0x16c) : mword 64) 4 = mword_of_int (VDI + 0x170)) by pcs.
    iEval (rewrite Hp170) in "Hpc".
    iPoseProof (vdi_170 with "Htext") as "Hi".
    iApply (wp_vdi_sw γ Φ (mword_of_int (VDI + 0x170)) false (mword_of_int 18 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 112 : mword 12)
              H13 (K - 4)%nat V14 V15 (mword_of_int 0x10001070) 112 (Z_to_bv 32 15 : mword 32)
              ltac:(rewrite HH13a4; bvc) vg_070 ltac:(vm_compute; reflexivity)
              ltac:(rewrite HH13s2; bvc) ltac:(reflexivity)
              with "Hcg Hpc Hi Hv [-]").
    iIntros "Hcg Hpc Hv". iClear "Hi".
    assert (Hp174 : add_vec_int (mword_of_int (VDI + 0x170) : mword 64) 4 = mword_of_int (VDI + 0x174)) by pcs.
    iEval (rewrite Hp174) in "Hpc".
    (* ===== EPILOGUE (0x174..0x17e) ===== *)
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try bvc. }
    assert (HH13sp : H13 !!! Regidx csp_rs1 = spr) by (peel; exact Hms3sp).
    iPoseProof (vdi_174 with "Htext") as "Hi".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (VDI + 0x174)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              H13 (K - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [Hs1c] [-]").
    { iEval (rewrite HH13sp Hb1). iExact "Hs1c". }
    iIntros "Hcg Hpc Hs1c". iClear "Hi".
    iEval (rewrite HH13sp Hb1) in "Hs1c".
    pose (P1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> H13).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr) by (rewrite /P1 upd_ne; [exact HH13sp | reg_neq]).
    assert (Hp176 : add_vec_int (mword_of_int (VDI + 0x174) : mword 64) 2 = mword_of_int (VDI + 0x176)) by pcs.
    iEval (rewrite Hp176) in "Hpc".
    iPoseProof (vdi_176 with "Htext") as "Hi".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (VDI + 0x176)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              P1 (K - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [Hs2c] [-]").
    { iEval (rewrite HP1sp Hb2). iExact "Hs2c". }
    iIntros "Hcg Hpc Hs2c". iClear "Hi".
    iEval (rewrite HP1sp Hb2) in "Hs2c".
    pose (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr) by (rewrite /P2 upd_ne; [exact HP1sp | reg_neq]).
    assert (Hp178 : add_vec_int (mword_of_int (VDI + 0x176) : mword 64) 2 = mword_of_int (VDI + 0x178)) by pcs.
    iEval (rewrite Hp178) in "Hpc".
    iPoseProof (vdi_178 with "Htext") as "Hi".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (VDI + 0x178)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              P2 (K - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [Hs3c] [-]").
    { iEval (rewrite HP2sp Hb3). iExact "Hs3c". }
    iIntros "Hcg Hpc Hs3c". iClear "Hi".
    iEval (rewrite HP2sp Hb3) in "Hs3c".
    pose (P3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr) by (rewrite /P3 upd_ne; [exact HP2sp | reg_neq]).
    assert (Hp17a : add_vec_int (mword_of_int (VDI + 0x178) : mword 64) 2 = mword_of_int (VDI + 0x17a)) by pcs.
    iEval (rewrite Hp17a) in "Hpc".
    iPoseProof (vdi_17a with "Htext") as "Hi".
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (VDI + 0x17a)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              P3 (K - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) ltac:(nzd) ltac:(nzd)
              with "Hcg Hpc Hi [Hs4c] [-]").
    { iEval (rewrite HP3sp Hb4). iExact "Hs4c". }
    iIntros "Hcg Hpc Hs4c". iClear "Hi".
    iEval (rewrite HP3sp Hb4) in "Hs4c".
    pose (P4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr) by (rewrite /P4 upd_ne; [exact HP3sp | reg_neq]).
    assert (Hp17c : add_vec_int (mword_of_int (VDI + 0x17a) : mword 64) 2 = mword_of_int (VDI + 0x17c)) by pcs.
    iEval (rewrite Hp17c) in "Hpc".
    (* +0x17c addi sp,sp,32 : the frame pop *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = m !!! Regidx csp_rs1).
    { rewrite HP4sp. rewrite /spr. apply vdi_sp_cancel. }
    assert (Hpop : P4 !!! Regidx csp_rs1 = pa_stk (add_vec (P4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv. rewrite HP4sp. symmetry. exact Hsprstk. }
    iAssert (stack_own (m !!! Regidx csp_rs1) 4%nat) with "[Hs1c Hs2c Hs3c Hs4c]" as "Hframe".
    { rewrite stack_own_slots; cbn [seq].
      iSplitL "Hs1c". { iExists (m !!! Regidx (mword_of_int 1 : mword 5)). iExact "Hs1c". }
      iSplitL "Hs2c". { iExists (m !!! Regidx (mword_of_int 8 : mword 5)). iExact "Hs2c". }
      iSplitL "Hs3c". { iExists (m !!! Regidx (mword_of_int 9 : mword 5)). iExact "Hs3c". }
      iSplitL "Hs4c". { iExists (m !!! Regidx (mword_of_int 18 : mword 5)). iExact "Hs4c". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (vdi_17c with "Htext") as "Hi".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (VDI + 0x17c)) (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4%nat Hpop
              with "Hcg Hpc Hi Hframe [-]").
    iIntros "Hcg Hpc". iClear "Hi".
    pose (P5 := <[Regidx csp_rs1 := regval_into_reg (add_vec (P4 !!! Regidx csp_rs1)
        (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    iEval (rewrite Hknk) in "Hcg".
    assert (Hp17e : add_vec_int (mword_of_int (VDI + 0x17c) : mword 64) 2 = mword_of_int (VDI + 0x17e)) by pcs.
    iEval (rewrite Hp17e) in "Hpc".
    (* +0x17e ret *)
    assert (HP5ra : P5 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
      rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_ne; [| reg_neq].
      rewrite /P1 upd_eq. reflexivity. }
    assert (Hrt : ret_pc (P5 !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rewrite HP5ra; reflexivity).
    iPoseProof (vdi_17e with "Htext") as "Hi".
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (VDI + 0x17e)) (mword_of_int 1 : mword 5) P5 K ltac:(nzd) with "Hcg Hpc Hi [-]").
    iIntros "Hcg Hpc". iClear "Hi". iEval (rewrite Hrt) in "Hpc".
    (* ===== hand the caller the post ===== *)
    assert (HD : set_hi (set_lo zero64 (word_lo pd)) (word_hi pd) = pd).
    { rewrite (vdi_word_lo_small pd Hpdlt). rewrite (vdi_word_hi_small pd Hpdlt).
      exact (vdi_reassemble pd Hpdlt). }
    assert (HA : set_hi (set_lo zero64 (lo32 pav)) (Z_to_bv 32 0) = pav)
      by (exact (vdi_reassemble pav Hpavlt)).
    assert (HU : set_hi (set_lo zero64 (lo32 pu)) (Z_to_bv 32 0) = pu)
      by (exact (vdi_reassemble pu Hpult)).
    assert (HV15 : V15 = VirtioState (virtio_init_cfg pd pav pu) zero32 zero16 zero16 dk).
    { rewrite /V15 /vdi_v /virtio_init_cfg. rewrite HD HA HU. reflexivity. }
    iEval (rewrite HV15) in "Hv".
    assert (Havs : avail_sub (Some nb) 3 = Some (nb - 3)%nat)
      by (rewrite avail_sub_Some; reflexivity).
    iAssert (kalloc_env γa (avail_sub (Some nb) 3) (m !!! Regidx (mword_of_int 4 : mword 5))) with "[Havl]" as "Henv".
    { rewrite Havs. iExists γk. iFrame "Hklock Havl Hpanic". }
    assert (Hthread : forall c : mword 5, is_cs_idx c = true ->
              c <> (mword_of_int 1 : mword 5) -> c <> csp_rs1 ->
              c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
              c <> (mword_of_int 18 : mword 5) ->
              P5 !!! Regidx c = m !!! Regidx c).
    { intros c Hc N1 Nsp N8 N9 N18.
      pose proof (is_cs_idx_true_neq (mword_of_int 10 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx10.
      pose proof (is_cs_idx_true_neq (mword_of_int 11 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx11.
      pose proof (is_cs_idx_true_neq (mword_of_int 12 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx12.
      pose proof (is_cs_idx_true_neq (mword_of_int 13 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx13.
      pose proof (is_cs_idx_true_neq (mword_of_int 14 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx14.
      pose proof (is_cs_idx_true_neq (mword_of_int 15 : mword 5) c ltac:(vm_compute; reflexivity) Hc) as Nx15.
      rewrite /P5 upd_ne; [| congruence].
      rewrite /P4 upd_ne; [| congruence].
      rewrite /P3 upd_ne; [| congruence].
      rewrite /P2 upd_ne; [| congruence].
      rewrite /P1 upd_ne; [| congruence].
      rewrite /H13 upd_ne; [| congruence].
      rewrite /H12 upd_ne; [| congruence].
      rewrite /H11 upd_ne; [| congruence].
      rewrite /H10 upd_ne; [| congruence].
      rewrite /H9 upd_ne; [| congruence].
      rewrite /H8 upd_ne; [| congruence].
      rewrite /H7 upd_ne; [| congruence].
      rewrite /H6 upd_ne; [| congruence].
      rewrite /H5 upd_ne; [| congruence].
      rewrite /H4 upd_ne; [| congruence].
      rewrite /H3 upd_ne; [| congruence].
      rewrite /H2 upd_ne; [| congruence].
      rewrite /H1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hms3cs c Hc).
      rewrite /G4 upd_ne; [| congruence].
      rewrite /G3 upd_ne; [| congruence].
      rewrite /G2 upd_ne; [| congruence].
      rewrite /G1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hms2cs c Hc).
      rewrite /F6 upd_ne; [| congruence].
      rewrite /F5 upd_ne; [| congruence].
      rewrite /F4 upd_ne; [| congruence].
      rewrite /F3 upd_ne; [| congruence].
      rewrite /F2 upd_ne; [| congruence].
      rewrite /F1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hms1cs c Hc).
      rewrite /E7 upd_ne; [| congruence].
      rewrite /E6 upd_ne; [| congruence].
      rewrite /E5 upd_ne; [| congruence].
      rewrite /E4 upd_ne; [| congruence].
      rewrite /E3 upd_ne; [| congruence].
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hk3cs c Hc).
      rewrite /D2 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hk2cs c Hc).
      rewrite /C3 upd_ne; [| congruence].
      rewrite /C2 upd_ne; [| congruence].
      rewrite /C1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hk1cs c Hc).
      rewrite /B39 upd_ne; [| congruence].
      rewrite /B38 upd_ne; [| congruence].
      rewrite /B37 upd_ne; [| congruence].
      rewrite /B36 upd_ne; [| congruence].
      rewrite /B35 upd_ne; [| congruence].
      rewrite /B34 upd_ne; [| congruence].
      rewrite /B33 upd_ne; [| congruence].
      rewrite /B32 upd_ne; [| congruence].
      rewrite /B31 upd_ne; [| congruence].
      rewrite /B30 upd_ne; [| congruence].
      rewrite /B29 upd_ne; [| congruence].
      rewrite /B28 upd_ne; [| congruence].
      rewrite /B27 upd_ne; [| congruence].
      rewrite /B26 upd_ne; [| congruence].
      rewrite /B25 upd_ne; [| congruence].
      rewrite /B24 upd_ne; [| congruence].
      rewrite /B23 upd_ne; [| congruence].
      rewrite /B22 upd_ne; [| congruence].
      rewrite /B21 upd_ne; [| congruence].
      rewrite /B20 upd_ne; [| congruence].
      rewrite /B19 upd_ne; [| congruence].
      rewrite /B18 upd_ne; [| congruence].
      rewrite /B17 upd_ne; [| congruence].
      rewrite /B16 upd_ne; [| congruence].
      rewrite /B15 upd_ne; [| congruence].
      rewrite /B14 upd_ne; [| congruence].
      rewrite /B13 upd_ne; [| congruence].
      rewrite /B12 upd_ne; [| congruence].
      rewrite /B11 upd_ne; [| congruence].
      rewrite /B10 upd_ne; [| congruence].
      rewrite /B9 upd_ne; [| congruence].
      rewrite /B8 upd_ne; [| congruence].
      rewrite /B7 upd_ne; [| congruence].
      rewrite /B6 upd_ne; [| congruence].
      rewrite /B5 upd_ne; [| congruence].
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hilcs c Hc).
      rewrite /W7 upd_ne; [| congruence].
      rewrite /W6 upd_ne; [| congruence].
      rewrite /W5 upd_ne; [| congruence].
      rewrite /W4 upd_ne; [| congruence].
      rewrite /W3 upd_ne; [| congruence].
      rewrite /W2 upd_ne; [| congruence].
      rewrite /W1 upd_ne; [reflexivity | congruence]. }
    iApply ("Hcont" $! P5 pd pav pu with
      "Hcg Hcpu Hpc [%] [%] [%] [%] Henv Hv Hbpd Hbpav Hbpu Hdesc Havail Hused Hfree Hlk Hlnm Hcp").
    { try iPureIntro. unfold callee_saved.
      split. { rewrite /P5 upd_eq. exact Hwv. }
      split. { apply Hthread; vm_compute; first [reflexivity | discriminate]. }
      split. { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
               rewrite /P3 upd_ne; [| reg_neq]. rewrite /P2 upd_eq. reflexivity. }
      split. { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_ne; [| reg_neq].
               rewrite /P3 upd_eq. reflexivity. }
      split. { rewrite /P5 upd_ne; [| reg_neq]. rewrite /P4 upd_eq. reflexivity. }
      repeat split; apply Hthread; vm_compute; first [reflexivity | discriminate]. }
    { try iPureIntro. exact Hpdv. }
    { try iPureIntro. exact Hpavv. }
    { try iPureIntro. exact Hpuv. }
  Qed.
End ProofVirtioDiskInit.
End VirtioDiskInitProof.
