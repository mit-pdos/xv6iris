(* ProofPrepareReturnParts.v -- the PURE obligations of prepare_return's body,
   separated from the WP walk so that the walk reads as one instruction per
   step and so that each of these can be checked (and re-checked) on its own.

   Two groups, and they are of quite different character:

   §1 ADDRESS AND CONSTANT ARITHMETIC -- the four trapframe slot addresses,
      the [TRAMPOLINE] the LUI/ADDI/SLLI triple builds, the
      [uservec - trampoline] the two AUIPC/ADDI pairs subtract to ZERO, and
      the [usertrap] the third pair builds.  All closed, all [vm_compute];
      they are here rather than inline because each is a LAYOUT FACT (e.g.
      that usertrap really does sit at prepare_return+0x140) and a relayout
      should break one named lemma, not a step of the walk.

   §2 THE sstatus READ-MODIFY-WRITE, AT THE FIELD LEVEL.  This is the only
      part of prepare_return that is not bookkeeping:

        x = r_sstatus(); x &= ~SSTATUS_SPP; x |= SSTATUS_SPIE; w_sstatus(x);

      [wp_csrw_sstatus_val_s_sconf] wants five facts about the written word
      and yields SPP/SPIE of the mstatus it installs, so what has to be
      proved is SEVEN FIELDS of [prr_sst] -- and NOT the whole-word identity
      [sstatus_read ms0 = prr_sst W], which would need [lower_mstatus]'s nest
      of slice updates to be reasoned about as a word.  Each field is three
      lines, because slicing distributes over the bitwise ops
      ([WpGprCsrwC.bv_extract_and] / [bv_extract_or]) and each mask's own
      slice is a closed computation. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Import RiscvModelBytes.
Require Import PageGeom.
Require Import TrampPt.
Require Import WpMmodeLeafBase.
Require Import WpGprCsrwCommon.
Require Import WpGprCsrwC.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import ProcInv.
Require Import SpecPrepareReturn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Notation PRR := KernelSyms.prepare_return (only parsing).

(* a syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  §1  ADDRESS AND CONSTANT ARITHMETIC                                   *)
(* ===================================================================== *)

(* a 12-bit displacement whose sign extension is its own 64-bit literal --
   the shape every [add_vec base (sign_extend' 64 imm)] reduces through. *)
Lemma prr_avi (v : mword 64) (d : Z) :
  (sign_extend' 64 (mword_of_int d : mword 12) : mword 64) = (mword_of_int d : mword 64) ->
  add_vec v (sign_extend' 64 (mword_of_int d : mword 12)) = add_vec_int v d.
Proof. intro H. by rewrite H. Qed.

(* ---- the four KERNEL slots, by byte displacement ---- *)
(* kernel_satp 0, kernel_sp 8, kernel_trap 16, kernel_hartid 32; the epc the
   last load READS sits at 24.  Each is [a_tf_word] at the matching index, so
   [ProcInv.tf_page_word_upd] applies without further arithmetic. *)
Lemma prr_tf_addr_00 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 0 : mword 12))
  = a_tf_word tfp tf_ksatp_idx.
Proof.
  rewrite (prr_avi (page_base tfp) 0 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

Lemma prr_tf_addr_08 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 8 : mword 12))
  = a_tf_word tfp tf_ksp_idx.
Proof.
  rewrite (prr_avi (page_base tfp) 8 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

Lemma prr_tf_addr_16 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 16 : mword 12))
  = a_tf_word tfp tf_ktrap_idx.
Proof.
  rewrite (prr_avi (page_base tfp) 16 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

Lemma prr_tf_addr_24 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 24 : mword 12))
  = a_tf_word tfp tf_epc_idx.
Proof.
  rewrite (prr_avi (page_base tfp) 24 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

Lemma prr_tf_addr_32 (tfp : mword 44) :
  add_vec (page_base tfp) (sign_extend' 64 (mword_of_int 32 : mword 12))
  = a_tf_word tfp tf_khartid_idx.
Proof.
  rewrite (prr_avi (page_base tfp) 32 ltac:(apply bv_eq; vm_compute; reflexivity)).
  rewrite /a_tf_word /pa_add. f_equal.
Qed.

(* the two [struct proc] fields the body reads off [a0] *)
Lemma prr_p_trapframe (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 88 : mword 12)) = p_trapframe pa.
Proof. reflexivity. Qed.

Lemma prr_p_kstack (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 64 : mword 12)) = p_kstack pa.
Proof. rewrite /p_kstack. f_equal; try (apply bv_eq; by vm_compute). Qed.

(* ---- the vector: [TRAMPOLINE + (uservec - trampoline)] ---- *)
(* +0x10 lui a4,0x4000 / +0x14 c.addi a4,a4,-1 / +0x16 c.slli a4,a4,12 builds
   [MAXVA - PGSIZE] in three steps rather than one, because no single
   instruction can hold a 38-bit constant. *)
Lemma prr_lui_a4 : luival (mword_of_int 16384 : mword 20) = (mword_of_int 0x4000000 : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prr_addi_a4 :
  add_vec (mword_of_int 0x4000000 : mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int 0x3FFFFFF : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prr_slli_a4 :
  shift_bits_left (mword_of_int 0x3FFFFFF : mword 64)
    (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
  = uservec_tvec.
Proof. rewrite /uservec_tvec /TRAMPOLINE. apply bv_eq. vm_compute. reflexivity. Qed.

(* THE DIFFERENCE IS ZERO, and that is the whole content of +0x18..+0x28:
   uservec IS the first byte of trampoline.S, so the [sub a5,a5,a3] subtracts
   [_trampoline] from itself.  Both operands are built by an AUIPC/ADDI pair
   off THIS function's pc, so the lemma is also the layout check. *)
Lemma prr_uservec_addr :
  add_vec (add_vec (mword_of_int (PRR + 0x18) : mword 64)
             (auipc_off (mword_of_int 4 : mword 20)))
    (sign_extend' 64 (mword_of_int 2916 : mword 12))
  = (mword_of_int KernelSyms.uservec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prr_trampoline_addr :
  add_vec (add_vec (mword_of_int (PRR + 0x20) : mword 64)
             (auipc_off (mword_of_int 4 : mword 20)))
    (sign_extend' 64 (mword_of_int 2908 : mword 12))
  = (mword_of_int KernelSyms.trampoline : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prr_uservec_off_zero :
  sub_vec (mword_of_int KernelSyms.uservec : mword 64)
          (mword_of_int KernelSyms.trampoline : mword 64)
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma prr_tvec_val :
  add_vec (mword_of_int 0 : mword 64) uservec_tvec = uservec_tvec.
Proof. rewrite /uservec_tvec. apply bv_eq. vm_compute. reflexivity. Qed.

(* the write is legal: TRAMPOLINE is page-aligned, so mtvec.Mode = Direct *)
Lemma prr_tvec_mode :
  trapVectorMode_forwards (_get_Mtvec_Mode uservec_tvec) <> TV_Reserved.
Proof. rewrite /uservec_tvec /TRAMPOLINE. vm_compute. discriminate. Qed.

(* ---- the usertrap pointer: +0x44 auipc a4,0x0 / +0x48 addi a4,a4,252 ---- *)
Lemma prr_usertrap_addr :
  add_vec (add_vec (mword_of_int (PRR + 0x44) : mword 64)
             (auipc_off (mword_of_int 0 : mword 20)))
    (sign_extend' 64 (mword_of_int 252 : mword 12))
  = (mword_of_int KernelSyms.usertrap : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- kernel_sp = p->kstack + PGSIZE: +0x3c c.lui a3,0x1 / +0x3e c.add ---- *)
Lemma prr_lui_pgsize :
  luival (sign_extend' 20 (mword_of_int 1 : mword 6)) = (mword_of_int 4096 : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  §2  THE sstatus READ-MODIFY-WRITE, AT THE FIELD LEVEL                 *)
(* ===================================================================== *)

(* [andi a5,a5,-257] clears SSTATUS_SPP (bit 8); [ori a5,a5,32] sets
   SSTATUS_SPIE (bit 5).  Named as 64-bit literals so that every field's
   own slice below is a CLOSED computation. *)
Definition prr_and_mask : mword 64 := mword_of_int (-257).
Definition prr_or_mask  : mword 64 := mword_of_int 32.

Definition prr_sst (W : mword 64) : mword 64 :=
  bv_or (bv_and W prr_and_mask) prr_or_mask.

(* the two ALU steps, in the shape [wp_andi_s_sconf] / [wp_ori_s_sconf] want *)
Lemma prr_andi_step (W : mword 64) :
  and_vec W (sign_extend' 64 (mword_of_int 3839 : mword 12)) = bv_and W prr_and_mask.
Proof. f_equal; try (apply bv_eq; by vm_compute). Qed.

Lemma prr_ori_step (W : mword 64) :
  or_vec (bv_and W prr_and_mask) (sign_extend' 64 (mword_of_int 32 : mword 12))
  = prr_sst W.
Proof. rewrite /prr_sst. f_equal; try (apply bv_eq; by vm_compute). Qed.

(* ---- the four fields [sconf] PINS, which the mask must leave alone.
   None of SIE (bit 1), MXR (19), FS (14:13), VS (10:9), XS (16:15) meets
   bit 8 or bit 5, so at each the and-mask's slice is all-ones and the
   or-mask's is zero. ---- *)
Local Ltac prr_keep :=
  rewrite /prr_sst; to_bv;
  rewrite bv_extract_or bv_extract_and;
  rewrite bv_and_ones_r; [| by vm_compute];
  rewrite bv_or_0_r; [reflexivity | by vm_compute].

Lemma prr_sst_sie (W : mword 64) :
  _get_Sstatus_SIE (prr_sst W) = _get_Sstatus_SIE W.
Proof. prr_keep. Qed.

Lemma prr_sst_mxr (W : mword 64) :
  _get_Sstatus_MXR (prr_sst W) = _get_Sstatus_MXR W.
Proof. prr_keep. Qed.

Lemma prr_sst_fs (W : mword 64) :
  _get_Sstatus_FS (prr_sst W) = _get_Sstatus_FS W.
Proof. prr_keep. Qed.

Lemma prr_sst_vs (W : mword 64) :
  _get_Sstatus_VS (prr_sst W) = _get_Sstatus_VS W.
Proof. prr_keep. Qed.

Lemma prr_sst_xs (W : mword 64) :
  _get_Sstatus_XS (prr_sst W) = _get_Sstatus_XS W.
Proof. prr_keep. Qed.

(* ---- and the two the mask MOVES, which are the point of the function ---- *)
(* SPP := 0 -- the sret goes to User *)
Lemma prr_sst_spp (W : mword 64) :
  _get_Sstatus_SPP (prr_sst W) = ('b"0" : mword 1).
Proof.
  rewrite /prr_sst; to_bv.
  rewrite bv_extract_or bv_extract_and.
  rewrite bv_and_0_r; [| by vm_compute].
  rewrite bv_or_0_r; [| by vm_compute].
  apply bv_eq; by vm_compute.
Qed.

(* SPIE := 1 -- interrupts on once there *)
Lemma prr_sst_spie (W : mword 64) :
  _get_Sstatus_SPIE (prr_sst W) = ('b"1" : mword 1).
Proof.
  rewrite /prr_sst; to_bv.
  rewrite bv_extract_or.
  rewrite bv_or_ones_r; [| by vm_compute].
  apply bv_eq; by vm_compute.
Qed.

(* ---- what the write's five premises reduce to, given the mstatus the
   [csrr sstatus] named.  The S-view of a lowered mstatus agrees with its
   M-view field by field ([WpGprCsrwC.sX_lower]), and [sconf_ms_facts] pins
   the four that matter; SIE is pinned by the arm index the csrr handed
   back.  Bundled here so the walk applies the leaf with five [ltac:]s. ---- *)
Section PrrSstatus.
  Context (ms : mword 64).
  Hypothesis Hmsf : sconf_ms_facts ms.
  Hypothesis Hsie : _get_Mstatus_SIE ms = ('b"0" : mword 1).


  Lemma prr_w_sie : _get_Sstatus_SIE (prr_sst (sstatus_read ms)) = ('b"0" : mword 1).
  Proof.
    rewrite prr_sst_sie /sstatus_read subrange_full sSIE_lower. exact Hsie.
  Qed.

  Lemma prr_w_mxr : _get_Sstatus_MXR (prr_sst (sstatus_read ms)) = ('b"0" : mword 1).
  Proof.
    destruct Hmsf as (_ & _ & HMXR & _).
    apply eq_vec_true_iff in HMXR.
    rewrite prr_sst_mxr /sstatus_read subrange_full sMXR_lower. exact HMXR.
  Qed.

  Lemma prr_w_fs :
    _get_Sstatus_FS (prr_sst (sstatus_read ms)) = extStatus_map_forwards Off.
  Proof.
    destruct Hmsf as (_ & _ & _ & _ & _ & HFS & _).
    rewrite prr_sst_fs /sstatus_read subrange_full sFS_lower. exact HFS.
  Qed.

  Lemma prr_w_vs :
    _get_Sstatus_VS (prr_sst (sstatus_read ms)) = extStatus_map_forwards Off.
  Proof.
    destruct Hmsf as (_ & _ & _ & _ & _ & _ & HVS & _).
    rewrite prr_sst_vs /sstatus_read subrange_full sVS_lower. exact HVS.
  Qed.

  Lemma prr_w_xs :
    _get_Sstatus_XS (prr_sst (sstatus_read ms)) = extStatus_map_forwards Off.
  Proof.
    destruct Hmsf as (_ & _ & _ & _ & HXS & _).
    rewrite prr_sst_xs /sstatus_read subrange_full sXS_lower. exact HXS.
  Qed.
End PrrSstatus.
