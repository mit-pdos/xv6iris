(** * WkTimerinitAux.v -- the per-instruction SCAFFOLDING of the weak
      [timerinit()] chain: the decode facts at [dstateM] and the 21
      [WeakLeafM.winstr_m] TOKENS built from them.

    Split out of [WkTimerinit.v] for the reason [WkStartAux] was split out of
    [WkStartNew]: the [vm_compute]-heavy decode layer is STABLE while the
    proof script above it is iterated, and recompiling the two together is
    minutes per edit.  Nothing here is weak-memory-specific; it is
    [CodeTimerinitAux]'s vocabulary re-derived in the [winstr_m] shape the
    SC-shaped leaves ([WeakLeafO]'s [_run] wrappers) consume.

    ONE LEMMA PER INSTRUCTION, and after it a call site never mentions a
    decode fact again: [wsti_NN kbs Hcov] applied to [wkernel_text kbs]
    yields the whole token.  This is the [CodeTimerinit.tmi_*] analogue --
    see [WkStartAux] §5 for the same construction on [start()]. *)

From Stdlib Require Import ZArith Zquot Zwf FunctionalExtensionality.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras RiscvExec RiscvTryStep.
Require Import WpGpr.
Require Import WpMmodeShiftiop WpMmodeLeafBase WpMmodeUtype WpMmodeItype WpMmodeRtype
  WpMmodeJalr WpMmodeLoad WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import KernelRvcDecode.
Require Import CodeTimerinitAux.
Require Import WpTimerinit.
(* -- weak machinery -- *)
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import MinstretInv.
Require Import WeakLeafM.
Require Import ExecCommon WpDecode.
Require Import WkEntryEff.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelDecode00 KernelDecode01 KernelDecode04 KernelDecode06 KernelDecode07
  KernelDecode11 KernelDecode12 KernelDecode13 KernelDecode14 KernelDecode15
  KernelDecode17 KernelDecode20 KernelDecode21 KernelDecode24 KernelDecode31.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* [WpDecodeBridge.decode_bridge_ms_bv]'s closing recipe: a bare
   [vm_compute; reflexivity] can fail on a decoded AST whose bitvector leaves
   carry a DIFFERENT (but propositionally equal) well-formedness proof term
   than the hand-written literal's; [bv_eq] closes exactly that gap. *)
Local Ltac vm_refl :=
  vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].

(* ====================================================================== *)
(** ** 1. Kernel-image byte-window facts (reuses [WkEntryEff.kb_win]).

    The window word is [kb_word_at A] -- literally the four bytes at
    [A..A+3], so ONE helper covers every alignment case.  Unlike
    [WkStartAux]'s [stw_NN] literals these need not be closed numerals: the
    word never reaches a leaf's unifier, because [winstr_m] hides the
    [FetchResult] behind an existential and only the 16-bit RVC encoding (a
    literal, below) is passed on. *)

Lemma tikb_9 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x0 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x0)) j).
Proof. kb_win. Qed.
Lemma tikb_10 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x2)) j).
Proof. kb_win. Qed.
Lemma tikb_11 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x4 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x4)) j).
Proof. kb_win. Qed.
Lemma tikb_12 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x6 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x6)) j).
Proof. kb_win. Qed.
Lemma tikb_13 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x8 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x30a027f3 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_14 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0xc + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0xc)) j).
Proof. kb_win. Qed.
Lemma tikb_15 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0xe + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0xe)) j).
Proof. kb_win. Qed.
Lemma tikb_16 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x10 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x10)) j).
Proof. kb_win. Qed.
Lemma tikb_17 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x12 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x30a79073 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_18 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x16 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x306027f3 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_19 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x1a + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x0027e793 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_20 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x1e + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x30679073 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_21 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x22 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0xc01027f3 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_22 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x26 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x000f4737 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_23 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2a + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x24070713 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_24 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x2e + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x2e)) j).
Proof. kb_win. Qed.
Lemma tikb_25 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x30 + Z.of_nat j)
  = Some (nth_byte (mword_of_int 0x14d79073 : mword 32) j).
Proof. kb_win. Qed.
Lemma tikb_26 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x34 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x34)) j).
Proof. kb_win. Qed.
Lemma tikb_27 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x36 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x36)) j).
Proof. kb_win. Qed.
Lemma tikb_28 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x38 + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x38)) j).
Proof. kb_win. Qed.
Lemma tikb_29 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.timerinit + 0x3a + Z.of_nat j)
  = Some (nth_byte (kb_word_at (KernelSyms.timerinit + 0x3a)) j).
Proof. kb_win. Qed.

(* ====================================================================== *)
(** ** 2. Decode facts at the concrete reference state [dstateM].

    A BASE instruction needs [tigood_NN] / [tidec_NN]; an RVC one needs
    those two about the compressed encoding plus [tilpad_NN] (the
    intermediate compressed AST is not a landing pad), [tigoodexp_NN] (its
    expansion reads no register) and [tiexp_NN] (what it expands to). *)

(* ---- 9. c.addi sp, -16 ---- *)
Lemma tigood_9 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_9 :
  exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) dstateM
  = Some (C_ADDI (i9, Regidx csp_rs1), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_9 : is_lpad_instruction (C_ADDI (i9, Regidx csp_rs1)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_9 : forall s : mstate,
  goodb0 D_none (execute (C_ADDI (i9, Regidx csp_rs1))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_9 : forall s : mstate,
  exec (execute (C_ADDI (i9, Regidx csp_rs1))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)), s).
Proof. exact (exec_execute_C_ADDI i9 (Regidx csp_rs1)). Qed.

(* ---- 10. c.sdsp ra, 8(sp) ---- *)
Lemma tigood_10 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_10 :
  exec (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) dstateM
  = Some (C_SDSP (u10, Regidx ti_ra), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_10 : is_lpad_instruction (C_SDSP (u10, Regidx ti_ra)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_10 : forall s : mstate,
  goodb0 D_none (execute (C_SDSP (u10, Regidx ti_ra))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_10 : forall s : mstate,
  exec (execute (C_SDSP (u10, Regidx ti_ra))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u10 ('b"000")),
                            Regidx ti_ra, Regidx csp_rs1, 8)), s).
Proof. exact (exec_execute_C_SDSP u10 (Regidx ti_ra)). Qed.

(* ---- 11. c.sdsp s0, 0(sp) ---- *)
Lemma tigood_11 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_11 :
  exec (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) dstateM
  = Some (C_SDSP (u11, Regidx ti_s0), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_11 : is_lpad_instruction (C_SDSP (u11, Regidx ti_s0)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_11 : forall s : mstate,
  goodb0 D_none (execute (C_SDSP (u11, Regidx ti_s0))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_11 : forall s : mstate,
  exec (execute (C_SDSP (u11, Regidx ti_s0))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec u11 ('b"000")),
                            Regidx ti_s0, Regidx csp_rs1, 8)), s).
Proof. exact (exec_execute_C_SDSP u11 (Regidx ti_s0)). Qed.

(* ---- 12. c.addi4spn s0, sp, 16 ---- *)
Lemma tigood_12 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_12 :
  exec (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) dstateM
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_12 :
  is_lpad_instruction (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_12 : forall s : mstate,
  goodb0 D_none (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_12 : forall s : mstate,
  exec (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s
  = Some (ExecuteAs (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)), s).
Proof.
  intro s. rewrite (exec_execute_C_ADDI4SPN (Cregidx (mword_of_int 0)) nz12).
  repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].
Qed.

(* ---- 13. csrr a5, menvcfg ---- *)
Lemma tigood_13 :
  goodb0 D_m (ext_decode (mword_of_int 0x30a027f3 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_13 :
  exec (ext_decode (mword_of_int 0x30a027f3 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_refl. Qed.

(* ---- 14. c.li a4, -1 ---- *)
Lemma tigood_14 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x577d : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_14 :
  exec (ext_decode_compressed (mword_of_int 0x577d : mword 16)) dstateM
  = Some (C_LI (i14, Regidx ti_a4), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_14 : is_lpad_instruction (C_LI (i14, Regidx ti_a4)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_14 : forall s : mstate,
  goodb0 D_none (execute (C_LI (i14, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_14 : forall s : mstate,
  exec (execute (C_LI (i14, Regidx ti_a4))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI)), s).
Proof.
  intro s. rewrite (exec_execute_C_LI i14 (Regidx ti_a4)).
  repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].
Qed.

(* ---- 15. c.slli a4, 63 ---- *)
Lemma tigood_15 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x177e : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_15 :
  exec (ext_decode_compressed (mword_of_int 0x177e : mword 16)) dstateM
  = Some (C_SLLI (sh15, Regidx ti_a4), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_15 : is_lpad_instruction (C_SLLI (sh15, Regidx ti_a4)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_15 : forall s : mstate,
  goodb0 D_none (execute (C_SLLI (sh15, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_15 : forall s : mstate,
  exec (execute (C_SLLI (sh15, Regidx ti_a4))) s
  = Some (ExecuteAs (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)), s).
Proof. exact (exec_execute_C_SLLI sh15 (Regidx ti_a4)). Qed.

(* ---- 16. c.or a5, a4 ---- *)
Lemma tigood_16 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_16 :
  exec (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16)) dstateM
  = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_16 :
  is_lpad_instruction (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_16 : forall s : mstate,
  goodb0 D_none (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_16 : forall s : mstate,
  exec (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)), s).
Proof.
  intro s. rewrite (exec_execute_C_OR (Cregidx (mword_of_int 7)) (Cregidx (mword_of_int 6))).
  repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ].
Qed.

(* ---- 17. csrw menvcfg, a5 ---- *)
Lemma tigood_17 :
  goodb0 D_m (ext_decode (mword_of_int 0x30a79073 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_17 :
  exec (ext_decode (mword_of_int 0x30a79073 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_refl. Qed.

(* ---- 18. csrr a5, mcounteren ---- *)
Lemma tigood_18 :
  goodb0 D_m (ext_decode (mword_of_int 0x306027f3 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_18 :
  exec (ext_decode (mword_of_int 0x306027f3 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_refl. Qed.

(* ---- 19. ori a5, a5, 2 ---- *)
Lemma tigood_19 :
  goodb0 D_m (ext_decode (mword_of_int 0x0027e793 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_19 :
  exec (ext_decode (mword_of_int 0x0027e793 : mword 32)) dstateM
  = Some (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI), dstateM).
Proof. vm_refl. Qed.

(* ---- 20. csrw mcounteren, a5 ---- *)
Lemma tigood_20 :
  goodb0 D_m (ext_decode (mword_of_int 0x30679073 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_20 :
  exec (ext_decode (mword_of_int 0x30679073 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_refl. Qed.

(* ---- 21. csrr a5, time ---- *)
Lemma tigood_21 :
  goodb0 D_m (ext_decode (mword_of_int 0xc01027f3 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_21 :
  exec (ext_decode (mword_of_int 0xc01027f3 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_refl. Qed.

(* ---- 22. lui a4, 0xf4 ---- *)
Lemma tigood_22 :
  goodb0 D_m (ext_decode (mword_of_int 0x000f4737 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_22 :
  exec (ext_decode (mword_of_int 0x000f4737 : mword 32)) dstateM
  = Some (UTYPE (i22, Regidx ti_a4, LUI), dstateM).
Proof. vm_refl. Qed.

(* ---- 23. addi a4, a4, 576 ---- *)
Lemma tigood_23 :
  goodb0 D_m (ext_decode (mword_of_int 0x24070713 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_23 :
  exec (ext_decode (mword_of_int 0x24070713 : mword 32)) dstateM
  = Some (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI), dstateM).
Proof. vm_refl. Qed.

(* ---- 24. c.add a5, a4 ---- *)
Lemma tigood_24 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_24 :
  exec (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) dstateM
  = Some (C_ADD (Regidx ti_a5, Regidx ti_a4), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_24 : is_lpad_instruction (C_ADD (Regidx ti_a5, Regidx ti_a4)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_24 : forall s : mstate,
  goodb0 D_none (execute (C_ADD (Regidx ti_a5, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_24 : forall s : mstate,
  exec (execute (C_ADD (Regidx ti_a5, Regidx ti_a4))) s
  = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)), s).
Proof. exact (exec_execute_C_ADD (Regidx ti_a5) (Regidx ti_a4)). Qed.

(* ---- 25. csrw stimecmp, a5 ---- *)
Lemma tigood_25 :
  goodb0 D_m (ext_decode (mword_of_int 0x14d79073 : mword 32)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_25 :
  exec (ext_decode (mword_of_int 0x14d79073 : mword 32)) dstateM
  = Some (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_refl. Qed.

(* ---- 26. c.ldsp ra, 8(sp) ---- *)
Lemma tigood_26 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_26 :
  exec (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) dstateM
  = Some (C_LDSP (u10, Regidx ti_ra), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_26 : is_lpad_instruction (C_LDSP (u10, Regidx ti_ra)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_26 : forall s : mstate,
  goodb0 D_none (execute (C_LDSP (u10, Regidx ti_ra))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_26 : forall s : mstate,
  exec (execute (C_LDSP (u10, Regidx ti_ra))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")),
                           Regidx csp_rs1, Regidx ti_ra, false, 8)), s).
Proof. exact (exec_execute_C_LDSP u10 (Regidx ti_ra)). Qed.

(* ---- 27. c.ldsp s0, 0(sp) ---- *)
Lemma tigood_27 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_27 :
  exec (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) dstateM
  = Some (C_LDSP (u11, Regidx ti_s0), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_27 : is_lpad_instruction (C_LDSP (u11, Regidx ti_s0)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_27 : forall s : mstate,
  goodb0 D_none (execute (C_LDSP (u11, Regidx ti_s0))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_27 : forall s : mstate,
  exec (execute (C_LDSP (u11, Regidx ti_s0))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")),
                           Regidx csp_rs1, Regidx ti_s0, false, 8)), s).
Proof. exact (exec_execute_C_LDSP u11 (Regidx ti_s0)). Qed.

(* ---- 28. c.addi sp, 16 ---- *)
Lemma tigood_28 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_28 :
  exec (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) dstateM
  = Some (C_ADDI (i28, Regidx csp_rs1), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_28 : is_lpad_instruction (C_ADDI (i28, Regidx csp_rs1)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_28 : forall s : mstate,
  goodb0 D_none (execute (C_ADDI (i28, Regidx csp_rs1))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_28 : forall s : mstate,
  exec (execute (C_ADDI (i28, Regidx csp_rs1))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI)), s).
Proof. exact (exec_execute_C_ADDI i28 (Regidx csp_rs1)). Qed.

(* ---- 29. c.ret ---- *)
Lemma tigood_29 :
  goodb0 D_m (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) dstateM = true.
Proof. vm_refl. Qed.
Lemma tidec_29 :
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) dstateM
  = Some (C_JR (Regidx ti_ra), dstateM).
Proof. vm_refl. Qed.
Lemma tilpad_29 : is_lpad_instruction (C_JR (Regidx ti_ra)) = false.
Proof. reflexivity. Qed.
Lemma tigoodexp_29 : forall s : mstate,
  goodb0 D_none (execute (C_JR (Regidx ti_ra))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.
Lemma tiexp_29 : forall s : mstate,
  exec (execute (C_JR (Regidx ti_ra))) s
  = Some (ExecuteAs (JALR (zeros' 12, Regidx ti_ra, zreg)), s).
Proof. exact (exec_execute_C_JR (Regidx ti_ra)). Qed.

(* ====================================================================== *)
(** ** 3. THE PER-INSTRUCTION TOKENS ([WeakLeafM.winstr_m]).

    One [iPoseProof] per instruction at the call site, and no decode fact is
    ever named above this file.  The RVC ones feed [winstr_m_of_text] the
    two decode shapes as TERMS (the ∀-state one is [kd_<hex>] plus the
    expansion; the reference-state one is §2's four facts); the base ones
    need only the two §2 facts. *)

Section WkTimerinitTokens.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* 9. c.addi sp, -16   (timerinit + 0x0) *)
  Lemma wsti_9 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc9 true
      (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc9 (F_RVC (mword_of_int 0x1141))
              (kb_word_at (KernelSyms.timerinit + 0x0))
              (ITYPE (sign_extend' 12 i9, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDI (i9, Regidx csp_rs1))
                 (conj (kd_1141 t HC) (conj tilpad_9 tiexp_9)))
              (conj tigood_9
                 (ex_intro _ (C_ADDI (i9, Regidx csp_rs1))
                    (conj tidec_9 (conj tilpad_9 (conj tigoodexp_9 tiexp_9)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x0)
      (kb_word_at (KernelSyms.timerinit + 0x0)) Hcov tikb_9).
  Qed.

  (* 10. c.sdsp ra, 8(sp)   (timerinit + 0x2) *)
  Lemma wsti_10 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc10 true
      (STORE (zero_extend' 12 (concat_vec u10 ('b"000")),
              Regidx ti_ra, Regidx csp_rs1, 8)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc10 (F_RVC (mword_of_int 0xe406))
              (kb_word_at (KernelSyms.timerinit + 0x2))
              (STORE (zero_extend' 12 (concat_vec u10 ('b"000")),
                      Regidx ti_ra, Regidx csp_rs1, 8))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_SDSP (u10, Regidx ti_ra))
                 (conj (kd_e406 t HC) (conj tilpad_10 tiexp_10)))
              (conj tigood_10
                 (ex_intro _ (C_SDSP (u10, Regidx ti_ra))
                    (conj tidec_10 (conj tilpad_10 (conj tigoodexp_10 tiexp_10)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2)
      (kb_word_at (KernelSyms.timerinit + 0x2)) Hcov tikb_10).
  Qed.

  (* 11. c.sdsp s0, 0(sp)   (timerinit + 0x4) *)
  Lemma wsti_11 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc11 true
      (STORE (zero_extend' 12 (concat_vec u11 ('b"000")),
              Regidx ti_s0, Regidx csp_rs1, 8)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc11 (F_RVC (mword_of_int 0xe022))
              (kb_word_at (KernelSyms.timerinit + 0x4))
              (STORE (zero_extend' 12 (concat_vec u11 ('b"000")),
                      Regidx ti_s0, Regidx csp_rs1, 8))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_SDSP (u11, Regidx ti_s0))
                 (conj (kd_e022 t HC) (conj tilpad_11 tiexp_11)))
              (conj tigood_11
                 (ex_intro _ (C_SDSP (u11, Regidx ti_s0))
                    (conj tidec_11 (conj tilpad_11 (conj tigoodexp_11 tiexp_11)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x4)
      (kb_word_at (KernelSyms.timerinit + 0x4)) Hcov tikb_11).
  Qed.

  (* 12. c.addi4spn s0, sp, 16   (timerinit + 0x6) *)
  Lemma wsti_12 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc12 true
      (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc12 (F_RVC (mword_of_int 0x0800))
              (kb_word_at (KernelSyms.timerinit + 0x6))
              (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1, Regidx ti_s0, ADDI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ =>
                 ex_intro _ (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))
                   (conj (kd_0800 t HC) (conj tilpad_12 tiexp_12)))
              (conj tigood_12
                 (ex_intro _ (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))
                    (conj tidec_12 (conj tilpad_12 (conj tigoodexp_12 tiexp_12)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x6)
      (kb_word_at (KernelSyms.timerinit + 0x6)) Hcov tikb_12).
  Qed.

  (* 13. csrr a5, menvcfg   (timerinit + 0x8) *)
  Lemma wsti_13 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc13 false
      (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc13 (F_Base (mword_of_int 0x30a027f3))
              (mword_of_int 0x30a027f3)
              (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_30a027f3 t Hmi Hcfg)
              (conj tigood_13 tidec_13)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x8)
      (mword_of_int 0x30a027f3) Hcov tikb_13).
  Qed.

  (* 14. c.li a4, -1   (timerinit + 0xc) *)
  Lemma wsti_14 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc14 true
      (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc14 (F_RVC (mword_of_int 0x577d))
              (kb_word_at (KernelSyms.timerinit + 0xc))
              (ITYPE (sign_extend' 12 i14, Regidx cli_rs1, Regidx ti_a4, ADDI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_LI (i14, Regidx ti_a4))
                 (conj (kd_577d t HC) (conj tilpad_14 tiexp_14)))
              (conj tigood_14
                 (ex_intro _ (C_LI (i14, Regidx ti_a4))
                    (conj tidec_14 (conj tilpad_14 (conj tigoodexp_14 tiexp_14)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0xc)
      (kb_word_at (KernelSyms.timerinit + 0xc)) Hcov tikb_14).
  Qed.

  (* 15. c.slli a4, 63   (timerinit + 0xe) *)
  Lemma wsti_15 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc15 true (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc15 (F_RVC (mword_of_int 0x177e))
              (kb_word_at (KernelSyms.timerinit + 0xe))
              (SHIFTIOP (sh15, Regidx ti_a4, Regidx ti_a4, SLLI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_SLLI (sh15, Regidx ti_a4))
                 (conj (kd_177e t HC) (conj tilpad_15 tiexp_15)))
              (conj tigood_15
                 (ex_intro _ (C_SLLI (sh15, Regidx ti_a4))
                    (conj tidec_15 (conj tilpad_15 (conj tigoodexp_15 tiexp_15)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0xe)
      (kb_word_at (KernelSyms.timerinit + 0xe)) Hcov tikb_15).
  Qed.

  (* 16. c.or a5, a4   (timerinit + 0x10) *)
  Lemma wsti_16 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc16 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc16 (F_RVC (mword_of_int 0x8fd9))
              (kb_word_at (KernelSyms.timerinit + 0x10))
              (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ =>
                 ex_intro _ (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
                   (conj (kd_8fd9 t HC) (conj tilpad_16 tiexp_16)))
              (conj tigood_16
                 (ex_intro _ (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
                    (conj tidec_16 (conj tilpad_16 (conj tigoodexp_16 tiexp_16)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x10)
      (kb_word_at (KernelSyms.timerinit + 0x10)) Hcov tikb_16).
  Qed.

  (* 17. csrw menvcfg, a5   (timerinit + 0x12) *)
  Lemma wsti_17 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc17 false
      (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc17 (F_Base (mword_of_int 0x30a79073))
              (mword_of_int 0x30a79073)
              (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_30a79073 t Hmi Hcfg)
              (conj tigood_17 tidec_17)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x12)
      (mword_of_int 0x30a79073) Hcov tikb_17).
  Qed.

  (* 18. csrr a5, mcounteren   (timerinit + 0x16) *)
  Lemma wsti_18 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc18 false
      (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc18 (F_Base (mword_of_int 0x306027f3))
              (mword_of_int 0x306027f3)
              (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_306027f3 t Hmi Hcfg)
              (conj tigood_18 tidec_18)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x16)
      (mword_of_int 0x306027f3) Hcov tikb_18).
  Qed.

  (* 19. ori a5, a5, 2   (timerinit + 0x1a) *)
  Lemma wsti_19 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc19 false (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc19 (F_Base (mword_of_int 0x0027e793))
              (mword_of_int 0x0027e793)
              (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_0027e793 t Hmi Hcfg)
              (conj tigood_19 tidec_19)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x1a)
      (mword_of_int 0x0027e793) Hcov tikb_19).
  Qed.

  (* 20. csrw mcounteren, a5   (timerinit + 0x1e) *)
  Lemma wsti_20 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc20 false
      (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc20 (F_Base (mword_of_int 0x30679073))
              (mword_of_int 0x30679073)
              (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_30679073 t Hmi Hcfg)
              (conj tigood_20 tidec_20)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x1e)
      (mword_of_int 0x30679073) Hcov tikb_20).
  Qed.

  (* 21. csrr a5, time   (timerinit + 0x22) *)
  Lemma wsti_21 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc21 false
      (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc21 (F_Base (mword_of_int 0xc01027f3))
              (mword_of_int 0xc01027f3)
              (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_c01027f3 t Hmi Hcfg)
              (conj tigood_21 tidec_21)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x22)
      (mword_of_int 0xc01027f3) Hcov tikb_21).
  Qed.

  (* 22. lui a4, 0xf4   (timerinit + 0x26) *)
  Lemma wsti_22 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc22 false (UTYPE (i22, Regidx ti_a4, LUI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc22 (F_Base (mword_of_int 0x000f4737))
              (mword_of_int 0x000f4737)
              (UTYPE (i22, Regidx ti_a4, LUI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_000f4737 t Hmi Hcfg)
              (conj tigood_22 tidec_22)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x26)
      (mword_of_int 0x000f4737) Hcov tikb_22).
  Qed.

  (* 23. addi a4, a4, 576   (timerinit + 0x2a) *)
  Lemma wsti_23 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc23 false (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc23 (F_Base (mword_of_int 0x24070713))
              (mword_of_int 0x24070713)
              (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_24070713 t Hmi Hcfg)
              (conj tigood_23 tidec_23)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2a)
      (mword_of_int 0x24070713) Hcov tikb_23).
  Qed.

  (* 24. c.add a5, a4   (timerinit + 0x2e) *)
  Lemma wsti_24 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc24 true (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc24 (F_RVC (mword_of_int 0x97ba))
              (kb_word_at (KernelSyms.timerinit + 0x2e))
              (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, ADD))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_ADD (Regidx ti_a5, Regidx ti_a4))
                 (conj (kd_97ba t HC) (conj tilpad_24 tiexp_24)))
              (conj tigood_24
                 (ex_intro _ (C_ADD (Regidx ti_a5, Regidx ti_a4))
                    (conj tidec_24 (conj tilpad_24 (conj tigoodexp_24 tiexp_24)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x2e)
      (kb_word_at (KernelSyms.timerinit + 0x2e)) Hcov tikb_24).
  Qed.

  (* 25. csrw stimecmp, a5   (timerinit + 0x30) *)
  Lemma wsti_25 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc25 false
      (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc25 (F_Base (mword_of_int 0x14d79073))
              (mword_of_int 0x14d79073)
              (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [reflexivity | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ _ _ Hmi Hcfg => kd_14d79073 t Hmi Hcfg)
              (conj tigood_25 tidec_25)
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x30)
      (mword_of_int 0x14d79073) Hcov tikb_25).
  Qed.

  (* 26. c.ldsp ra, 8(sp)   (timerinit + 0x34) *)
  Lemma wsti_26 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc26 true
      (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")),
             Regidx csp_rs1, Regidx ti_ra, false, 8)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc26 (F_RVC (mword_of_int 0x60a2))
              (kb_word_at (KernelSyms.timerinit + 0x34))
              (LOAD (zero_extend' 12 (concat_vec u10 ('b"000")),
                     Regidx csp_rs1, Regidx ti_ra, false, 8))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_LDSP (u10, Regidx ti_ra))
                 (conj (kd_60a2 t HC) (conj tilpad_26 tiexp_26)))
              (conj tigood_26
                 (ex_intro _ (C_LDSP (u10, Regidx ti_ra))
                    (conj tidec_26 (conj tilpad_26 (conj tigoodexp_26 tiexp_26)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x34)
      (kb_word_at (KernelSyms.timerinit + 0x34)) Hcov tikb_26).
  Qed.

  (* 27. c.ldsp s0, 0(sp)   (timerinit + 0x36) *)
  Lemma wsti_27 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc27 true
      (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")),
             Regidx csp_rs1, Regidx ti_s0, false, 8)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc27 (F_RVC (mword_of_int 0x6402))
              (kb_word_at (KernelSyms.timerinit + 0x36))
              (LOAD (zero_extend' 12 (concat_vec u11 ('b"000")),
                     Regidx csp_rs1, Regidx ti_s0, false, 8))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_LDSP (u11, Regidx ti_s0))
                 (conj (kd_6402 t HC) (conj tilpad_27 tiexp_27)))
              (conj tigood_27
                 (ex_intro _ (C_LDSP (u11, Regidx ti_s0))
                    (conj tidec_27 (conj tilpad_27 (conj tigoodexp_27 tiexp_27)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x36)
      (kb_word_at (KernelSyms.timerinit + 0x36)) Hcov tikb_27).
  Qed.

  (* 28. c.addi sp, 16   (timerinit + 0x38) *)
  Lemma wsti_28 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc28 true
      (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc28 (F_RVC (mword_of_int 0x0141))
              (kb_word_at (KernelSyms.timerinit + 0x38))
              (ITYPE (sign_extend' 12 i28, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDI (i28, Regidx csp_rs1))
                 (conj (kd_0141 t HC) (conj tilpad_28 tiexp_28)))
              (conj tigood_28
                 (ex_intro _ (C_ADDI (i28, Regidx csp_rs1))
                    (conj tidec_28 (conj tilpad_28 (conj tigoodexp_28 tiexp_28)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x38)
      (kb_word_at (KernelSyms.timerinit + 0x38)) Hcov tikb_28).
  Qed.

  (* 29. c.ret   (timerinit + 0x3a) *)
  Lemma wsti_29 (kbs : _) :
    wkb_covers kbs ->
    wkernel_text kbs -∗
    winstr_m ti_pc29 true (JALR (zeros' 12, Regidx ti_ra, zreg)).
  Proof.
    intros Hcov. iIntros "Ht".
    iApply (winstr_m_of_text kbs ti_pc29 (F_RVC (mword_of_int 0x8082))
              (kb_word_at (KernelSyms.timerinit + 0x3a))
              (JALR (zeros' 12, Regidx ti_ra, zreg))
              ltac:(vm_compute; reflexivity)
              ltac:(apply acc_wf_of_leb; vm_compute; reflexivity)
              ltac:(ram_win)
              ltac:(split; [apply bv_eq; vm_compute; reflexivity
                           | vm_compute; reflexivity])
              ltac:(reflexivity)
              (fun t _ HC _ _ _ => ex_intro _ (C_JR (Regidx ti_ra))
                 (conj (kd_8082 t HC) (conj tilpad_29 tiexp_29)))
              (conj tigood_29
                 (ex_intro _ (C_JR (Regidx ti_ra))
                    (conj tidec_29 (conj tilpad_29 (conj tigoodexp_29 tiexp_29)))))
              with "Ht").
    iPureIntro. exact (wkb_window kbs (KernelSyms.timerinit + 0x3a)
      (kb_word_at (KernelSyms.timerinit + 0x3a)) Hcov tikb_29).
  Qed.

End WkTimerinitTokens.
