(** * WkStartAux.v -- the per-instruction SCAFFOLDING of the weak [start()]
      chain: the 39 encoding words, their kernel-image byte windows, the
      decode facts at [dstateM], and the small register/RAM drivers.

    Split out of [WkStartNew.v] (which now holds only the theorem) for the
    reason [WkEntryEff]/[WkEntryNew] were split: the [vm_compute]-heavy
    decode layer is STABLE, while the proof script above it is iterated --
    and a whole-file recompile of the two together is minutes per edit.
    Nothing here is weak-memory-specific; it is the [CodeStartAux] vocabulary
    re-derived in the [winstr]/[goodb0] shapes the weak leaves consume. *)

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
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WeakLeafWin.
Require Import WeakLeafEff8 WeakLeafLd8.
Require Import ExecCommon WpDecode WpAuipc WpMmodeJal WpMmodeMul.
Require Import WpGprCsrrCommon WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMretWp.
Require Import StackOwn WpTimerinit.
Require Import WkStackOwn WkGprAcc.
Require Import WeakLeafSdspOff WeakLeafTor.
Require Import WeakLeafItype WeakLeafUtypeShift WeakLeafRtypeW WeakLeafJump.
Require Import WeakLeafCsrrM WeakLeafCsrw WeakLeafCsrw2 WeakLeafCsrw3.
Require Import WeakLeafPmpcfg0 WeakLeafMret.
Require Import CodeEntry CodeEntryAux KernelText.
Require Import KernelDecode00 KernelDecode01 KernelDecode02 KernelDecode03 KernelDecode04.
Require Import KernelDecode05 KernelDecode06 KernelDecode07 KernelDecode08 KernelDecode09.
Require Import KernelDecode10 KernelDecode11 KernelDecode12 KernelDecode13 KernelDecode14.
Require Import KernelDecode15 KernelDecode16 KernelDecode17 KernelDecode18 KernelDecode19.
Require Import KernelDecode20 KernelDecode21 KernelDecode22 KernelDecode23 KernelDecode24.
Require Import KernelDecode25 KernelDecode26 KernelDecode27 KernelDecode28 KernelDecode29.
Require Import KernelDecode30 KernelDecode31.
Require Import CodeStart CodeStartAux WpStartNew MbootVocab CodeTimerinitAux.
Require Import MstatusFacts StackOwn.
Require Import WkEntryEff.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. Per-instruction encoding words

    [kb_word_at A] (KernelText.v) is the 32-bit little-endian word starting
    AT [A] -- for an RVC instruction this is NOT the 4-aligned "containing"
    word, it is literally the 4 bytes at [A]..[A+3] (the real fetch window),
    so ONE helper covers every alignment case uniformly. *)

(* THE WORDS ARE CLOSED LITERALS, NOT [kb_word_at] APPLICATIONS -- and this is
   a PERFORMANCE invariant, not a style choice.  [kb_word_at A] is a lookup in
   the whole [KernelInstrs.kernel_bytes] map; [vm_compute] dispatches it in
   microseconds, but the UNIFIER inside [iApply] reduces with lazy conversion,
   and a leaf application whose fetch word is such a term makes every
   unification step walk that map.  Measured: one [wwp_addi_rvc_leaf] with
   [h := subrange_vec_dec (kb_word_at ...) 15 0] did not finish in 10 minutes;
   the same call with [h := mword_of_int 0x1141] takes seconds.  ([WkTimerinit]
   uses literals throughout for this reason.)  The tie back to the image is
   [stkb_NN] below, whose [kb_win] proof is a [vm_compute] and so is cheap. *)
Definition stw_30 : mword 32 := mword_of_int 0xE4061141.  (* start + 0x0 *)
Definition stw_31 : mword 32 := mword_of_int 0xE022E406.  (* start + 0x2 *)
Definition stw_32 : mword 32 := mword_of_int 0x800E022.  (* start + 0x4 *)
Definition stw_33 : mword 32 := mword_of_int 0x27F30800.  (* start + 0x6 *)
Definition stw_34 : mword 32 := mword_of_int 0x300027F3.  (* start + 0x8 *)
Definition stw_35 : mword 32 := mword_of_int 0x7137779.  (* start + 0xc *)
Definition stw_36 : mword 32 := mword_of_int 0x7FF70713.  (* start + 0xe *)
Definition stw_37 : mword 32 := mword_of_int 0x67058FF9.  (* start + 0x12 *)
Definition stw_38 : mword 32 := mword_of_int 0x7136705.  (* start + 0x14 *)
Definition stw_39 : mword 32 := mword_of_int 0x80070713.  (* start + 0x16 *)
Definition stw_40 : mword 32 := mword_of_int 0x90738FD9.  (* start + 0x1a *)
Definition stw_41 : mword 32 := mword_of_int 0x30079073.  (* start + 0x1c *)
Definition stw_42 : mword 32 := mword_of_int 0x1797.  (* start + 0x20 *)
Definition stw_43 : mword 32 := mword_of_int 0xE0678793.  (* start + 0x24 *)
Definition stw_44 : mword 32 := mword_of_int 0x34179073.  (* start + 0x28 *)
Definition stw_45 : mword 32 := mword_of_int 0x90734781.  (* start + 0x2c *)
Definition stw_46 : mword 32 := mword_of_int 0x18079073.  (* start + 0x2e *)
Definition stw_47 : mword 32 := mword_of_int 0x17FD67C1.  (* start + 0x32 *)
Definition stw_48 : mword 32 := mword_of_int 0x907317FD.  (* start + 0x34 *)
Definition stw_49 : mword 32 := mword_of_int 0x30279073.  (* start + 0x36 *)
Definition stw_50 : mword 32 := mword_of_int 0x30379073.  (* start + 0x3a *)
Definition stw_51 : mword 32 := mword_of_int 0x104027F3.  (* start + 0x3e *)
Definition stw_52 : mword 32 := mword_of_int 0x2207E793.  (* start + 0x42 *)
Definition stw_53 : mword 32 := mword_of_int 0x10479073.  (* start + 0x46 *)
Definition stw_54 : mword 32 := mword_of_int 0x83A957FD.  (* start + 0x4a *)
Definition stw_55 : mword 32 := mword_of_int 0x907383A9.  (* start + 0x4c *)
Definition stw_56 : mword 32 := mword_of_int 0x3B079073.  (* start + 0x4e *)
Definition stw_57 : mword 32 := mword_of_int 0x907347BD.  (* start + 0x52 *)
Definition stw_58 : mword 32 := mword_of_int 0x3A079073.  (* start + 0x54 *)
Definition stw_ae0 : mword 32 := mword_of_int 0x30A027F3.  (* start + 0x58 *)
Definition stw_ae1 : mword 32 := mword_of_int 0x17764705.  (* start + 0x5c *)
Definition stw_ae2 : mword 32 := mword_of_int 0x8FD91776.  (* start + 0x5e *)
Definition stw_ae3 : mword 32 := mword_of_int 0x90738FD9.  (* start + 0x60 *)
Definition stw_ae4 : mword 32 := mword_of_int 0x30A79073.  (* start + 0x62 *)
Definition stw_59 : mword 32 := mword_of_int 0xF5FFF0EF.  (* start + 0x66 *)
Definition stw_60 : mword 32 := mword_of_int 0xF14027F3.  (* start + 0x6a *)
Definition stw_61 : mword 32 := mword_of_int 0x823E2781.  (* start + 0x6e *)
Definition stw_62 : mword 32 := mword_of_int 0x73823E.  (* start + 0x70 *)
Definition stw_63 : mword 32 := mword_of_int 0x30200073.  (* start + 0x72 *)

(* the 16-bit halfword of each RVC instruction (low half of its fetch window) *)
Definition sth_30 : mword 16 := mword_of_int 0x1141.
Definition sth_31 : mword 16 := mword_of_int 0xE406.
Definition sth_32 : mword 16 := mword_of_int 0xE022.
Definition sth_33 : mword 16 := mword_of_int 0x800.
Definition sth_35 : mword 16 := mword_of_int 0x7779.
Definition sth_37 : mword 16 := mword_of_int 0x8FF9.
Definition sth_38 : mword 16 := mword_of_int 0x6705.
Definition sth_40 : mword 16 := mword_of_int 0x8FD9.
Definition sth_45 : mword 16 := mword_of_int 0x4781.
Definition sth_47 : mword 16 := mword_of_int 0x67C1.
Definition sth_48 : mword 16 := mword_of_int 0x17FD.
Definition sth_54 : mword 16 := mword_of_int 0x57FD.
Definition sth_55 : mword 16 := mword_of_int 0x83A9.
Definition sth_57 : mword 16 := mword_of_int 0x47BD.
Definition sth_ae1 : mword 16 := mword_of_int 0x4705.
Definition sth_ae2 : mword 16 := mword_of_int 0x1776.
Definition sth_ae3 : mword 16 := mword_of_int 0x8FD9.
Definition sth_61 : mword 16 := mword_of_int 0x2781.
Definition sth_62 : mword 16 := mword_of_int 0x823E.


(* ====================================================================== *)
(** ** 1. Kernel-image byte-window facts (reuses [WkEntryEff.kb_win]) *)

Lemma stkb_30 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x0 + Z.of_nat j) = Some (nth_byte stw_30 j).
Proof. kb_win. Qed.
Lemma stkb_31 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x2 + Z.of_nat j) = Some (nth_byte stw_31 j).
Proof. kb_win. Qed.
Lemma stkb_32 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x4 + Z.of_nat j) = Some (nth_byte stw_32 j).
Proof. kb_win. Qed.
Lemma stkb_33 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x6 + Z.of_nat j) = Some (nth_byte stw_33 j).
Proof. kb_win. Qed.
Lemma stkb_34 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x8 + Z.of_nat j) = Some (nth_byte stw_34 j).
Proof. kb_win. Qed.
Lemma stkb_35 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0xc + Z.of_nat j) = Some (nth_byte stw_35 j).
Proof. kb_win. Qed.
Lemma stkb_36 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0xe + Z.of_nat j) = Some (nth_byte stw_36 j).
Proof. kb_win. Qed.
Lemma stkb_37 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x12 + Z.of_nat j) = Some (nth_byte stw_37 j).
Proof. kb_win. Qed.
Lemma stkb_38 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x14 + Z.of_nat j) = Some (nth_byte stw_38 j).
Proof. kb_win. Qed.
Lemma stkb_39 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x16 + Z.of_nat j) = Some (nth_byte stw_39 j).
Proof. kb_win. Qed.
Lemma stkb_40 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x1a + Z.of_nat j) = Some (nth_byte stw_40 j).
Proof. kb_win. Qed.
Lemma stkb_41 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x1c + Z.of_nat j) = Some (nth_byte stw_41 j).
Proof. kb_win. Qed.
Lemma stkb_42 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x20 + Z.of_nat j) = Some (nth_byte stw_42 j).
Proof. kb_win. Qed.
Lemma stkb_43 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x24 + Z.of_nat j) = Some (nth_byte stw_43 j).
Proof. kb_win. Qed.
Lemma stkb_44 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x28 + Z.of_nat j) = Some (nth_byte stw_44 j).
Proof. kb_win. Qed.
Lemma stkb_45 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x2c + Z.of_nat j) = Some (nth_byte stw_45 j).
Proof. kb_win. Qed.
Lemma stkb_46 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x2e + Z.of_nat j) = Some (nth_byte stw_46 j).
Proof. kb_win. Qed.
Lemma stkb_47 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x32 + Z.of_nat j) = Some (nth_byte stw_47 j).
Proof. kb_win. Qed.
Lemma stkb_48 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x34 + Z.of_nat j) = Some (nth_byte stw_48 j).
Proof. kb_win. Qed.
Lemma stkb_49 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x36 + Z.of_nat j) = Some (nth_byte stw_49 j).
Proof. kb_win. Qed.
Lemma stkb_50 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x3a + Z.of_nat j) = Some (nth_byte stw_50 j).
Proof. kb_win. Qed.
Lemma stkb_51 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x3e + Z.of_nat j) = Some (nth_byte stw_51 j).
Proof. kb_win. Qed.
Lemma stkb_52 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x42 + Z.of_nat j) = Some (nth_byte stw_52 j).
Proof. kb_win. Qed.
Lemma stkb_53 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x46 + Z.of_nat j) = Some (nth_byte stw_53 j).
Proof. kb_win. Qed.
Lemma stkb_54 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x4a + Z.of_nat j) = Some (nth_byte stw_54 j).
Proof. kb_win. Qed.
Lemma stkb_55 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x4c + Z.of_nat j) = Some (nth_byte stw_55 j).
Proof. kb_win. Qed.
Lemma stkb_56 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x4e + Z.of_nat j) = Some (nth_byte stw_56 j).
Proof. kb_win. Qed.
Lemma stkb_57 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x52 + Z.of_nat j) = Some (nth_byte stw_57 j).
Proof. kb_win. Qed.
Lemma stkb_58 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x54 + Z.of_nat j) = Some (nth_byte stw_58 j).
Proof. kb_win. Qed.
Lemma stkb_ae0 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x58 + Z.of_nat j) = Some (nth_byte stw_ae0 j).
Proof. kb_win. Qed.
Lemma stkb_ae1 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x5c + Z.of_nat j) = Some (nth_byte stw_ae1 j).
Proof. kb_win. Qed.
Lemma stkb_ae2 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x5e + Z.of_nat j) = Some (nth_byte stw_ae2 j).
Proof. kb_win. Qed.
Lemma stkb_ae3 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x60 + Z.of_nat j) = Some (nth_byte stw_ae3 j).
Proof. kb_win. Qed.
Lemma stkb_ae4 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x62 + Z.of_nat j) = Some (nth_byte stw_ae4 j).
Proof. kb_win. Qed.
Lemma stkb_59 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x66 + Z.of_nat j) = Some (nth_byte stw_59 j).
Proof. kb_win. Qed.
Lemma stkb_60 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x6a + Z.of_nat j) = Some (nth_byte stw_60 j).
Proof. kb_win. Qed.
Lemma stkb_61 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x6e + Z.of_nat j) = Some (nth_byte stw_61 j).
Proof. kb_win. Qed.
Lemma stkb_62 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x70 + Z.of_nat j) = Some (nth_byte stw_62 j).
Proof. kb_win. Qed.
Lemma stkb_63 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms.start + 0x72 + Z.of_nat j) = Some (nth_byte stw_63 j).
Proof. kb_win. Qed.

(* ====================================================================== *)
(** ** 2. Decode facts at the concrete reference state [dstateM], and the
    RVC intermediate-instruction witnesses.  Base instructions need only
    [stdec_NN]/[stgood_NN]; RVC instructions additionally need [stlpad_NN]
    (the intermediate compressed AST is never a landing pad) and
    [stgoodexp_NN] (its expansion reads no register).

    NOTE: raw [vm_compute; reflexivity] on the WHOLE [exec (...) dstateM]
    equation occasionally fails with a spurious "Unable to unify" whose two
    sides print IDENTICALLY (a universe-residue artifact of re-elaborating
    the Sail [exec] monad fresh against the fully-unfolded [dstateM] record;
    reproduced in isolation -- confirmed NOT a real term mismatch). The
    robust fix, used only where the raw form fails (recorded per-site
    below): apply the EXISTING generic [kd_<hex>] lemma AT [dstateM] instead
    of re-deriving the equation from scratch. *)

Lemma st_misaC_dstateM :
  eq_vec (_get_Misa_C (register_lookup misa dstateM.(sregs))) ('b"1") = true.
Proof. vm_compute. reflexivity. Qed.

(* THE ROBUST FIX (found by bisection): a raw [vm_compute; reflexivity] over
   the WHOLE [exec md dst = Some (target, dst)] equation can fail this way
   when a [goodb0]/[exec] fact about the SAME underlying decode already
   exists elsewhere in the file (order-independent; reproduced in isolation;
   the printed terms are byte-identical, so it is a universe-elaboration
   artifact, not a real mismatch). Splitting the check into a BOOLEAN
   instruction-equality decision ([bool_decide], which only needs
   [instruction]'s decidable equality, not [mstate]'s -- [mstate] has no
   [EqDecision], being record of functions) plus a plain state-equality
   check sidesteps it completely. Use this whenever the raw one-shot
   [vm_compute; reflexivity] fails; both conjuncts are STILL cheap
   [vm_compute]s, just against Bool/mstate instead of the option pair. *)
Lemma decode_pair_of_bool (md : M instruction) (s0 target : instruction) (dst : mstate) :
  bool_decide (match exec md dst with Some (i, _) => i | None => s0 end = target) = true ->
  (match exec md dst with Some (_, s) => s | None => dst end) = dst ->
  s0 <> target ->
  exec md dst = Some (target, dst).
Proof.
  intros Hi Hs Hne. apply bool_decide_eq_true in Hi.
  destruct (exec md dst) as [p|] eqn:E.
  - destruct p as [i s]. cbn in Hi, Hs. rewrite Hi Hs. reflexivity.
  - cbn in Hi. exfalso. apply Hne. exact Hi.
Qed.

(* ---- 30: c.addi sp,-16 (C_ADDI) ---- *)
Lemma stdec_30 : exec (ext_decode_compressed sth_30) dstateM
  = Some (C_ADDI (i9, Regidx csp_rs1), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_30 : goodb0 D_m (ext_decode_compressed sth_30) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_30 : is_lpad_instruction (C_ADDI (i9, Regidx csp_rs1)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_30 : forall s, goodb0 D_none (execute (C_ADDI (i9, Regidx csp_rs1))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 31: c.sdsp ra,8(sp) (C_SDSP) ---- *)
Lemma stdec_31 : exec (ext_decode_compressed sth_31) dstateM
  = Some (C_SDSP (u10, Regidx ti_ra), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_31 : goodb0 D_m (ext_decode_compressed sth_31) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_31 : is_lpad_instruction (C_SDSP (u10, Regidx ti_ra)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_31 : forall s, goodb0 D_none (execute (C_SDSP (u10, Regidx ti_ra))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 32: c.sdsp s0,0(sp) (C_SDSP) ---- *)
Lemma stdec_32 : exec (ext_decode_compressed sth_32) dstateM
  = Some (C_SDSP (u11, Regidx ti_s0), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_32 : goodb0 D_m (ext_decode_compressed sth_32) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_32 : is_lpad_instruction (C_SDSP (u11, Regidx ti_s0)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_32 : forall s, goodb0 D_none (execute (C_SDSP (u11, Regidx ti_s0))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 33: c.addi4spn s0,sp,16 (C_ADDI4SPN) ---- *)
Lemma stdec_33 : exec (ext_decode_compressed sth_33) dstateM
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_33 : goodb0 D_m (ext_decode_compressed sth_33) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_33 : is_lpad_instruction (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_33 : forall s,
  goodb0 D_none (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 34: csrr a5,mstatus (BASE) ---- *)
Lemma stdec_34 : exec (ext_decode stw_34) dstateM
  = Some (CSRReg (WpGprCsrrA.csr_mstatus, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_34 : goodb0 D_m (ext_decode stw_34) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 35: c.lui a4,0xffffe (C_LUI) ---- *)
Lemma stdec_35 : exec (ext_decode_compressed sth_35) dstateM
  = Some (C_LUI (si35, Regidx ti_a4), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_35 : goodb0 D_m (ext_decode_compressed sth_35) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_35 : is_lpad_instruction (C_LUI (si35, Regidx ti_a4)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_35 : forall s, goodb0 D_none (execute (C_LUI (si35, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 36: addi a4,a4,2047 (BASE) ---- *)
Lemma stdec_36 : exec (ext_decode stw_36) dstateM
  = Some (ITYPE (si36, Regidx ti_a4, Regidx ti_a4, ADDI), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_36 : goodb0 D_m (ext_decode stw_36) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 37: c.and a5,a4 (C_AND) ---- *)
Lemma stdec_37 : exec (ext_decode_compressed sth_37) dstateM
  = Some (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_37 : goodb0 D_m (ext_decode_compressed sth_37) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_37 : is_lpad_instruction
  (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_37 : forall s,
  goodb0 D_none (execute (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 38: c.lui a4,1 (C_LUI) ---- *)
Lemma stdec_38 : exec (ext_decode_compressed sth_38) dstateM
  = Some (C_LUI (si38, Regidx ti_a4), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_38 : goodb0 D_m (ext_decode_compressed sth_38) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_38 : is_lpad_instruction (C_LUI (si38, Regidx ti_a4)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_38 : forall s, goodb0 D_none (execute (C_LUI (si38, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 39: addi a4,a4,-2048 (BASE) ---- *)
Lemma stdec_39 : exec (ext_decode stw_39) dstateM
  = Some (ITYPE (si39, Regidx ti_a4, Regidx ti_a4, ADDI), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_39 : goodb0 D_m (ext_decode stw_39) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 40: c.or a5,a4 (C_OR, via [ke_8fd9]) ---- *)
Lemma stdec_40 : exec (ext_decode_compressed sth_40) dstateM
  = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_40 : goodb0 D_m (ext_decode_compressed sth_40) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_40 : is_lpad_instruction
  (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_40 : forall s,
  goodb0 D_none (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 41: csrw mstatus,a5 (BASE, config funnel) ---- *)
Lemma stdec_41 : exec (ext_decode stw_41) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_mstatus, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_41 : goodb0 D_m (ext_decode stw_41) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 42: auipc a5,1 (BASE) ---- *)
Lemma stdec_42 : exec (ext_decode stw_42) dstateM
  = Some (UTYPE (si42, Regidx ti_a5, AUIPC), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_42 : goodb0 D_m (ext_decode stw_42) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 43: addi a5,a5,-506 (BASE) ---- *)
Lemma stdec_43 : exec (ext_decode stw_43) dstateM
  = Some (ITYPE (si43, Regidx ti_a5, Regidx ti_a5, ADDI), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_43 : goodb0 D_m (ext_decode stw_43) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 44: csrw mepc,a5 (BASE) ---- *)
Lemma stdec_44 : exec (ext_decode stw_44) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_mepc, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_44 : goodb0 D_m (ext_decode stw_44) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 45: c.li a5,0 (C_LI) ---- *)
Lemma stdec_45 : exec (ext_decode_compressed sth_45) dstateM
  = Some (C_LI (si45, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_45 : goodb0 D_m (ext_decode_compressed sth_45) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_45 : is_lpad_instruction (C_LI (si45, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_45 : forall s, goodb0 D_none (execute (C_LI (si45, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 46: csrw satp,a5 (BASE) ---- *)
Lemma stdec_46 : exec (ext_decode stw_46) dstateM
  = Some (CSRReg (WpGprCsrwB.csr_satp, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_46 : goodb0 D_m (ext_decode stw_46) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 47: c.lui a5,0x10 (C_LUI) ---- *)
Lemma stdec_47 : exec (ext_decode_compressed sth_47) dstateM
  = Some (C_LUI (si47, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_47 : goodb0 D_m (ext_decode_compressed sth_47) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_47 : is_lpad_instruction (C_LUI (si47, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_47 : forall s, goodb0 D_none (execute (C_LUI (si47, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 48: c.addi a5,-1 (C_ADDI) ---- *)
Lemma stdec_48 : exec (ext_decode_compressed sth_48) dstateM
  = Some (C_ADDI (si48, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_48 : goodb0 D_m (ext_decode_compressed sth_48) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_48 : is_lpad_instruction (C_ADDI (si48, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_48 : forall s, goodb0 D_none (execute (C_ADDI (si48, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 49: csrw medeleg,a5 (BASE) ---- *)
Lemma stdec_49 : exec (ext_decode stw_49) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_medeleg, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_49 : goodb0 D_m (ext_decode stw_49) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 50: csrw mideleg,a5 (BASE) ---- *)
Lemma stdec_50 : exec (ext_decode stw_50) dstateM
  = Some (CSRReg (WpGprCsrwB.csr_mideleg, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_50 : goodb0 D_m (ext_decode stw_50) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 51: csrr a5,sie (BASE) ---- *)
Lemma stdec_51 : exec (ext_decode stw_51) dstateM
  = Some (CSRReg (WpGprCsrrB.csr_sie, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_51 : goodb0 D_m (ext_decode stw_51) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 52: ori a5,a5,544 (BASE) ---- *)
Lemma stdec_52 : exec (ext_decode stw_52) dstateM
  = Some (ITYPE (si52, Regidx ti_a5, Regidx ti_a5, ORI), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_52 : goodb0 D_m (ext_decode stw_52) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 53: csrw sie,a5 (BASE) ---- *)
Lemma stdec_53 : exec (ext_decode stw_53) dstateM
  = Some (CSRReg (WpGprCsrwB.csr_sie, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_53 : goodb0 D_m (ext_decode stw_53) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 54: c.li a5,-1 (C_LI) ---- *)
Lemma stdec_54 : exec (ext_decode_compressed sth_54) dstateM
  = Some (C_LI (si54, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_54 : goodb0 D_m (ext_decode_compressed sth_54) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_54 : is_lpad_instruction (C_LI (si54, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_54 : forall s, goodb0 D_none (execute (C_LI (si54, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 55: c.srli a5,10 (C_SRLI) ---- *)
Lemma stdec_55 : exec (ext_decode_compressed sth_55) dstateM
  = Some (C_SRLI (ssh55, Cregidx (mword_of_int 7)), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_55 : goodb0 D_m (ext_decode_compressed sth_55) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_55 : is_lpad_instruction (C_SRLI (ssh55, Cregidx (mword_of_int 7))) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_55 : forall s,
  goodb0 D_none (execute (C_SRLI (ssh55, Cregidx (mword_of_int 7)))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 56: csrw pmpaddr0,a5 (BASE) ---- *)
Lemma stdec_56 : exec (ext_decode stw_56) dstateM
  = Some (CSRReg (WpGprCsrwB.csr_pmpaddr0, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_56 : goodb0 D_m (ext_decode stw_56) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 57: c.li a5,15 (C_LI) ---- *)
Lemma stdec_57 : exec (ext_decode_compressed sth_57) dstateM
  = Some (C_LI (si57, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_57 : goodb0 D_m (ext_decode_compressed sth_57) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_57 : is_lpad_instruction (C_LI (si57, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_57 : forall s, goodb0 D_none (execute (C_LI (si57, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 58: csrw pmpcfg0,a5 (BASE, config funnel) ---- *)
Lemma stdec_58 : exec (ext_decode stw_58) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_pmpcfg0, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_58 : goodb0 D_m (ext_decode stw_58) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- ae0: csrr a5,menvcfg (BASE) ---- *)
Lemma stdec_ae0 : exec (ext_decode stw_ae0) dstateM
  = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_ae0 : goodb0 D_m (ext_decode stw_ae0) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- ae1: c.li a4,1 (C_LI) ---- *)
Lemma stdec_ae1 : exec (ext_decode_compressed sth_ae1) dstateM
  = Some (C_LI (sae_li, Regidx ti_a4), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_ae1 : goodb0 D_m (ext_decode_compressed sth_ae1) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_ae1 : is_lpad_instruction (C_LI (sae_li, Regidx ti_a4)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_ae1 : forall s, goodb0 D_none (execute (C_LI (sae_li, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- ae2: c.slli a4,0x3d (C_SLLI) ---- *)
Lemma stdec_ae2 : exec (ext_decode_compressed sth_ae2) dstateM
  = Some (C_SLLI (sae_slli, Regidx ti_a4), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_ae2 : goodb0 D_m (ext_decode_compressed sth_ae2) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_ae2 : is_lpad_instruction (C_SLLI (sae_slli, Regidx ti_a4)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_ae2 : forall s, goodb0 D_none (execute (C_SLLI (sae_slli, Regidx ti_a4))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- ae3: c.or a5,a4 (C_OR, via [ke_8fd9]) ---- *)
Lemma stdec_ae3 : exec (ext_decode_compressed sth_ae3) dstateM
  = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_ae3 : goodb0 D_m (ext_decode_compressed sth_ae3) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_ae3 : is_lpad_instruction
  (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6))) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_ae3 : forall s,
  goodb0 D_none (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- ae4: csrw menvcfg,a5 (BASE) ---- *)
Lemma stdec_ae4 : exec (ext_decode stw_ae4) dstateM
  = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_ae4 : goodb0 D_m (ext_decode stw_ae4) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 59: jal ra,timerinit (BASE) ---- *)
Lemma stdec_59 : exec (ext_decode stw_59) dstateM
  = Some (JAL (sjimm59, Regidx ti_ra), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_59 : goodb0 D_m (ext_decode stw_59) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 60: csrr a5,mhartid (BASE) ---- *)
Lemma stdec_60 : exec (ext_decode stw_60) dstateM
  = Some (CSRReg (ExecCommon.csr_csrr, zreg, Regidx ti_a5, CSRRS), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_60 : goodb0 D_m (ext_decode stw_60) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 61: c.addiw a5,0 (C_ADDIW) ---- *)
Lemma stdec_61 : exec (ext_decode_compressed sth_61) dstateM
  = Some (C_ADDIW (si61, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_61 : goodb0 D_m (ext_decode_compressed sth_61) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_61 : is_lpad_instruction (C_ADDIW (si61, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_61 : forall s, goodb0 D_none (execute (C_ADDIW (si61, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 62: c.mv tp,a5 (C_MV) ---- *)
Lemma stdec_62 : exec (ext_decode_compressed sth_62) dstateM
  = Some (C_MV (Regidx st_tp, Regidx ti_a5), dstateM).
Proof.
  apply (decode_pair_of_bool _ (MRET tt)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - discriminate.
Qed.
Lemma stgood_62 : goodb0 D_m (ext_decode_compressed sth_62) dstateM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stlpad_62 : is_lpad_instruction (C_MV (Regidx st_tp, Regidx ti_a5)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma stgoodexp_62 : forall s, goodb0 D_none (execute (C_MV (Regidx st_tp, Regidx ti_a5))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(* ---- 63: mret (BASE, config funnel) ---- *)
Lemma stdec_63 : exec (ext_decode stw_63) dstateM = Some (MRET tt, dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma stgood_63 : goodb0 D_m (ext_decode stw_63) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(* ====================================================================== *)
(** ** 3. Small RAM/alignment/register-nonzero facts, off [WkEntryEff]'s
    generic tactics. *)

(* [WpStartNew]'s register-map drivers are [Local Ltac]s, so they do not
   travel with the [st_m*] definitions they unfold -- re-declared here
   verbatim (the [ti_*] half is needed too, since [st_mti] is built on
   [ti_mout]). *)
Ltac st_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

Ltac st_look :=
  repeat first [ rewrite upd_eq
               | rewrite upd_ne; [ | st_reg_neq ] ];
  first [ reflexivity | assumption ].

Ltac st_unfold :=
  unfold st_mout, st_m61, st_m60, st_mti, st_m59,
         st_m_ae3, st_m_ae2, st_m_ae1, st_m_ae0, st_m57, st_m55, st_m54,
         st_m52, st_m51, st_m48, st_m47, st_m45, st_m43, st_m42, st_m40,
         st_m39, st_m38, st_m37, st_m36, st_m35, st_m34, st_m33, st_m30,
         ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

Ltac st_ram4 :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; destruct j as [|[|[|[|]]]];
  [ram_lit|ram_lit|ram_lit|ram_lit|exfalso; lia].

Ltac st_ram8 :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; destruct j as [|[|[|[|[|[|[|[|]]]]]]]];
  [ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|ram_lit|exfalso; lia].

(* the [agree] hypothesis every leaf wants is [agree_m_regs] with its middle
   two arguments swapped (WkEntryNew's finding: the leaf's own order is
   cur_privilege/misa/mseccfg, [agree_m_regs]'s is cur_privilege/mseccfg/misa) --
   inlined at each call site as [(fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)]. *)

(* A [c.sdsp]/store leaf takes the base+data GPR cells SEPARATELY
   ([WkGprAcc.gpr_file_acc_2]); a store never touches the GPR file, so the
   two cells come back at THE SAME values and must be folded back into the
   untouched [gpr_file] -- a genuine (funext) equality, since [regfile] is a
   raw function, not a [gmap]. *)
Lemma rf_upd2_same (f : regfile) (k1 k2 : regidx) (v1 v2 : mword 64) :
  k1 <> k2 -> f !!! k1 = v1 -> f !!! k2 = v2 -> <[k1 := v1]> (<[k2 := v2]> f) = f.
Proof.
  intros Hne H1 H2. apply functional_extensionality. intro j.
  unfold insert, regfile_insert, rf_upd.
  destruct (bool_decide (j = k1)) eqn:E1.
  - apply bool_decide_eq_true in E1. subst j. rewrite rf_lookup in H1. exact (eq_sym H1).
  - destruct (bool_decide (j = k2)) eqn:E2.
    + apply bool_decide_eq_true in E2. subst j. rewrite rf_lookup in H2. exact (eq_sym H2).
    + reflexivity.
Qed.
