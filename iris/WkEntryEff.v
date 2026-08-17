(** * WkEntryEff.v — the [_entry] boot chain's WEAK-TIER pure layer (M4 batch 4)

    The weak twin of the [_entry] cone needs, per instruction, exactly what
    the porting guide (claude-notes/projects/weak-memory-porting.md §2g) says
    a leaf needs — and for a REGISTER-ONLY instruction the whole per-shape
    price collapses to ONE new fact: the [execute]'s [exec_eff] mirror with
    the EMPTY trace.  With it,

      - the certificate is [WeakEff.wcert_nowrite] at the fetch-only trace
        (a register-only instruction's step trace IS the fetch read(s)), with
        [Q := wQ_pure] — the log does not move, so the state interpretation
        crosses the step by two rewrites;
      - the [wP_eff] obligation is the appropriate fetch-arm lemma
        ([WeakFetchEff.wP_eff_of_leaf_base] / [WeakFetchRvc.wP_eff_of_leaf_rvc4]
        / [WeakFetch2.wP_eff_of_leaf_base2] / [_rvc2]) at [es_x := []], whose
        premise (c) the mirror discharges at every [b] because it is
        state-generic;
      - the funnel's own [exec] fact is [WeakCert.exec_eff_exec] of the same
        mirror at the flat state.

    This file holds the PURE half: the seven register-only [exec_eff] mirrors
    (§2 — each is its SC twin's script with the [exec_eff_*] combinators of
    [WeakEff]/[WeakLeafEffCommon] substituted name-for-name), the small
    literal dischargers (§1), and the [_entry] chain's per-instruction static
    facts (§3: kernel-image bytes, decodes at the concrete reference state
    [WpDecodeBridge.dstateM], landing-pad/alignment/goodb0 facts).  The Iris
    half — the leaf compositions and the whole-[_entry] theorem — is
    [WkEntryNew.v].

    Import discipline: NO [SailStdpp.Base] and no top-level
    [Import SailStdpp.Values] above the one [gmap Arch.pa] definition
    ([wkb_covers]) — the binder-position Countable-instance trap (durable
    notes; [WeakLeafWin.v] header). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase WpDecodeBridge.
Require Import ExecCommon WpDecode WpAuipc WpMmodeJal WpMmodeMul WpGprCsrrCommon WpGprCsrrA.
Require Import CodeEntry CodeEntryAux.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelText.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The weak kernel-image coverage predicate

    The weak text resource is [WeakInstr.wkernel_text kbs] over an
    [Arch.pa]-keyed byte map; the dumped image [KernelInstrs.kernel_bytes] is
    [Z]-keyed.  [wkb_covers kbs] is the seam: every image byte is in [kbs] at
    its physical address.  (Defined ABOVE the [Values] import — the
    Countable-instance trap.) *)

Definition wkb_covers (kbs : gmap Arch.pa (bv 8)) : Prop :=
  forall (A : Z) (b : bv 8),
    KernelInstrs.kernel_bytes !! A = Some b ->
    kbs !! (SailStdpp.Values.mword_of_int A : Arch.pa) = Some b.

(** A 4-byte window of the image, transported to the [Arch.pa] map. *)
Lemma wkb_window (kbs : gmap Arch.pa (bv 8)) (A : Z)
    (w : SailStdpp.Values.mword 32) :
  wkb_covers kbs ->
  (forall j : nat, (j < 4)%nat ->
     KernelInstrs.kernel_bytes !! (A + Z.of_nat j) = Some (nth_byte w j)) ->
  forall j : nat, (j < 4)%nat ->
    kbs !! pa_add (SailStdpp.Values.mword_of_int A : Arch.pa) j
    = Some (nth_byte w j).
Proof.
  intros Hcov Hb j Hj. rewrite pa_add_mword. exact (Hcov _ _ (Hb j Hj)).
Qed.

Import SailStdpp.Values.
Import Defs.

(* ====================================================================== *)
(** ** 1. Literal dischargers *)

Lemma acc_wf_of_leb (a : Arch.pa) (n : N) :
  (pa_z a + Z.of_N n <=? 18446744073709551616) = true -> acc_wf a n.
Proof. intro H. unfold acc_wf. apply Z.leb_le. exact H. Qed.

Lemma addr_is_ram_of_leb (a : Arch.pa) :
  andb (ram_base <=? uint a) (uint a <? ram_base + ram_size) = true ->
  addr_is_ram a.
Proof.
  intro H. apply andb_prop in H as [H1 H2]. unfold addr_is_ram.
  split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Ltac ram_lit := apply addr_is_ram_of_leb; vm_compute; reflexivity.

(** RAM facts for a 4-byte window at a concrete address. *)
Ltac ram_win :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj;
  destruct j as [|[|[|[|]]]]; [ram_lit|ram_lit|ram_lit|ram_lit|exfalso; lia].

(** The Machine decode read-set never contains the [minstret_increment]
    flag — the [D (R_bool minstret_increment) = false] premise of every
    fetch-arm lemma. *)
Lemma D_m_mi : D_m (R_bool minstret_increment) = false.
Proof. vm_compute. reflexivity. Qed.

(** [WpDecodeBridge.agree_m], restated at a bare register file — the shape
    the fetch-arm lemmas' agreement premise takes at [wm_regs σ]. *)
Lemma agree_m_regs (rs : Riscv.rv64d_types.regstate) :
  register_lookup cur_privilege rs = Machine ->
  register_lookup mseccfg rs = mword_of_int 0 ->
  register_lookup misa rs = MISA_C ->
  forall r, D_m r = true ->
    register_lookup r rs = register_lookup r (sregs dstateM).
Proof.
  intros H1 H2 H3.
  exact (agree_m (MState rs ∅ DevModel.dev0_state) H1 H2 H3).
Qed.

(** misa-bit facts off the pinned whole value. *)
Lemma misaC_of_val (rs : Riscv.rv64d_types.regstate) :
  register_lookup misa rs = MISA_C ->
  eq_vec (_get_Misa_C (register_lookup misa rs)) ('b"1") = true.
Proof. intros ->. vm_compute. reflexivity. Qed.

Lemma misaA_of_val (rs : Riscv.rv64d_types.regstate) :
  register_lookup misa rs = MISA_C ->
  eq_vec (_get_Misa_A (register_lookup misa rs)) ('b"1") = true.
Proof. intros ->. vm_compute. reflexivity. Qed.

Lemma misaM_of_val (rs : Riscv.rv64d_types.regstate) :
  register_lookup misa rs = MISA_C ->
  eq_vec (_get_Misa_M (register_lookup misa rs)) ('b"1") = true.
Proof. intros ->. vm_compute. reflexivity. Qed.

(** One-read no-write traces: [WeakLeafEffCommon.nowrite_read1] (hoisted). *)

(* ====================================================================== *)
(** ** 2. THE SEVEN REGISTER-ONLY [exec_eff] MIRRORS

    Each is its SC twin with the [exec_eff] combinators substituted; every
    trace is [[]].  State-generic, so ONE lemma serves the funnel's flat
    instantiation, the certificate's confined instantiation (at every [b]),
    and the successor register frame. *)

(** *** 2a. The tiny self-run helpers *)

Lemma exec_eff_get_arch_pc s :
  exec_eff (get_arch_pc tt) s
  = Some (register_lookup PC s.(sregs), s, []).
Proof. unfold get_arch_pc. exact (exec_eff_read_reg PC s). Qed.

Lemma exec_eff_set_next_pc (target : mword 64) s :
  exec_eff (set_next_pc target) s = Some (tt, set_reg s nextPC target, []).
Proof.
  unfold set_next_pc. cbn match.
  (* the SYMBOLIC model's branch announcement: silent, empty trace *)
  (* [>>] associates the announce and the [nextPC] write into one silent prefix here *)
  erewrite exec_eff_bind0_nil; [|reflexivity].
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_rX_bits_x0 (i : mword 5) s :
  uint i = 0 -> exec_eff (rX_bits (Regidx i)) s = Some (zero_reg, s, []).
Proof.
  intro H. unfold rX_bits; cbn match. rewrite H. unfold rX.
  replace (Z.eqb 0 0) with true by reflexivity. cbn match.
  apply exec_eff_returnM.
Qed.

(** *** 2b. [jump_to] — the [execR_eff] mirror of [ExecCommon.exec_jump_to] *)

Lemma exec_eff_jump_to (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec target 1) = false ->
  exec_eff (jump_to target) s
  = Some (RETIRE_SUCCESS, set_reg s nextPC target, []).
Proof.
  intros Halign Hbit1.
  unfold jump_to. rewrite exec_eff_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_eff_bind_nil.
      2:{ erewrite execR_eff_bind_nil.
          2:{ apply execR_eff_returnR. }
          rewrite execR_eff_liftR. unfold assert_exp. rewrite Halign.
          cbn match. rewrite exec_eff_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_eff_bind_nil _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_eff_returnR. }
      rewrite Hbit1. cbv iota beta. apply execR_eff_returnR. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_eff_bind_nil _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_eff_liftR. rewrite exec_eff_set_next_pc. reflexivity. }
  rewrite (execR_eff_returnR RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

(** *** 2c. AUIPC / LUI *)

Lemma exec_eff_execute_UTYPE_AUIPC_gpr (rd : mword 5) (imm : mword 20) s :
  exec_eff (execute (UTYPE (imm, Regidx rd, AUIPC))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (add_vec (register_lookup PC s.(sregs)) (auipc_off imm))),
          []).
Proof.
  change (execute (UTYPE (imm, Regidx rd, AUIPC)))
    with (execute_UTYPE imm (Regidx rd) AUIPC).
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (add_vec (register_lookup PC s.(sregs))
                (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_get_arch_pc s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_UTYPE_LUI_gpr (rd : mword 5) (imm : mword 20) s :
  exec_eff (execute (UTYPE (imm, Regidx rd, LUI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (luival imm)),
          []).
Proof.
  change (execute (UTYPE (imm, Regidx rd, LUI)))
    with (execute_UTYPE imm (Regidx rd) LUI).
  unfold execute_UTYPE. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(** *** 2d. ADDI (the C.ADDI expansion's execute) *)

Lemma exec_eff_execute_ITYPE_ADDI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec_eff (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_addi_val rs1 imm s)),
          []).
Proof.
  change (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)))
    with (execute_ITYPE imm (Regidx rs1) (Regidx rd) ADDI).
  unfold execute_ITYPE, gpr_addi_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                       else register_lookup
                              (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(** *** 2e. RTYPE ADD (the C.ADD expansion's execute) *)

Lemma exec_eff_execute_RTYPE_ADD_gpr (rs2 rs1 rd : mword 5) s :
  exec_eff (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_rd_val rs2 rs1 s)),
          []).
Proof.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
  unfold execute_RTYPE, gpr_rd_val. cbn match.
  rewrite (exec_eff_bind_nil _ _ _
             (add_vec
                (if Z.eqb (uint rs1) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                (if Z.eqb (uint rs2) 0 then zero_reg
                 else register_lookup
                        (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
      apply exec_eff_returnm. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  apply exec_eff_returnm.
Qed.

(** *** 2f. MUL *)

Lemma exec_eff_execute_MUL_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec_eff (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_mul_val rs2 rs1 s)),
          []).
Proof.
  intro Hrd. unfold gpr_mul_val.
  change (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)))
    with (execute_MUL (Regidx rs2) (Regidx rs1) (Regidx rd) mulop_mul).
  unfold execute_MUL.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false
    by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_eff_returnm.
Qed.

(** *** 2g. JAL *)

Lemma exec_eff_execute_JAL_gpr (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec
            (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0)
    ('b"0") = true ->
  bit_to_bool (access_vec_dec
                 (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))
                 1) = false ->
  exec_eff (execute (JAL (imm, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC
                     (add_vec (register_lookup PC s.(sregs))
                        (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs))),
          []).
Proof.
  intros Hrd Halign Hbit1.
  change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
  unfold execute_JAL, get_next_pc.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg nextPC s)).
  cbv beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg PC s)).
  cbv beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_jump_to _ s Halign Hbit1)).
  cbv beta iota delta [RETIRE_SUCCESS].
  erewrite exec_eff_bind0_nil.
  2:{ rewrite (exec_eff_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
                 (set_reg s nextPC
                    (add_vec (register_lookup PC s.(sregs))
                       (sign_extend' 64 imm)))).
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
  apply exec_eff_returnm.
Qed.

(** *** 2h. CSRRS a1, mhartid *)

Lemma exec_eff_check_CSR_result_csrr s :
  exec_eff (check_CSR_result csr_csrr Machine CSRRead) s
  = Some (CSR_Check_OK tt, s, []).
Proof.
  unfold check_CSR_result.
  assert (H : check_CSR csr_csrr Machine CSRRead = returnM true)
    by (vm_compute; reflexivity).
  rewrite H.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM true s)).
  exact (exec_eff_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_eff_read_CSR_csrr s :
  exec_eff (read_CSR csr_csrr) s
  = Some (register_lookup mhartid s.(sregs), s, []).
Proof. exact (exec_eff_read_reg (R_bitvector_64 mhartid) s). Qed.

Lemma exec_eff_csr_id_read_callback_csrr s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_csrr d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_csrr d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_CSRReg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (register_lookup mhartid s.(sregs))),
          []).
Proof.
  intros Hrd Hpriv.
  change (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS).
  unfold execute_CSRReg.
  replace (csr_access_type CSRRS (SailStdpp.Instances.generic_eq (Regidx rd) zreg)
             (SailStdpp.Instances.generic_eq zreg zreg)) with CSRRead
    by (replace (SailStdpp.Instances.generic_eq zreg zreg) with true by (vm_compute; reflexivity);
        symmetry; apply csr_access_type_CSRRS_true).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_rX_bits_x0 (zero_extend' 5 ('b"00")) s
                ltac:(vm_compute; reflexivity))).
  unfold doCSR.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_check_CSR_result_csrr s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  replace (not (ext_check_CSR csr_csrr Machine CSRRead)) with false
    by (vm_compute; reflexivity).
  replace (if SailStdpp.Instances.generic_neq CSRRead CSRWrite then read_CSR csr_csrr
           else returnM (zeros' 64))
    with (read_CSR csr_csrr) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_CSR_csrr s)).
  match goal with |- exec_eff (Defs.bind ?D ?K) s = _ =>
    replace D with (returnM (register_lookup mhartid s.(sregs)) : M (mword 64))
      by (vm_compute; reflexivity) end.
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_returnM (register_lookup mhartid s.(sregs)) s)).
  replace (SailStdpp.Instances.generic_eq CSRRead CSRRead) with true by reflexivity.
  assert (Hin : exec_eff
      (Defs.bind0
         (csr_id_read_callback csr_csrr (register_lookup mhartid s.(sregs)))
         (wX_bits (Regidx rd) (register_lookup mhartid s.(sregs)))) s
    = Some (tt,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs))),
            [])).
  { rewrite (exec_eff_bind0_nil _ _ _ _ _
      (exec_eff_csr_id_read_callback_csrr s
         (register_lookup mhartid s.(sregs)))).
    rewrite (exec_eff_wX_bits_gpr rd (register_lookup mhartid s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ Hin).
  apply exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 3. THE [_entry] CHAIN'S STATIC FACTS

    Per instruction: the image bytes of its containing 32-bit word, the
    decode (and, for RVC, the compressed decode) at the concrete reference
    state [dstateM], the [goodb0] read-set witnesses, and the misc literal
    facts.  Every proof is a [vm_compute] against the tracked image
    [KernelInstrs.kernel_bytes]. *)

(** The containing words of the three compressed instructions (the 32-bit
    fetch window includes the following instruction's first half). *)
Definition w_e2 : mword 32 := kb_word_at (KernelSyms._entry + 0x8).
Definition w_e4 : mword 32 := kb_word_at (KernelSyms._entry + 0xe).
Definition w_e6 : mword 32 := kb_word_at (KernelSyms._entry + 0x14).

(** *** 3a. The image bytes, per instruction word *)

Ltac kb_byte :=
  vm_compute;
  first [ reflexivity
        | apply f_equal; apply bv_eq; vm_compute; reflexivity ].

Ltac kb_win :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj;
  destruct j as [|[|[|[|]]]];
  [ kb_byte | kb_byte | kb_byte | kb_byte | exfalso; lia ].

Lemma kb_e0 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x0 + Z.of_nat j)
  = Some (nth_byte w_auipc j).
Proof. kb_win. Qed.

Lemma kb_e1 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x4 + Z.of_nat j)
  = Some (nth_byte w_ld j).
Proof. kb_win. Qed.

Lemma kb_e2 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x8 + Z.of_nat j)
  = Some (nth_byte w_e2 j).
Proof. kb_win. Qed.

Lemma kb_e3 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0xa + Z.of_nat j)
  = Some (nth_byte w_csrr j).
Proof. kb_win. Qed.

Lemma kb_e4 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0xe + Z.of_nat j)
  = Some (nth_byte w_e4 j).
Proof. kb_win. Qed.

Lemma kb_e5 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x10 + Z.of_nat j)
  = Some (nth_byte w_mul j).
Proof. kb_win. Qed.

Lemma kb_e6 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x14 + Z.of_nat j)
  = Some (nth_byte w_e6 j).
Proof. kb_win. Qed.

Lemma kb_e7 : forall j : nat, (j < 4)%nat ->
  KernelInstrs.kernel_bytes !! (KernelSyms._entry + 0x16 + Z.of_nat j)
  = Some (nth_byte w_jal j).
Proof. kb_win. Qed.

(** *** 3b. The RVC halfword extraction / classification facts *)

Lemma sub_e2 : subrange_vec_dec w_e2 15 0 = h_lui.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rvc_e2 : isRVC h_lui = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sub_e4 : subrange_vec_dec w_e4 15 0 = h_addi.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rvc_e4 : isRVC h_addi = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sub_e6 : subrange_vec_dec w_e6 15 0 = h_add.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rvc_e6 : isRVC h_add = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nrvc_e0 : isRVC (subrange_vec_dec w_auipc 15 0) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma nrvc_e1 : isRVC (subrange_vec_dec w_ld 15 0) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma nrvc_e3 : isRVC (subrange_vec_dec w_csrr 15 0) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma nrvc_e5 : isRVC (subrange_vec_dec w_mul 15 0) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma nrvc_e7 : isRVC (subrange_vec_dec w_jal 15 0) = false.
Proof. vm_compute. reflexivity. Qed.

(** *** 3c. The decodes and read-set witnesses at [dstateM] *)

Lemma dec_e0 : exec (ext_decode w_auipc) dstateM
  = Some (UTYPE (imm_auipc, Regidx i_auipc, AUIPC), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e0 : goodb0 D_m (ext_decode w_auipc) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e1 : exec (ext_decode w_ld) dstateM
  = Some (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e1 : goodb0 D_m (ext_decode w_ld) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e2 : exec (ext_decode_compressed h_lui) dstateM
  = Some (C_LUI (imm_clui, rd_clui), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e2 : goodb0 D_m (ext_decode_compressed h_lui) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e3 : exec (ext_decode w_csrr) dstateM
  = Some (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e3 : goodb0 D_m (ext_decode w_csrr) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e4 : exec (ext_decode_compressed h_addi) dstateM
  = Some (C_ADDI (imm_caddi, rsd_caddi), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e4 : goodb0 D_m (ext_decode_compressed h_addi) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e5 : exec (ext_decode w_mul) dstateM
  = Some (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul),
          dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e5 : goodb0 D_m (ext_decode w_mul) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e6 : exec (ext_decode_compressed h_add) dstateM
  = Some (C_ADD (rsd_cadd, rs2_cadd), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e6 : goodb0 D_m (ext_decode_compressed h_add) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_e7 : exec (ext_decode w_jal) dstateM
  = Some (JAL (imm_jal, Regidx i_jal), dstateM).
Proof. vm_compute. reflexivity. Qed.
Lemma good_e7 : goodb0 D_m (ext_decode w_jal) dstateM = true.
Proof. vm_compute. reflexivity. Qed.

(** *** 3d. The RVC expansions' [goodb0] witnesses (no register is read, so
    the read-set is empty) *)

Definition D_none (r : register) : bool := false.

Lemma good_exp_e2 : forall s : mstate,
  goodb0 D_none (execute (C_LUI (imm_clui, rd_clui))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

Lemma good_exp_e4 : forall s : mstate,
  goodb0 D_none (execute (C_ADDI (imm_caddi, rsd_caddi))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

Lemma good_exp_e6 : forall s : mstate,
  goodb0 D_none (execute (C_ADD (rsd_cadd, rs2_cadd))) s = true.
Proof. intro s. vm_compute. reflexivity. Qed.

(** *** 3e. Landing-pad and register-nonzero facts *)

Lemma lpad_e0 : is_lpad_instruction (UTYPE (imm_auipc, Regidx i_auipc, AUIPC))
  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e1 :
  is_lpad_instruction (LOAD (imm_ld, Regidx i_ld, Regidx i_ld, false, 8))
  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e2 :
  is_lpad_instruction (UTYPE (sign_extend' 20 imm_clui, rd_clui, LUI)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e3 :
  is_lpad_instruction (CSRReg (csr_csrr, zreg, Regidx i_rd_csrr, CSRRS))
  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e4 :
  is_lpad_instruction
    (ITYPE (sign_extend' 12 imm_caddi, rsd_caddi, rsd_caddi, ADDI)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e5 :
  is_lpad_instruction
    (MUL (Regidx i_mul_rs2, Regidx i_mul_rs1, Regidx i_mul_rd, mulop_mul))
  = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e6 :
  is_lpad_instruction (RTYPE (rs2_cadd, rsd_cadd, rsd_cadd, ADD)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_e7 : is_lpad_instruction (JAL (imm_jal, Regidx i_jal)) = false.
Proof. vm_compute. reflexivity. Qed.

(** *** 3f. The compressed-C_LUI / C_ADDI / C_ADD lpad facts for the
    [winstr] decode field's intermediate instruction *)

Lemma lpad_i0_e2 : is_lpad_instruction (C_LUI (imm_clui, rd_clui)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_i0_e4 : is_lpad_instruction (C_ADDI (imm_caddi, rsd_caddi)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma lpad_i0_e6 : is_lpad_instruction (C_ADD (rsd_cadd, rs2_cadd)) = false.
Proof. vm_compute. reflexivity. Qed.
