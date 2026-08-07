(** * WeakLeafEffCommon.v — the [exec_eff] kit every shape file shares (M4)

    Batch 1 built four shape files in parallel ([WeakLeafEff8] the 8-byte
    LOAD, [WeakLeafEff8s] the 8-byte STORE, [WeakLeafBase4] both at width 4,
    [WeakLeafAmo4] the M-mode [amoswap.w.aq]), and each of them re-declared
    the same monad-level twins and the same WIDTH-INDEPENDENT register-only
    leaves.  The statements were identical and the shadowing was harmless,
    but it is exactly the near-duplicate family the guiding principle says
    not to keep — and a fifth shape would have made a fifth copy.  This file
    is the single home; the shape files [Require Import] it and declare only
    what is genuinely about their width or their access.

    §0  THE MONAD KIT.  [WeakEff] supplies the twins of [Defs.returnm] /
        [Defs.bind] / [read_reg] / [write_reg]; what is missing, and what
        every mirrored SC script names, is the twin of the model's own
        [returnM] (as opposed to [Defs.returnm] — the two are convertible but
        a SYNTACTIC rewrite must match the [returnM …] that appears in model
        terms), the two short-circuit boolean connectives at the empty trace,
        and the two one-bus-step memory arms — [RiscvFetchExec.exec_MemRead]
        / [_MemWrite]'s twins, which are WHERE THE TRACE ELEMENT IS BORN.

    §1  THE WIDTH-INDEPENDENT LEAVES.  [split_misaligned] (stated width-
        generically here, with the width-8 and width-4 instances the shape
        files use), [translationMode] at Machine/Bare, the three [WpGpr]
        register-file leaves and [ext_data_get_addr] over them, and the
        one-turn [untilMT] loop lemma every [vmem_*_addr] goes through.
        None of them mentions a width or an access kind. *)
From Stdlib Require Import ZArith Zwf.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import ExecCommon.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WpGpr.
(* [have_nom_val], named by the enablement chain's [have_nominal_privLevel]
   mirror (§2 below). *)
Require Import WpGprCsrwCommon.

Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. THE MONAD KIT *)

Lemma exec_eff_returnM {X} (x : X) s :
  exec_eff (returnM x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Lemma exec_eff_and_boolM_nil (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (and_boolM l r) s
  = (if bl then exec_eff r sl else Some (false, sl, [])).
Proof.
  intro H. unfold and_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [reflexivity | apply exec_eff_returnm].
Qed.

Lemma exec_eff_or_boolM_nil (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (or_boolM l r) s
  = (if bl then Some (true, sl, []) else exec_eff r sl).
Proof.
  intro H. unfold or_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [apply exec_eff_returnm | reflexivity].
Qed.

(** The one-bus-step READ, [RiscvFetchExec.exec_MemRead]'s twin: on a RAM
    address the outcome exposes the [read_bytes] match AND emits the read's
    [WEread] in front of the continuation's trace. *)
Lemma exec_eff_MemRead {X} (n : N) (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.ReadReq.pa req) = false ->
  exec_eff (Interface.Next (Interface.MemRead n req) k) s
  = match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
    | Some w =>
        match exec_eff (k (inl (w, None))) s with
        | Some (y, s', es) =>
            Some (y, s',
                  WEread (classify (Interface.ReadReq.access_kind req))
                         (Interface.ReadReq.pa req) n :: es)
        | None => None
        end
    | None => None
    end.
Proof. intros Hd. cbn [exec_eff]. rewrite Hd. reflexivity. Qed.

(** ... and the WRITE, [RiscvFetchExec.exec_MemWrite]'s twin. *)
Lemma exec_eff_MemWrite {X} (n : N) (req : Interface.WriteReq.t n)
    (k : (option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.WriteReq.pa req) = false ->
  exec_eff (Interface.Next (Interface.MemWrite n req) k) s
  = match exec_eff (k (inl None))
            (MState s.(sregs)
               (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                            (Interface.WriteReq.value req)) s.(mdev)) with
    | Some (y, s', es) =>
        Some (y, s', WEwrite (classify (Interface.WriteReq.access_kind req))
                             (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) :: es)
    | None => None
    end.
Proof. intros Hd. cbn [exec_eff]. rewrite Hd. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. THE WIDTH-INDEPENDENT LEAVES *)

(** [split_misaligned] moved DOWN to the PHYSICAL address in the sail bump
    (it used to be the vmem-level split): it now takes the plan's granule
    and splittability, and [CannotSplit] alone decides the unsplit arm —
    the address and the granule never enter into it
    ([RiscvExtras.exec_split_misaligned_unsplit] is the SC original). *)
Lemma exec_eff_split_misaligned_unsplit (addr : mword 64) (width g : Z) s :
  exec_eff (split_misaligned (Physaddr addr) width g CannotSplit) s
  = Some ((1, width), s, []).
Proof.
  unfold split_misaligned.
  change (generic_eq CannotSplit CannotSplit) with true.
  cbn [orb]. apply exec_eff_returnM.
Qed.

(** ... and the vmem level now splits only across a PAGE boundary
    ([split_on_page_boundary]); an in-page access yields (width, 0) — one
    part, nothing beyond the boundary.  Mirrors
    [RiscvExtras.exec_split_on_page_boundary_intra] (pure, register-free,
    so the trace is empty). *)
Lemma exec_eff_split_on_page_boundary_intra {n : Z} (addr : mword n) (width : Z) s :
  eq_vec (and_vec addr (update_subrange_vec_dec ((ones n) : bits n) (pagesize_bits - 1) 0
                          (zeros' (12 - 1 - (0 - 1)))))
         (and_vec (sub_vec_int (add_vec_int addr width) 1)
                  (update_subrange_vec_dec ((ones n) : bits n) (pagesize_bits - 1) 0
                     (zeros' (12 - 1 - (0 - 1))))) = true ->
  exec_eff (split_on_page_boundary addr width) s = Some ((width, 0), s, []).
Proof.
  intro Hin. unfold split_on_page_boundary. rewrite Hin. apply exec_eff_returnM.
Qed.

(** ... and the ALIGNED instance every M-mode leaf uses, width-generic.
    The proof is [RiscvExtras.exec_split_on_page_boundary_aligned]'s,
    verbatim, with the closing [exec_returnm] step at [exec_eff] — copied
    rather than hoisted because factoring the [eq_vec] core out of
    [RiscvExtras] would touch the bottom of the tree for a pure fact only
    this mirror re-needs.  (If [RiscvExtras] ever exposes the [Hintra]
    fact, collapse this to one line.) *)
Lemma exec_eff_split_on_page_boundary_aligned (a : mword 64) (w : Z) s :
  vmem_width w ->
  is_aligned_vaddr (Virtaddr a) w = true ->
  exec_eff (split_on_page_boundary a w) s = Some ((w, 0), s, []).
Proof.
  intros Hw Halign.
  assert (Hpos : 0 < w) by (apply vmem_width_pos; exact Hw).
  assert (Hle : w <= 8) by (apply vmem_width_le; exact Hw).
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  assert (Hal : bv_unsigned a mod w = 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_eq in Halign.
    rewrite uint_unsigned in Halign.
    assert (Hrm : Z.rem (bv_unsigned a) w = (bv_unsigned a) mod w)
      by (apply Z.rem_mod_nonneg; [ exact Hr0 | lia ]).
    rewrite Hrm in Halign. exact Halign. }
  assert (Hnw : bv_unsigned a + (w - 1) < 2 ^ 64)
    by (apply z_alignw_room; assumption).
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1) = bv_unsigned a + (w - 1)).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hww : bv_wrap 64 w = w)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hww. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + w - 1 = bv_unsigned a + (w - 1)) by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0 Hpos; lia | exact Hnw ]. }
  apply exec_eff_split_on_page_boundary_intra.
  apply eq_vec_true_iff. apply bv_eq.
  rewrite !and_vec64_unsigned. rewrite page_mask64_val.
  rewrite Hsub.
  assert (Hnn : 0 <= bv_unsigned a + (w - 1)) by (clear - Hr0 Hpos; lia).
  rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
  rewrite (z_land_pagemask (bv_unsigned a + (w - 1)) Hnn Hnw).
  rewrite <- (z_shiftr12_stable_w (bv_unsigned a) w Hr0 Hw Hal). reflexivity.
Qed.

Lemma exec_eff_split_on_page_boundary_aligned8 (a : mword 64) s :
  is_aligned_vaddr (Virtaddr a) 8 = true ->
  exec_eff (split_on_page_boundary a 8) s = Some ((8, 0), s, []).
Proof.
  apply exec_eff_split_on_page_boundary_aligned.
  unfold vmem_width. tauto.
Qed.

(** *** The [pmaCheck] kit, once — the eff mirror of [RiscvExtras]'s.

    The sail bump made [pmaCheck] answer a PLAN ([result
    Phys_Mem_Access_Info ExceptionType], an early-return body whose tail
    runs [mag_pma_check]), so every shape file's [exec_eff_pmaCheck_*]
    is the same six-step walk [RiscvExtras.pma_ok_peel] does for SC.
    Everything on the path is register-only (one [pma_regions] read), so
    every trace is [[]]. *)

Lemma exec_eff_assert_exp'_true (msg : string) s :
  exec_eff (Defs.assert_exp' true msg) s = Some (eq_refl, s, []).
Proof. unfold Defs.assert_exp'. cbn match. apply exec_eff_returnM. Qed.

Lemma exec_eff_is_mag_applicable_load_data (width : Z) s :
  exec_eff (is_mag_applicable_access (Load Data) width) s
  = Some (Z.leb width xlen_bytes, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_is_mag_applicable_store_data (width : Z) s :
  exec_eff (is_mag_applicable_access (Store Data) width) s
  = Some (Z.leb width xlen_bytes, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_is_mag_applicable_fetch (width : Z) s :
  exec_eff (is_mag_applicable_access (InstructionFetch tt) width) s
  = Some (false, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_is_mag_applicable_amo (op : amoop) (aq rl : bool) (width : Z) s :
  exec_eff (is_mag_applicable_access (Atomic (op, aq, rl, Data, Data)) width) s
  = Some (true, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_mag_pma_check_aligned (pma : PMA) (acc : MemoryAccessType mem_payload)
    (paddr : physaddr) (width : Z) (b : bool) s :
  exec_eff (is_mag_applicable_access acc width) s = Some (b, s, []) ->
  is_aligned_paddr paddr width = true ->
  exec_eff (mag_pma_check pma acc paddr width) s = Some (Ok (CannotSplit, 0), s, []).
Proof.
  intros Hma Halign.
  unfold mag_pma_check.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hma).
  rewrite Halign. cbn [orb]. apply exec_eff_returnM.
Qed.

(** [RiscvExtras.pma_ok_peel]'s eff twin, same four arguments:
    [Hmatch] : matching_pma_region … = Some <the destructed region>
    [Hfield] : the access's PMA permission field = true
    [Hmag]   : exec_eff (is_mag_applicable_access <acc> <width>) s
               = Some (_, s, [])
    [Halign] : is_aligned_paddr <paddr> <width> = true
    The caller destructs the region first, exactly as in SC. *)
Ltac pma_ok_eff_peel Hmatch Hfield Hmag Halign :=
  unfold pmaCheck; rewrite exec_eff_catch_early_return;
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pma_regions _)); cbn beta;
  rewrite Hmatch;
  cbn [PMA_Region_attributes] in Hfield |- *;
  cbn match;
  rewrite execR_eff_bind_eq; rewrite execR_eff_returnR; cbn match beta;
  lazymatch goal with
  | |- context[Defs.assert_exp' _ _] =>
      (* the assert-bind is itself the LEFT operand of the canAccess bind, so
         [execR_eff_liftR_seq] has nothing to match until [execR_eff_bind_eq]
         exposes it *)
      cbn [Riscv.rv64d.not negb];
      rewrite execR_eff_bind_eq;
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ _)); cbn beta;
      rewrite execR_eff_returnR; cbn match beta
  | _ =>
      rewrite execR_eff_bind_eq; rewrite execR_eff_returnR; cbn match beta
  end;
  rewrite Hfield; cbn [Riscv.rv64d.not negb];
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_mag_pma_check_aligned _ _ _ _ _ _ Hmag Halign));
  cbn beta; cbn match; rewrite execR_eff_returnR; cbn [app]; reflexivity.

Lemma exec_eff_translationMode_M s :
  exec_eff (translationMode Machine) s = Some (Bare, s, []).
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

(** *** The register-file leaves ([WpGpr]'s, mirrored). *)

Lemma exec_eff_rX_bits_gpr (i : mword 5) s :
  exec_eff (rX_bits (Regidx i)) s
  = Some (if Z.eqb (uint i) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) s.(sregs), s, []).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold rX_bits, rX. rewrite H. cbn match. apply exec_eff_returnm. }
  all: unfold rX_bits, rX; rewrite H; cbn match; reflexivity.
Qed.

Lemma exec_eff_wX_bits_at (i : mword 5) (r : register_bitvector_64) s (v : mword 64) :
  wX (Regno (uint i)) v
    = Defs.bind0 (Defs.write_reg (R_bitvector_64 r) (regval_into_reg v)) (returnM tt) ->
  exec_eff (wX_bits (Regidx i) v) s
  = Some (tt, set_reg s (R_bitvector_64 r) (regval_into_reg v), []).
Proof.
  intro Heq. unfold wX_bits. rewrite Heq.
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg (R_bitvector_64 r) _ s)).
  apply exec_eff_returnm.
Qed.

Lemma exec_eff_wX_bits_gpr (i : mword 5) (v : mword 64) s :
  exec_eff (wX_bits (Regidx i) v) s
  = Some (tt, if Z.eqb (uint i) 0 then s
              else set_reg s (R_bitvector_64 (gpr_of_Z (uint i))) (regval_into_reg v), []).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold wX_bits, wX. rewrite H. cbn match.
      rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_returnm tt s)). reflexivity. }
  all: rewrite (exec_eff_wX_bits_at i (gpr_of_Z (uint i)) s v ltac:(rewrite H; vm_compute; reflexivity));
       rewrite H; reflexivity.
Qed.

Lemma exec_eff_ext_data_get_addr_gpr (rs1 : mword 5) (offset : mword 64) acc w s :
  exec_eff (ext_data_get_addr (Regidx rs1) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec
      (if Z.eqb (uint rs1) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset)), s, []).
Proof.
  unfold ext_data_get_addr.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  cbn match. apply exec_eff_returnm.
Qed.

(** *** The one-turn [untilMT] loop — every [vmem_*_addr] goes through it,
    at every width and both directions. *)

Lemma execR_eff_untilMT_1 {R Vars} (vars vars' : Vars) (measure : Vars -> Z)
   (cond : Vars -> Defs.monadR R exception bool)
   (body : Vars -> Defs.monadR R exception Vars) s s' es :
  measure vars = 1 ->
  execR_eff (body vars) s = Some (inr vars', s', es) ->
  execR_eff (cond vars') s' = Some (inr true, s', []) ->
  execR_eff (Defs.untilMT vars measure cond body) s = Some (inr vars', s', es).
Proof.
  intros Hm Hb Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge]; [| exfalso; rewrite Hm in Hge; lia ].
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hb).
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hc).
  cbn match. rewrite execR_eff_returnR. cbn match.
  rewrite app_nil_r. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. THE eff ENABLEMENT CHAIN (hoisted from [WeakLeafCsrw] §1a/§1b)

    The [hartSupports] / [currentlyEnabled] cone every CSR-writing (and the
    MRET) [execute] mirror walks: all register-only (one [misa] read at
    most), so every trace is [[]].  Each is its SC twin
    ([WpGprCsrwCommon] / [WpGprCsrwA]) under the usual substitutions.
    ([WeakFetchEff] keeps identical private copies of [_hartSupports_S],
    [_hartSupports_Zicsr] and [_currentlyEnabled_S]; the shadowing is
    harmless because the statements are the same.) *)

Lemma exec_eff_hartSupports_S s :
  exec_eff (hartSupports Ext_S) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_U s :
  exec_eff (hartSupports Ext_U) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_U) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zicsr s :
  exec_eff (hartSupports Ext_Zicsr) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zicfilp s :
  exec_eff (hartSupports Ext_Zicfilp) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Sv32 s :
  exec_eff (hartSupports Ext_Sv32) s = Some (false, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv32) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb false (Z.eqb xlen 32)) with false by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Sv39 s :
  exec_eff (hartSupports Ext_Sv39) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sv39) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_rec_cE_Zicsr_any (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec_eff (_rec_currentlyEnabled Ext_Zicsr k acc) s = Some (true, s, []).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Zicsr.
Qed.

Lemma exec_eff_currentlyEnabled_S s :
  exec_eff (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_S s)).
  cbn match.
  match goal with |- context[Defs.and_boolM ?l _] =>
    assert (Hmb : exec_eff l s
                  = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                            ('b"1"), s, []))
      by (rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s));
          apply exec_eff_returnM);
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hmb)
  end.
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?a] =>
      exact (exec_eff_rec_cE_Zicsr_any k a s ltac:(vm_compute; reflexivity)) end.
  - reflexivity.
Qed.

Lemma exec_eff_currentlyEnabled_U s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_U) s = Some (true, s, []).
Proof.
  intro HU. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_U) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_U s)). cbn match.
  match goal with |- context[Defs.and_boolM ?l _] =>
    assert (Hu : exec_eff l s = Some (true, s, [])) by
      (rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s));
       rewrite (exec_eff_returnM _ s); rewrite HU; reflexivity);
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hu)
  end. cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)); cbn match
  end.
  apply exec_eff_hartSupports_Zicsr.
Qed.

Lemma exec_eff_virtual_memory_supported s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (virtual_memory_supported tt) s = Some (true, s, []).
Proof.
  intro HS. unfold virtual_memory_supported. destruct (Defs.Zwf_guarded _).
  cbn [_rec_virtual_memory_supported]. unfold Defs.assert_exp'.
  replace (Z.geb 3 0) with true by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Sv32 ?k ?a] =>
    assert (H32 : exec_eff (_rec_currentlyEnabled Ext_Sv32 k a) s
                  = Some (false, s, [])) end.
  { match goal with |- exec_eff (_rec_currentlyEnabled Ext_Sv32 ?k ?a) s = _ =>
      destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv32 s)).
    reflexivity. }
  rewrite (exec_eff_or_boolM_nil _ _ _ _ _ H32). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    assert (H39 : exec_eff (_rec_currentlyEnabled Ext_Sv39 k a) s
                  = Some (true, s, [])) end.
  { match goal with |- exec_eff (_rec_currentlyEnabled Ext_Sv39 ?k ?a) s = _ =>
      destruct a end.
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (Z.sub 3 1) 0) with true by reflexivity. cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv39 s)).
    cbn match.
    match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
      assert (HSm : exec_eff (_rec_currentlyEnabled Ext_S k a) s
                    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                              ('b"1"), s, [])) end.
    { match goal with |- exec_eff (_rec_currentlyEnabled Ext_S ?k ?a) s = _ =>
        destruct a end.
      cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
      replace (Z.geb (Z.sub (Z.sub 3 1) 1) 0) with true by reflexivity. cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_S s)).
      cbn match.
      match goal with |- context[Defs.and_boolM ?l _] =>
        assert (Hmb : exec_eff l s
                      = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                                ('b"1"), s, []))
          by (rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s));
              apply exec_eff_returnM);
        rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hmb)
      end.
      destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"))
        eqn:Hb.
      - match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
          exact (exec_eff_rec_cE_Zicsr_any k2 a2 s ltac:(reflexivity)) end.
      - reflexivity. }
    rewrite HSm. rewrite HS. reflexivity. }
  rewrite (exec_eff_or_boolM_nil _ _ _ _ _ H39). reflexivity.
Qed.

Lemma exec_eff_lowest_supported_privLevel s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (lowest_supported_privLevel tt) s = Some (User, s, []).
Proof.
  intro HU. unfold lowest_supported_privLevel.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_U s HU)).
  cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_have_nominal_privLevel (priv : mword 2) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (have_nominal_privLevel priv) s = Some (have_nom_val priv, s, []).
Proof.
  intros HU HS. unfold have_nominal_privLevel, have_nom_val.
  destruct (eq_vec priv ('b"00")) eqn:E0.
  - exact (exec_eff_currentlyEnabled_U s HU).
  - destruct (eq_vec priv ('b"01")) eqn:E1.
    + rewrite (exec_eff_currentlyEnabled_S s). rewrite HS. reflexivity.
    + apply exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 3. The two trace/window nat-helpers every register-only leaf uses
    (hoisted from [WkEntryEff] / [WkEntryNew]; [WeakLeafCsrw] had clones). *)

(** One-read no-write trace (the fetch of a 4-aligned or RVC instruction). *)
Lemma nowrite_read1 (ak : akinfo) (pa : Arch.pa) (n : N) :
  nowrite_trace [WEread ak pa n].
Proof. constructor; [exact I|constructor]. Qed.

(** The data half of a text-only window ([wwin pc pc 0]) is empty. *)
Lemma win0_absurd (Q : nat -> Prop) :
  forall j : nat, (j < N.to_nat 0)%nat -> Q j.
Proof. intros j Hj. exfalso. cbn in Hj. lia. Qed.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_MemRead.
Print Assumptions exec_eff_rX_bits_gpr.
Print Assumptions execR_eff_untilMT_1.
Print Assumptions exec_eff_have_nominal_privLevel.
Print Assumptions exec_eff_virtual_memory_supported.
