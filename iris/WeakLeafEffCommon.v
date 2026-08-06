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
From Stdlib Require Import ZArith.
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

(** [split_misaligned] short-circuits on the aligned arm at EVERY width, so
    the shape files' width-8 and width-4 copies are one lemma.  ([WpLoad]'s
    SC original is stated at 8 only; the two instances below are what the
    call sites name.) *)
Lemma exec_eff_split_misaligned_aligned_w (n : Z) (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr n = true ->
  exec_eff (split_misaligned vaddr n) s = Some ((1, n), s, []).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb].
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_split_misaligned_aligned (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 8 = true ->
  exec_eff (split_misaligned vaddr 8) s = Some ((1, 8), s, []).
Proof. exact (exec_eff_split_misaligned_aligned_w 8 vaddr s). Qed.

Lemma exec_eff_split_misaligned_aligned_4 (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 4 = true ->
  exec_eff (split_misaligned vaddr 4) s = Some ((1, 4), s, []).
Proof. exact (exec_eff_split_misaligned_aligned_w 4 vaddr s). Qed.

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
(** ** 2. Soundness check *)

Print Assumptions exec_eff_MemRead.
Print Assumptions exec_eff_rX_bits_gpr.
Print Assumptions execR_eff_untilMT_1.
