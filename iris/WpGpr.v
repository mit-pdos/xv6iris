From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec RiscvTryStep RiscvExtras ExecCommon.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Definition gpr_of_Z (n : Z) : register_bitvector_64 :=
  if Z.eqb n 1 then x1 else if Z.eqb n 2 then x2
  else if Z.eqb n 3 then x3 else if Z.eqb n 4 then x4 else if Z.eqb n 5 then x5
  else if Z.eqb n 6 then x6 else if Z.eqb n 7 then x7 else if Z.eqb n 8 then x8
  else if Z.eqb n 9 then x9 else if Z.eqb n 10 then x10 else if Z.eqb n 11 then x11
  else if Z.eqb n 12 then x12 else if Z.eqb n 13 then x13 else if Z.eqb n 14 then x14
  else if Z.eqb n 15 then x15 else if Z.eqb n 16 then x16 else if Z.eqb n 17 then x17
  else if Z.eqb n 18 then x18 else if Z.eqb n 19 then x19 else if Z.eqb n 20 then x20
  else if Z.eqb n 21 then x21 else if Z.eqb n 22 then x22 else if Z.eqb n 23 then x23
  else if Z.eqb n 24 then x24 else if Z.eqb n 25 then x25 else if Z.eqb n 26 then x26
  else if Z.eqb n 27 then x27 else if Z.eqb n 28 then x28 else if Z.eqb n 29 then x29
  else if Z.eqb n 30 then x30 else x31.

Lemma uint5_lt (i : mword 5) : 0 <= uint i < 32.
Proof. pose proof (uint_range i ltac:(lia)) as H. change (2^5-1) with 31 in H. lia. Qed.

Lemma exec_wX_bits_gpr (i : mword 5) (v : mword 64) s :
  exec (wX_bits (Regidx i) v) s
  = Some (tt, if Z.eqb (uint i) 0 then s
              else set_reg s (R_bitvector_64 (gpr_of_Z (uint i))) (regval_into_reg v)).
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
      rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt s)). reflexivity. }
  all: rewrite (exec_wX_bits_at i (gpr_of_Z (uint i)) s v ltac:(rewrite H; vm_compute; reflexivity));
       rewrite H; reflexivity.
Qed.

Lemma exec_rX_bits_gpr (i : mword 5) s :
  exec (rX_bits (Regidx i)) s
  = Some (if Z.eqb (uint i) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) s.(sregs), s).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  1:{ unfold rX_bits, rX. rewrite H. cbn match. apply exec_returnm. }
  all: unfold rX_bits, rX; rewrite H; cbn match; reflexivity.
Qed.

(* register-generic ADD execute: reads rs1/rs2, writes rd, all via the file-generic
   rX/wX lemmas — works for ANY register triple. *)
Definition gpr_rd_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_ADD_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_rd_val rs2 rs1 s))).
Proof.
  unfold gpr_rd_val.
  eapply exec_execute_RTYPE_ADD.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

(* ====================================================================== *)
(* The general-purpose register file as a SINGLE resource: all of x1..x31  *)
(* in one separating conjunction (special/CSR registers stay separate).    *)


Section GprFile.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.
  (* Backing of register index [r].  Indexing by [regidx] (not
     register_bitvector_64) means index 0 = x0 is a genuine key even though
     there is no x0 register: since x0 is hardwired zero, its entry owns nothing
     and simply asserts the value is [zero_reg]; x1..x31 back the real register. *)
  Definition gpr_pt (r : regidx) (v : mword 64) : iProp Σ :=
    match r with
    | Regidx i => if Z.eqb (uint i) 0
                  then ⌜ v = zero_reg ⌝
                  else (R_bitvector_64 (gpr_of_Z (uint i))) ↦ᵣ v
    end%I.

  (* [gpr_file m] holds the WHOLE register file, indexed by [regidx]: [m] has an
     entry for every register index (so any [Regidx i] can be looked up total),
     and each entry backs its register (x0's is just the value-zero fact). *)
  (* The register map is now a total function [regidx -> mword 64] (see
     RegFile.v).  [gpr_file] still folds over a gmap, via the [rf_to_gmap]
     bridge, so the existing [big_sepM_*] interface is reused unchanged; the
     [dom] conjunct is kept (now always true) so callers' [ [%Hdom Hfmap] ]
     destructuring survives. *)
  Definition gpr_file (f : regfile) : iProp Σ :=
    (⌜ ∀ r : regidx, r ∈ dom (rf_to_gmap f) ⌝ ∗
     [∗ map] r ↦ v ∈ rf_to_gmap f, gpr_pt r v)%I.

  Lemma gpr_file_dom (f : regfile) : ⊢@{iPropI Σ} ⌜ ∀ r : regidx, r ∈ dom (rf_to_gmap f) ⌝.
  Proof. iPureIntro. apply rf_to_gmap_dom. Qed.

  (* Read/write accessors over the function rep (the interface leaves use). *)
  Lemma gpr_file_lookup_acc (f : regfile) (i : regidx) :
    gpr_file f ⊢ gpr_pt i (f i) ∗ (gpr_pt i (f i) -∗ gpr_file f).
  Proof.
    unfold gpr_file. iIntros "[$ Hm]".
    iDestruct (big_sepM_lookup_acc _ _ _ _ (rf_to_gmap_lookup f i) with "Hm") as "[$ Hcl]".
    iIntros "Hpt". iApply "Hcl". done.
  Qed.

  Lemma gpr_file_insert_acc (f : regfile) (i : regidx) (w : mword 64) :
    gpr_file f ⊢ gpr_pt i (f i) ∗ (gpr_pt i w -∗ gpr_file (<[i := w]> f)).
  Proof.
    unfold gpr_file. iIntros "[_ Hm]".
    iDestruct (big_sepM_insert_acc _ _ _ _ (rf_to_gmap_lookup f i) with "Hm") as "[$ Hcl]".
    iIntros "Hpt". iSplitR; [iApply gpr_file_dom |].
    rewrite rf_to_gmap_upd. iApply ("Hcl" with "Hpt").
  Qed.

  (* Reading register index [i] off its [gpr_pt] entry, uniformly over x0 vs a
     real register: the value the model's [rX] would return equals the entry's
     value [v].  Conclusion is pure, so callers keep [reg_interp]/[gpr_pt]. *)
  Lemma gpr_pt_value (i : mword 5) (v : mword 64) (σ : mstate) :
    reg_interp σ.(sregs) -∗ gpr_pt (Regidx i) v -∗
    ⌜ (if Z.eqb (uint i) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) σ.(sregs)) = v ⌝.
  Proof.
    iIntros "Hreg Hpt". unfold gpr_pt; cbn match.
    destruct (Z.eqb (uint i) 0) eqn:Hz.
    - iDestruct "Hpt" as %Hv. iPureIntro. symmetry; exact Hv.
    - iDestruct (reg_valid_dq with "Hreg Hpt") as %L. iPureIntro. exact L.
  Qed.

  (* x0 is hardwired zero, and its [gpr_file] entry owns nothing but that
     fact — so the map's value at index 0 IS [zero_reg].  Callers need this to
     read a store's (or an [addi rd,zero,imm]'s) source operand when the
     instruction names x0.  The [gpr_file] is handed back alongside the fact,
     so a whole-function proof can read the slot mid-stream. *)
  Lemma gpr_file_x0 (f : regfile) (i : mword 5) :
    uint i = 0 -> gpr_file f -∗ ⌜ f !!! Regidx i = zero_reg ⌝ ∗ gpr_file f.
  Proof.
    intro Hi. iIntros "Hf".
    iDestruct (gpr_file_lookup_acc f (Regidx i) with "Hf") as "[Hpt Hclose]".
    unfold gpr_pt; cbn match.
    replace (Z.eqb (uint i) 0) with true by (symmetry; apply Z.eqb_eq; exact Hi).
    iDestruct "Hpt" as %Hv.
    iSplitR; [ iPureIntro; exact Hv | ].
    iApply "Hclose". iPureIntro. exact Hv.
  Qed.

  (* For a nonzero index the [gpr_pt] entry IS the register points-to. *)
  Lemma gpr_pt_nz (i : mword 5) (v : mword 64) :
    uint i <> 0 ->
    gpr_pt (Regidx i) v = (R_bitvector_64 (gpr_of_Z (uint i)) ↦ᵣ v)%I.
  Proof.
    intro H. unfold gpr_pt; cbn match.
    replace (Z.eqb (uint i) 0) with false by (symmetry; apply Z.eqb_neq; exact H).
    reflexivity.
  Qed.
End GprFile.

(* exec-level register-generic ADD step (32-bit, F_Base): one lemma, ANY rd/rs1/rs2. *)
Section ForwardAddGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs2 rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s0).


End ForwardAddGpr.

(* gpr_of_Z always lands in x1..x31, hence differs from any non-GPR register. *)
Lemma gpr_of_Z_ne_nextPC (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) (R_bitvector_64 nextPC) = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.
Lemma gpr_of_Z_ne_PC (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) (R_bitvector_64 PC) = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.
Lemma gpr_of_Z_ne_minstret (n : Z) : register_beq (R_bitvector_64 (gpr_of_Z n)) minstret = false.
Proof. unfold gpr_of_Z; repeat case_match; reflexivity. Qed.

Ltac gpr_trans := first
  [ rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_nextPC _))
  | rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_PC _))
  | rewrite (irrelevant_register_set _ _ _ _ (gpr_of_Z_ne_minstret _))
  | rewrite irrelevant_register_set; [|vm_compute; reflexivity] ].



(* The [register_beq <special> (gpr_of_Z n) = false] side conditions of
   [irrelevant_register_set] are proved ONCE here, in an empty context, for the
   register names that straight-line WPs step over.  Doing the 32-way
   [case_match] split *inline* instead is degenerate: [destruct] re-types the
   whole proof context per case, and WP contexts embed huge Sail terms — Ltac
   profiling showed a single inline [reg_ne] costing 6.6 s (853 destructs) in
   WpGprLoad.  Here each lemma is ~1 ms of [vm_compute] per case. *)
Lemma regbeq_nextPC_gpr (n : Z) :
  register_beq nextPC (R_bitvector_64 (gpr_of_Z n)) = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_gpr_nextPC (n : Z) :
  register_beq (R_bitvector_64 (gpr_of_Z n)) nextPC = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_PC_gpr (n : Z) :
  register_beq PC (R_bitvector_64 (gpr_of_Z n)) = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_gpr_PC (n : Z) :
  register_beq (R_bitvector_64 (gpr_of_Z n)) PC = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_minstret_gpr (n : Z) :
  register_beq minstret (R_bitvector_64 (gpr_of_Z n)) = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_gpr_minstret (n : Z) :
  register_beq (R_bitvector_64 (gpr_of_Z n)) minstret = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_gpr_minc (n : Z) :
  register_beq (R_bitvector_64 (gpr_of_Z n)) (R_bool minstret_increment) = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.
Lemma regbeq_minc_gpr (n : Z) :
  register_beq (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z n)) = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.

(* Try the pre-proved shapes first ([apply] is O(1)); [vm_compute] next (covers
   fully-concrete register pairs instantly); the inline case split stays only as
   a last-resort fallback — see the note above for why it must not run on the
   common path, and why its leaves end in [vm_compute; reflexivity] rather than
   bare [reflexivity] (kernel-conversion reflexivity re-normalizes the
   ~300-constructor [register_beq] match per case). *)
Ltac reg_ne := solve
  [ apply regbeq_nextPC_gpr | apply regbeq_gpr_nextPC
  | apply regbeq_PC_gpr | apply regbeq_gpr_PC
  | apply regbeq_minstret_gpr | apply regbeq_gpr_minstret
  | apply regbeq_gpr_minc | apply regbeq_minc_gpr
  | vm_compute; reflexivity
  | (unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity) ].
Ltac tmig := rewrite irrelevant_register_set; [ | reg_ne ].

Section CleanGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 rd : mword 5) (mst0 : mword 64).

End CleanGpr.


(* Shared by WpGprLoad and WpGprStore (moved from WpGprLoad.v so the two
   compile in parallel): *)
(* the bare-mode 64-bit address translation extracts bits [63:0] -- a noop. *)
Lemma subrange_id (a : mword 64) : subrange_vec_dec a (xlen - 0 - 1) 0 = a.
Proof.
  apply bv_eq. unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (xlen - 0 - 1 - 0 + 1)) with 64%N.
  apply bv_wrap_bv_unsigned.
Qed.

(* register-generic base-address read (any rs1, INCLUDING x0 -> zero_reg). *)
Lemma exec_ext_data_get_addr_gpr (rs1 : mword 5) (offset : mword 64) acc w s :
  exec (ext_data_get_addr (Regidx rs1) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec
      (if Z.eqb (uint rs1) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset)), s).
Proof.
  unfold ext_data_get_addr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  cbn match. apply exec_returnm.
Qed.

(* A BIG-OP UNDER A TRANSPARENT NAME IS AN [iFrame] BOMB (optimization.md):
   a [∗ map] over the register file; named in 91 files, and on the machine chain the critical path now runs through.
   AT THE END OF THE FILE, so this file's own lemmas -- the accessors every
   consumer should be using -- can still take it apart. *)
Global Typeclasses Opaque gpr_file.
