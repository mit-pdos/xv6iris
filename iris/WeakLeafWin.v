(** * WeakLeafWin.v — the shared LEAF WINDOW KIT (M4 batch-2 consolidation)

    Every batch-2 leaf certifies its step over the same confined window: the
    instruction's 4 TEXT bytes at the pc plus an [n]-byte DATA word at the
    effective address.  The kit is WIDTH-shaped, not access-shaped, and after
    the fifth leaf three near-identical copies of it existed
    ([WeakLeafLd8]'s 8-byte kit, [WeakLeafLw4]'s 4-byte kit, the AMO leaf's
    §2) — exactly the near-duplicate cross-product the durable notes forbid.
    This file is the ONE width-parameterized copy, plus the small
    register-bookkeeping helpers every leaf shares:

      §1  [wwin pc ea n] — the window — with its membership / inversion /
          nonzero / pinned / conf-text / conf-data / write-domain lemmas.
          [set_solver] on a [gset Arch.pa] does not terminate (durable
          notes), so every membership fact is discharged algebraically.
      §2  the register-side helpers: [set_lookup_ne], the shared peel tactic
          [leaf_peel], the funnel-read bridge [reg_at_flat], and the two
          width-independent successor register frames ([load_sexec_facts]
          for the load shape, [store_regs_facts] for the store/AMO
          pre-write tower).
      §3  the two data-word alignment extractors ([wpt8_align],
          [wpt4_align]).

    LAYOUT CONSTRAINT (durable notes, the binder-position instance trap):
    every [gset Arch.pa] definition and statement lives ABOVE the
    [Import SailStdpp.Values] line — [Values]/[Base] re-export a SECOND
    [Countable Arch.pa] instance, and a window written below it elaborates
    against the wrong one while printing identically.  This file, like the
    leaves, deliberately does NOT [Require Import SailStdpp.Base]. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE WINDOW: 4 text bytes + an [n]-byte data word *)

Definition wwin (pc ea : Arch.pa) (n : N) : gset Arch.pa :=
  list_to_set ((pa_add pc <$> seq 0 4) ++ (pa_add ea <$> seq 0 (N.to_nat n))).

Lemma wwin_text (pc ea : Arch.pa) (n : N) (j : nat) :
  (j < 4)%nat -> pa_add pc j ∈ wwin pc ea n.
Proof.
  intros Hj. rewrite /wwin elem_of_list_to_set elem_of_app. left.
  apply elem_of_list_fmap. exists j. split; [reflexivity|].
  apply elem_of_seq. lia.
Qed.

Lemma wwin_data (pc ea : Arch.pa) (n : N) (j : nat) :
  (j < N.to_nat n)%nat -> pa_add ea j ∈ wwin pc ea n.
Proof.
  intros Hj. rewrite /wwin elem_of_list_to_set elem_of_app. right.
  apply elem_of_list_fmap. exists j. split; [reflexivity|].
  apply elem_of_seq. lia.
Qed.

Lemma wwin_inv (pc ea : Arch.pa) (n : N) (a : Arch.pa) :
  a ∈ wwin pc ea n ->
  (exists j : nat, (j < 4)%nat /\ a = pa_add pc j) \/
  (exists j : nat, (j < N.to_nat n)%nat /\ a = pa_add ea j).
Proof.
  rewrite /wwin elem_of_list_to_set elem_of_app.
  intros [H|H]; apply elem_of_list_fmap in H as (j & -> & Hj%elem_of_seq);
    [left|right]; exists j; (split; [lia|reflexivity]).
Qed.

(** (i) NONZERO.  RAM starts at [RiscvPtsto.ram_base = 0x80000000], and
    [pa_z] IS [uint], so this is one [lia] over [addr_is_ram]. *)

Lemma addr_is_ram_pa_z_nz (a : Arch.pa) : addr_is_ram a -> pa_z a <> 0.
Proof. unfold addr_is_ram, ram_base, pa_z. lia. Qed.

Lemma wwin_nonzero (pc ea : Arch.pa) (n : N) :
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < N.to_nat n)%nat -> addr_is_ram (pa_add ea j)) ->
  forall a, a ∈ wwin pc ea n -> pa_z a <> 0.
Proof.
  intros Hpc Hea a [(j & Hj & ->)|(j & Hj & ->)]%wwin_inv;
    apply addr_is_ram_pa_z_nz; [exact (Hpc j Hj) | exact (Hea j Hj)].
Qed.

(** (ii) PINNEDNESS (the WHOLE-WINDOW form — an owned-data leaf's shape;
    an invariant-form leaf uses [WeakCert.trace_pin] instead and never needs
    this).  Free for the four text bytes ([WeakFunnel.winstr_pinned]: text is
    unwritten this era) and owned for the data bytes ([wpt8_pinned] /
    [wpt4_pinned]).  Both produce the fact at [acc_addr], which
    [WeakBridge.acc_wf_byte] identifies with [pa_z (pa_add …)]. *)

Lemma wwin_pinned (σ : wmstate) (pc ea : Arch.pa) (n : N) :
  acc_wf pc 4 -> acc_wf ea n ->
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)) ->
  (forall j : nat, (j < N.to_nat n)%nat -> pinned_read σ (acc_addr ea j)) ->
  forall a, a ∈ wwin pc ea n -> pinned_read σ (pa_z a).
Proof.
  intros Hwpc Hwea Hpc Hea a [(j & Hj & ->)|(j & Hj & ->)]%wwin_inv.
  - rewrite (acc_wf_byte pc 4 j Hwpc ltac:(lia)). exact (Hpc j Hj).
  - rewrite (acc_wf_byte ea n j Hwea Hj). exact (Hea j Hj).
Qed.

(** (iii) THE TWO "byte is in the confined map" FAMILIES — one
    [wmem_restrict_lookup] per byte, over the flat facts the leaf's resources
    hand out. *)

Lemma wwin_conf_text (σ : wmstate) (pc ea : Arch.pa) (n : N)
    (w : SailStdpp.Values.mword 32) :
  (forall j : nat, (j < 4)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add pc j = Some (nth_byte w j)) ->
  forall j : nat, (j < 4)%nat ->
    wmem_restrict σ (wwin pc ea n) !! pa_add pc j = Some (nth_byte w j).
Proof.
  intros H j Hj.
  exact (wmem_restrict_lookup σ _ _ _ (wwin_text pc ea n j Hj) (H j Hj)).
Qed.

Lemma wwin_conf_data (σ : wmstate) (pc ea : Arch.pa) (n : N) {wd : N}
    (v : bv wd) :
  (forall j : nat, (j < N.to_nat n)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte v j)) ->
  forall j : nat, (j < N.to_nat n)%nat ->
    wmem_restrict σ (wwin pc ea n) !! pa_add ea j = Some (nth_byte v j).
Proof.
  intros H j Hj.
  exact (wmem_restrict_lookup σ _ _ _ (wwin_data pc ea n j Hj) (H j Hj)).
Qed.

(** (iv) THE WRITE-DOMAIN CONFINEMENT ([WeakCert.write_bytes_dom_sub] at this
    window): a store/AMO leaf's [dom (mem s_exec) ⊆ W] obligation, where the
    successor's memory is [write_bytes] of the data word over the restricted
    base.  (Failure mode 4 of the porting guide — a window that covers the
    reads but not the writes — is discharged HERE, which is why the data word
    is in the window even when no read of it needs pinning.) *)

Lemma wwin_wdom (σ : wmstate) (pc ea : Arch.pa) (n : N) {wd : N} (v : bv wd) :
  dom (write_bytes (wmem_restrict σ (wwin pc ea n)) ea n v) ⊆ wwin pc ea n.
Proof.
  apply write_bytes_dom_sub; [apply wmem_restrict_dom|].
  intros j Hj. by apply wwin_data.
Qed.

(** FROM HERE ON [SailStdpp.Values] IS IMPORTED — for the ['b"…"] literal
    notation the model's register premises are stated with.  Every
    [gset Arch.pa] fact this file states is above this line (the
    binder-position instance trap; header comment). *)
Import SailStdpp.Values.

(* ====================================================================== *)
(** ** 2. The register-side helpers every leaf shares *)

Lemma set_lookup_ne (r r' : register) (s : mstate) (x : type_of_register r') :
  register_beq r r' = false ->
  register_lookup r (sregs (set_reg s r' x)) = register_lookup r (sregs s).
Proof. intros H. rewrite sregs_set_reg. by apply irrelevant_register_set. Qed.

(** The register [r] is passed EXPLICITLY, never left as an [_]: the
    [ltac:(reg_ne)] hole is elaborated before the enclosing application is
    unified with the goal, so with [r] an evar [reg_ne] "solves" the side
    condition by picking a lemma that INSTANTIATES [r] to something else
    entirely (durable notes: a tactic in an argument position whose expected
    type is still an evar). *)
Ltac leaf_peel r :=
  rewrite (set_lookup_ne r nextPC _ _ ltac:(reg_ne))
          (set_lookup_ne r (R_bool minstret_increment) _ _ ltac:(reg_ne)).

(** A register read at [σ], through the funnel's [minstret_increment]
    pre-write.  [sregs (wflat_st σ)] IS [wm_regs σ] by conversion. *)
Lemma reg_at_flat (r : register) (σ : wmstate) (b : bool) :
  register_beq r (R_bool minstret_increment) = false ->
  register_lookup r
    (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) b))
    = register_lookup r (wm_regs σ).
Proof. intros H. exact (set_mi_lookup r (wflat_st σ) b H). Qed.

(** THE LOAD-SHAPE SUCCESSOR REGISTER FRAME (width-independent): the
    bookkeeping facts [wP_eff_of_leaf_base] (and
    [WeakEffSkel.exec_eff_riscv_step_base]) ask for alongside the run — the
    hart is still active, the [minstret_increment] flag survived, and the run
    moved neither the memory nor the devices. *)
Lemma load_sexec_facts (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (rd : mword 5)
    (x : SailStdpp.Values.mword 64) :
  let s_exec :=
    set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
      (R_bitvector_64 (gpr_of_Z (uint rd))) x in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = npc.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    by rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
               (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment)
               (R_bitvector_64 (gpr_of_Z (uint rd))) _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite (set_lookup_ne nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(** THE STORE-SHAPE PRE-WRITE TOWER (width-independent).  A store/AMO-class
    successor is an [MState] LITERAL over [sregs] of this tower (notes, "THE
    SECOND LEAF"), so the register facts are stated at the TOWER; consumers
    reach them by [exact]/[eq_trans] — conversion sees through
    [sregs (MState …)]. *)
Lemma store_regs_facts (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) :
  register_lookup hart_state
      (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc))
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment)
      (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc))
    = b
  /\ register_lookup nextPC
      (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc))
    = npc.
Proof.
  split_and!.
  - rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
            (set_lookup_ne hart_state (R_bool minstret_increment)
               _ _ ltac:(reg_ne)).
    reflexivity.
  - rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 3. The data-word alignment extractors *)

Section align.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wpt8_align (ea : Arch.pa) (dq : dfrac) (v : bv 64) (ws : wstate) :
    vwp_hold (wpt8 ea dq v) ws ⊢ ⌜is_aligned_paddr (Physaddr ea) 8 = true⌝.
  Proof.
    rewrite /wpt8 !vwp_hold_sep !vwp_hold_pure. by iIntros "(%H & _)".
  Qed.

  Lemma wpt4_align (ea : Arch.pa) (dq : dfrac) (v : bv 32) (ws : wstate) :
    vwp_hold (wpt4 ea dq v) ws ⊢ ⌜is_aligned_paddr (Physaddr ea) 4 = true⌝.
  Proof.
    rewrite /wpt4 !vwp_hold_sep !vwp_hold_pure. by iIntros "(%H & _)".
  Qed.

  Lemma wpt8_own_align (c : CPU) (ea : Arch.pa) (v : bv 64) (ws : wstate) :
    vwp_hold (wpt8_own c ea v) ws ⊢ ⌜is_aligned_paddr (Physaddr ea) 8 = true⌝.
  Proof.
    rewrite /wpt8_own !vwp_hold_sep !vwp_hold_pure. by iIntros "(%H & _)".
  Qed.

  Lemma wpt4_own_align (c : CPU) (ea : Arch.pa) (v : bv 32) (ws : wstate) :
    vwp_hold (wpt4_own c ea v) ws ⊢ ⌜is_aligned_paddr (Physaddr ea) 4 = true⌝.
  Proof.
    rewrite /wpt4_own !vwp_hold_sep !vwp_hold_pure. by iIntros "(%H & _)".
  Qed.

End align.
