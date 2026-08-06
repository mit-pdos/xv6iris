(** * WeakLeafLd8.v — M4's FIRST COMPLETE WEAK INSTRUCTION LEAF (batch 2)

    The [ld]-class plain 8-byte LOAD, end to end: from the M-mode config
    bundle, the PC cell, [WeakFunnel.winstr] and eight owned data bytes to
    [WP (Loop) {{ Φ }}].  Nothing about the weak machine is left as a premise
    — no certificate, no [wP_eff], no [exec]/[exec_eff] fact.  Every leaf of
    the M4 sweep is this file with a different [execute] lemma and a
    different data width, so ITS MARGINAL SIZE OVER THE SC LEAF
    ([WpMmodeLoad.wp_ld_gpr]) IS THE SWEEP'S PER-INSTRUCTION UNIT PRICE.

    Assembled entirely out of what batches 0/1 landed:

      - [WeakFunnel.wwp_instr] — THE FUNNEL.  It does the whole [riscv_step]
        wrapper (privilege read, [should_inc_minstret], the
        [minstret_increment] pre-write, the hart-active gate, the PC tick,
        the [minstret] bump, the clock tick), so this file owes exactly what
        an SC leaf owes: ONE [execute] fact.
      - [WeakFetchEff.wP_eff_of_leaf_base] — THE RECIPE.  Text bytes +
        decode fact + the [execute]'s [exec_eff] fact ⇒ the certificate's
        [wP_eff] obligation, with no model peeling anywhere.
      - [WeakLeafEff8.exec_eff_execute_LOAD_8_gpr] — THE SHAPE.  The LOAD's
        own [exec_eff] fact, trace [[WEread wak_plain ea 8]]; its SC twin
        [WpMmodeLeafBase.exec_execute_LOAD_8_gpr] is what the funnel's
        callback hands back.
      - [WeakWord8]'s [↦w₈] family — THE RESOURCE.  [wwp_ld8] discharges the
        read obligation and pins the flat doubleword; [wwp_ld8_carry] frames
        it across the step.

    THREE SECTIONS, and the middle one is the price.

    §1  [wcert_load_w] — [WeakCert.wcert_load] made WIDTH-GENERIC.  Its proof
        was already generic on the nose ([4] appears only as the [n] of
        [coh_ts] and inside [wQ_load_w 4] / [wV_load_w 4]), so this is the
        same script with [4] replaced by [n], plus the subsumption check
        [wcert_load_w_4] that the width-4 original IS the [n := 4] instance
        (the regression check [WeakWord8.wP_load_w_4] & co. make), plus the
        width-8 instance at the concrete fetch element.

    §2  THE WINDOW AND THE [wP_eff] HALF.  [wld8_window pc ea] is the text
        word plus the data doubleword; [wld8_window_pc] / [_ea] /
        [_nonzero] discharge the three window obligations
        [wP_eff_of_leaf_base] asks for, and [wP_eff_ld8] feeds it the
        [execute] fact RE-INSTANTIATED AT THE CONFINED MEMORY.  That second
        instantiation of the same library lemma — at
        [WeakCert.wmem_restrict σ W] rather than [WeakBridge.wflat_st σ] —
        is the whole per-instruction cost (porting guide §2).

    §3  [wwp_ld8_leaf] — the leaf.  [WeakFunnel.wwp_instr] at
        [P := wP_eff … ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 8])],
        [Q := wQ_load_w 8 ea] and §1's certificate, with §2 discharging
        [⌜P σ⌝] inside the callback.

    EVERY PURE / GEOMETRY SIDE CONDITION IS A PREMISE (alignment, the PMP/PMA
    match, [dev_addr], the decode facts, [agree_on], [goodb0]).  A real call
    site discharges each by [vm_compute]; they are the SC leaf's premises
    verbatim and are not part of the price being measured. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
(* DELIBERATELY NOT [Require Import SailStdpp.Base]: it re-exports
   [SailStdpp.Instances]' [Countable_mword], a SECOND [Countable Arch.pa]
   instance, and then [gset Arch.pa] written anywhere in this file elaborates
   against it while [WeakCert.wmem_restrict] wants the [bv_countable] one —
   the two print identically (durable notes, the instance trap).  Everything
   this file needs from [Base] arrives through [Riscv.rv64d]. *)
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff WeakLeafEff8.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE WIDTH-GENERIC PLAIN-LOAD CERTIFICATE

    [WeakCert.wcert_load] is stated at width 4 with the [4] written into the
    body, but its proof never uses it: [4] occurs only as the [n] of
    [WeakInterp.coh_ts] and inside [WeakInstr.wQ_load] = [wQ_load_w 4] /
    [wV_load] = [wV_load_w 4], both of which [WeakInstr] already states
    width-generically.  The script below is [wcert_load]'s, verbatim, with
    [4] replaced by [n]. *)

Lemma wcert_load_w (n : N) (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEread akl ea n]) (wQ_load_w n ea).
Proof.
  intros Hcoh. apply wstep_cert_eff. intros s s' HP Hi Hl Hws.
  rewrite weffs_cons2 !weff_apply_read in Hl Hws.
  rewrite (coh_ts_log (wread_post s akf pf (coh_ts s pf nf)) s ea n
             (wread_post_log s akf pf (coh_ts s pf nf))) in Hl Hws.
  rewrite !wread_post_log in Hl.
  rewrite (wread_post_ws_weak (wread_post s akf pf (coh_ts s pf nf)) akl ea
             (coh_ts s ea n) Hcoh) in Hws.
  rewrite /wQ_load_w /wV_load_w. split_and!; [exact Hi|exact Hl|].
  intros j Hj. rewrite Hws.
  rewrite -(coh_ts_lookup s ea n j Hj) /acc_addr.
  apply (load_post_run_gain (fun a t => view_byte a t)
           (wm_ws (wread_post s akf pf (coh_ts s pf nf))) (ak_sync akl)
           (pa_z ea) (coh_ts s ea n) j).
  - intros w a t. apply load_byte_gain.
  - rewrite coh_ts_length. exact Hj.
Qed.

(** THE SUBSUMPTION CHECK: [WeakCert.wcert_load]'s exact statement is the
    [n := 4] instance, on the nose.  (The same regression check
    [WeakWord8.wP_load_w_4] & co. make after that generalization.) *)
Lemma wcert_load_w_4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N) (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEread akl ea 4]) (wQ_load ea).
Proof. exact (wcert_load_w 4 cid pc akf pf nf akl ea). Qed.

(** ... and the width-8 instance AT THE CONCRETE FETCH ELEMENT
    [WeakFetchEff]'s replay produces — the [WeakFetchEff.wcert_load_base4]
    twin at width 8.  [[a] ++ [b]] IS [[a; b]], so this is one [exact]. *)
Lemma wcert_load8_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEread akl ea 8]))
    (wQ_load_w 8 ea).
Proof.
  intros Hcoh. exact (wcert_load_w 8 cid pc wak_plain pc 4 akl ea Hcoh).
Qed.

(* ====================================================================== *)
(** ** 2. THE WINDOW AND THE [wP_eff] HALF *)

(** *** 2a. The window: the instruction's text word plus its data doubleword. *)

Definition wld8_window (pc ea : Arch.pa) : gset Arch.pa :=
  list_to_set ((pa_add pc <$> seq 0 4) ++ (pa_add ea <$> seq 0 8)).

(** THE THREE MEMBERSHIP FACTS.  [set_solver] on a [gset Arch.pa] does not
    terminate (durable notes), so every one of these is discharged
    algebraically — [elem_of_list_to_set], [elem_of_app],
    [elem_of_list_fmap], [elem_of_seq] — and none of them mentions a
    decision procedure. *)

Lemma wld8_window_text (pc ea : Arch.pa) (j : nat) :
  (j < 4)%nat -> pa_add pc j ∈ wld8_window pc ea.
Proof.
  intros Hj. rewrite /wld8_window elem_of_list_to_set elem_of_app. left.
  apply elem_of_list_fmap. exists j. split; [reflexivity|].
  apply elem_of_seq. lia.
Qed.

Lemma wld8_window_data (pc ea : Arch.pa) (j : nat) :
  (j < 8)%nat -> pa_add ea j ∈ wld8_window pc ea.
Proof.
  intros Hj. rewrite /wld8_window elem_of_list_to_set elem_of_app. right.
  apply elem_of_list_fmap. exists j. split; [reflexivity|].
  apply elem_of_seq. lia.
Qed.

Lemma wld8_window_inv (pc ea : Arch.pa) (a : Arch.pa) :
  a ∈ wld8_window pc ea ->
  (exists j : nat, (j < 4)%nat /\ a = pa_add pc j) \/
  (exists j : nat, (j < 8)%nat /\ a = pa_add ea j).
Proof.
  rewrite /wld8_window elem_of_list_to_set elem_of_app.
  intros [H|H]; apply elem_of_list_fmap in H as (j & -> & Hj%elem_of_seq);
    [left|right]; exists j; (split; [lia|reflexivity]).
Qed.

(** *** 2b. The three window obligations of [WeakFetchEff.wP_eff_of_leaf_base].

    (i) NONZERO.  RAM starts at [RiscvPtsto.ram_base = 0x80000000], and
    [pa_z] IS [uint], so this is one [lia] over [addr_is_ram]. *)

Lemma addr_is_ram_pa_z_nz (a : Arch.pa) : addr_is_ram a -> pa_z a <> 0.
Proof. unfold addr_is_ram, ram_base, pa_z. lia. Qed.

Lemma wld8_window_nonzero (pc ea : Arch.pa) :
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
  forall a, a ∈ wld8_window pc ea -> pa_z a <> 0.
Proof.
  intros Hpc Hea a [(j & Hj & ->)|(j & Hj & ->)]%wld8_window_inv;
    apply addr_is_ram_pa_z_nz; [exact (Hpc j Hj) | exact (Hea j Hj)].
Qed.

(** (ii) PINNEDNESS.  Free for the four text bytes ([WeakFunnel.winstr_pinned]:
    text is unwritten this era) and owned for the eight data bytes
    ([WeakWord8.wpt8_pinned]).  Both produce the fact at [acc_addr], which
    [WeakBridge.acc_wf_byte] identifies with [pa_z (pa_add …)]. *)

Lemma wld8_window_pinned (σ : wmstate) (pc ea : Arch.pa) :
  acc_wf pc 4 -> acc_wf ea 8 ->
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)) ->
  (forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr ea j)) ->
  forall a, a ∈ wld8_window pc ea -> pinned_read σ (pa_z a).
Proof.
  intros Hwpc Hwea Hpc Hea a [(j & Hj & ->)|(j & Hj & ->)]%wld8_window_inv.
  - rewrite (acc_wf_byte pc 4 j Hwpc ltac:(lia)). exact (Hpc j Hj).
  - rewrite (acc_wf_byte ea 8 j Hwea ltac:(lia)). exact (Hea j Hj).
Qed.

(** (iii) THE TWO "byte is in the confined map" FAMILIES — one
    [wmem_restrict_lookup] per byte, over the flat facts
    [WeakFunnel.winstr_flat] (text) and [WeakWord8.wwp_ld8] (data) already
    hand out. *)

Lemma wld8_window_conf_text (σ : wmstate) (pc ea : Arch.pa)
    (w : SailStdpp.Values.mword 32) :
  (forall j : nat, (j < 4)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add pc j = Some (nth_byte w j)) ->
  forall j : nat, (j < 4)%nat ->
    wmem_restrict σ (wld8_window pc ea) !! pa_add pc j = Some (nth_byte w j).
Proof.
  intros H j Hj.
  exact (wmem_restrict_lookup σ _ _ _ (wld8_window_text pc ea j Hj) (H j Hj)).
Qed.

Lemma wld8_window_conf_data (σ : wmstate) (pc ea : Arch.pa) (v : bv 64) :
  (forall j : nat, (j < 8)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte v j)) ->
  forall j : nat, (j < 8)%nat ->
    wmem_restrict σ (wld8_window pc ea) !! pa_add ea j = Some (nth_byte v j).
Proof.
  intros H j Hj.
  exact (wmem_restrict_lookup σ _ _ _ (wld8_window_data pc ea j Hj) (H j Hj)).
Qed.

(** FROM HERE ON [SailStdpp.Values] IS IMPORTED — for the ['b"…"] literal
    notation, which the model's register premises are stated with.  The
    import is placed HERE, after §2a, because it also re-exports a SECOND
    [Countable Arch.pa] instance: every [gset Arch.pa] this file writes is
    above this line, elaborated against the instance [WeakCert.wmem_restrict]
    uses (durable notes, the binder-position instance trap). *)
Import SailStdpp.Values.

(** *** 2c. THE SECOND INSTANTIATION — the whole per-instruction cost.

    [WeakLeafEff8.exec_eff_execute_LOAD_8_gpr] again, at the CONFINED state
    [MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)] with the funnel's two
    pre-writes ([minstret_increment := b] and [nextPC := pc+4]) on top.  The
    SC/eff execute lemmas are state-generic, so nothing is re-proved here:
    what this costs is the register peels that move each config fact past the
    two pre-writes, and the [wmem_restrict_lookup] of the eight data bytes.
    [W] is [(W : _)] for the instance-trap reason above. *)

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
Local Ltac ld8_peel r :=
  rewrite (set_lookup_ne r nextPC _ _ ltac:(reg_ne))
          (set_lookup_ne r (R_bool minstret_increment) _ _ ltac:(reg_ne)).

Lemma exec_eff_ld8_at (s0 : mstate) (b : bool)
    (pc : SailStdpp.Values.mword 64) (rs1 rd : mword 5) (imm : mword 12)
    (ea : Arch.pa) (v : bv 64) :
  uint rd <> 0 ->
  register_lookup cur_privilege s0.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1")
    = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s0.(sregs)))
    = PMM_Disabled ->
  pmp_all_off (register_lookup pmpcfg_n s0.(sregs)) ->
  pma_allows_all (register_lookup pma_regions s0.(sregs)) ->
  register_lookup htif_tohost_base s0.(sregs) = None ->
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s0.(sregs))
          (sign_extend' 64 imm) = ea ->
  is_aligned_paddr (Physaddr ea) 8 = true ->
  (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
  (forall j : nat, (j < 8)%nat -> s0.(mem) !! pa_add ea j = Some (nth_byte v j)) ->
  exec_eff (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    (set_reg (set_reg s0 (R_bool minstret_increment) b)
             nextPC (add_vec_int pc 4))
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b)
                   nextPC (add_vec_int pc 4))
                  (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v),
          [WEread wak_plain ea 8]).
Proof.
  intros Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hal Hram8 Hbytes.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram8 0%nat); lia).
  assert (Hram7 : addr_is_ram (pa_add ea 7)) by (apply Hram8; lia).
  destruct (pma_all_ram Lpma ea 8
              (pma_access_ram _ _ _ Hram Hram7
                 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & Hread & _).
  set (s := set_reg (set_reg s0 (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 4)).
  (* every config register, moved past the funnel's two pre-writes *)
  assert (Lpriv_s : register_lookup cur_privilege s.(sregs) = Machine)
    by (unfold s; ld8_peel cur_privilege; exact Lpriv).
  assert (Lms_s : register_lookup mstatus s.(sregs)
                  = register_lookup mstatus s0.(sregs))
    by (unfold s; ld8_peel mstatus; reflexivity).
  assert (Lsec_s : register_lookup mseccfg s.(sregs)
                   = register_lookup mseccfg s0.(sregs))
    by (unfold s; ld8_peel mseccfg; reflexivity).
  assert (Lpmpc_s : register_lookup pmpcfg_n s.(sregs)
                    = register_lookup pmpcfg_n s0.(sregs))
    by (unfold s; ld8_peel pmpcfg_n; reflexivity).
  assert (Lpma_s : register_lookup pma_regions s.(sregs)
                   = register_lookup pma_regions s0.(sregs))
    by (unfold s; ld8_peel pma_regions; reflexivity).
  assert (Lhtif_s : register_lookup htif_tohost_base s.(sregs) = None)
    by (unfold s; ld8_peel htif_tohost_base; exact Lhtif).
  (* the base register, and the two identity bridges the model's [Let]s need *)
  assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                          s.(sregs))
                  = (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity|].
    unfold s; ld8_peel (R_bitvector_64 (gpr_of_Z (uint rs1))); reflexivity. }
  assert (Ha8 : zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = ea).
  { rewrite Hbase Hea zero_extend'_id subrange_id. reflexivity. }
  assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
  { rewrite Hbase Hea !zero_extend'_id subrange_id.
    change (0 * 8) with 0. rewrite avi0. reflexivity. }
  (* [extend_value false] is the identity on an already-64-bit value *)
  assert (Hev : extend_value false
            (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
  { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
  rewrite -Hev -Hpa.
  apply (exec_eff_execute_LOAD_8_gpr rs1 rd imm v region s Hrd Lpriv_s).
  - rewrite Lms_s. exact Lmprv.
  - rewrite Lsec_s. exact Lpmm.
  - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Hal.
    exact Hal.
  - apply exec_eff_pmpCheck_machine_none.
    intro i. rewrite Lpmpc_s. exact (proj1 (Lpmp i)).
  - rewrite Lpma_s Hpa. exact Hmatch.
  - rewrite Hpa. exact Hal.
  - exact Hread.
  - rewrite Hpa.
    exact (exec_eff_within_clint_false ea 8 s
             (addr_is_ram_not_in_clint _ Hram) ltac:(lia)).
  - rewrite Hpa.
    exact (exec_eff_within_sig_false ea 8 s
             (addr_is_ram_not_in_sig _ Hram) ltac:(lia)).
  - rewrite Hpa. exact (exec_eff_within_htif_false ea 8 s Lhtif_s).
  - rewrite Hpa. exact (addr_is_ram_not_dev _ Hram).
  - intros j Hj. rewrite Hpa. unfold s. rewrite !mem_set_reg.
    exact (Hbytes j ltac:(lia)).
Qed.

(** The three bookkeeping facts about the [execute]'s successor that
    [wP_eff_of_leaf_base] (and [WeakEffSkel.exec_eff_riscv_step_base]) ask for
    alongside the run: the hart is still active, the [minstret_increment] flag
    survived, and the run moved neither the memory nor the devices. *)
Lemma ld8_sexec_facts (s0 : mstate) (b : bool)
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

(** *** 2d. THE [wP_eff] HALF, as a standalone lemma over the resources.

    This is the obligation that was blocked until [WeakFetchEff] landed: the
    certificate's precondition, discharged from the four text bytes
    ([WeakFunnel.winstr_bytes]), the eight owned data bytes
    ([WeakWord8.wpt8]) and the latest-write authority, plus the M-mode
    register tower and the instruction's own pure geometry.  Note what is NOT
    here: no model peel, no [vm_compute], no [riscv_step]. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wpt8_align (ea : Arch.pa) (dq : dfrac) (v : bv 64) (ws : wstate) :
    vwp_hold (wpt8 ea dq v) ws ⊢ ⌜is_aligned_paddr (Physaddr ea) 8 = true⌝.
  Proof.
    rewrite /wpt8 !vwp_hold_sep !vwp_hold_pure. by iIntros "(%H & _)".
  Qed.

  Lemma wP_eff_ld8 (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12)
      (ea : Arch.pa) (v : bv 64) (dq : dfrac)
      (D : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    (* --- the M-mode config tower, at σ's own registers --- *)
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_all_off (register_lookup pmpcfg_n (wm_regs σ)) ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
      = PMM_Disabled ->
    eq_vec (register_lookup elp (wm_regs σ))
           (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* --- the instruction's pure geometry (every one a [vm_compute] at a
           real call site) --- *)
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    uint rd <> 0 ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the decode, exactly as the decode library states it --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), dst) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_Base w) -∗
    vwp_hold (wpt8 ea dq v) (wm_ws σ) -∗
    ⌜wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 8]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
           Hal4 HnotRVC Hrd Hea Hram8 Hagree HDmi Hgood Hdec.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_Base w) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wwp_ld8 σ ea dq v Hwf with "Hlat Hpt")
      as %[[Haccea Hpinea] Hflat8].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    iPureIntro.
    destruct Hfok as (Hal2 & Hrampc & w' & [Hww _] & Htext). subst w'.
    apply (wP_eff_of_leaf_base cid σ (wld8_window pc ea) pc w
             (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
             [WEread wak_plain ea 8] D dst).
    - exact Hwf.
    - exact (wld8_window_nonzero pc ea Hrampc Hram8).
    - exact (wld8_window_pinned σ pc ea Haccpc Haccea Hpinpc Hpinea).
    - exact Lpc.
    - exact Lpriv.
    - exact (pmp_all_off_allows_all _ Lpmp).
    - exact Lpma.
    - exact Lhtif.
    - exact Lhart.
    - exact LmisaS.
    - exact LmIE.
    - exact Lelp.
    - exact Hal4.
    - exact Hrampc.
    - exact (wld8_window_conf_text σ pc ea w Htext).
    - exact HnotRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - reflexivity.
    - intro b. eexists. split_and!.
      + exact (exec_eff_ld8_at
                 (MState (wm_regs σ) (wmem_restrict σ (wld8_window pc ea))
                    (wm_dev σ)) b pc rs1 rd imm ea v
                 Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Halea Hram8
                 (wld8_window_conf_data σ pc ea v Hflat8)).
      + rewrite (proj1 (ld8_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wld8_window pc ea))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v))).
        exact Lhart.
      + exact (proj1 (proj2 (ld8_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wld8_window pc ea))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v)))).
      + rewrite (proj1 (proj2 (proj2 (ld8_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wld8_window pc ea))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v))))).
        apply wmem_restrict_dom.
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    ONE INTERFACE WART SHOWS UP HERE AND IT IS THE MAIN FINDING OF THIS FILE.
    [WeakFunnel.wwp_cb] asks the leaf to hand back [wmstate_norg σ'], whose
    [dev_interp (wm_dev σ')] conjunct needs [wm_dev σ' = wm_dev σ];
    [WeakInstr.wstep_post] only says [wm_dev σ' = mdev t], and [dev_interp]
    is an authoritative half that cannot be moved without its fragment.  So
    the leaf has to learn what [t] IS — which means replaying the WHOLE step
    a SECOND time, now at the FLAT state, even though [wP_eff_of_leaf_base]
    has just replayed it at the confined one.  §3a is that replay.  It is
    ~50 lines of pure duplication that belongs in the funnel (which knows [t]
    outright): see the report at the end of the file.

    §3a is nevertheless cheap to state, because every premise of it is a
    premise §2d already has. *)

(** *** 3a. The step at the FLAT state, and its device frame. *)

Lemma exec_eff_step_all_ticks_dev (s t0 : mstate) (es : list weff) :
  exec_eff (riscv_step false) s = Some (tt, t0, es) ->
  forall tick : bool, exists t' : mstate,
    exec_eff (riscv_step tick) s = Some (tt, t', es) /\ mdev t' = mdev t0.
Proof.
  intros H0 tick. destruct tick.
  - destruct (exec_eff_tick_clock t0) as (c & ti & p & Htick).
    eexists. split.
    + exact (exec_eff_riscv_step_tick s t0 _ es H0 Htick).
    + by rewrite !mdev_set_reg.
  - exists t0. split; [exact H0 | reflexivity].
Qed.

Lemma exec_ld8_step_flat (σ : wmstate)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (rs1 rd : mword 5) (imm : mword 12) (ea : Arch.pa) (v : bv 64)
    (D : register -> bool) (dst : mstate) :
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_all_off (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
    = PMM_Disabled ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  fetch_flat_ok (wflat_st σ) pc (F_Base w) ->
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst
    = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), dst) ->
  uint rd <> 0 ->
  add_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  (wm_regs σ))
          (sign_extend' 64 imm) = ea ->
  is_aligned_paddr (Physaddr ea) 8 = true ->
  (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
  (forall j : nat, (j < 8)%nat ->
     wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte v j)) ->
  forall tick : bool, exists t : mstate,
    exec (riscv_step tick) (wflat_st σ) = Some (tt, t) /\ mdev t = wm_dev σ.
Proof.
  intros Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
         Hal4 Hfok Hagree HDmi Hgood Hdec Hrd Hea Halea Hram8 Hbytes tick.
  set (sf := wflat_st σ).
  destruct (exec_eff_should_inc_minstret_Some
              (register_lookup cur_privilege (sregs sf)) sf) as [b Hsi].
  assert (Lpriv_a : register_lookup cur_privilege
            (sregs (set_reg sf (R_bool minstret_increment) b)) = Machine)
    by (rewrite (set_mi_lookup cur_privilege _ b eq_refl); exact Lpriv).
  assert (Lpc_a : register_lookup PC
            (sregs (set_reg sf (R_bool minstret_increment) b)) = pc)
    by (rewrite (set_mi_lookup PC _ b eq_refl); exact Lpc).
  assert (Lhart_a : register_lookup hart_state
            (sregs (set_reg sf (R_bool minstret_increment) b))
            = HART_ACTIVE tt)
    by (rewrite (set_mi_lookup hart_state _ b eq_refl); exact Lhart).
  assert (Lelp_a : eq_vec (register_lookup elp
            (sregs (set_reg sf (R_bool minstret_increment) b)))
            (landing_pad_bits_backwards LP_EXPECTED) = false)
    by (rewrite (set_mi_lookup elp _ b eq_refl); exact Lelp).
  assert (Hdisp : exec_eff (dispatchInterrupt Machine)
            (set_reg sf (R_bool minstret_increment) b)
            = Some (None, set_reg sf (R_bool minstret_increment) b, [])).
  { apply exec_eff_dispatchInterrupt_machine_none.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaS.
    - rewrite (set_mi_lookup mstatus _ b eq_refl). exact LmIE. }
  assert (Hfetch : exec_eff (fetch tt)
            (set_reg sf (R_bool minstret_increment) b)
            = Some (F_Base w, set_reg sf (R_bool minstret_increment) b,
                    [WEread wak_plain pc 4])).
  { apply (exec_eff_fetch_flat_base4 _ pc w).
    - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl).
      exact (pmp_all_off_allows_all _ Lpmp).
    - rewrite (set_mi_lookup pma_regions _ b eq_refl). exact Lpma.
    - exact Lpc_a.
    - exact Lpriv_a.
    - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl). exact Lhtif.
    - exact Hal4.
    - exact (fetch_flat_ok_mem sf _ pc (F_Base w) (mem_set_reg _ _ _) Hfok). }
  assert (Hdec_a : exec_eff (ext_decode w)
            (set_reg sf (R_bool minstret_increment) b)
            = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8),
                    set_reg sf (R_bool minstret_increment) b, [])).
  { refine (exec_eff_decode_bridge D (ext_decode w) dst _ _ _ Hgood Hdec).
    intros r HDr.
    assert (Hne : register_beq r (R_bool minstret_increment) = false).
    { destruct (register_beq r (R_bool minstret_increment)) eqn:Hb;
        [|reflexivity].
      exfalso. rewrite (register_beq_eq _ _ Hb) in HDr.
      by rewrite HDmi in HDr. }
    rewrite (set_mi_lookup r _ b Hne). exact (Hagree r HDr). }
  pose proof (exec_eff_ld8_at sf b pc rs1 rd imm ea v Hrd Lpriv Lmprv Lpmm
                Lpmp Lpma Lhtif Hea Halea Hram8 Hbytes) as Hex.
  pose proof (exec_eff_riscv_step_base sf _ w
                (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pc b
                [WEread wak_plain pc 4] [WEread wak_plain ea 8]
                Hsi Lhart_a Lpriv_a Hdisp Hfetch Hdec_a Lelp_a eq_refl Lpc_a
                Hex
                (eq_trans (proj1 (ld8_sexec_facts sf b (add_vec_int pc 4) rd
                                    (regval_into_reg v))) Lhart)
                (proj1 (proj2 (ld8_sexec_facts sf b (add_vec_int pc 4) rd
                                 (regval_into_reg v))))) as Hstep.
  destruct (exec_eff_step_all_ticks_dev sf _ _ Hstep tick) as (t & Ht & Hdv).
  exists t. split; [exact (exec_eff_exec _ _ _ _ _ Ht)|].
  rewrite Hdv. destruct b; by rewrite !mdev_set_reg.
Qed.

(** *** 3b. THE LEAF.

    Read the statement against [WpMmodeLoad.wp_ld_gpr], the SC [ld] leaf:
    [instr] became [winstr_bytes] plus the decode field as a premise
    ([WeakFunnel.winstr_intro] rebuilds [winstr] from the two);
    [phys_word_pointsto ea dq v] became [vwp_hold (wpt8 ea dq v) ws] paired
    with this hart's [WeakGhost.hart_ws] cell, which is what NAMES the view
    the resource is held at; and the continuation gains the one extra
    argument [⌜ws_le ws ws'⌝] — a load only ever raises views, so every
    OTHER resource the caller holds crosses the step by
    [WeakVProp.vwp_hold_mono] with no further work.  Everything else is the
    SC statement.

    The [D]/[dst] decode-bridge premises are quantified over the register
    file rather than stated at one, because [WeakFunnel.wwp_cb] does not hand
    the leaf the config register VALUES at [σ] (see the report). *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  (** A register read at [σ], through the funnel's [minstret_increment]
      pre-write.  [sregs (wflat_st σ)] IS [wm_regs σ] by conversion. *)
  Lemma reg_at_flat (r : register) (σ : wmstate) (b : bool) :
    register_beq r (R_bool minstret_increment) = false ->
    register_lookup r
      (sregs (set_reg (wflat_st σ) (R_bool minstret_increment) b))
      = register_lookup r (wm_regs σ).
  Proof. intros H. exact (set_mi_lookup r (wflat_st σ) b H). Qed.

  Lemma wwp_ld8_leaf Φ
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rd0 npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), t)) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea dqv v) ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8 ea dqv v) ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz Hrd Hea Hram8 Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* half the config to the funnel, half kept to read the registers at σ *)
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hminv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL & %HKF)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wwp_instr Φ pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              pmpcfg0 (dq := DfracOwn (q/2))
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 8]))
              (wQ_load_w 8 ea) Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_load8_base4 (fin_to_nat cpu_id) pc wak_plain ea eq_refl)
              with "Hmm_wp Hpmpc_wp Hpc [] ").
    { iApply (winstr_intro pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* every config register, read off the KEPT half, at [wm_regs σ] *)
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")  as %Lpriv_a.
    iDestruct (reg_valid_dq with "Hreg Hms_k")    as %Lms_a.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")  as %Lpmpc_a.
    iDestruct (reg_valid_dq with "Hreg Hmisa")    as %Lmisa_a.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg") as %Lsec_a.
    iDestruct (reg_valid_dq with "Hreg Hpma")     as %Lpma_a.
    iDestruct (reg_valid_dq with "Hreg Hhtif")    as %Lhtif_a.
    iDestruct (reg_valid_dq with "Hreg Help")     as %Lelp_a.
    iDestruct (reg_valid_dq with "Hreg Hhs_k")    as %Lhart_a.
    iDestruct (reg_valid    with "Hreg Hrs1c")    as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat cur_privilege σ b eq_refl))
                  Lpriv_a)  as Lpriv.
    pose proof (eq_trans (eq_sym (reg_at_flat mstatus σ b eq_refl))
                  Lms_a)    as Lms.
    pose proof (eq_trans (eq_sym (reg_at_flat pmpcfg_n σ b eq_refl))
                  Lpmpc_a)  as Lpmpc.
    pose proof (eq_trans (eq_sym (reg_at_flat misa σ b eq_refl))
                  Lmisa_a)  as Lmisa.
    pose proof (eq_trans (eq_sym (reg_at_flat mseccfg σ b eq_refl))
                  Lsec_a)   as Lsec.
    pose proof (eq_trans (eq_sym (reg_at_flat pma_regions σ b eq_refl))
                  Lpma_a)   as Lpma.
    pose proof (eq_trans (eq_sym (reg_at_flat htif_tohost_base σ b eq_refl))
                  Lhtif_a)  as Lhtif.
    pose proof (eq_trans (eq_sym (reg_at_flat elp σ b eq_refl))
                  Lelp_a)   as Lelp.
    pose proof (eq_trans (eq_sym (reg_at_flat hart_state σ b eq_refl))
                  Lhart_a)  as Lhart.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a)   as Lrs1.
    (* the effective address, at [σ]'s own register file *)
    assert (Hea_σ : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (wm_regs σ)) (sign_extend' 64 imm) = ea).
    { rewrite (proj2 (Z.eqb_neq (uint rs1) 0) Hrs1nz) Lrs1. exact Hea. }
    (* the agreement, at [σ]'s registers *)
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | by rewrite Lmisa | by rewrite Lsec]. }
    (* ---- the certificate's precondition (§2d) ---- *)
    iDestruct (wP_eff_ld8 (fin_to_nat cpu_id) σ pc w rs1 rd imm ea v dqv D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) ltac:(by rewrite Lpma)
                 Lhtif Lhart ltac:(by rewrite Lmisa) ltac:(by rewrite Lms)
                 ltac:(by rewrite Lms) ltac:(by rewrite Lsec)
                 ltac:(by rewrite Lelp) Hal4 HnotRVC Hrd Hea_σ Hram8
                 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the text word and the data doubleword ---- *)
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (wwp_ld8 σ ea dqv v Hwf with "Hlat Hpt") as %[_ Hflat8].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact AND the whole
           step (whose successor's device state is [σ]'s) ---- *)
    pose proof (exec_eff_ld8_at (wflat_st σ) b pc rs1 rd imm ea v Hrd Lpriv
                  ltac:(by rewrite Lms) ltac:(by rewrite Lsec)
                  ltac:(rewrite Lpmpc; exact Hpmp) ltac:(by rewrite Lpma) Lhtif Hea_σ Halea
                  Hram8 Hflat8) as Hexf.
    pose proof (exec_ld8_step_flat σ pc w rs1 rd imm ea v D dst
                  Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) ltac:(by rewrite Lpma) Lhtif
                  Lhart ltac:(by rewrite Lmisa) ltac:(by rewrite Lms)
                  ltac:(by rewrite Lms) ltac:(by rewrite Lsec)
                  ltac:(by rewrite Lelp) Hal4 Hfok Hag_σ HDmi Hgood Hdec Hrd
                  Hea_σ Halea Hram8 Hflat8) as Hflatstep.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame: determinism identifies the funnel's [t] with ours *)
    assert (Hdevt : mdev t = wm_dev σ).
    { destruct (Hflatstep tick) as (t2 & Ht2 & Hdv).
      assert (t = t2) as -> by congruence. exact Hdv. }
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as (HQi & HQl & HQv).
    (* the hart's own view cell moves to [σ']'s *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+4] *)
    iEval (rewrite (proj2 (proj2 (proj2 (proj2 (ld8_sexec_facts (wflat_st σ) b
             (add_vec_int pc 4) rd (regval_into_reg v))))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    (* recombine the two config halves, exactly as the SC leaf does *)
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hminv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k".
      iPureIntro. exact (conj HmIE (conj HMPRV (conj HSXL HKF))). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm'' Hpmpc'' [$Hpc' $Hnpc] Hrs1c Hrdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_ld8_carry σ σ' t ea dqv v with "Hpt").
      split_and!; [exact Hregs|exact Hdevs|exact Hmems|exact Himgs
                  |exact Hlogs|exact Hwsle|exact Hwf'|exact Hbnd'].
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. WHAT THIS COST, AND THE ONE SEAM THAT SHOULD BE RESHAPED

    THE PRICE, in CODE lines (comments and the import block excluded);
    the SC leaf this is measured against, [WpMmodeLoad.wp_ld_gpr], is 128:

      §1  the width-generic certificate + two instances ..........   37
      §2a the window ............................................   25
      §2b its three obligations .................................   40
      §2c the [execute] lemma at a generic [s0] .................   137
      §2d the [wP_eff] half .....................................  102
      §3a the SECOND replay of the step, for the device frame ...  116
      §3b the WP composition proper .............................  191
                                                                  ----
                                                          total    648

    §2a+§2b+§2d = 167 is the price the porting guide predicted (the window
    plus ONE re-instantiation of the leaf's own SC library lemma at the
    confined memory).  §1 (37) is paid once for the whole plain-load family,
    not per leaf.  §2c (137) is the SC leaf's own execute-fact block hoisted
    to an arbitrary [s0 : mstate] so that BOTH instantiations — confined and
    flat — are the same lemma applied twice; ~50 of it is work the SC leaf
    already does inline.

    §3a IS NOT.  It exists only because [WeakFunnel.wwp_cb] asks the leaf to
    return [wmstate_norg σ'], whose [dev_interp (wm_dev σ')] conjunct needs
    [wm_dev σ' = wm_dev σ] — and [WeakInstr.wstep_post] gives only
    [wm_dev σ' = mdev t], where [t] is the funnel's OWN successor, which the
    funnel constructs by register writes and then forgets.  The leaf's only
    way to learn [mdev t] is to replay the entire step a second time, at the
    FLAT state, and identify the two successors by determinism of [exec].
    That replay duplicates, premise for premise, what
    [WeakFetchEff.wP_eff_of_leaf_base] has just done at the confined state,
    and it will be duplicated ×50 by the sweep.

    THE FIX, and it is small and belongs in [WeakFunnel]: split [dev_interp]
    out of [wmstate_norg] the way [reg_interp] was already split out, and let
    the funnel carry it — it holds [t] concretely and closes the obligation
    with one [mdev_set_reg] chain.  (An equivalent, even cheaper fix: add
    [⌜mdev t = wm_dev σ⌝] to [wwp_cb]'s post-step argument list.)  Either
    deletes §3a from this file and from every leaf after it.

    TWO SMALLER SEAMS, worth recording:

    - [wwp_cb] hands the leaf [⌜register_lookup PC (wm_regs σ) = pc⌝] and
      NOTHING else about [σ]'s registers, although the funnel has just read
      the whole M-mode config tower off the bundle it was given.  So every
      leaf re-splits [mmode_config] into halves and re-reads the same nine
      registers through [reg_valid_dq].  Handing the callback the tower's
      values (or simply [⌜cfg_ok (wflat_st σ)⌝] plus the four pins the decode
      bridge needs) would delete ~25 lines per leaf.  It is also what forces
      the [D]/[dst] agreement premise here to be quantified over the register
      file instead of stated at [σ].

    - [WeakFetchEff.wP_eff_of_leaf_base] takes the [execute]'s [exec_eff]
      fact at a state written out as [MState (wm_regs σ) (wmem_restrict σ W)
      (wm_dev σ)].  Stating the leaf's own execute lemma over an ARBITRARY
      [s0 : mstate] (as [exec_eff_ld8_at] below does) is what makes the two
      instantiations — confined and flat — literally the same lemma applied
      twice, and it also dodges the [gmap Arch.pa] binder-instance trap
      outright.  Recommend that shape for every leaf of the sweep. *)

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions wcert_load_w.
Print Assumptions wP_eff_ld8.
Print Assumptions wwp_ld8_leaf.
