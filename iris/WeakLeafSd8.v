(** * WeakLeafSd8.v — M4 batch 2: the [sd]-class 8-byte STORE leaf, end to end

    The store analog of [WeakLeafLd8.v] (READ THAT FILE FIRST — it is the
    template and this file deliberately mirrors its section structure): from
    the M-mode config bundle, the PC cell, [WeakFunnel.winstr] and the OWNED
    eight-byte window at the effective address to [WP (Loop) {{ Φ }}].
    Nothing about the weak machine is left as a premise — no certificate, no
    [wP_eff], no [exec]/[exec_eff] fact.

    WHAT THE STORE EXERCISES THAT THE LOAD DID NOT:

      - THE [Q] HALF IS REAL.  [wQ_store8] names the MESSAGE the step appended
        ([wwrite_msg (Some cid) ea 8 v] at the log's fresh top) — the identity
        M3c's Q-type fix exists for — and the leaf USES it: the eight
        latest-write elements of the window are retargeted at that message
        ([WeakWord8.wlat8_store_prim]) and the log authority grows by it
        ([WeakGhost.wlog_update]), or [wmstate_norg σ'] would be unprovable.
      - THE [↦w₈]-IN / [↦w₈]-OUT CONTRACT.  The caller hands
        [vwp_hold (ea ↦w₈{1} vold) ws] and receives
        [vwp_hold (ea ↦w₈{1} vnew) ws'] — the window at the STORED value, at
        the successor's view — plus the store's timestamp fact in the
        [wQ_store] shape: [T ≤ flr (ws_view ws') (acc_addr ea j)] for every
        byte, at the leaf-chosen timestamp [T] (= [S (length (wm_log σ))]).
      - THE RELEASE-DEPOSIT SURFACE.  A releasing store freezes a payload [R]
        at its own timestamp ([WeakInstr.wwp_release_deposit]); the leaf takes
        [vwp_hold R ws] and hands back [monPred_at R (view_scl T)] — the
        OBJECTIVE payload a lock/escrow invariant stores.  A caller with no
        payload passes [R := emp].

    Assembled out of what batches 0/1 landed: [WeakFunnel.wwp_instr] (the
    funnel, with both fixed seams — [wcfg_regs] and the device frame),
    [WeakFetchEff.wP_eff_of_leaf_base] (the recipe),
    [WeakLeafEff8s.exec_eff_execute_STORE_8_gpr] (the shape — trace
    [[WEwrite wak_plain ea 8 v]]), and [WeakWord8]'s [↦w₈] tower (the
    resource, including the store-window update [wlat8_store_prim]).

    THREE SECTIONS, mirroring [WeakLeafLd8]:

    §1  [wcert_store_w] — [WeakCert.wcert_store] made WIDTH-GENERIC, the same
        way [WeakLeafLd8.wcert_load_w] generalized [wcert_load]: the script
        was generic on the nose ([4] appears only as the [n] of the window
        fold and inside [wQ_store_w 4]/[wV_store_w 4]), so this is the same
        script with [4] replaced by [n], plus the subsumption check
        [wcert_store_w_4] that the width-4 original IS the [n := 4] instance,
        plus the width-8 instance at the concrete fetch element.

    §2  THE WINDOW AND THE [wP_eff] HALF.  The window is the SHARED kit's
        [WeakLeafWin.wwin pc ea 8] (text word + data doubleword) with its
        membership/nonzero/pinned/conf-text lemmas; the WRITE side of
        confinement is [wwin_wdom] (the written domain stays inside the
        window; a store has no data-byte read, so the [conf_data] family is
        not needed at all).  What is per-leaf: the [execute] lemma at an
        arbitrary [s0 : mstate] ([exec_eff_sd8_at]) and the [wP_eff] half
        ([wP_eff_sd8]).

    §3  [wwp_sd8_leaf] — the leaf.  [WeakFunnel.wwp_instr] at
        [P := wP_eff … ([WEread wak_plain pc 4] ++ [WEwrite wak_plain ea 8 v])],
        [Q := wQ_store8 (Some cid) ea v] and §1's certificate; the post-step
        half retargets the window's elements, grows the log authority, and
        rebuilds [↦w₈] at the new value from [wQ_store8]'s view conjunct.

    EVERY PURE / GEOMETRY SIDE CONDITION IS A PREMISE (alignment, the PMP/PMA
    match, [dev_addr], the decode facts, [agree_on], [goodb0]); a real call
    site discharges each by [vm_compute], exactly as for the SC leaf
    [WpMmodeStore.wp_store_gpr]. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
(* DELIBERATELY NOT [Require Import SailStdpp.Base] — the [Countable Arch.pa]
   instance trap; see [WeakLeafLd8.v]'s header comment.  Everything this file
   needs from [Base] arrives through [Riscv.rv64d]. *)
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff WeakLeafEff8s.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [store_regs_facts], [reg_at_flat], [wpt8_align]). *)
Require Import WeakLeafWin.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE WIDTH-GENERIC STORE CERTIFICATE

    [WeakCert.wcert_store] is stated at width 4 with the [4] written into the
    body, but its proof never uses it: [4] occurs only as the width of the
    store's window fold and inside [WeakInstr.wQ_store] = [wQ_store_w 4] /
    [wV_store] = [wV_store_w 4], both of which [WeakInstr] already states
    width-generically.  The script below is [wcert_store]'s, verbatim, with
    [4] replaced by [n] — the same move [WeakLeafLd8.wcert_load_w] made for
    the load family. *)

Lemma wcert_store_w (n : N) (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (akw : akinfo) (ea : Arch.pa) (v : bv (8 * n)) :
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEwrite akw ea n v])
    (wQ_store_w n (Some cid) ea v).
Proof.
  apply wstep_cert_eff. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  rewrite weffs_cons2 weff_apply_read weff_apply_write in Hl Hws.
  rewrite wwrite_post_log wread_post_log in Hl.
  rewrite wwrite_post_ws wread_post_log in Hws.
  rewrite /wQ_store_w /wV_store_w. split_and!; [exact Hi|exact Hl|exact Hle|].
  intros j Hj. rewrite Hws flr_ws_view /acc_addr.
  etrans; [|apply Nat.le_max_r].
  apply (store_post_run_coh (wm_ws (wread_post s akf pf (coh_ts s pf nf)))
           (ak_sync akw) (pa_z ea) (N.to_nat n) (S (length (wm_log s))) j).
  exact Hj.
Qed.

(** THE SUBSUMPTION CHECK: [WeakCert.wcert_store]'s exact statement is the
    [n := 4] instance, on the nose. *)
Lemma wcert_store_w_4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid) [WEread akf pf nf; WEwrite akw ea 4 v])
    (wQ_store (Some cid) ea v).
Proof. exact (wcert_store_w 4 cid pc akf pf nf akw ea v). Qed.

(** ... and the width-8 instance AT THE CONCRETE FETCH ELEMENT
    [WeakFetchEff]'s replay produces — the [WeakFetchEff.wcert_store_base4]
    twin at width 8.  [[a] ++ [b]] IS [[a; b]], so this is one [exact]. *)
Lemma wcert_store8_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akw : akinfo) (ea : Arch.pa) (v : bv 64) :
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEwrite akw ea 8 v]))
    (wQ_store8 (Some cid) ea v).
Proof. exact (wcert_store_w 8 cid pc wak_plain pc 4 akw ea v). Qed.

(* ====================================================================== *)
(** ** 2. THE WINDOW AND THE [wP_eff] HALF

    *** 2a/2b. The window and every window obligation are the SHARED kit's
    ([WeakLeafWin]): [wwin pc ea 8] with [wwin_nonzero] / [wwin_pinned] /
    [wwin_conf_text], and the WRITE-DOMAIN CONFINEMENT [wwin_wdom] —
    [wP_eff_of_leaf_base]'s last obligation, [dom (mem s_exec) ⊆ W] over the
    store successor's [write_bytes] memory (failure mode 4 of the porting
    guide: the data word is in the window even though a store never reads
    it). *)

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation the
    model's register premises are stated with; every [gset Arch.pa] lives in
    [WeakLeafWin] (the binder-position instance trap — durable notes). *)
Import SailStdpp.Values.

(** *** 2c. THE SECOND INSTANTIATION — the whole per-instruction cost.

    [WeakLeafEff8s.exec_eff_execute_STORE_8_gpr] at an ARBITRARY [s0] with
    the funnel's two pre-writes ([minstret_increment := b] and
    [nextPC := pc+4]) on top — so the confined and the flat instantiation are
    literally this lemma applied twice (the batch-2 convention).  What it
    costs is the register peels that move each config fact past the two
    pre-writes; unlike the load there is NO memory premise at all — a store
    reads nothing. *)

(* The STORE side of the HTIF gate is [WeakFetchEff.exec_eff_within_htif_w_false]
   (§1 there, next to its [_readable] twin); the peel is [WeakLeafWin.leaf_peel]. *)

Lemma exec_eff_sd8_at (s0 : mstate) (b : bool)
    (pc : SailStdpp.Values.mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
    (ea : Arch.pa) (vs : SailStdpp.Values.mword 64) :
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
  (if Z.eqb (uint rs2) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s0.(sregs))
    = vs ->
  is_aligned_paddr (Physaddr ea) 8 = true ->
  (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
  exec_eff (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    (set_reg (set_reg s0 (R_bool minstret_increment) b)
             nextPC (add_vec_int pc 4))
  = Some (RETIRE_SUCCESS,
          MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                          nextPC (add_vec_int pc 4)))
                 (write_bytes s0.(mem) ea 8 vs) s0.(mdev),
          [WEwrite wak_plain ea 8 vs]).
Proof.
  intros Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Hal Hram8.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram8 0%nat); lia).
  assert (Hram7 : addr_is_ram (pa_add ea 7)) by (apply Hram8; lia).
  destruct (pma_all_ram Lpma ea 8
              (pma_access_ram _ _ _ Hram Hram7
                 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & _ & Hwrite & _).
  set (s := set_reg (set_reg s0 (R_bool minstret_increment) b)
                    nextPC (add_vec_int pc 4)).
  (* every config register, moved past the funnel's two pre-writes *)
  assert (Lpriv_s : register_lookup cur_privilege s.(sregs) = Machine)
    by (unfold s; leaf_peel cur_privilege; exact Lpriv).
  assert (Lms_s : register_lookup mstatus s.(sregs)
                  = register_lookup mstatus s0.(sregs))
    by (unfold s; leaf_peel mstatus; reflexivity).
  assert (Lsec_s : register_lookup mseccfg s.(sregs)
                   = register_lookup mseccfg s0.(sregs))
    by (unfold s; leaf_peel mseccfg; reflexivity).
  assert (Lpmpc_s : register_lookup pmpcfg_n s.(sregs)
                    = register_lookup pmpcfg_n s0.(sregs))
    by (unfold s; leaf_peel pmpcfg_n; reflexivity).
  assert (Lpma_s : register_lookup pma_regions s.(sregs)
                   = register_lookup pma_regions s0.(sregs))
    by (unfold s; leaf_peel pma_regions; reflexivity).
  assert (Lhtif_s : register_lookup htif_tohost_base s.(sregs) = None)
    by (unfold s; leaf_peel htif_tohost_base; exact Lhtif).
  (* the base register, uniform over [rs1] (x0 -> zero_reg) *)
  assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                          s.(sregs))
                  = (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs1))); reflexivity. }
  (* the data register, ditto over [rs2] *)
  assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                          s.(sregs)) = vs).
  { destruct (Z.eqb (uint rs2) 0) eqn:Ez; [exact Hvs|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs2))). exact Hvs. }
  (* the two identity bridges the model's [Let]s need *)
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
  rewrite -Hdata -Hpa.
  apply (exec_eff_execute_STORE_8_gpr rs2 rs1 imm region s Lpriv_s).
  - rewrite Lms_s. exact Lmprv.
  - rewrite Lsec_s. exact Lpmm.
  - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Hal.
    exact Hal.
  - apply exec_eff_pmpCheck_machine_none.
    intro i. rewrite Lpmpc_s. exact (proj1 (Lpmp i)).
  - rewrite Lpma_s Hpa. exact Hmatch.
  - rewrite Hpa. exact Hal.
  - exact Hwrite.
  - rewrite Hpa.
    exact (exec_eff_within_clint_false ea 8 s
             (addr_is_ram_not_in_clint _ Hram) ltac:(lia)).
  - rewrite Hpa.
    exact (exec_eff_within_sig_false ea 8 s
             (addr_is_ram_not_in_sig _ Hram) ltac:(lia)).
  - rewrite Hpa. exact (exec_eff_within_htif_w_false ea 8 s Lhtif_s).
  - rewrite Hpa. exact (addr_is_ram_not_dev _ Hram).
Qed.

(* A store writes NO register, so the successor's register file IS the
   pre-write tower's: the facts are [WeakLeafWin.store_regs_facts]. *)

(** *** 2d. THE [wP_eff] HALF, as a standalone lemma over the resources.

    The certificate's precondition, discharged from the four text bytes
    ([WeakFunnel.winstr_bytes]) and the owned eight-byte window
    ([WeakWord8.wpt8] — pinnedness of the data bytes, wrap-freedom, and the
    write-domain confinement), plus the M-mode register tower and the
    instruction's own pure geometry.  No model peel, no [vm_compute], no
    [riscv_step] — and, versus the load, no data-byte lookups either. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_sd8 (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 64) (vs : SailStdpp.Values.mword 64)
      (dq : dfrac) (D : register -> bool) (dst : mstate) :
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
    (* --- the instruction's pure geometry --- *)
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) (wm_regs σ))
      = vs ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the decode, exactly as the decode library states it --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), dst) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_Base w) -∗
    vwp_hold (wpt8 ea dq vold) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc 4] ++ [WEwrite wak_plain ea 8 vs]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
           Hal4 HnotRVC Hea Hvs Hram8 Hagree HDmi Hgood Hdec.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_Base w) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wpt8_flat_pin σ ea dq vold Hwf with "Hlat Hpt")
      as %[Haccea Hflatpin].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    iPureIntro.
    assert (Hpinea : forall j : nat, (j < 8)%nat ->
              pinned_read σ (acc_addr ea j))
      by (intros j Hj; exact (proj2 (Hflatpin j Hj))).
    destruct Hfok as (Hal2 & Hrampc & w' & [Hww _] & Htext). subst w'.
    apply (wP_eff_of_leaf_base cid σ (wwin pc ea 8) pc w
             (STORE (imm, Regidx rs2, Regidx rs1, 8))
             [WEwrite wak_plain ea 8 vs] D dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 8 Hrampc Hram8).
    - exact (wwin_pinned σ pc ea 8 Haccpc Haccea Hpinpc Hpinea).
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
    - exact (wwin_conf_text σ pc ea 8 w Htext).
    - exact HnotRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - reflexivity.
    - intro b. eexists. split_and!.
      + exact (exec_eff_sd8_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b pc rs1 rs2 imm ea vs
                 Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Halea Hram8).
      + exact (eq_trans (proj1 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 4))) Lhart).
      + exact (proj1 (proj2 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 4)))).
      + exact (wwin_wdom σ pc ea 8 vs).
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    Read the statement against the SC store leaf [WpMmodeStore.wp_store_gpr]:
    [instr] became [winstr_bytes] plus the decode field as a premise;
    [ea ↦ₚ₈ vold] became [vwp_hold (ea ↦w₈{1} vold) ws] paired with this
    hart's [WeakGhost.hart_ws] cell (which NAMES the view the resource is
    held at); the window comes back at the STORED value and the successor's
    view; and the continuation gains the store's weak-memory OUTPUT — the
    leaf-chosen timestamp [T] with its per-byte floor fact (the [wQ_store]
    shape) and the release payload [R] frozen at [view_scl T]
    ([WeakInstr.wwp_release_deposit]).  Everything else is the SC statement.

    THE FULL FRACTION IS FORCED, not a convenience: retargeting the window's
    latest-write elements at the appended message is a [ghost_map_update],
    which needs [DfracOwn 1] — same as the SC leaf's full-owned target
    window.

    The device frame is the funnel's [⌜mdev t = mdev s_exec⌝] (seam 1) and
    the config reads are its [⌜wcfg_regs σ pmpcfg0⌝] (seam 2); the only
    registers the leaf reads for itself are its own two operands. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wwp_sd8_leaf
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 : mword 5) (imm : mword 12)
      (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rs2v npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
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
         = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), t)) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea (DfracOwn 1) vold) ws -∗
    vwp_hold R ws -∗
    (∀ (ws' : wstate) (T : nat),
       ⌜ws_le ws ws'⌝ -∗
       ⌜forall j : nat, (j < 8)%nat ->
          (T <= flr (ws_view ws') (acc_addr ea j))%nat⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8 ea (DfracOwn 1) rs2v) ws' -∗
       monPred_at R (view_scl T) -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz Hrs2nz Hea Hram8 Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEwrite wak_plain ea 8 rs2v]))
              (wQ_store8 (Some (fin_to_nat cpu_id)) ea rs2v)
              Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_store8_base4 (fin_to_nat cpu_id) pc wak_plain ea rs2v)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (STORE (imm, Regidx rs2, Regidx rs1, 8))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* the config, as the funnel read it (seam 2) *)
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    (* the TWO registers the funnel does not read: base and data *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a)   as Lrs1.
    iDestruct (reg_valid with "Hreg Hrs2c") as %Lrs2_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs2))) σ b eq_refl))
                  Lrs2_a)   as Lrs2.
    (* the effective address and the stored value, at σ's own register file *)
    assert (Hea_σ : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (wm_regs σ)) (sign_extend' 64 imm) = ea).
    { rewrite (proj2 (Z.eqb_neq (uint rs1) 0) Hrs1nz) Lrs1. exact Hea. }
    assert (Hvs_σ : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                            (wm_regs σ)) = rs2v).
    { rewrite (proj2 (Z.eqb_neq (uint rs2) 0) Hrs2nz). exact Lrs2. }
    (* the agreement, at σ's registers *)
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]. }
    (* ---- the certificate's precondition (§2d) ---- *)
    iDestruct (wP_eff_sd8 (fin_to_nat cpu_id) σ pc w rs1 rs2 imm ea vold rs2v
                 (DfracOwn 1) D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp Hal4 HnotRVC Hea_σ
                 Hvs_σ Hram8 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt")
      as %HP.
    iDestruct (wpt8_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact ---- *)
    pose proof (exec_eff_sd8_at (wflat_st σ) b pc rs1 rs2 imm ea rs2v Lpriv
                  Lmprv Lpmm ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
                  Hvs_σ Halea Hram8) as Hexf.
    (* ---- the ONE register write the wrapper expects: nextPC ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (MState (sregs (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4)))
                    (write_bytes (mem (wflat_st σ)) ea 8 rs2v)
                    (mdev (wflat_st σ))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame (seam 1): the [execute] moved no device *)
    assert (Hdevt : mdev t = wm_dev σ) by (rewrite Hdevt0; reflexivity).
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf'
                       & Hbnd').
    destruct HQ as (HQi & HQl & HQle & HQv).
    (* the release deposit: freeze R at the store's own timestamp *)
    iDestruct (wwp_release_deposit R σ Hbnd with "HR") as "HRdep".
    (* THE WINDOW UPDATE: retarget the eight elements at the message [wQ_store8]
       names (failure mode 3 of the porting guide, discharged) *)
    iDestruct (wpt8_at_elems with "Hpt") as "(%Halea2 & %Haccea & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iMod (wlat8_store_prim (Some (fin_to_nat cpu_id)) σ ea rs2v
            with "Hlat H0 H1 H2 H3 H4 H5 H6 H7") as "[Hlat Hl8]".
    (* the log authority grows by the SAME message *)
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat cpu_id)) ea 8 rs2v]
            with "Hlogauth") as "Hlogauth".
    (* the hart's own view cell moves to σ' *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+4] *)
    iEval (cbn [sregs]) in "Hpc'".
    iEval (rewrite (proj2 (proj2 (store_regs_facts (wflat_st σ) b
             (add_vec_int pc 4))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    (* the config comes back WHOLE from the funnel: nothing to recombine *)
    iApply ("Hcont" $! (wm_ws σ') (S (length (wm_log σ))) with
              "[%] [%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hrs2c Hhws [Hl8] HRdep").
    - exact Hwsle.
    - intros j Hj. apply HQv. exact Hj.
    - (* the window, rebuilt at the successor's view AT THE STORED VALUE:
         [wQ_store8]'s view conjunct is exactly [wlat8_wpt8]'s floor premise *)
      iApply (wlat8_wpt8 ea (DfracOwn 1) (S (length (wm_log σ))) rs2v
                (wm_ws σ') Halea2 Haccea
                ltac:(intros j Hj; apply HQv; exact Hj) with "Hl8").
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. WHAT THIS COST — the second data point on the batch-2 unit price

    Against [WeakLeafLd8]'s 472 (its own count, comments/blanks excluded,
    statements included; §1's certificate is per-FAMILY and excluded there
    too), this file is SMALLER, for two reasons worth recording:

      - the window kit (§2a/2b of the load, 65 lines) is REUSED, not cloned —
        the window is width-shaped, not access-shaped; the store's only new
        window fact is the 15-line write-domain confinement
        ([WeakLeafWin.wwin_wdom]);
      - a store's [execute] has NO memory premise, so the load's
        [wwin_conf_data] family and the eight per-byte
        [wmem_restrict_lookup]s disappear; in exchange the WP composition
        gains the window update + log growth + deposit block (~25 lines) —
        the [Q]-half machinery the load never touched.

    The [↦w₈] store tower ([wlat8_store_prim], [wlat8_wpt8]) and the
    width-generic [wQ_store_w] family were already in place ([WeakWord8],
    M4-prep), so the store's marginal price over the load is dominated by
    §2c's execute block — the same ~137-line shape at a generic [s0]. *)

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions wcert_store_w.
Print Assumptions wP_eff_sd8.
Print Assumptions wwp_sd8_leaf.
