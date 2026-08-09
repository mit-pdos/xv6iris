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

    §2  THE WINDOW AND THE [wP_eff] HALF.  The window is the SHARED kit's
        [WeakLeafWin.wwin pc ea 8] (text word + data doubleword;
        [wwin_nonzero]/[wwin_pinned]/[wwin_conf_*] discharge the window
        obligations [wP_eff_of_leaf_base] asks for), and [wP_eff_ld8] feeds
        it the [execute] fact RE-INSTANTIATED AT THE CONFINED MEMORY.  That
        second instantiation of the same library lemma — at
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
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [load_sexec_facts], [reg_at_flat], [wpt8_align]). *)
Require Import WeakLeafWin.

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
  intros Hcoh. apply wstep_cert_eff. intros s s' Hi Hl Hws.
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
(** ** 2. THE WINDOW AND THE [wP_eff] HALF

    *** 2a/2b. The window and its obligations are the SHARED kit's
    ([WeakLeafWin]): [wwin pc ea 8] — the instruction's text word plus its
    data doubleword — with [wwin_nonzero] / [wwin_pinned] / [wwin_conf_text]
    / [wwin_conf_data] discharging the window obligations
    [WeakFetchEff.wP_eff_of_leaf_base] asks for. *)

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation the
    model's register premises are stated with.  Every [gset Arch.pa] this
    cone writes lives in [WeakLeafWin], above ITS [Values] import (durable
    notes, the binder-position instance trap). *)
Import SailStdpp.Values.

(** *** 2c. THE SECOND INSTANTIATION — the whole per-instruction cost.

    [WeakLeafEff8.exec_eff_execute_LOAD_8_gpr] again, at the CONFINED state
    [MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)] with the funnel's two
    pre-writes ([minstret_increment := b] and [nextPC := pc+4]) on top.  The
    SC/eff execute lemmas are state-generic, so nothing is re-proved here:
    what this costs is the register peels ([WeakLeafWin.leaf_peel]) that move
    each config fact past the two pre-writes, and the [wmem_restrict_lookup]
    of the eight data bytes. *)

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
  (* the base register, and the two identity bridges the model's [Let]s need *)
  assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                          s.(sregs))
                  = (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs1))); reflexivity. }
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

(** The successor's bookkeeping facts are [WeakLeafWin.load_sexec_facts]
    (width-independent, shared with the other load-class leaves). *)

(** *** 2d. THE [wP_eff] HALF, as a standalone lemma over the resources.

    This is the obligation that was blocked until [WeakFetchEff] landed: the
    certificate's precondition, discharged from the four text bytes
    ([WeakFunnel.winstr_bytes]), the eight owned data bytes
    ([WeakWord8.wpt8]) and the latest-write authority, plus the M-mode
    register tower and the instruction's own pure geometry.  Note what is NOT
    here: no model peel, no [vm_compute], no [riscv_step]. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

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
    apply (wP_eff_of_leaf_base cid σ (wwin pc ea 8) pc w
             (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
             [WEread wak_plain ea 8] D dst).
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
      + exact (exec_eff_ld8_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b pc rs1 rd imm ea v
                 Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Halea Hram8
                 (wwin_conf_data σ pc ea 8 v Hflat8)).
      + rewrite (proj1 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v))).
        exact Lhart.
      + exact (proj1 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v)))).
      + rewrite (proj1 (proj2 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 4) rd (regval_into_reg v))))).
        apply wmem_restrict_dom.
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    The device frame — [wmstate_norg σ']'s [dev_interp (wm_dev σ')] conjunct,
    which needs [wm_dev σ' = wm_dev σ] while [WeakInstr.wstep_post] gives only
    [wm_dev σ' = mdev t] — is handed over by the funnel as
    [⌜mdev t = mdev s_exec⌝], and [load_sexec_facts] says the [execute]'s own
    successor moved no device.  Two lines.  (Before that argument was added to
    [WeakFunnel.wwp_cb] the leaf had to replay the entire [riscv_step] a
    second time at the FLAT state and identify the two successors by
    determinism of [exec] — 116 lines duplicating, premise for premise, what
    [wP_eff_of_leaf_base] does at the confined state.) *)

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

    The [D]/[dst] decode-bridge premise is still quantified over the register
    file — a leaf's statement cannot mention [σ], which [WeakFunnel.wwp_cb]
    quantifies over — but INSTANTIATING it is now three [exact]s off
    [WeakFunnel.wcfg_regs], the config reads the funnel hands over, instead
    of a second [mmode_config] half and nine [reg_valid_dq]s. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wwp_ld8_leaf
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
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz Hrd Hea Hram8 Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 8]))
              (wQ_load_w 8 ea) Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_load8_base4 (fin_to_nat cpu_id) pc wak_plain ea eq_refl)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* the config, as the funnel read it -- no second [mmode_config] half,
       no [reg_valid_dq], no transport past the [minstret_increment] write *)
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    (* the ONE register the funnel does not read: this instruction's base *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
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
    { apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]. }
    (* ---- the certificate's precondition (§2d) ---- *)
    iDestruct (wP_eff_ld8 (fin_to_nat cpu_id) σ pc w rs1 rd imm ea v dqv D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp Hal4 HnotRVC Hrd Hea_σ Hram8
                 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the data doubleword ---- *)
    iDestruct (wwp_ld8 σ ea dqv v Hwf with "Hlat Hpt") as %[_ Hflat8].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact ---- *)
    pose proof (exec_eff_ld8_at (wflat_st σ) b pc rs1 rd imm ea v Hrd Lpriv
                  Lmprv Lpmm ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
                  Halea Hram8 Hflat8) as Hexf.
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
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame: the funnel's successor moved no device past the
       [execute]'s, and the [execute] moved none at all *)
    assert (Hdevt : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
                (add_vec_int pc 4) rd (regval_into_reg v)))))). }
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as (HQi & HQl & HQv).
    (* the hart's own view cell moves to [σ']'s *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+4] *)
    iEval (rewrite (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
             (add_vec_int pc 4) rd (regval_into_reg v))))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    (* the config comes back WHOLE from the funnel: nothing to recombine *)
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hrdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_ld8_carry σ σ' t ea dqv v with "Hpt").
      split_and!; [exact Hregs|exact Hdevs|exact Hmems|exact Himgs
                  |exact Hlogs|exact Hwsle|exact Hwf'|exact Hbnd'].
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. WHAT THIS COST

    THE PRICE, in CODE lines (comments and blank lines excluded, statements
    included), after the two funnel-seam fixes AND the batch-2 consolidation
    (the window kit, the register helpers and [wpt8_align] hoisted to
    [WeakLeafWin]; [addr_is_ram_pa_z_nz] there too).  The SC leaf this is
    measured against, [WpMmodeLoad.wp_ld_gpr], is 152 by the same count:

      §1  the width-generic certificate + instances     37  (per FAMILY)
      §2c the [execute] lemma at a generic [s0] ..     137
      §2d the [wP_eff] half ......................     102
      §3  the WP composition proper ..............     142

    plus the leaf's share of the ONE shared window kit.  The definitive
    price history (648 → 509 → this) lives in
    [claude-notes/projects/weak-memory.md], "THE BATCH-2 UNIT PRICE, FINAL".

    ONE SMALLER SEAM, worth recording:

    - [WeakFetchEff.wP_eff_of_leaf_base] takes the [execute]'s [exec_eff]
      fact at a state written out as [MState (wm_regs σ) (wmem_restrict σ W)
      (wm_dev σ)].  Stating the leaf's own execute lemma over an ARBITRARY
      [s0 : mstate] (as [exec_eff_ld8_at] above does) is what makes the two
      instantiations — confined and flat — literally the same lemma applied
      twice, and it also dodges the [gmap Arch.pa] binder-instance trap
      outright.  Recommend that shape for every leaf of the sweep. *)

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions wcert_load_w.
Print Assumptions wP_eff_ld8.
Print Assumptions wwp_ld8_leaf.
