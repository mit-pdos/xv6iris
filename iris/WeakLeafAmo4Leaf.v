(** * WeakLeafAmo4Leaf.v — M4 batch 2: the M-mode [amoswap.w.aq] leaf, end to
      end — THE lock instruction

    The last batch-2 shape, and the most novel one: TWO ADJACENT memory
    effects ([WEread aka ea 4; WEwrite akw ea 4 v] — the acquire-flavoured
    read of the OLD lock word immediately followed by the exclusive write of
    the NEW one), and a read half that fires in INVARIANT FORM — the leaf
    owns NOTHING at the lock word and carries NO view hypothesis about the
    acquirer, because the read's access kind is [ak_latest], whose
    admissibility condition IS [WeakMem.latest]
    ([WeakInstr.wwp_amoswap_w_aq_inv]'s design, [WeakBridge.ak_pins]).

    THE ALTITUDE IS [WeakAcquire.wacq_cb], NOT THE FUNNEL.  The existing lock
    library ([WeakAcquire.wwp_acquire_swap], [WeakBranch.wwp_acquire_loop_real])
    opens the lock invariant ITSELF, hands the leaf the lock word [v] the swap
    will return (read off the invariant's [wlat4] elements with no view
    hypothesis, [WeakLock.wlat4_flat_gen]) and runs [wacquire_core] — the
    element retarget, the log growth and the payload thaw — on the way back.
    So this leaf's deliverable is the ATTEMPT premise those lemmas consume:
    a lemma concluding [wacq_cb Φ γ lk R pc P], from the SC-style resources
    (the config bundle, the PC cell, [winstr_bytes], the three operand
    registers, this hart's view cell).  It therefore slots under
    [wwp_acquire_loop_real]'s per-instruction premise shape with NO
    restatement of the lock library — and, because [wacq_cb] sits directly on
    [WeakInstr.wp_winstr], the [riscv_step] wrapper assembly and the register
    bookkeeping that [WeakFunnel.wwp_instr] does for an owned-memory leaf are
    done HERE, by the same script (§5 mirrors the funnel's proof).

    THE PIN-REFINED CERTIFICATE CHAIN IS NOW [WeakCert]'s (consolidated).
    [WeakCert.wP_eff]'s whole-window pinnedness is UNPROVABLE for a
    contended acquire — the lock word is in the window (the write's
    footprint is confined by it) while the acquirer's index need not cover
    the latest write to it — so the confinement premise is TRACE-KEYED:
    [WeakCert.trace_pin] (only a read whose kind does not self-pin needs its
    footprint pinned), with [wstep_eff_confined_pin] as the primary
    induction and [wP_eff_pin] / [wstep_cert_eff_pin] / [wcert_amo_aq_pin]
    (+ [WeakFetchEff.wcert_amo_aq_pin_base4], [wP_eff_pin_of_leaf_base]) on
    top.  For this instruction the premise collapses to "the four TEXT
    bytes are pinned" — free from [WeakFunnel.winstr_pinned] — because the
    AMO's read is [ak_latest] and a write is not a read ([amo4_trace_pin],
    §2).

    LAYOUT.
      §2  the window: the SHARED kit's [WeakLeafWin.wwin pc ea 4] (text word
          + the 4-byte LOCK word; [wwin_wdom] is the write-domain
          confinement), and the trace-pin fact [amo4_trace_pin];
      §3  the [execute] at an arbitrary [s0 : mstate] ([exec_eff_amo4_at],
          wrapping batch 1's [WeakLeafAmo4.exec_eff_execute_AMOSWAP_4_gpr] —
          note the FOUR MMIO gates, both [within_htif_readable] AND
          [_writable]), and the successor's register facts
          ([amo4_sexec_facts] — the successor is an [MState] LITERAL under
          one [set_reg], the AMO-class gotcha);
      §4  the [wP_eff_pin] half ([wP_eff_pin_amo4], one application of
          [WeakFetchEff.wP_eff_pin_of_leaf_base]);
      §5  the leaf: [wwp_amo4_acq_leaf], concluding [wacq_cb].

    EVERY PURE / GEOMETRY SIDE CONDITION IS A PREMISE (alignment, the decode
    facts, [agree_on], [goodb0], the stored value being [lock_one]); a real
    call site discharges each by [vm_compute], exactly as for the SC leaves. *)
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
   needs from [Base] arrives through [Riscv.rv64d].  ([Require Import] of a
   module that itself imported [Base] — [WeakFunnel], [WeakLeafAmo4] — does
   NOT re-export [Base]'s instances; [Import] is not transitive.) *)
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff.
Require Import WeakFunnel WpDecodeBridge.
Require Import WeakExec WeakLock WeakAcquire WeakBranch.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes SmodeCore.
Require Import RegFile WpGpr WpMmodeLeafBase WpLock.
(* Batch 1's mirror: the [amoswap.w.aq] [exec_eff] fact (two adjacent
   effects), read-only use. *)
Require Import WeakLeafAmo4.
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [reg_at_flat]).  The [within_htif_writable] gate
   ([exec_eff_within_htif_w_false]) is [WeakFetchEff] §1's. *)
Require Import WeakLeafWin.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 2. THE WINDOW: the text word plus the 4-byte LOCK word

    The SHARED kit's [WeakLeafWin.wwin pc ea 4] ([wwin_nonzero] /
    [wwin_conf_text] / [wwin_conf_data]; [wwin_wdom] is the write-domain
    confinement — the lock word is in the window although the AMO's READ of
    it needs no pinnedness, because the WRITE's footprint is confined by the
    window).  What is per-leaf is only the TRACE-PIN fact below. *)

(** THE TRACE-PIN FACT, at this instruction's trace: the fetch is the only
    non-pinning read (its footprint is the TEXT, pinned for free), the AMO's
    read pins itself ([ak_latest]), and a write is not a read. *)
Lemma amo4_trace_pin (σ : wmstate) (pc lk : Arch.pa) (v : bv (8 * 4)) :
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pc j)) ->
  trace_pin σ [WEread wak_plain pc 4;
               WEread (AkInfo false true true) lk 4;
               WEwrite (AkInfo false true false) lk 4 v].
Proof.
  intros Hpc ak pa n Hin Hnp j Hj.
  apply elem_of_cons in Hin as [He|Hin].
  { injection He as -> -> ->. exact (Hpc j Hj). }
  apply elem_of_cons in Hin as [He|Hin].
  { injection He as -> -> ->. discriminate Hnp. }
  apply elem_of_cons in Hin as [He|Hin].
  { discriminate He. }
  apply elem_of_nil in Hin. destruct Hin.
Qed.

(** FROM HERE ON [SailStdpp.Values] IS IMPORTED — for the ['b"…"] literal
    notation the model's register premises are stated with.  Every
    [gset Arch.pa] fact this file states is above this line. *)
Import SailStdpp.Values.

(* ====================================================================== *)
(** ** 3. THE [execute] AT AN ARBITRARY [s0] — the whole per-instruction cost

    [WeakLeafAmo4.exec_eff_execute_AMOSWAP_4_gpr] with the funnel-shaped two
    pre-writes ([minstret_increment := b], [nextPC := pc+4]) on top, stated
    over an ARBITRARY [s0 : mstate] (the batch-2 convention: the confined and
    the flat instantiation are the same lemma applied twice).  What it costs
    is the register peels past the two pre-writes and the identity bridges
    for the model's address [Let]s.  The AMO probes FOUR MMIO gates — both
    HTIF windows; [exec_eff_within_htif_w_false] is [WeakLeafSd8]'s. *)

Lemma exec_eff_amo4_at (s0 : mstate) (b : bool)
    (pc : SailStdpp.Values.mword 64) (rs1 rs2 rd : mword 5)
    (ea : Arch.pa) (w sv : SailStdpp.Values.mword 32) :
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
          (zeros' 64) = ea ->
  sign_extend' (Z.mul 8 (__id 4))
    (trunc (Z.mul (__id 4) 8)
       (if Z.eqb (uint rs2) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
               s0.(sregs))) = sv ->
  is_aligned_paddr (Physaddr ea) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
  (forall j : nat, (j < 4)%nat -> s0.(mem) !! pa_add ea j = Some (nth_byte w j)) ->
  exec_eff (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
    (set_reg (set_reg s0 (R_bool minstret_increment) b)
             nextPC (add_vec_int pc 4))
  = Some (RETIRE_SUCCESS,
          set_reg (MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                                   nextPC (add_vec_int pc 4)))
                          (write_bytes s0.(mem) ea 4 sv) s0.(mdev))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg
                     (sign_extend' 64
                        (autocast (T := SailStdpp.Values.mword)
                           (w : SailStdpp.Values.mword (8 * 4))
                         : SailStdpp.Values.mword (4 * 8)))),
          [WEread (AkInfo false true true) ea 4;
           WEwrite (AkInfo false true false) ea 4 sv]).
Proof.
  intros Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hsv Hal Hram4 Hbytes.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram4 0%nat); lia).
  assert (Hram3 : addr_is_ram (pa_add ea 3)) by (apply Hram4; lia).
  destruct (pma_all_ram Lpma ea 4
              (pma_access_ram _ _ _ Hram Hram3
                 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & Hread & Hwrite & Hamo & _).
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
                          s.(sregs))
                  = (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs2) 0) eqn:Ez; [reflexivity|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs2))); reflexivity. }
  (* the stored value and the two address bridges the model's [Let]s need *)
  assert (Hsv_s : sign_extend' (Z.mul 8 (__id 4))
                    (trunc (Z.mul (__id 4) 8)
                       (if Z.eqb (uint rs2) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                               s.(sregs))) = sv)
    by (rewrite Hdata; exact Hsv).
  assert (Ha8 : zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (zeros' 64)) (xlen - 0 - 1) 0) = ea).
  { rewrite Hbase Hea zero_extend'_id subrange_id. reflexivity. }
  assert (Hpa : zero_extend' 64 (zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (zeros' 64)) (xlen - 0 - 1) 0)) = ea).
  { rewrite Ha8 zero_extend'_id. reflexivity. }
  rewrite -Hsv_s -Hpa.
  apply (exec_eff_execute_AMOSWAP_4_gpr rs2 rs1 rd region w s Hrd Lpriv_s).
  - rewrite Lms_s. exact Lmprv.
  - rewrite Lsec_s. exact Lpmm.
  - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Hal.
    exact Hal.
  - rewrite Hpa. apply exec_eff_pmpCheck_machine_none.
    intro i. rewrite Lpmpc_s. exact (proj1 (Lpmp i)).
  - rewrite Lpma_s Hpa. exact Hmatch.
  - rewrite Hpa. exact Hal.
  - exact Hread.
  - exact Hwrite.
  - exact (Hamo AMOSWAP 4 eq_refl).
  - rewrite Hpa.
    exact (exec_eff_within_clint_false ea 4 s
             (addr_is_ram_not_in_clint _ Hram) ltac:(lia)).
  - rewrite Hpa.
    exact (exec_eff_within_sig_false ea 4 s
             (addr_is_ram_not_in_sig _ Hram) ltac:(lia)).
  - rewrite Hpa. exact (exec_eff_within_htif_false ea 4 s Lhtif_s).
  - rewrite Hpa. exact (exec_eff_within_htif_w_false ea 4 s Lhtif_s).
  - rewrite Hpa. exact (addr_is_ram_not_dev _ Hram).
  - intros j Hj. rewrite Hpa. unfold s. rewrite !mem_set_reg.
    apply Hbytes. lia.
Qed.

(** The successor's bookkeeping facts.  THE AMO-CLASS GOTCHA (notes, "THE
    SECOND LEAF"): the successor is an [MState] LITERAL under one [set_reg],
    not a [set_reg] tower — so each fact is stated at that exact shape and
    proved by peeling the [rd] write, collapsing the literal ([cbn [sregs]]),
    then peeling the pre-write tower; consumers use [exact]/[eq_trans]. *)
Lemma amo4_sexec_facts (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (rd : mword 5)
    (M : _) (D : _) (x : SailStdpp.Values.mword 64) :
  let s_exec :=
    set_reg (MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                             nextPC npc)) M D)
            (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg x) in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ register_lookup nextPC (sregs s_exec) = npc
  /\ mem s_exec = M
  /\ mdev s_exec = D.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    cbn [sregs].
    rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
            (set_lookup_ne hart_state (R_bool minstret_increment)
               _ _ ltac:(reg_ne)).
    reflexivity.
  - rewrite (set_lookup_ne (R_bool minstret_increment)
               (R_bitvector_64 (gpr_of_Z (uint rd))) _ _ ltac:(reg_ne)).
    cbn [sregs].
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - rewrite (set_lookup_ne nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    cbn [sregs].
    rewrite sregs_set_reg. apply register_lookup_set.
  - rewrite mem_set_reg. reflexivity.
  - rewrite mdev_set_reg. reflexivity.
Qed.

(* ====================================================================== *)
(** *** 4. THE [wP_eff_pin] HALF, over the resources.

    Versus the load/store leaves' [wP_eff_*] lemmas, the ONE structural
    difference is the invariant form: the lock word's flat bytes arrive as a
    PURE premise (handed by [WeakAcquire.wacq_cb], off the invariant's
    [wlat4] elements) — no [vwp_hold], no view hypothesis, no ownership. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_pin_amo4 (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 rd : mword 5) (lk : Arch.pa) (v sv : SailStdpp.Values.mword 32)
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
    (* --- the instruction's pure geometry --- *)
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    uint rd <> 0 ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (zeros' 64) = lk ->
    sign_extend' (Z.mul 8 (__id 4))
      (trunc (Z.mul (__id 4) 8)
         (if Z.eqb (uint rs2) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                 (wm_regs σ))) = sv ->
    is_aligned_paddr (Physaddr lk) 4 = true ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add lk j)) ->
    (* --- the lock word's flat bytes: the INVARIANT-FORM premise --- *)
    (forall j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte v j)) ->
    (* --- the decode, exactly as the decode library states it --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd),
              dst) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_Base w) -∗
    ⌜wP_eff_pin (Some cid)
       ([WEread wak_plain pc 4]
        ++ [WEread (AkInfo false true true) lk 4;
            WEwrite (AkInfo false true false) lk 4 sv]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
           Hal4 HnotRVC Hrd Hea Hsv Halk Hram4 Hflatlk Hagree HDmi Hgood Hdec.
    iIntros "Hlat #Hbs".
    iDestruct (winstr_bytes_lookup σ pc (F_Base w) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpinpc.
    iPureIntro.
    destruct Hfok as (Hal2 & Hrampc & w' & [Hww _] & Htext). subst w'.
    apply (wP_eff_pin_of_window cid _ σ (wwin pc lk 4)).
    - exact Hwf.
    - exact (wwin_nonzero pc lk 4 Hrampc Hram4).
    - exact (amo4_trace_pin σ pc lk sv Hpinpc).
    - apply (exec_eff_step_of_leaf_base σ (wwin pc lk 4) pc w
               (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
               [WEread (AkInfo false true true) lk 4;
                WEwrite (AkInfo false true false) lk 4 sv] D dst).
      + exact Lpc.
      + exact Lpriv.
      + exact (pmp_all_off_allows_all _ Lpmp).
      + exact Lpma.
      + exact Lhtif.
      + exact Lhart.
      + exact LmisaS.
      + exact LmIE.
      + exact Lelp.
      + exact Hal4.
      + exact Hrampc.
      + exact (wwin_conf_text σ pc lk 4 w Htext).
      + exact HnotRVC.
      + exact Hagree.
      + exact HDmi.
      + exact Hgood.
      + exact Hdec.
      + reflexivity.
      + intro b. eexists. split_and!.
        * exact (exec_eff_amo4_at
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc lk 4))
                      (wm_dev σ)) b pc rs1 rs2 rd lk v sv
                   Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hsv Halk Hram4
                   (wwin_conf_data σ pc lk 4 v Hflatlk)).
        * exact (eq_trans (proj1 (amo4_sexec_facts
                     (MState (wm_regs σ) (wmem_restrict σ (wwin pc lk 4))
                        (wm_dev σ)) b (add_vec_int pc 4) rd _ _ _)) Lhart).
        * exact (proj1 (proj2 (amo4_sexec_facts
                     (MState (wm_regs σ) (wmem_restrict σ (wwin pc lk 4))
                        (wm_dev σ)) b (add_vec_int pc 4) rd _ _ _))).
        * rewrite (proj1 (proj2 (proj2 (proj2 (amo4_sexec_facts
                     (MState (wm_regs σ) (wmem_restrict σ (wwin pc lk 4))
                        (wm_dev σ)) b (add_vec_int pc 4) rd _ _ _))))).
          apply (wwin_wdom σ pc lk 4).
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 5. THE LEAF — the attempt premise of the lock library

    [wwp_amo4_acq_leaf] concludes [WeakAcquire.wacq_cb Φ γ lk R pc P] with
    [P := wP_eff_pin … [fetch; read; write]], so a caller instantiates
    [WeakBranch.wwp_acquire_loop_real]'s attempt premise with it directly
    (certificate: [wcert_amo_aq_pin_base4], [ak_coh]/[ak_sync] by
    [reflexivity]) — the lock library is consumed WITHOUT restatement.

    Because [wacq_cb] sits directly on [WeakInstr.wp_winstr] (the invariant
    is opened by [wwp_acquire_swap] AROUND this callback), the [riscv_step]
    wrapper — the [minstret_increment] pre-write, the fetch, the interrupt
    gate, the decode, the PC tick, the [minstret] bump, the clock tick — is
    assembled HERE, by [WeakFunnel.wwp_instr]'s own script over the SAME
    library lemmas; the funnel itself cannot be used at this altitude.

    WHAT THE CALLER GETS BACK, per arm, one instruction later: the config
    bundle rebuilt whole, [pc_is (pc+4)], the operand cells, [rd] holding the
    sign-extended OLD lock word [v], this hart's view cell at [ws'] — and, on
    the SUCCESS arm ([v = lock_zero]), the holder token plus the payload [R]
    THAWED at the hart's own index ([vwp_hold R ws']; the retarget, the log
    growth and the thaw are [wacquire_core]'s, run by [wwp_acquire_swap]).
    The continuation is taken under [▷] so the failure arm can be built from
    the loop's [▷ (Kb -∗ WP)] retry edge. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wwp_amo4_acq_leaf (γ : gname) (lk : Arch.pa) (R : vProp Σ)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rs2 rd : mword 5) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rs2v rd0 npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (zeros' 64) = lk ->
    (* the stored value IS the lock constant: [rs2] holds 1 *)
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) rs2v)
      = (lock_one : SailStdpp.Values.mword 32) ->
    is_aligned_paddr (Physaddr lk) 4 = true ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add lk j)) ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd),
                 t)) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd),
              dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    ▷ (∀ (v : bv 32) (ws' : wstate),
         ⌜ws_le ws ws'⌝ -∗
         mmode_config (DfracOwn q) -∗
         pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
         pc_is (add_vec_int pc 4) -∗
         R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
         R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
         R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
           regval_into_reg
             (sign_extend' 64
                (autocast (T := SailStdpp.Values.mword)
                   (v : SailStdpp.Values.mword (8 * 4))
                 : SailStdpp.Values.mword (4 * 8))) -∗
         hart_ws cpu_id ws' -∗
         ((⌜v = lock_zero⌝ ∗ vwp_hold R ws' ∗ locked γ cpu_id)
          ∨ ⌜v ≠ lock_zero⌝) -∗
         WWP Loop) -∗
    wacq_cb γ lk R pc
      (wP_eff_pin (Some (fin_to_nat cpu_id))
         ([WEread wak_plain pc 4]
          ++ [WEread (AkInfo false true true) lk 4;
              WEwrite (AkInfo false true false) lk 4 lock_one])).
  Proof.
    intros Hpmp Hal4 Hrs1nz Hrs2nz Hrdnz Hea Hsv Halk Hram4
           Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrs2c Hrdc #Hbs Hhws Hcont".
    rewrite /wacq_cb.
    iIntros (σ v) "%Hflatlk Hlat Hrest".
    iDestruct (wmstate_rest_split σ with "Hrest") as "[Hreg Hnorg]".
    iDestruct "Hnorg" as "(%Hbnd & %Hnv & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* the config bundle, exactly as the funnel opens it *)
    iDestruct "Hmm" as "(#Hhw & #Hmiv0 & Hhs & Hpriv & Hmst0)".
    iDestruct "Hmst0" as (mstatus0) "(Hmstatus & %HmIE & %HMPRV & %HSXL & %HKF)".
    iAssert (minstret_inv) as "#Hmiv"; [iExact "Hmiv0"|].
    iDestruct "Hmiv0" as "#(Hinv & Hcinv & Hgc)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    (* every register the wrapper / fetch / decode reads, at [wm_regs σ] *)
    iDestruct (reg_valid    with "Hreg Hpc")       as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")     as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")     as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")     as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lmseccfg.
    iDestruct (reg_valid_dq with "Hreg Hmstatus")  as %Lmstatus.
    iDestruct (reg_valid_dq with "Hreg Help")      as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hhs")       as %Lhs.
    iDestruct (reg_valid    with "Hreg Hrs1c")     as %Lrs1.
    iDestruct (reg_valid    with "Hreg Hrs2c")     as %Lrs2.
    (* the config facts in the shapes the assembly consumes *)
    assert (LmisaS' : eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ)))
                        ('b"1") = true) by (rewrite Lmisa; exact HmisaS).
    assert (LmIE' : eq_vec (_get_Mstatus_MIE
                        (register_lookup mstatus (wm_regs σ))) ('b"1") = false)
      by (rewrite Lmstatus; exact HmIE).
    assert (Lmprv' : eq_vec (_get_Mstatus_MPRV
                        (register_lookup mstatus (wm_regs σ))) ('b"1") = false)
      by (rewrite Lmstatus; exact HMPRV).
    assert (Lpmm' : pmm_mode_backwards
                      (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
                    = PMM_Disabled)
      by (rewrite Lmseccfg; exact Hseccfg1).
    assert (Lelp' : eq_vec (register_lookup elp (wm_regs σ))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    assert (Lpmp' : pmp_all_off (register_lookup pmpcfg_n (wm_regs σ)))
      by (rewrite Lpmpc; exact Hpmp).
    assert (Lpma' : pma_allows_all (register_lookup pma_regions (wm_regs σ)))
      by (rewrite Lpma; exact Hpma_all).
    assert (LmisaC' : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                        ('b"1") = true) by (rewrite Lmisa; exact HmisaC).
    (* the effective address and the stored value, at σ's registers *)
    assert (Hea_σ : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (wm_regs σ)) (zeros' 64) = lk).
    { rewrite (proj2 (Z.eqb_neq (uint rs1) 0) Hrs1nz) Lrs1. exact Hea. }
    assert (Hsv_σ : sign_extend' (Z.mul 8 (__id 4))
                      (trunc (Z.mul (__id 4) 8)
                         (if Z.eqb (uint rs2) 0 then zero_reg
                          else register_lookup
                                 (R_bitvector_64 (gpr_of_Z (uint rs2)))
                                 (wm_regs σ)))
                    = (lock_one : SailStdpp.Values.mword 32)).
    { rewrite (proj2 (Z.eqb_neq (uint rs2) 0) Hrs2nz) Lrs2. exact Hsv. }
    (* the agreement, at σ's registers *)
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | rewrite Lmisa; exact Hmisa_val0
                    | rewrite Lmseccfg; exact Hmseccfg_val0]. }
    (* the text facts *)
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    (* φ-upgrade: the fetch window's violation-freedom, off the text bundle;
       the lock word's half is the CALLER's ([wwp_acquire_swap] holds the
       invariant's element bundle at σ'). *)
    iDestruct (winstr_nv cpu_id (wm_img σ) (wm_log σ) pc (F_Base w)
                 with "Hlat Hbs") as %Hnvpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* ---- the certificate's precondition (§4c) ---- *)
    iDestruct (wP_eff_pin_amo4 (fin_to_nat cpu_id) σ pc w rs1 rs2 rd lk v
                 lock_one D dst
                 Hwf Lpc Lpriv Lpmp' Lpma' Lhtif Lhs LmisaS' LmIE' Lmprv'
                 Lpmm' Lelp' Hal4 HnotRVC Hrdnz Hea_σ Hsv_σ Halk Hram4
                 Hflatlk Hag_σ HDmi Hgood Hdec with "Hlat Hbs") as %HP.
    (* ---- open the minstret invariant, held across the ▷ ---- *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (mst0 mi0) "[Hmst Hmi]".
    (* the [minstret_increment] flag, funnel-chosen *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege (wflat_st σ).(sregs)) (wflat_st σ))
      as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi")
      as "[Hreg Hmi]".
    (* ---- the state the run really starts from ---- *)
    assert (Lpriv_a : register_lookup cur_privilege
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = Machine).
    { rewrite (set_mi_lookup cur_privilege _ b eq_refl) wflat_st_regs.
      exact Lpriv. }
    assert (Lpc_a : register_lookup PC
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs) = pc).
    { rewrite (set_mi_lookup PC _ b eq_refl) wflat_st_regs. exact Lpc. }
    assert (Lmisa_a : register_lookup misa
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = misa0).
    { rewrite (set_mi_lookup misa _ b eq_refl) wflat_st_regs. exact Lmisa. }
    assert (Lmstatus_a : register_lookup mstatus
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = mstatus0).
    { rewrite (set_mi_lookup mstatus _ b eq_refl) wflat_st_regs.
      exact Lmstatus. }
    assert (Lelp_a : register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = elp0).
    { rewrite (set_mi_lookup elp _ b eq_refl) wflat_st_regs. exact Lelp. }
    assert (Lmseccfg_a : register_lookup mseccfg
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = mseccfg0).
    { rewrite (set_mi_lookup mseccfg _ b eq_refl) wflat_st_regs.
      exact Lmseccfg. }
    assert (Lhs_a : register_lookup hart_state
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs)
              = HART_ACTIVE tt).
    { rewrite (set_mi_lookup hart_state _ b eq_refl) wflat_st_regs. exact Lhs. }
    (* fetch, at the post-write state (only the MEMORY matters) *)
    assert (Hfetch : exec (fetch tt)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (F_Base w,
                      set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply (exec_fetch_flat _ pc (F_Base w)).
      - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl) wflat_st_regs.
        exact (pmp_all_off_allows_all _ Lpmp').
      - rewrite (set_mi_lookup pma_regions _ b eq_refl) wflat_st_regs.
        exact Lpma'.
      - rewrite Lmisa_a. exact HmisaC.
      - exact Lpc_a.
      - exact Lpriv_a.
      - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl) wflat_st_regs.
        exact Lhtif.
      - apply (fetch_flat_ok_mem (wflat_st σ)); [apply mem_set_reg | exact Hfok]. }
    (* the interrupt dispatch is a no-op *)
    assert (Hdisp : exec (dispatchInterrupt Machine)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (None,
                      set_reg (wflat_st σ) (R_bool minstret_increment) b)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none _ _
               (exec_currentlyEnabled_S
                  (set_reg (wflat_st σ) (R_bool minstret_increment) b))).
      - rewrite Lmisa_a. exact HmisaS.
      - rewrite Lmstatus_a. exact HmIE. }
    assert (Help_a : eq_vec (register_lookup elp
              (set_reg (wflat_st σ) (R_bool minstret_increment) b).(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { rewrite Lelp_a. exact Help_np. }
    (* the decode, off the PURE decode premise *)
    pose proof (Hdecf (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  ltac:(rewrite Lpriv_a; reflexivity)
                  ltac:(rewrite Lmisa_a; exact HmisaC)
                  ltac:(rewrite Lmisa_a; exact HmisaA)
                  ltac:(rewrite Lmisa_a; exact Hmisa_val0)
                  ltac:(unfold cfg_ok; left; split;
                        [ exact Lpriv_a
                        | rewrite Lmseccfg_a; exact Hmseccfg_val0 ])) as Hdec_a.
    (* ---- the [execute] fact at the FLAT state (nextPC written inside) ---- *)
    assert (Hbytes_flat : forall j : nat, (j < 4)%nat ->
              (wflat_st σ).(mem) !! pa_add lk j = Some (nth_byte v j))
      by exact Hflatlk.
    pose proof (exec_eff_exec _ _ _ _ _
                  (exec_eff_amo4_at (wflat_st σ) b pc rs1 rs2 rd lk v lock_one
                     Hrdnz Lpriv Lmprv' Lpmm' Lpmp' Lpma' Lhtif Hea_σ Hsv_σ
                     Halk Hram4 Hbytes_flat)) as Hexec.
    set (s_exec := set_reg
           (MState (sregs (set_reg (set_reg (wflat_st σ)
                             (R_bool minstret_increment) b)
                            nextPC (add_vec_int pc 4)))
                   (write_bytes (wflat_st σ).(mem) lk 4
                      (lock_one : SailStdpp.Values.mword 32))
                   (wflat_st σ).(mdev))
           (R_bitvector_64 (gpr_of_Z (uint rd)))
           (regval_into_reg
              (sign_extend' 64
                 (autocast (T := SailStdpp.Values.mword)
                    (v : SailStdpp.Values.mword (8 * 4))
                  : SailStdpp.Values.mword (4 * 8)))))
      in Hexec.
    pose proof (amo4_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                  (write_bytes (wflat_st σ).(mem) lk 4
                     (lock_one : SailStdpp.Values.mword 32))
                  (wflat_st σ).(mdev)
                  (sign_extend' 64
                     (autocast (T := SailStdpp.Values.mword)
                        (v : SailStdpp.Values.mword (8 * 4))
                      : SailStdpp.Values.mword (4 * 8))))
      as (Fhs & Fmi & Fnpc & Fmem & Fdev).
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg
               (sign_extend' 64
                  (autocast (T := SailStdpp.Values.mword)
                     (v : SailStdpp.Values.mword (8 * 4))
                   : SailStdpp.Values.mword (4 * 8))))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    (* ---- the whole step: [run_hart_active], then the wrapper's writes ---- *)
    assert (Hha : exec (run_hart_active 0)
              (set_reg (wflat_st σ) (R_bool minstret_increment) b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec)).
    { exact (exec_hart_active_progress_base_gen Machine
               (set_reg (wflat_st σ) (R_bool minstret_increment) b)
               (set_reg (wflat_st σ) (R_bool minstret_increment) b)
               s_exec w
               (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
               pc RETIRE_SUCCESS
               Lpriv_a Hdisp Hfetch Hdec_a Help_a eq_refl Lpc_a Hexec I). }
    assert (Lhs_e : register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt)
      by (rewrite Fhs wflat_st_regs; exact Lhs).
    pose proof (exec_riscv_step_hart_active (wflat_st σ) s_exec _ b
                  Hsi Lhs_a Hha Lhs_e Fmi) as Hstep0.
    (* the wrapper's own register writes: tick PC, maybe bump minstret *)
    iAssert (|==> ∃ t0 : mstate,
                ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
                ⌜mdev t0 = wm_dev σ⌝ ∗
                reg_interp (sregs t0) ∗ minstret_inv_body ∗
                PC ↦ᵣ (register_lookup nextPC (sregs s_exec)))%I
      with "[Hreg Hmst Hmi Hpc]" as ">Hw".
    { iMod (reg_update _ PC _ (register_lookup nextPC (sregs s_exec))
              with "Hreg Hpc") as "[Hreg Hpc]".
      destruct b.
      - iMod (reg_update _ minstret _
                (add_vec_int (register_lookup minstret
                   (sregs (set_reg s_exec PC
                             (register_lookup nextPC (sregs s_exec))))) 1)
                with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; rewrite !mdev_set_reg; exact Fdev|].
        iFrame "Hreg Hpc". iExists _, true. iFrame.
      - iModIntro. iExists _. iSplitR; [iPureIntro; exact Hstep0|].
        iSplitR; [iPureIntro; rewrite !mdev_set_reg; exact Fdev|].
        iFrame "Hreg Hpc". iExists _, false. iFrame. }
    iDestruct "Hw" as (t0) "(%Hst0 & %Hdev0 & Hreg & Hbody & Hpc)".
    destruct (exec_tick_clock t0) as (c' & ti' & p' & Htick).
    pose proof (exec_riscv_step_tick _ _ _ Hst0 Htick) as Hst1.
    (* ---- hand everything to [wacq_cb]'s shape ---- *)
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hcl".
    iSplitR; [iPureIntro; exact Lpc|].
    iSplitR; [iPureIntro; exact Hpin|].
    iSplitR; [iPureIntro; exact HP|].
    iSplitR; [iPureIntro; exact Hnvpc|].
    iFrame "Hlat".
    iExists t0, (set_reg (set_reg (set_reg t0 mcycle c') mtime ti') mip p').
    iSplitR; [iPureIntro; exact Hst0|].
    iSplitR; [iPureIntro; exact Hst1|].
    iNext. iIntros (tick σ') "%Hpost Harm".
    iMod "Hcl" as "_".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf'
                       & Hbnd').
    destruct Hlogs as [l Hlogs].
    (* the log authority grows to σ''s log *)
    iMod (wlog_update (wm_log σ) l with "Hlogauth") as "Hlogauth".
    (* the hart's own view cell moves to σ''s *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    (* the device frame: [t] is register writes over [s_exec], which moved
       no device *)
    assert (Hdevt : wm_dev σ' = wm_dev σ).
    { rewrite Hdevs. destruct tick; [rewrite !mdev_set_reg|]; exact Hdev0. }
    (* the PC the wrapper hands back IS [pc+4] *)
    iEval (rewrite Fnpc) in "Hpc".
    (* the clock cells (tick branch only), then close the minstret invariant *)
    iAssert (|={⊤ ∖ ↑wlockN ∖ ↑minstretN}=>
               reg_interp (wm_regs σ'))%I with "[Hreg]" as ">Hreg".
    { destruct tick.
      - iInv "Hcinv" as ">Hcb" "Hclosec".
        iDestruct "Hcb" as (c0 t0c p0) "(Hc & Ht & Hp)".
        iMod (reg_update _ mcycle _ c' with "Hreg Hc") as "[Hreg Hc]".
        iMod (reg_update _ mtime _ ti' with "Hreg Ht") as "[Hreg Ht]".
        iMod (reg_update _ mip _ p' with "Hreg Hp") as "[Hreg Hp]".
        iMod ("Hclosec" with "[Hc Ht Hp]") as "_".
        { iNext. iExists c', ti', p'. iFrame. }
        iModIntro. rewrite Hregs. iExact "Hreg".
      - iModIntro. rewrite Hregs. iExact "Hreg". }
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro.
    (* [wmstate_rest σ'] back, then the continuation *)
    iSplitL "Hreg Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_rest_nonv.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iFrame "Hreg". rewrite Hdevt Hlogs. iFrame. }
    iApply ("Hcont" $! v (wm_ws σ') with
              "[%] [Hhs Hpriv Hmstatus] Hpmpc [$Hpc $Hnpc] Hrs1c Hrs2c Hrdc
               Hhws Harm").
    - exact Hwsle.
    - iApply (mmode_config_rebuild (DfracOwn q) mstatus0 HmIE HMPRV HSXL HKF
                with "Hhw Hmiv Hhs Hpriv Hmstatus").
  Qed.

  (** THE SLOT-IN CHECK: [WeakBranch.wwp_acquire_loop_real] at THIS leaf's
      [P] and certificate — the pin-form twin of
      [WeakBranch.wwp_acquire_loop_real_cert], with the AMO's access kinds
      pinned to what the model emits ([reflexivity] on both side conditions).
      A caller instantiates the attempt premise with [wwp_amo4_acq_leaf]
      (its conclusion IS this [wacq_cb], definitionally) and is left, per
      instruction, with nothing about the weak machine at all. *)
  Corollary wwp_amo4_acquire_loop (γ : gname) (lk : Arch.pa) (R : vProp Σ)
      (pca pcb : SailStdpp.Values.mword 64)
      (akf2 : akinfo) (pf2 : Arch.pa) (nf2 : N)
      (K Kb : iProp Σ) :
    gen_id = 0%nat ->
    acc_wf pca 4 ->
    acc_wf pcb 4 ->
    acc_wf lk 4 ->
    inv wlockN (wlock_inv γ lk R) -∗
    □ (K -∗ ▷ (Kb -∗ WWP Loop) -∗
         wacq_cb γ lk R pca
           (wP_eff_pin (Some (fin_to_nat cpu_id))
              ([WEread wak_plain pca 4]
               ++ [WEread (AkInfo false true true) lk 4;
                   WEwrite (AkInfo false true false) lk 4 lock_one]))) -∗
    □ (Kb -∗ (K -∗ WWP Loop) -∗
         wbr_cb pcb
           (wP_eff (Some (fin_to_nat cpu_id)) [WEread akf2 pf2 nf2]) wQ_pure) -∗
    K -∗ WWP Loop.
  Proof.
    intros Hgid Hacca Haccb Hacclk.
    (* the footprint, fully concrete here: the four text bytes of [pca] and
       the four bytes of the lock word *)
    assert (Hfoot : forall a : Z,
              weffs_touch
                ([WEread wak_plain pca 4]
                 ++ [WEread (AkInfo false true true) lk 4;
                     WEwrite (AkInfo false true false) lk 4 lock_one]) a ->
              (exists j : nat, (j < 4)%nat /\ a = acc_addr pca j) \/
              (exists j : nat, (j < 4)%nat /\ a = acc_addr lk j)).
    { intros a Ha. apply weffs_touch_cons in Ha as [Ha|Ha].
      - left. destruct Ha as (j & Hj & ->). exists j.
        split; [cbn in Hj; lia|done].
      - right. apply weffs_touch_cons in Ha as [Ha|Ha].
        + destruct Ha as (j & Hj & ->). exists j. split; [cbn in Hj; lia|done].
        + destruct (weffs_touch_write1 _ lk _ _ a Ha) as (j & Hj & ->).
          exists j. split; [cbn in Hj; lia|done]. }
    iIntros "#Hinv #Hatt #Hbr HK".
    iApply (wwp_acquire_loop_real γ lk R pca pcb _ _ _ K Kb
              ([WEread wak_plain pca 4]
               ++ [WEread (AkInfo false true true) lk 4;
                   WEwrite (AkInfo false true false) lk 4 lock_one])
              Hgid Hacca Haccb Hacclk Hfoot
              (wstep_cert_fr_pin _ _ _ _
                 (wcert_amo_aq_pin_base4 (fin_to_nat cpu_id) pca
                    (AkInfo false true true) (AkInfo false true false) lk
                    lock_one eq_refl eq_refl eq_refl))
              (wcert_nowrite (fin_to_nat cpu_id) pcb [WEread akf2 pf2 nf2]
                 (nowrite_trace_read akf2 pf2 nf2))
              with "Hinv Hatt Hbr HK").
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 6. Soundness check *)

Print Assumptions wcert_amo_aq_pin.
Print Assumptions wP_eff_pin_amo4.
Print Assumptions wwp_amo4_acq_leaf.
Print Assumptions wwp_amo4_acquire_loop.
