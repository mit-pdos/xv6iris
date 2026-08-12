(** * WeakLeafTor.v — the two COMPRESSED width-8 leaves under a WRITTEN TOR
      PMP entry (M4, seam 2 of the weak [start()]/[timerinit()] port)

    [timerinit()]'s prologue/epilogue are a [c.sdsp] and a [c.ldsp] of the
    return address / callee-saved registers through [sp], executed AFTER
    [start()] has programmed pmpaddr0/pmpcfg0 with a TOR entry covering all of
    RAM.  Every batch-2 leaf in the tree so far ([WeakLeafLd8], [WeakLeafSd8],
    [WeakLeafLw4], [WeakLeafSw4], [WeakLeafAmo4Leaf]) demands [pmp_all_off],
    which those two accesses cannot supply.  This file is the pair that can.

    THREE DELTAS over [WeakLeafLd8] / [WeakLeafSd8] — read those two files
    first; everything not listed here is cloned from them verbatim.

    (1) THE PMP PREMISE.  [pmp_all_off pmpcfg0] becomes the PAIR
        [pmp_allows_all pmpcfg0] (the FETCH side, which is all
        [WeakFunnel.wwp_instr] and the fetch recipe ever need) plus
        [WpMmodeLeafBase.pmp_tor0_grants pmpcfg0 pmpaddrs ea 8] (the DATA
        side).  Under [pmp_all_off] the single fact implied both, via
        [pmp_all_off_allows_all]; a written TOR entry is not off, so the two
        obligations separate — which is also why the leaf now carries the
        [pmpaddr_n] cell (returned unchanged: nothing here writes it, and the
        funnel does not read it).  Inside, the [exec_eff] pmpCheck fact comes
        from [WeakPmpTorEff.exec_eff_pmpCheck_machine_tor0] instead of
        [WeakPmpEff.exec_eff_pmpCheck_machine_none].

    (2) COMPRESSED, AT BOTH ALIGNMENTS.  [c.ldsp]/[c.sdsp] are [is_rvc = true]
        and [timerinit] contains them at 4-aligned AND at 2-not-4-aligned pcs,
        so each leaf takes an [al4 : bool] parameter, exactly as
        [WeakLeafRegOnly]'s register-only kit does.  §0 below is that kit's
        missing COMPRESSED member: [wP_eff_of_leaf_rvc], the union of
        [WeakFetchRvc.wP_eff_of_leaf_rvc4] and
        [WeakFetch2.wP_eff_of_leaf_rvc2].  Both fetch arms read ONE element
        ([WEread wak_plain pc 4] resp. [… pc 2]), so — unlike the split
        [F_Base] fetch — the width-generic certificate families
        [WeakLeafLd8.wcert_load_w] / [WeakLeafSd8.wcert_store_w] apply at
        [nf := if al4 then 4 else 2] with ONE term covering both alignments.

    (3) THE PC BUMP IS 2.  The recipes state the pre-write at [pc+2], so §1's
        [execute] lemmas take a GENERIC [npc] parameter (the [pc] argument of
        [WeakLeafLd8.exec_eff_ld8_at] / [WeakLeafSd8.exec_eff_sd8_at] then has
        no other use and is dropped) and the continuation is
        [pc_is (add_vec_int pc 2)].

    Everything else — the window [WeakLeafWin.wwin pc ea 8] and every window
    obligation, the [↦w₈] resource lemmas, [wpt8_align], the load/store
    successor register frames, the device-frame two-liner, the [hart_ws]
    threading and the [wmstate_norg] re-establishment — is the batch-2 recipe
    unchanged. *)
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
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff.
Require Import WeakLeafEffCommon WeakLeafEff8 WeakLeafEff8s.
Require Import WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [load_sexec_facts], [store_regs_facts], [reg_at_flat],
   [wpt8_align]). *)
Require Import WeakLeafWin.
(* The width-generic certificate families (§1 of each of the two leaves). *)
Require Import WeakLeafLd8 WeakLeafSd8.
(* THE NEW PMP ARM. *)
Require Import WeakPmpTorEff.

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation the
    model's register premises are stated with.  This file DEFINES no
    [gset Arch.pa] — every window it uses is [WeakLeafWin]'s [wwin], and the
    one place a window type is written it is written [W : _] (durable notes,
    the binder-position instance trap), exactly as [WeakLeafRegOnly] does. *)
Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. THE ALIGNMENT-UNION COMPRESSED RECIPE

    [WeakLeafRegOnly.wP_eff_of_leaf_regonly] is this move for the
    register-only [F_Base] pair; this is its [F_RVC] twin, and it exists for
    the same reason: [timerinit()] uses the SAME compressed instruction shape
    at BOTH fetch alignments, so a per-alignment leaf pair would double the
    sweep.  The premise lists of [WeakFetchRvc.wP_eff_of_leaf_rvc4] and
    [WeakFetch2.wP_eff_of_leaf_rvc2] are IDENTICAL but for the alignment
    facts, so the union is the pair [2-aligned = true] / [4-aligned = al4] and
    the whole proof is a [destruct al4] into two [exact]s.

    The compressed fetch reads ONE element at either alignment, so — unlike
    the split [F_Base] fetch, which needs a three-element certificate family
    — the conclusion is a ONE-element prefix whose width is the only thing
    [al4] decides. *)

Lemma wP_eff_of_leaf_rvc
    (al4 : bool) (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
    (w : SailStdpp.Values.mword 32)
    (i0 i : instruction) (es_x : list weff)
    (D D0 : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* (a) the text word, IN THE CONFINED MEMORY, at EITHER alignment *)
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  subrange_vec_dec w 15 0 = h ->
  isRVC h = true ->
  (* (b) the COMPRESSED decode, and the expansion *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode_compressed h) dst = true ->
  exec (ext_decode_compressed h) dst = Some (i0, dst) ->
  (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
  (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s)) ->
  (* (c) the EXPANDED instruction's [execute], at [exec_eff] *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 2))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid)
    ([WEread wak_plain pc (if al4 then 4%N else 2%N)] ++ es_x) σ.
Proof.
  destruct al4;
    intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
           Hal2 Hal4 Hram Htext Hsub HisRVC Hagree HDmi Hgood Hdec Hgood0 Hexp
           Hexec.
  - exact (wP_eff_of_leaf_rvc4 cid σ W pc h w i0 i es_x D D0 dst Hwf HW0 HWp
             Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
             Hal4 Hram Htext Hsub HisRVC Hagree HDmi Hgood Hdec Hgood0 Hexp
             Hexec).
  - exact (wP_eff_of_leaf_rvc2 cid σ W pc h w i0 i es_x D D0 dst Hwf HW0 HWp
             Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
             Hal2 Hal4 Hram Htext Hsub HisRVC Hagree HDmi Hgood Hdec Hgood0
             Hexp Hexec).
Qed.

(* ====================================================================== *)
(** ** 1. THE TWO [execute] LEMMAS, AT A GENERIC [s0] AND A GENERIC [npc]

    [WeakLeafLd8.exec_eff_ld8_at] / [WeakLeafSd8.exec_eff_sd8_at] with EXACTLY
    two changes:

      (a) the premise [pmp_all_off (register_lookup pmpcfg_n s0.(sregs))]
          becomes
          [pmp_tor0_grants (register_lookup pmpcfg_n s0.(sregs))
                           (register_lookup pmpaddr_n s0.(sregs)) ea 8],
          discharged inside by [WeakPmpTorEff.exec_eff_pmpCheck_machine_tor0]
          (pmpaddr_n peeled past the funnel's two pre-writes by
          [WeakLeafWin.leaf_peel], exactly as every other config register is);
      (b) the baked [nextPC (add_vec_int pc 4)] becomes a generic [npc], so
          ONE lemma serves the compressed pc+2 as well (and the now-unused
          [pc] argument is dropped).

    Everything else is identical — in particular the whole PMA / [within_*] /
    device / byte-lookup half, which the PMP configuration does not touch. *)

Lemma exec_eff_ld8_tor_at (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (rs1 rd : mword 5) (imm : mword 12)
    (ea : Arch.pa) (v : bv 64) :
  uint rd <> 0 ->
  register_lookup cur_privilege s0.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1")
    = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s0.(sregs)))
    = PMM_Disabled ->
  pmp_tor0_grants (register_lookup pmpcfg_n s0.(sregs))
                  (register_lookup pmpaddr_n s0.(sregs)) ea 8 ->
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
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b)
                   nextPC npc)
                  (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v),
          [WEread wak_plain ea 8]).
Proof.
  intros Hrd Lpriv Lmprv Lpmm Htor Lpma Lhtif Hea Hal Hram8 Hbytes.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram8 0%nat); lia).
  assert (Hram7 : addr_is_ram (pa_add ea 7)) by (apply Hram8; lia).
  destruct (pma_all_ram Lpma ea 8
              (pma_access_ram _ _ _ Hram Hram7
                 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & Hread & _).
  set (s := set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc).
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
  (* THE ONE NEW PEEL: the address register the TOR grant is about *)
  assert (Lpaddr_s : register_lookup pmpaddr_n s.(sregs)
                     = register_lookup pmpaddr_n s0.(sregs))
    by (unfold s; leaf_peel pmpaddr_n; reflexivity).
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
  - (* THE TOR ARM, in place of [exec_eff_pmpCheck_machine_none] *)
    rewrite Hpa. apply (exec_eff_pmpCheck_machine_tor0 ea 8 (Load Data) s).
    + rewrite Lpmpc_s Lpaddr_s. exact Htor.
    + intros ent. eexists. apply exec_eff_returnM.
    + vm_compute; reflexivity.
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

Lemma exec_eff_sd8_tor_at (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
    (ea : Arch.pa) (vs : SailStdpp.Values.mword 64) :
  register_lookup cur_privilege s0.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1")
    = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s0.(sregs)))
    = PMM_Disabled ->
  pmp_tor0_grants (register_lookup pmpcfg_n s0.(sregs))
                  (register_lookup pmpaddr_n s0.(sregs)) ea 8 ->
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
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
  = Some (RETIRE_SUCCESS,
          MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                          nextPC npc))
                 (write_bytes s0.(mem) ea 8 vs) s0.(mdev),
          [WEwrite wak_plain ea 8 vs]).
Proof.
  intros Lpriv Lmprv Lpmm Htor Lpma Lhtif Hea Hvs Hal Hram8.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram8 0%nat); lia).
  assert (Hram7 : addr_is_ram (pa_add ea 7)) by (apply Hram8; lia).
  destruct (pma_all_ram Lpma ea 8
              (pma_access_ram _ _ _ Hram Hram7
                 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & _ & _ & Hwrite & _).
  set (s := set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc).
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
  assert (Lpaddr_s : register_lookup pmpaddr_n s.(sregs)
                     = register_lookup pmpaddr_n s0.(sregs))
    by (unfold s; leaf_peel pmpaddr_n; reflexivity).
  assert (Lpma_s : register_lookup pma_regions s.(sregs)
                   = register_lookup pma_regions s0.(sregs))
    by (unfold s; leaf_peel pma_regions; reflexivity).
  assert (Lhtif_s : register_lookup htif_tohost_base s.(sregs) = None)
    by (unfold s; leaf_peel htif_tohost_base; exact Lhtif).
  assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                          s.(sregs))
                  = (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            s0.(sregs))).
  { destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs1))); reflexivity. }
  assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                          s.(sregs)) = vs).
  { destruct (Z.eqb (uint rs2) 0) eqn:Ez; [exact Hvs|].
    unfold s; leaf_peel (R_bitvector_64 (gpr_of_Z (uint rs2))). exact Hvs. }
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
  - rewrite Hpa. apply (exec_eff_pmpCheck_machine_tor0 ea 8 (Store Data) s).
    + rewrite Lpmpc_s Lpaddr_s. exact Htor.
    + intros ent. eexists. apply exec_eff_returnM.
    + vm_compute; reflexivity.
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

(* ====================================================================== *)
(** ** 2. THE TWO [wP_eff] HALVES

    [WeakLeafLd8.wP_eff_ld8] / [WeakLeafSd8.wP_eff_sd8] over §0's
    alignment-union recipe: the [pmp_all_off] premise splits into
    [pmp_allows_all] (fetch) + [pmp_tor0_grants] (data), the [F_Base] text
    resource becomes [winstr_bytes pc (F_RVC h)] with the compressed decode +
    expansion premises, and the pre-write is at [pc+2].  The window word [w]
    is NOT a parameter: it comes out of [winstr_bytes]'s own ∃ field, through
    [WeakFunnel.winstr_bytes_lookup], together with
    [subrange_vec_dec w 15 0 = h] and [isRVC h = true]. *)

Section wP_eff_halves.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_ld8_tor (al4 : bool) (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (v : bv 64) (dq : dfrac)
      (D D0 : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    (* --- the M-mode config tower, at σ's own registers --- *)
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
    pmp_tor0_grants (register_lookup pmpcfg_n (wm_regs σ))
                    (register_lookup pmpaddr_n (wm_regs σ)) ea 8 ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
      = PMM_Disabled ->
    eq_vec (register_lookup elp (wm_regs σ))
           (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* --- the instruction's pure geometry --- *)
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the COMPRESSED decode and its expansion --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_RVC h) -∗
    vwp_hold (wpt8 ea dq v) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
          ++ [WEread wak_plain ea 8]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Htor Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv
           Lpmm Lelp Hal2 Hal4 Hrd Hea Hram8 Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_RVC h) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wwp_ld8 σ ea dq v Hwf with "Hlat Hpt")
      as %[[Haccea Hpinea] Hflat8].
    iDestruct (wpt8_align with "Hpt") as %Halea.
    iPureIntro.
    destruct Hfok as (Hal2' & Hrampc & w & [Hsub HisRVC] & Htext).
    apply (wP_eff_of_leaf_rvc al4 cid σ (wwin pc ea 8) pc h w i0
             (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
             [WEread wak_plain ea 8] D D0 dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 8 Hrampc Hram8).
    - exact (wwin_pinned σ pc ea 8 Haccpc Haccea Hpinpc Hpinea).
    - exact Lpc.
    - exact Lpriv.
    - exact Lpmp.
    - exact Lpma.
    - exact Lhtif.
    - exact Lhart.
    - exact LmisaS.
    - exact LmisaC.
    - exact LmIE.
    - exact Lelp.
    - exact Hal2.
    - exact Hal4.
    - exact Hrampc.
    - exact (wwin_conf_text σ pc ea 8 w Htext).
    - exact Hsub.
    - exact HisRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - exact Hgood0.
    - exact Hexp.
    - intro b. eexists. split_and!.
      + exact (exec_eff_ld8_tor_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b (add_vec_int pc 2) rs1 rd imm ea v
                 Hrd Lpriv Lmprv Lpmm Htor Lpma Lhtif Hea Halea Hram8
                 (wwin_conf_data σ pc ea 8 v Hflat8)).
      + rewrite (proj1 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v))).
        exact Lhart.
      + exact (proj1 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v)))).
      + rewrite (proj1 (proj2 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v))))).
        apply wmem_restrict_dom.
  Qed.

  Lemma wP_eff_ld8_tor_own (al4 : bool) (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (v : bv 64) (cid8 : CPU)
      (D D0 : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    (* --- the M-mode config tower, at σ's own registers --- *)
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
    pmp_tor0_grants (register_lookup pmpcfg_n (wm_regs σ))
                    (register_lookup pmpaddr_n (wm_regs σ)) ea 8 ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
      = PMM_Disabled ->
    eq_vec (register_lookup elp (wm_regs σ))
           (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* --- the instruction's pure geometry --- *)
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the COMPRESSED decode and its expansion --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_RVC h) -∗
    vwp_hold (wpt8_own cid8 ea v) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
          ++ [WEread wak_plain ea 8]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Htor Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv
           Lpmm Lelp Hal2 Hal4 Hrd Hea Hram8 Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_RVC h) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wwp_ld8_own cid8 σ ea v Hwf with "Hlat Hpt")
      as %[[Haccea Hpinea] Hflat8].
    iDestruct (wpt8_own_align with "Hpt") as %Halea.
    iPureIntro.
    destruct Hfok as (Hal2' & Hrampc & w & [Hsub HisRVC] & Htext).
    apply (wP_eff_of_leaf_rvc al4 cid σ (wwin pc ea 8) pc h w i0
             (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
             [WEread wak_plain ea 8] D D0 dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 8 Hrampc Hram8).
    - exact (wwin_pinned σ pc ea 8 Haccpc Haccea Hpinpc Hpinea).
    - exact Lpc.
    - exact Lpriv.
    - exact Lpmp.
    - exact Lpma.
    - exact Lhtif.
    - exact Lhart.
    - exact LmisaS.
    - exact LmisaC.
    - exact LmIE.
    - exact Lelp.
    - exact Hal2.
    - exact Hal4.
    - exact Hrampc.
    - exact (wwin_conf_text σ pc ea 8 w Htext).
    - exact Hsub.
    - exact HisRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - exact Hgood0.
    - exact Hexp.
    - intro b. eexists. split_and!.
      + exact (exec_eff_ld8_tor_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b (add_vec_int pc 2) rs1 rd imm ea v
                 Hrd Lpriv Lmprv Lpmm Htor Lpma Lhtif Hea Halea Hram8
                 (wwin_conf_data σ pc ea 8 v Hflat8)).
      + rewrite (proj1 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v))).
        exact Lhart.
      + exact (proj1 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v)))).
      + rewrite (proj1 (proj2 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2) rd (regval_into_reg v))))).
        apply wmem_restrict_dom.
  Qed.

  Lemma wP_eff_sd8_tor (al4 : bool) (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rs2 : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (vold : bv 64) (vs : SailStdpp.Values.mword 64)
      (cid8 : CPU) (D D0 : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
    pmp_tor0_grants (register_lookup pmpcfg_n (wm_regs σ))
                    (register_lookup pmpaddr_n (wm_regs σ)) ea 8 ->
    pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
    register_lookup htif_tohost_base (wm_regs σ) = None ->
    register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (wm_regs σ))) ('b"1")
      = false ->
    pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg (wm_regs σ)))
      = PMM_Disabled ->
    eq_vec (register_lookup elp (wm_regs σ))
           (landing_pad_bits_backwards LP_EXPECTED) = false ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) (wm_regs σ))
      = vs ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_RVC h) -∗
    vwp_hold (wpt8_own cid8 ea vold) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
          ++ [WEwrite wak_plain ea 8 vs]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Htor Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv
           Lpmm Lelp Hal2 Hal4 Hea Hvs Hram8 Hagree HDmi Hgood Hdec Hgood0 Hexp.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_RVC h) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_RVC h) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wpt8_own_flat_pin cid8 σ ea vold Hwf with "Hlat Hpt")
      as %[Haccea Hflatpin].
    iDestruct (wpt8_own_align with "Hpt") as %Halea.
    iPureIntro.
    assert (Hpinea : forall j : nat, (j < 8)%nat ->
              pinned_read σ (acc_addr ea j))
      by (intros j Hj; exact (proj2 (Hflatpin j Hj))).
    destruct Hfok as (Hal2' & Hrampc & w & [Hsub HisRVC] & Htext).
    apply (wP_eff_of_leaf_rvc al4 cid σ (wwin pc ea 8) pc h w i0
             (STORE (imm, Regidx rs2, Regidx rs1, 8))
             [WEwrite wak_plain ea 8 vs] D D0 dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 8 Hrampc Hram8).
    - exact (wwin_pinned σ pc ea 8 Haccpc Haccea Hpinpc Hpinea).
    - exact Lpc.
    - exact Lpriv.
    - exact Lpmp.
    - exact Lpma.
    - exact Lhtif.
    - exact Lhart.
    - exact LmisaS.
    - exact LmisaC.
    - exact LmIE.
    - exact Lelp.
    - exact Hal2.
    - exact Hal4.
    - exact Hrampc.
    - exact (wwin_conf_text σ pc ea 8 w Htext).
    - exact Hsub.
    - exact HisRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - exact Hgood0.
    - exact Hexp.
    - intro b. eexists. split_and!.
      + exact (exec_eff_sd8_tor_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b (add_vec_int pc 2) rs1 rs2 imm ea vs
                 Lpriv Lmprv Lpmm Htor Lpma Lhtif Hea Hvs Halea Hram8).
      + exact (eq_trans (proj1 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2))) Lhart).
      + exact (proj1 (proj2 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2)))).
      + exact (wwin_wdom σ pc ea 8 vs).
  Qed.

End wP_eff_halves.

(* ====================================================================== *)
(** ** 3. THE TWO LEAVES

    [WeakLeafLd8.wwp_ld8_leaf] / [WeakLeafSd8.wwp_sd8_leaf] with the three
    deltas of the header: the [pmp_allows_all] + [pmp_tor0_grants] premise
    pair and the extra [pmpaddr_n] cell (pinned in the callback by
    [reg_valid_dq] + [WeakLeafWin.reg_at_flat], since the funnel does not read
    it, and returned unchanged); [is_rvc := true] with the compressed decode
    premises; and the pc bump 2.

    The certificate is the WIDTH-GENERIC family instantiated at the
    alignment-dependent FETCH element — [WeakLeafLd8.wcert_load_w 8] resp.
    [WeakLeafSd8.wcert_store_w 8] at [nf := if al4 then 4 else 2] — so ONE
    term covers both alignments (a compressed fetch is one element at either
    alignment; only its width moves). *)

Section leaves.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (** *** 3a. [c.ldsp]-class: the compressed width-8 LOAD. *)

  Lemma wwp_ld8_tor_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rd0 npc0 : SailStdpp.Values.mword 64)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
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
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)),
                    s))) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_RVC h) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8 ea dqv v) ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
       pc_is (add_vec_int pc 2) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8 ea dqv v) ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hal2 Hal4 Hrs1nz Hrd Hea Hram8 Hdecf Hagree HDmi
           Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N);
                  WEread wak_plain ea 8])
              (wQ_fr (wQ_load_w 8 ea) _ _) Hgid Haccpc Hpmp
              (wstep_cert_fr _ _ _ _
                 (wcert_load_w 8 (fin_to_nat cpu_id) pc wak_plain pc
                    (if al4 then 4%N else 2%N) wak_plain ea eq_refl))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hnv & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the TWO registers the funnel does not read: the pmp ADDRESS register
       (which the TOR grant is about) and this instruction's base *)
    iDestruct (reg_valid_dq with "Hreg Hpaddr") as %Lpaddr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat pmpaddr_n σ b eq_refl))
                  Lpaddr_a) as Lpaddr.
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
    (* ---- the certificate's precondition (§2) ---- *)
    iDestruct (wP_eff_ld8_tor al4 (fin_to_nat cpu_id) σ pc h rs1 rd imm i0
                 ea v dqv D D0 dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp)
                 ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma
                 Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp Hal2 Hal4
                 Hrd Hea_σ Hram8 Hag_σ HDmi Hgood Hdec Hgood0 Hexp
                 with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the data doubleword ---- *)
    iDestruct (wwp_ld8 σ ea dqv v Hwf with "Hlat Hpt") as %[_ Hflat8].
    iDestruct (winstr_nv cpu_id _ _ pc (F_RVC h) with "Hlat Hbs") as %Hnvpc.
    iDestruct (nv_ok_wpt8 cpu_id _ _ ea dqv v (wm_ws σ)
                 with "Hlat Hpt") as %Hnvea.
    iDestruct (wpt8_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state ---- *)
    pose proof (exec_eff_ld8_tor_at (wflat_st σ) b (add_vec_int pc 2) rs1 rd
                  imm ea v Hrd Lpriv Lmprv Lpmm
                  ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma Lhtif Hea_σ
                  Halea Hram8 Hflat8) as Hexf.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame: the [execute] moved no device *)
    assert (Hdevt : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
                (add_vec_int pc 2) rd (regval_into_reg v)))))). }
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as ((HQi & HQl & HQv) & HQeff).
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+2] *)
    iEval (rewrite (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
             (add_vec_int pc 2) rd (regval_into_reg v))))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR.
      { iPureIntro.
        apply (nv_hart_of_wQ_eff_ok cpu_id σ σ' _ HQeff Hnv).
        intros a Ha. rewrite HQl.
        apply weffs_touch_cons in Ha as [Ha|Ha].
        - destruct Ha as (j & Hj & ->).
          apply Hnvpc. destruct al4; cbn in Hj; lia.
        - destruct (weffs_touch_read1 _ ea _ a Ha)
            as (j & Hj & ->).
          cbn in Hj. apply Hnvea. lia. }
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' Hpaddr [$Hpc' $Hnpc] Hrs1c Hrdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_ld8_carry σ σ' t ea dqv v with "Hpt").
      split_and!; [exact Hregs|exact Hdevs|exact Hmems|exact Himgs
                  |exact Hlogs|exact Hwsle|exact Hwf'|exact Hbnd'].
  Qed.

  Lemma wwp_ld8_tor_rvc_leaf_own (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rd : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (v : bv 64) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rd0 npc0 : SailStdpp.Values.mword 64)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
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
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)),
                    s))) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_RVC h) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8_own cpu_id ea v) ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
       pc_is (add_vec_int pc 2) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ (regval_into_reg v) -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8_own cpu_id ea v) ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hal2 Hal4 Hrs1nz Hrd Hea Hram8 Hdecf Hagree HDmi
           Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N);
                  WEread wak_plain ea 8])
              (wQ_fr (wQ_load_w 8 ea) _ _) Hgid Haccpc Hpmp
              (wstep_cert_fr _ _ _ _
                 (wcert_load_w 8 (fin_to_nat cpu_id) pc wak_plain pc
                    (if al4 then 4%N else 2%N) wak_plain ea eq_refl))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hnv & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the TWO registers the funnel does not read: the pmp ADDRESS register
       (which the TOR grant is about) and this instruction's base *)
    iDestruct (reg_valid_dq with "Hreg Hpaddr") as %Lpaddr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat pmpaddr_n σ b eq_refl))
                  Lpaddr_a) as Lpaddr.
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
    (* ---- the certificate's precondition (§2) ---- *)
    iDestruct (wP_eff_ld8_tor_own al4 (fin_to_nat cpu_id) σ pc h rs1 rd imm i0
                 ea v cpu_id D D0 dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp)
                 ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma
                 Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp Hal2 Hal4
                 Hrd Hea_σ Hram8 Hag_σ HDmi Hgood Hdec Hgood0 Hexp
                 with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the data doubleword ---- *)
    iDestruct (wwp_ld8_own cpu_id σ ea v Hwf with "Hlat Hpt") as %[_ Hflat8].
    iDestruct (winstr_nv cpu_id _ _ pc (F_RVC h) with "Hlat Hbs") as %Hnvpc.
    iDestruct (nv_ok_wpt8_own cpu_id _ _ ea v (wm_ws σ)
                 with "Hlat Hpt") as %Hnvea.
    iDestruct (wpt8_own_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state ---- *)
    pose proof (exec_eff_ld8_tor_at (wflat_st σ) b (add_vec_int pc 2) rs1 rd
                  imm ea v Hrd Lpriv Lmprv Lpmm
                  ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma Lhtif Hea_σ
                  Halea Hram8 Hflat8) as Hexf.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame: the [execute] moved no device *)
    assert (Hdevt : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
                (add_vec_int pc 2) rd (regval_into_reg v)))))). }
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as ((HQi & HQl & HQv) & HQeff).
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+2] *)
    iEval (rewrite (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
             (add_vec_int pc 2) rd (regval_into_reg v))))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR.
      { iPureIntro.
        apply (nv_hart_of_wQ_eff_ok cpu_id σ σ' _ HQeff Hnv).
        intros a Ha. rewrite HQl.
        apply weffs_touch_cons in Ha as [Ha|Ha].
        - destruct Ha as (j & Hj & ->).
          apply Hnvpc. destruct al4; cbn in Hj; lia.
        - destruct (weffs_touch_read1 _ ea _ a Ha)
            as (j & Hj & ->).
          cbn in Hj. apply Hnvea. lia. }
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' Hpaddr [$Hpc' $Hnpc] Hrs1c Hrdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_ld8_own_carry cpu_id σ σ' t ea v with "Hpt").
      split_and!; [exact Hregs|exact Hdevs|exact Hmems|exact Himgs
                  |exact Hlogs|exact Hwsle|exact Hwf'|exact Hbnd'].
  Qed.

  (** *** 3b. [c.sdsp]-class: the compressed width-8 STORE. *)

  Lemma wwp_sd8_tor_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rs2 : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddrs : type_of_register pmpaddr_n)
      (rs1v rs2v npc0 : SailStdpp.Values.mword 64)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    uint rs2 <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exists i0' : instruction,
         exec (decode_fetch (F_RVC h)) t = Some (i0', t) /\
         is_lpad_instruction i0' = false /\
         (forall s : mstate, exec (execute i0') s
            = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s))) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
    winstr_bytes pc (F_RVC h) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt8_own cpu_id ea vold) ws -∗
    vwp_hold R ws -∗
    (∀ (ws' : wstate) (T : nat),
       ⌜ws_le ws ws'⌝ -∗
       ⌜forall j : nat, (j < 8)%nat ->
          (T <= flr (ws_view ws') (acc_addr ea j))%nat⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
       pc_is (add_vec_int pc 2) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8_own cpu_id ea rs2v) ws' -∗
       monPred_at R (view_scl T) -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Htor Hal2 Hal4 Hrs1nz Hrs2nz Hea Hram8 Hdecf Hagree HDmi
           Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iApply (wwp_instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N);
                  WEwrite wak_plain ea 8 rs2v])
              (wQ_fr (wQ_store8 (Some (fin_to_nat cpu_id)) ea rs2v) _ _)
              Hgid Haccpc Hpmp
              (wstep_cert_fr _ _ _ _
                 (wcert_store_w 8 (fin_to_nat cpu_id) pc wak_plain pc
                    (if al4 then 4%N else 2%N) wak_plain ea rs2v))
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hnv & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the THREE registers the funnel does not read: pmpaddr_n, base, data *)
    iDestruct (reg_valid_dq with "Hreg Hpaddr") as %Lpaddr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat pmpaddr_n σ b eq_refl))
                  Lpaddr_a) as Lpaddr.
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a)   as Lrs1.
    iDestruct (reg_valid with "Hreg Hrs2c") as %Lrs2_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs2))) σ b eq_refl))
                  Lrs2_a)   as Lrs2.
    assert (Hea_σ : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                            (wm_regs σ)) (sign_extend' 64 imm) = ea).
    { rewrite (proj2 (Z.eqb_neq (uint rs1) 0) Hrs1nz) Lrs1. exact Hea. }
    assert (Hvs_σ : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                            (wm_regs σ)) = rs2v).
    { rewrite (proj2 (Z.eqb_neq (uint rs2) 0) Hrs2nz). exact Lrs2. }
    assert (Hag_σ : forall r, D r = true ->
              register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)).
    { apply Hagree; [exact Lpriv | exact Lmisa | exact Lsec]. }
    (* ---- the certificate's precondition (§2) ---- *)
    iDestruct (wP_eff_sd8_tor al4 (fin_to_nat cpu_id) σ pc h rs1 rs2 imm i0
                 ea vold rs2v cpu_id D D0 dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp)
                 ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma
                 Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp Hal2 Hal4
                 Hea_σ Hvs_σ Hram8 Hag_σ HDmi Hgood Hdec Hgood0 Hexp
                 with "Hlat Hbs Hpt") as %HP.
    iDestruct (wpt8_own_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state ---- *)
    pose proof (exec_eff_sd8_tor_at (wflat_st σ) b (add_vec_int pc 2) rs1 rs2
                  imm ea rs2v Lpriv Lmprv Lpmm
                  ltac:(rewrite Lpmpc Lpaddr; exact Htor) Lpma Lhtif Hea_σ
                  Hvs_σ Halea Hram8) as Hexf.
    (* ---- the ONE register write the wrapper expects: nextPC ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (MState (sregs (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 2)))
                    (write_bytes (mem (wflat_st σ)) ea 8 rs2v)
                    (mdev (wflat_st σ))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    assert (Hdevt : mdev t = wm_dev σ) by (rewrite Hdevt0; reflexivity).
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf'
                       & Hbnd').
    destruct HQ as ((HQi & (kc & HQl & _) & HQle & HQv) & HQeff).
    (* the release deposit: freeze R at the store's own timestamp *)
    iDestruct (wwp_release_deposit R σ Hbnd with "HR") as "HRdep".
    (* THE WINDOW UPDATE: retarget the eight elements at the message *)
    iDestruct (wpt8_own_at_elems with "Hpt") as "(%Halea2 & %Haccea & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3 & H4 & S4 & H5 & S5
        & H6 & S6 & H7 & S7)".
    iMod (wlat8_store_prim_own cpu_id kc σ ea rs2v
            with "Hlat H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7")
      as "[Hlat Hl8]".
    iDestruct (winstr_nv cpu_id _ _ pc (F_RVC h) with "Hlat Hbs") as %Hnvpc.
    iDestruct (nv_ok_wlat8_own cpu_id _ _ ea (S (length (wm_log σ))) rs2v
                 with "Hlat Hl8") as %Hnvea.
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat cpu_id)) kc ea 8 rs2v]
            with "Hlogauth") as "Hlogauth".
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+2] *)
    iEval (cbn [sregs]) in "Hpc'".
    iEval (rewrite (proj2 (proj2 (store_regs_facts (wflat_st σ) b
             (add_vec_int pc 2))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR.
      { iPureIntro.
        apply (nv_hart_of_wQ_eff_ok cpu_id σ σ' _ HQeff Hnv).
        intros a Ha. rewrite HQl.
        apply weffs_touch_cons in Ha as [Ha|Ha].
        - destruct Ha as (j & Hj & ->).
          apply Hnvpc. destruct al4; cbn in Hj; lia.
        - destruct (weffs_touch_write1 _ ea _ _ a Ha)
            as (j & Hj & ->).
          cbn in Hj. apply Hnvea. lia. }
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') (S (length (wm_log σ))) with
              "[%] [%] Hmm' Hpmpc' Hpaddr [$Hpc' $Hnpc] Hrs1c Hrs2c Hhws [Hl8]
               HRdep").
    - exact Hwsle.
    - intros j Hj. apply HQv. exact Hj.
    - iApply (wlat8_own_wpt8_own cpu_id ea (S (length (wm_log σ))) rs2v
                (wm_ws σ') Halea2 Haccea
                ltac:(intros j Hj; apply HQv; exact Hj) with "Hl8").
  Qed.

End leaves.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_ld8_tor_at.
Print Assumptions exec_eff_sd8_tor_at.
Print Assumptions wwp_ld8_tor_rvc_leaf.
Print Assumptions wwp_sd8_tor_rvc_leaf.
