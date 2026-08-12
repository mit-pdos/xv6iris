(** * WeakLeafSdspOff.v — the COMPRESSED width-8 STORE ([c.sdsp]) under the
      all-OFF boot PMP (M4, the [start()] prologue seam)

    [start()] opens with two [c.sdsp]s through [sp] (the saved return address
    and the frame pointer) — and they execute BEFORE the [pmpcfg0] write, so
    the PMP is still in its all-OFF reset state.  The two leaves that could
    otherwise serve them cannot:

      - [WeakLeafSd8.wwp_sd8_leaf] has the right PMP premise ([pmp_all_off])
        but the wrong FETCH: it is [F_Base] (a 4-byte instruction at a
        4-aligned pc), and [c.sdsp] is compressed;
      - [WeakLeafTor.wwp_sd8_tor_rvc_leaf] has the right fetch (F_RVC, at
        EITHER alignment, via the [al4] parameter) but the wrong PMP: it wants
        a WRITTEN TOR entry, which the boot machine does not have yet.

    This file is the missing corner: [WeakLeafTor]'s compressed store leaf with
    its PMP premise swapped back to [WeakLeafSd8]'s.  The delta against
    [WeakLeafTor] is EXACTLY the inverse of the delta that file recorded:

      (1) THE PMP PREMISE.  The PAIR [pmp_allows_all pmpcfg0] (fetch) +
          [WpMmodeLeafBase.pmp_tor0_grants pmpcfg0 pmpaddrs ea 8] (data)
          collapses back to the SINGLE [pmp_all_off pmpcfg0], which implies
          both — the fetch side through [pmp_all_off_allows_all], the data side
          inside [WeakLeafSd8.exec_eff_sd8_at] through
          [WeakPmpEff.exec_eff_pmpCheck_machine_none].
      (2) NO [pmpaddr_n] ANYWHERE.  The TOR leaf carried the [pmpaddr_n] cell
          only because its grant premise mentions that register; with the grant
          gone the cell goes with it (the funnel never reads it), and so does
          the leaf's [reg_valid_dq] peel.

    Everything else is [WeakLeafTor]'s [wwp_sd8_tor_rvc_leaf] verbatim: the
    alignment-union compressed recipe [WeakLeafTor.wP_eff_of_leaf_rvc] at the
    [al4] parameter, the width-generic store certificate
    [WeakLeafSd8.wcert_store_w 8] at the alignment-dependent fetch element, the
    [↦w₈]-in / [↦w₈]-out contract with the release-deposit surface
    [monPred_at R (view_scl T)], the [hart_ws] / [ws_le] threading, and the
    pc bump 2.

    §1 IS THE ONLY REAL WORK, and it is ten lines: [exec_eff_sd8_at] bakes
    [nextPC := add_vec_int pc 4] (it was written for the [F_Base] leaf), while
    a compressed store needs [pc+2].  Rather than clone its 100-line script
    with one arm changed, [exec_eff_sd8_off_at] REUSES it at the shifted
    argument [npc - 4] and folds the shift away with [InstrBytes.avi_assoc] —
    the successor-PC parameter is the only thing [pc] ever was in that
    statement.  (That is the [npc]-generalization [WeakLeafTor] performed by
    re-proving; here it is a corollary.) *)
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
Require Import WeakLeafEffCommon WeakLeafEff8s.
Require Import WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
(* The shared window kit + register helpers ([wwin], [leaf_peel],
   [store_regs_facts], [reg_at_flat], [wpt8_align]). *)
Require Import WeakLeafWin.
(* THE ALL-OFF DATA SIDE: [exec_eff_sd8_at], [wcert_store_w], and the store
   Q-half tower ([wpt8_at_elems], [wlat8_store_prim], [wlat8_wpt8]). *)
Require Import WeakLeafSd8.
(* THE COMPRESSED FETCH SIDE: the alignment-union recipe
   [wP_eff_of_leaf_rvc] (§0 there). *)
Require Import WeakLeafTor.

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation the
    model's register premises are stated with.  This file DEFINES no
    [gset Arch.pa] — every window it uses is [WeakLeafWin]'s [wwin] (the
    binder-position instance trap, durable notes). *)
Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [execute] MIRROR, AT A GENERIC SUCCESSOR PC

    [WeakLeafSd8.exec_eff_sd8_at] states the store's [exec_eff] at an arbitrary
    [s0 : mstate] with the funnel's two pre-writes on top, the second of which
    is [nextPC := add_vec_int pc 4] for its own [pc] parameter.  That [pc] has
    no other occurrence in the statement — it IS the successor PC — so the
    lemma already holds at every successor PC in the image of
    [fun p => add_vec_int p 4], which (addition on [mword 64] being invertible)
    is all of them.  [InstrBytes.avi_assoc] does the inversion in one rewrite;
    the compressed caller then uses [npc := add_vec_int pc 2]. *)

Lemma exec_eff_sd8_off_at (s0 : mstate) (b : bool)
    (npc : SailStdpp.Values.mword 64) (rs1 rs2 : mword 5) (imm : mword 12)
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
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
  = Some (RETIRE_SUCCESS,
          MState (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b)
                          nextPC npc))
                 (write_bytes s0.(mem) ea 8 vs) s0.(mdev),
          [WEwrite wak_plain ea 8 vs]).
Proof.
  intros Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Hal Hram8.
  pose proof (exec_eff_sd8_at s0 b (add_vec_int npc (-4)) rs1 rs2 imm ea vs
                Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Hal Hram8) as H.
  assert (Hz : (-4 + 4) = 0) by reflexivity.
  rewrite avi_assoc Hz avi0 in H.
  exact H.
Qed.

(* ====================================================================== *)
(** ** 2. THE [wP_eff] HALF

    [WeakLeafTor.wP_eff_sd8_tor] with the PMP premise pair replaced by
    [pmp_all_off]: the fetch obligation of
    [WeakLeafTor.wP_eff_of_leaf_rvc] is then [pmp_all_off_allows_all], and the
    execute obligation is §1's mirror.  The window word [w] is NOT a parameter:
    it comes out of [winstr_bytes]'s own ∃ field, through
    [WeakFunnel.winstr_bytes_lookup], together with
    [subrange_vec_dec w 15 0 = h] and [isRVC h = true]. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_sd8_rvc (al4 : bool) (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rs2 : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (vold : bv 64) (vs : SailStdpp.Values.mword 64)
      (cid8 : CPU) (D D0 : register -> bool) (dst : mstate) :
    wlog_wf (wm_log σ) ->
    (* --- the M-mode config tower, at σ's own registers --- *)
    register_lookup PC (wm_regs σ) = pc ->
    register_lookup cur_privilege (wm_regs σ) = Machine ->
    pmp_all_off (register_lookup pmpcfg_n (wm_regs σ)) ->
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
    add_vec (if Z.eqb (uint rs1) 0 then zero_reg
             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                    (wm_regs σ))
            (sign_extend' 64 imm) = ea ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) (wm_regs σ))
      = vs ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the COMPRESSED decode and its expansion --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode_compressed h) dst = true ->
    exec (ext_decode_compressed h) dst = Some (i0, dst) ->
    (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
    (forall s : mstate, exec (execute i0) s
       = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_RVC h) -∗
    vwp_hold (wpt8_own cid8 ea vold) (wm_ws σ) -∗
    ⌜wP_eff (Some cid)
       ([WEread wak_plain pc (if al4 then 4%N else 2%N)]
          ++ [WEwrite wak_plain ea 8 vs]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lmprv
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
    - exact (pmp_all_off_allows_all _ Lpmp).
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
      + exact (exec_eff_sd8_off_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                    (wm_dev σ)) b (add_vec_int pc 2) rs1 rs2 imm ea vs
                 Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hvs Halea Hram8).
      + exact (eq_trans (proj1 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2))) Lhart).
      + exact (proj1 (proj2 (store_regs_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 8))
                      (wm_dev σ)) b (add_vec_int pc 2)))).
      + exact (wwin_wdom σ pc ea 8 vs).
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    [WeakLeafTor.wwp_sd8_tor_rvc_leaf] minus the [pmpaddr_n] cell and its
    grant premise, plus [pmp_all_off pmpcfg0] in place of
    [pmp_allows_all pmpcfg0] (the funnel's fetch obligation is then
    [pmp_all_off_allows_all]).  The certificate is [WeakLeafSd8]'s
    width-generic family at the alignment-dependent fetch element —
    [wcert_store_w 8] at [nf := if al4 then 4 else 2] — so ONE term covers both
    fetch alignments (a compressed fetch is one element either way; only its
    width moves).

    The output surface is unchanged from the batch-2 store leaves: the window
    comes back at the STORED value at the successor's view, the leaf-chosen
    timestamp [T = S (length (wm_log σ))] carries the per-byte floor fact, and
    the release payload [R] is frozen at [view_scl T].  A caller with no
    payload passes [R := emp]. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Lemma wwp_sd8_off_rvc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
      (rs1 rs2 : mword 5) (imm : mword 12) (i0 : instruction)
      (ea : Arch.pa) (vold : bv 64) (R : vProp Σ) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rs2v npc0 : SailStdpp.Values.mword 64)
      (D D0 : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
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
       pc_is (add_vec_int pc 2) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rs2)) ↦ᵣ rs2v -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt8_own cpu_id ea rs2v) ws' -∗
       monPred_at R (view_scl T) -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hrs2nz Hea Hram8 Hdecf Hagree HDmi
           Hgood Hdec Hgood0 Hexp.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrs2c #Hbs Hhws Hpt HR Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iApply (wwp_instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread wak_plain pc (if al4 then 4%N else 2%N);
                  WEwrite wak_plain ea 8 rs2v])
              (wQ_store8 (Some (fin_to_nat cpu_id)) ea rs2v)
              Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_store_w 8 (fin_to_nat cpu_id) pc wak_plain pc
                 (if al4 then 4%N else 2%N) wak_plain ea rs2v)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
                (F_RVC h) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the TWO registers the funnel does not read: base and data *)
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
    iDestruct (wP_eff_sd8_rvc al4 (fin_to_nat cpu_id) σ pc h rs1 rs2 imm i0
                 ea vold rs2v cpu_id D D0 dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmisaC LmIE Lmprv Lpmm Lelp Hal2 Hal4
                 Hea_σ Hvs_σ Hram8 Hag_σ HDmi Hgood Hdec Hgood0 Hexp
                 with "Hlat Hbs Hpt") as %HP.
    iDestruct (wpt8_own_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state ---- *)
    pose proof (exec_eff_sd8_off_at (wflat_st σ) b (add_vec_int pc 2) rs1 rs2
                  imm ea rs2v Lpriv Lmprv Lpmm
                  ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
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
    destruct HQ as (HQi & (kc & HQl & _) & HQle & HQv).
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
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') (S (length (wm_log σ))) with
              "[%] [%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hrs2c Hhws [Hl8]
               HRdep").
    - exact Hwsle.
    - intros j Hj. apply HQv. exact Hj.
    - iApply (wlat8_own_wpt8_own cpu_id ea (S (length (wm_log σ))) rs2v
                (wm_ws σ') Halea2 Haccea
                ltac:(intros j Hj; apply HQv; exact Hj) with "Hl8").
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_sd8_off_at.
Print Assumptions wP_eff_sd8_rvc.
Print Assumptions wwp_sd8_off_rvc_leaf.
