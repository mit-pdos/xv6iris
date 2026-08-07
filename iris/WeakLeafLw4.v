(** * WeakLeafLw4.v — M4 batch 2: the [lw]/[lwu]-class 4-byte LOAD leaf

    The width-4 replay of [WeakLeafLd8.v] (READ THAT FILE FIRST — it is the
    template and this file deliberately mirrors its section structure): from
    the M-mode config bundle, the PC cell, [WeakFunnel.winstr] and the owned
    four data bytes ([WeakInstr.wpt4]) to [WP (Loop) {{ Φ }}].  Nothing about
    the weak machine is left as a premise — no certificate, no [wP_eff], no
    [exec]/[exec_eff] fact.

    WHAT THE WIDTH CHANGES, AND WHAT IT DOES NOT:

      - THE CERTIFICATE IS FREE.  Width 4 is [WeakCert]'s native width, and
        [WeakFetchEff.wcert_load_base4] already states [wcert_load] at the
        concrete fetch element this tree produces — so this file has NO §1 at
        all.  (The width-8 leaf had to generalize [wcert_load] to
        [wcert_load_w] first; that lemma serves ANY width and this file's
        certificate is its [n := 4] instance, already landed.)
      - THE SIGN FLAG IS FREE.  [WeakLeafBase4.exec_eff_execute_LOAD_4_gpr]
        leaves the instruction's [is_unsigned] bit [u] as a variable, so ONE
        leaf lemma below covers [lw] ([u = false], the loaded register is
        [sign_extend' 64 v]) and [lwu] ([u = true], [zero_extend' 64 v])
        alike: the written value is [extend_value u v].  Unlike the 8-byte
        load, [extend_value] is NOT the identity at width 4, so the value is
        carried in that shape rather than collapsed.
      - THE RESOURCE IS [↦w₄].  [WeakInstr.wpt4] with its own
        [wwp_lw4]/[wwp_lw4_carry]/[wpt4_flat_pin] kit — all of it landed at
        M2b/M3; nothing is re-proved here.
      - THE WINDOW IS 4+4: the SHARED kit's [WeakLeafWin.wwin pc ea 4],
        together with the kit's register helpers ([set_lookup_ne],
        [leaf_peel], [load_sexec_facts], [reg_at_flat], [wpt4_align]).

    Assembled out of what batches 0/1 landed: [WeakFunnel.wwp_instr] (the
    funnel, both seams fixed), [WeakFetchEff.wP_eff_of_leaf_base] (the
    recipe), [WeakLeafBase4.exec_eff_execute_LOAD_4_gpr] (the shape — trace
    [[WEread wak_plain ea 4]]), and [WeakInstr]'s [↦w₄] tower (the resource).

    EVERY PURE / GEOMETRY SIDE CONDITION IS A PREMISE (alignment, the PMP/PMA
    match, [dev_addr], the decode facts, [agree_on], [goodb0]); a real call
    site discharges each by [vm_compute], exactly as for the SC width-8
    leaf. *)
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
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakFetchEff WeakLeafBase4.
Require Import WeakFunnel WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
(* The shared window kit + register helpers ([wwin], [set_lookup_ne],
   [leaf_peel], [load_sexec_facts], [reg_at_flat], [wpt4_align]). *)
Require Import WeakLeafWin.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE CERTIFICATE — nothing to prove

    Width 4 is [WeakCert]'s native width: [WeakFetchEff.wcert_load_base4] IS
    this leaf's certificate, at the concrete fetch element and with
    [Q := wQ_load ea] (= [wQ_load_w 4 ea]).  §3 consumes it directly; the
    width-generic family [WeakLeafLd8.wcert_load_w] subsumes it at [n := 4]
    ([wcert_load_w_4], the recorded regression check). *)

(* ====================================================================== *)
(** ** 2. THE WINDOW AND THE [wP_eff] HALF *)

(** *** 2a/2b. The window and its obligations are the SHARED kit's
    ([WeakLeafWin]): [wwin pc ea 4] with [wwin_nonzero] / [wwin_pinned] /
    [wwin_conf_text] / [wwin_conf_data]. *)

(** [SailStdpp.Values] is imported for the ['b"…"] literal notation; every
    [gset Arch.pa] lives in [WeakLeafWin] (the instance trap — durable
    notes). *)
Import SailStdpp.Values.

(** *** 2c. THE SECOND INSTANTIATION — the whole per-instruction cost.

    [WeakLeafBase4.exec_eff_execute_LOAD_4_gpr] at an ARBITRARY [s0] with the
    funnel's two pre-writes ([minstret_increment := b] and [nextPC := pc+4])
    on top — so the confined and the flat instantiation are literally this
    lemma applied twice (the batch-2 convention).  The sign flag [u] rides
    along free; the loaded register value is [extend_value u v], which at
    width 4 is a REAL extension ([data2_id_4] collapses only the
    [update_subrange_vec_dec] wrapper, not the widening). *)

(** The register [r] is passed EXPLICITLY, never left as an [_] — see
    [WeakLeafLd8]'s comment on the evar-position trap. *)
Lemma exec_eff_lw4_at (s0 : mstate) (b u : bool)
    (pc : SailStdpp.Values.mword 64) (rs1 rd : mword 5) (imm : mword 12)
    (ea : Arch.pa) (v : bv 32) :
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
  is_aligned_paddr (Physaddr ea) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
  (forall j : nat, (j < 4)%nat -> s0.(mem) !! pa_add ea j = Some (nth_byte v j)) ->
  exec_eff (execute (LOAD (imm, Regidx rs1, Regidx rd, u, 4)))
    (set_reg (set_reg s0 (R_bool minstret_increment) b)
             nextPC (add_vec_int pc 4))
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b)
                   nextPC (add_vec_int pc 4))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (extend_value u (v : mword 32))),
          [WEread wak_plain ea 4]).
Proof.
  intros Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Hal Hram4 Hbytes.
  assert (Hram : addr_is_ram ea)
    by (rewrite -(pa_add_0 ea); apply (Hram4 0%nat); lia).
  assert (Hram3 : addr_is_ram (pa_add ea 3)) by (apply Hram4; lia).
  destruct (pma_all_ram Lpma ea 4
              (pma_access_ram _ _ _ Hram Hram3
                 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
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
  assert (Ha4 : zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0) = ea).
  { rewrite Hbase Hea zero_extend'_id subrange_id. reflexivity. }
  assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
            (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs))
                     (sign_extend' 64 imm)) (xlen - 0 - 1) 0)) (0 * 4)) = ea).
  { rewrite Hbase Hea !zero_extend'_id subrange_id.
    change (0 * 4) with 0. rewrite avi0. reflexivity. }
  (* the read's [update_subrange_vec_dec] wrapper is a noop on all 32 bits;
     the [extend_value u] widening stays *)
  assert (Hev : extend_value u
            (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v)
          = extend_value u (v : mword 32)).
  { rewrite (data2_id_4 v). reflexivity. }
  rewrite -Hev -Hpa.
  apply (exec_eff_execute_LOAD_4_gpr rs1 rd imm u v region s Hrd Lpriv_s).
  - rewrite Lms_s. exact Lmprv.
  - rewrite Lsec_s. exact Lpmm.
  - rewrite Ha4. unfold is_aligned_vaddr. unfold is_aligned_paddr in Hal.
    exact Hal.
  - apply exec_eff_pmpCheck_machine_none.
    intro i. rewrite Lpmpc_s. exact (proj1 (Lpmp i)).
  - rewrite Lpma_s Hpa. exact Hmatch.
  - rewrite Hpa. exact Hal.
  - exact Hread.
  - rewrite Hpa.
    exact (exec_eff_within_clint_false ea 4 s
             (addr_is_ram_not_in_clint _ Hram) ltac:(lia)).
  - rewrite Hpa.
    exact (exec_eff_within_sig_false ea 4 s
             (addr_is_ram_not_in_sig _ Hram) ltac:(lia)).
  - rewrite Hpa. exact (exec_eff_within_htif_false ea 4 s Lhtif_s).
  - rewrite Hpa. exact (addr_is_ram_not_dev _ Hram).
  - intros j Hj. rewrite Hpa. unfold s. rewrite !mem_set_reg.
    exact (Hbytes j ltac:(lia)).
Qed.

(** The successor's register frame is [WeakLeafWin.load_sexec_facts],
    width-independent (the successor writes ONE gpr with an arbitrary
    [mword 64] value) — reused, not cloned. *)

(** *** 2d. THE [wP_eff] HALF, as a standalone lemma over the resources. *)

Section wP_eff_half.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wP_eff_lw4 (cid : nat) (σ : wmstate)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12) (u : bool)
      (ea : Arch.pa) (v : bv 32) (dq : dfrac)
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
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
    (* --- the decode, exactly as the decode library states it --- *)
    (forall r, D r = true ->
       register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (LOAD (imm, Regidx rs1, Regidx rd, u, 4), dst) ->
    (* --- the resources --- *)
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    winstr_bytes pc (F_Base w) -∗
    vwp_hold (wpt4 ea dq v) (wm_ws σ) -∗
    ⌜wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 4]) σ⌝.
  Proof.
    intros Hwf Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp
           Hal4 HnotRVC Hrd Hea Hram4 Hagree HDmi Hgood Hdec.
    iIntros "Hlat #Hbs Hpt".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iDestruct (winstr_bytes_lookup σ pc (F_Base w) Hwf with "Hlat Hbs")
      as %[_ Hfok].
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpinpc.
    iDestruct (wwp_lw4 σ ea dq v Hwf with "Hlat Hpt")
      as %[[Haccea Hpinea] Hflat4].
    iDestruct (wpt4_align with "Hpt") as %Halea.
    iPureIntro.
    destruct Hfok as (Hal2 & Hrampc & w' & [Hww _] & Htext). subst w'.
    apply (wP_eff_of_leaf_base cid σ (wwin pc ea 4) pc w
             (LOAD (imm, Regidx rs1, Regidx rd, u, 4))
             [WEread wak_plain ea 4] D dst).
    - exact Hwf.
    - exact (wwin_nonzero pc ea 4 Hrampc Hram4).
    - exact (wwin_pinned σ pc ea 4 Haccpc Haccea Hpinpc Hpinea).
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
    - exact (wwin_conf_text σ pc ea 4 w Htext).
    - exact HnotRVC.
    - exact Hagree.
    - exact HDmi.
    - exact Hgood.
    - exact Hdec.
    - reflexivity.
    - intro b. eexists. split_and!.
      + exact (exec_eff_lw4_at
                 (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                    (wm_dev σ)) b u pc rs1 rd imm ea v
                 Hrd Lpriv Lmprv Lpmm Lpmp Lpma Lhtif Hea Halea Hram4
                 (wwin_conf_data σ pc ea 4 v Hflat4)).
      + rewrite (proj1 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                      (wm_dev σ)) b (add_vec_int pc 4) rd
                   (regval_into_reg (extend_value u (v : mword 32))))).
        exact Lhart.
      + exact (proj1 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                      (wm_dev σ)) b (add_vec_int pc 4) rd
                   (regval_into_reg (extend_value u (v : mword 32)))))).
      + rewrite (proj1 (proj2 (proj2 (load_sexec_facts
                   (MState (wm_regs σ) (wmem_restrict σ (wwin pc ea 4))
                      (wm_dev σ)) b (add_vec_int pc 4) rd
                   (regval_into_reg (extend_value u (v : mword 32))))))).
        apply wmem_restrict_dom.
  Qed.

End wP_eff_half.

(* ====================================================================== *)
(** ** 3. THE LEAF

    Read the statement against [WeakLeafLd8.wwp_ld8_leaf]: the width and the
    resource changed ([↦w₈] → [↦w₄]), the instruction gained its free sign
    flag [u], and the destination register comes back as
    [regval_into_reg (extend_value u v)] — [lw] at [u = false], [lwu] at
    [u = true], ONE lemma.  Everything else is the 8-byte statement.  The
    device frame is the funnel's [⌜mdev t = mdev s_exec⌝] (seam 1) and the
    config reads are its [⌜wcfg_regs σ pmpcfg0⌝] (seam 2); the only register
    the leaf reads for itself is its own base operand. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_lw4_leaf Φ
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 rd : mword 5) (imm : mword 12) (u : bool)
      (ea : Arch.pa) (v : bv 32) (dqv : dfrac) (q : Qp)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (rs1v rd0 npc0 : SailStdpp.Values.mword 64)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_all_off pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    uint rd <> 0 ->
    add_vec rs1v (sign_extend' 64 imm) = ea ->
    (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add ea j)) ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (LOAD (imm, Regidx rs1, Regidx rd, u, 4), t)) ->
    (forall rs : regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (LOAD (imm, Regidx rs1, Regidx rd, u, 4), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wpt4 ea dqv v) ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       R_bitvector_64 (gpr_of_Z (uint rd))
         ↦ᵣ (regval_into_reg (extend_value u (v : mword 32))) -∗
       hart_ws cpu_id ws' -∗
       vwp_hold (wpt4 ea dqv v) ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz Hrd Hea Hram4 Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hrdc #Hbs Hhws Hpt Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* THE WHOLE config goes to the funnel: it hands the reads back. *)
    iApply (wwp_instr Φ pc false (LOAD (imm, Regidx rs1, Regidx rd, u, 4))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id))
                 ([WEread wak_plain pc 4] ++ [WEread wak_plain ea 4]))
              (wQ_load ea) Hgid Haccpc (pmp_all_off_allows_all _ Hpmp)
              (wcert_load_base4 (fin_to_nat cpu_id) pc wak_plain ea eq_refl)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (LOAD (imm, Regidx rs1, Regidx rd, u, 4))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %->.
    (* the config, as the funnel read it (seam 2) *)
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
    iDestruct (wP_eff_lw4 (fin_to_nat cpu_id) σ pc w rs1 rd imm u ea v dqv D dst
                 Hwf Lpc0 Lpriv ltac:(rewrite Lpmpc; exact Hpmp) Lpma
                 Lhtif Lhart LmisaS LmIE Lmprv Lpmm Lelp Hal4 HnotRVC Hrd Hea_σ
                 Hram4 Hag_σ HDmi Hgood Hdec with "Hlat Hbs Hpt") as %HP.
    (* ---- the flat facts: the data word ---- *)
    iDestruct (wwp_lw4 σ ea dqv v Hwf with "Hlat Hpt") as %[_ Hflat4].
    iDestruct (wpt4_align with "Hpt") as %Halea.
    (* ---- the run, at the FLAT state: the SC [execute] fact ---- *)
    pose proof (exec_eff_lw4_at (wflat_st σ) b u pc rs1 rd imm ea v Hrd Lpriv
                  Lmprv Lpmm ltac:(rewrite Lpmpc; exact Hpmp) Lpma Lhtif Hea_σ
                  Halea Hram4 Hflat4) as Hexf.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value u (v : mword 32)))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (extend_value u (v : mword 32)))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hexf)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    (* the device frame (seam 1): the [execute] moved no device *)
    assert (Hdevt : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ).
      exact (proj1 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
                (add_vec_int pc 4) rd
                (regval_into_reg (extend_value u (v : mword 32)))))))). }
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' & Hbnd').
    destruct HQ as (HQi & HQl & HQv).
    (* the hart's own view cell moves to [σ']'s *)
    iMod (hart_ws_update cpu_id (wm_ws σ) (wm_ws σ) (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    (* the PC the funnel hands back IS [pc+4] *)
    iEval (rewrite (proj2 (proj2 (proj2 (proj2 (load_sexec_facts (wflat_st σ) b
             (add_vec_int pc 4) rd
             (regval_into_reg (extend_value u (v : mword 32))))))))) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevt HQl. iFrame. }
    (* the config comes back WHOLE from the funnel: nothing to recombine *)
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hrdc Hhws [Hpt]").
    - exact Hwsle.
    - iApply (wwp_lw4_carry σ σ' t ea dqv v with "Hpt").
      split_and!; [exact Hregs|exact Hdevs|exact Hmems|exact Himgs
                  |exact Hlogs|exact Hwsle|exact Hwf'|exact Hbnd'].
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions wcert_load_base4.
Print Assumptions wP_eff_lw4.
Print Assumptions wwp_lw4_leaf.
