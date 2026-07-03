(* WpGprRvc.v -- the RVC (compressed, 2-byte) EXPANSION library.

   The per-RVC WP lemmas that used to live here (wp_cli/caddi/clui/cslli/
   csrli/cmv/cadd/cor/cand/caddiw/cld/cldsp/csdsp/caddi16sp/caddi4spn + the
   wp_rvc_* engines) are GONE: the [ExecuteAs] indirection is now folded into
   the [instr] predicate itself (InstrBytes.v) -- [instr pc true i] carries
   the compressed DECODED form i0 together with its state-generic expansion
   [forall s, exec (execute i0) s = Some (ExecuteAs i, s)], so a compressed
   instruction is stepped by the base-instruction WP of its TARGET [i]
   (wp_addi_gpr / wp_lui_gpr / wp_slli_gpr / wp_srli_gpr / wp_add_gpr /
   wp_or_gpr / wp_and_gpr / wp_addiw_gpr / wp_ld_gpr / wp_store_gpr /
   wp_jalr_gpr / the _tor and S-mode variants), all generalized over an
   [is_rvc : bool] whose only trace is the pc increment
   [if is_rvc then 2 else 4].

   What remains here:
     - the operand-encoding abbreviations (cli_rs1 / csp_rs1 /
       caddi16sp_imm / caddi4spn_imm) and value helpers (cli_wval,
       sext6_12_64, add_vec_zero_l, gpr_file_x0, rvc_width_true/false)
       chains use to normalize the base-WP-shaped written values;
     - the [exec_execute_C_*] ExecuteAs-expansion facts, which now feed the
       [instr] CONSTRUCTORS (each kernel_text -∗ instr pc true <target>
       proof supplies decode_C_* + exec_execute_C_* for the indirect arm);
     - [wp_cret_gpr], the one RVC step with no rd<>0 base-WP target
       (jalr x0), restated over the unfolded [JALR (0, ra, x0)]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr WpGprAddi WpGprLui WpGprShift WpGprLogic WpGprLoad WpGprJalr WpGprStore.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* RVC operand encodings (reused verbatim from the old WpRvc.v).          *)
(* ===================================================================== *)
Definition cli_rs1 : mword 5 := zero_extend' 5 ('b"00").
Definition csp_rs1 : mword 5 := zero_extend' 5 ('b"10").
Definition caddi16sp_imm (imm : mword 6) : mword 12 := sign_extend' 12 (concat_vec imm (Ox"0")).
Definition caddi4spn_imm (nzimm : mword 8) : mword 12 := concat_vec ('b"00") (concat_vec nzimm ('b"00")).

(* ===================================================================== *)
(* ExecuteAs-expansion facts: exec (execute (C_..)) = ExecuteAs base.       *)
(* Representation-independent; reused verbatim.                            *)
(* ===================================================================== *)
Lemma exec_execute_C_LI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LI (imm, rd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, zreg, rd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LI. apply exec_returnM. Qed.

Lemma exec_execute_C_LUI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LUI (imm, rd))) s
    = Some (ExecuteAs (UTYPE (sign_extend' 20 imm, rd, LUI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LUI. apply exec_returnM. Qed.

Lemma exec_execute_C_SRLI (shamt : mword 6) (crsd : cregidx) s :
  exec (execute (C_SRLI (shamt, crsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SRLI. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SLLI (shamt : mword 6) (rsd : regidx) s :
  exec (execute (C_SLLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SLLI. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_MV (rd rs2 : regidx) s :
  exec (execute (C_MV (rd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_MV. apply exec_returnM. Qed.

Lemma exec_execute_C_ADD (rsd rs2 : regidx) s :
  exec (execute (C_ADD (rsd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADD. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, rsd, rsd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI16SP (imm : mword 6) s :
  exec (execute (C_ADDI16SP imm)) s
    = Some (ExecuteAs (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI16SP, caddi16sp_imm. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI4SPN (rdc : cregidx) (nzimm : mword 8) s :
  exec (execute (C_ADDI4SPN (rdc, nzimm))) s
    = Some (ExecuteAs (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx rdc, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI4SPN, caddi4spn_imm. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_OR (rsd rs2 : cregidx) s :
  exec (execute (C_OR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, OR)), s).
Proof. unfold execute. cbn match. unfold execute_C_OR. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_AND (rsd rs2 : cregidx) s :
  exec (execute (C_AND (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, AND)), s).
Proof. unfold execute. cbn match. unfold execute_C_AND. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDIW (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDIW (imm, rsd))) s
  = Some (ExecuteAs (ADDIW (sign_extend' 12 imm, rsd, rsd)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDIW. apply exec_returnM. Qed.

Lemma exec_execute_C_LD (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LD (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LD. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_LDSP (uimm : mword 6) (rd : regidx) s :
  exec (execute (C_LDSP (uimm, rd))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, rd, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LDSP. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SDSP (uimm : mword 6) (rs2 : regidx) s :
  exec (execute (C_SDSP (uimm, rs2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), rs2, sp, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SDSP. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_JR (rs1 : regidx) s :
  exec (execute (C_JR rs1)) s = Some (ExecuteAs (JALR (zeros' 12, rs1, zreg)), s).
Proof. unfold execute. cbn match. unfold execute_C_JR. apply exec_returnM. Qed.

(* ===================================================================== *)
(* Helper facts shared by chains that step compressed instructions via     *)
(* the (is_rvc-generalized) BASE-instruction WPs.                           *)
(* ===================================================================== *)
(* sign-extending imm6 to 12 bits then to 64 is the same as extending it to 64
   directly (nested sign extension collapses); lets chains state the write
   value of a compressed addi/addiw with a single [sign_extend' 64 imm6]. *)
Lemma sext6_12_64 (x : mword 6) : sign_extend' 64 (sign_extend' 12 x) = sign_extend' 64 x.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed.
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  reflexivity.
Qed.

(* adding the zero register is a noop (used by c.li = addi rd,x0 and c.mv = add rd,x0). *)
Lemma add_vec_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof. apply bv_add_0_l. vm_compute. reflexivity. Qed.

(* the value a c.li rd, imm6 (= addi rd, x0, sext imm6) writes. *)
Definition cli_wval (imm6 : mword 6) : mword 64 :=
  sign_extend' 64 imm6.

(* the [if is_rvc then 2 else 4] pc-increment of the generalized base WPs,
   reduced at the two literal widths -- chains rewrite these away before their
   concrete pc-arithmetic facts. *)
Lemma rvc_width_true : (if true then 2 else 4)%Z = 2%Z.
Proof. reflexivity. Qed.
Lemma rvc_width_false : (if false then 2 else 4)%Z = 4%Z.
Proof. reflexivity. Qed.

(* the file's x0 entry is hardwired zero.  Chains stepping c.li / c.mv
   through the (is_rvc-generalized) base ADDI / ADD WPs read the x0 source
   OFF THE FILE (the base WPs' written value is phrased over [m !!! rs1]),
   so they need its value pinned; formerly the per-RVC WPs baked the zero in. *)
Section GprFileX0.
  Context `{!riscvGS Σ}.

  Lemma gpr_file_x0 (m : gmap regidx (mword 64)) (i : mword 5) :
    uint i = 0 ->
    gpr_file m -∗ ⌜ m !!! Regidx i = zero_reg ⌝ ∗ gpr_file m.
  Proof.
    iIntros (Hi) "[%Hdom Hmap]".
    assert (Hm : m !! Regidx i = Some (m !!! Regidx i))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm with "Hmap") as "[Hpt Hcl]".
    iEval (unfold gpr_pt; rewrite Hi; simpl) in "Hpt".
    iDestruct "Hpt" as %Hz.
    iSplitR; [iPureIntro; exact Hz|].
    iSplitR; [iPureIntro; exact Hdom|].
    iApply "Hcl". iEval (unfold gpr_pt; rewrite Hi; simpl). iPureIntro. exact Hz.
  Qed.
End GprFileX0.

(* ===================================================================== *)
(* ret / c.ret  =  jalr x0, 0(ra):  a CONTROL-FLOW op whose destination is  *)
(* x0, which [wp_jalr_gpr] (rd <> 0) does not cover.  Stated over the       *)
(* UNFOLDED target [JALR (zeros12, Regidx ra, zreg)] -- the c.ret caller    *)
(* supplies [instr pc true ..] built from the C_JR decode + the             *)
(* [exec_execute_C_JR] expansion; a hypothetical 4-byte ret would use       *)
(* [is_rvc = false].  Since rd = x0 there is NO link write, so the          *)
(* [gpr_file] is UNCHANGED and PC jumps to the target [ (m!!!ra) with low   *)
(* bit cleared ].  Mirrors [wp_jalr_gpr] (the mseccfg.MLPE / Zicfilp check  *)
(* + target alignment) but with NO destination register.                    *)
(* ===================================================================== *)
Section RvcRet.
  Context `{!riscvGS Σ}.

  Definition cret_target (vra : mword 64) : mword 64 :=
    update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0").

  Lemma wp_cret_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (ra : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    is_aligned_paddr (Physaddr (cret_target (m !!! Regidx ra))) 4 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (cret_target (m !!! Regidx ra)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hra Halign) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hal0 Hal1].
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hmlpe & %Help_np)".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iApply (wp_instr E Φ pc true (JALR (zeros' 12, Regidx ra, zreg)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx ra = Some (m !!! Regidx ra))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg") as %Lsec.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value ra (m !!! Regidx ra) s_pc with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* base register at s_pc = m!!!ra (ra <> 0) *)
    assert (Lrav : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs)
                   = m !!! Regidx ra).
    { rewrite -Hrv. replace (Z.eqb (uint ra) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hra). reflexivity. }
    (* Zicfilp disabled at s_pc (Machine + MLPE off) *)
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false.
      - unfold s_pc; tmig; exact Lpriv.
      - unfold s_pc; tmig; rewrite Lsec; exact Hmlpe. }
    (* target computed by the model with base at s_pc = cret_target (m!!!ra) *)
    assert (Htgt : update_vec_dec (add_vec
                     (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                     (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0")
                   = cret_target (m !!! Regidx ra)).
    { unfold cret_target. rewrite Lrav. reflexivity. }
    assert (Hexec_spc :
      exec (execute (JALR (zeros' 12, Regidx ra, zreg))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc nextPC (cret_target (m !!! Regidx ra)))).
    { change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx cli_rs1).
      rewrite (exec_execute_JALR_ret (zeros' 12) ra cli_rs1 s_pc Hra
                 ltac:(vm_compute; reflexivity) Hzic
                 ltac:(rewrite Htgt; exact Hal0) ltac:(rewrite Htgt; exact Hal1)).
      rewrite Htgt. reflexivity. }
    (* update nextPC := target so the ghost heap matches s_exec *)
    iMod (reg_update _ nextPC _ (cret_target (m !!! Regidx ra)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).(sregs)
             = cret_target (m !!! Regidx ra)).
    { rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hmst_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k Hmst_k". }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

End RvcRet.
