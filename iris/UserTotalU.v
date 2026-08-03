(* ===================================================================== *)
(* UserTotalU.v -- the two U-mode EXECUTE TOTALITIES (worklist item B+C).  *)
(*                                                                         *)
(*   base_exec_total_u_holds / rvc_exec_total_u_holds  (UserClassifyAsm.v) *)
(*                                                                         *)
(* This file builds and CLOSES both totalities (Qed, no admits):           *)
(*   * the decode-agreement discharge (post_fetch_cfg + hw_config +        *)
(*     user_cfg  ==>  agree_on D_u sigma_f dstateU), so decode_total_u_set *)
(*     fires at the fetched state;                                         *)
(*   * reusable "finish" glue per result SHAPE (state-unchanged retire /   *)
(*     illegal / trap / enter-wait ; single-gpr-write retire ; jump),      *)
(*     re-establishing  mstate_interp ∗ gpr_file ∗ nextPC value-agnostic.  *)
(*   * per-family arms (jumps, CSR, RVC compute/direct/jump) dispatched by  *)
(*     the two `_holds` proofs; memory families are section Variables the   *)
(*     parent instantiates with UserMemClassify.v's proven arms.           *)
(*                                                                         *)
(* See the FRONTIER block at the bottom for the family->arm map and the     *)
(* verbatim memory Variable contract the sibling must match.               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr RegFile UserBits.
Require Import UserPtTree UserExec UserStep UserCompute UserClassify UserClassifyAsm.
Require Import WpDecodeBridge DecodeTotalU DecodeSetU UserExecFacts UserCsr WpMmodeLeafBase.
Require Import WpDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Item (C): the cheap missing execute facts.                             *)
(*   base ILLEGAL  -> Illegal_Instruction tt      (a `u_result_ok`)       *)
(*   C_J           -> ExecuteAs (JAL ...)          (syntactic expansion)  *)
(*   C_BEQZ        -> ExecuteAs (BTYPE ... BEQ)    (syntactic expansion)  *)
(* (ZICBOP is NOT here -- prefetch runs a real translateAddr on the        *)
(*  runtime address; it is memory/ADUE-coupled, see the FRONTIER note.)    *)
(* ===================================================================== *)

Lemma exec_execute_ILLEGAL_U (w : mword 32) (s : mstate) :
  exec (execute (ILLEGAL w)) s = Some (Illegal_Instruction tt, s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_J_U (imm : mword 11) (s : mstate) :
  exec (execute (C_J imm)) s
    = Some (ExecuteAs (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)), s).
Proof. apply exec_returnm. Qed.

Lemma exec_execute_C_BEQZ_U (imm : mword 8) (rs : cregidx) (s : mstate) :
  exec (execute (C_BEQZ (imm, rs))) s
    = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")),
                              zreg, creg2reg_idx rs, BEQ)), s).
Proof. apply exec_returnm. Qed.

(* The decode-width facts carried by the refined [decodable_u] (DecodeSetU):
   the memory families' widths land in {1,2,4,8} (base LOAD/STORE/LR/SC) or
   {1,2,4,8,16} (AMO).  [base_exec_total_u_holds] extracts these from [Hdi]
   and threads them to the memory arms. *)
Lemma width_ok1248_cases (w : Z) :
  width_ok1248 w = true -> w = 1 \/ w = 2 \/ w = 4 \/ w = 8.
Proof.
  unfold width_ok1248. intro H.
  repeat (apply orb_true_iff in H as [H|H]); apply Z.eqb_eq in H; auto.
Qed.

Lemma awidth_ok_cases (w : Z) :
  awidth_ok w = true -> w = 1 \/ w = 2 \/ w = 4 \/ w = 8 \/ w = 16.
Proof.
  unfold awidth_ok. intro H.
  repeat (apply orb_true_iff in H as [H|H]); apply Z.eqb_eq in H; auto.
Qed.

(* LR/SC decode is now pinned to {4,8} in [decodable_u] (DecodeSetU's
   goodbP_zalrsc_gate carries [lrsc_width_valid width]). *)
Lemma lrsc_width_valid_cases (w : Z) :
  lrsc_width_valid w = true -> w = 4 \/ w = 8.
Proof.
  unfold lrsc_width_valid. intro H.
  destruct (Z.eqb w 4) eqn:E4.
  - apply Z.eqb_eq in E4; auto.
  - destruct (Z.eqb w 8) eqn:E8.
    + apply Z.eqb_eq in E8; auto.
    + discriminate H.
Qed.

Section UserTotalU.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The decode-agreement discharge: from the totality's config premises  *)
  (* (post_fetch_cfg's cur_privilege/menvcfg at sigma_f, hw_config's misa, *)
  (* user_cfg's senvcfg/mstateen0/sstateen0), the fetched state agrees     *)
  (* with the U-mode decode reference on the whole decode read set D_u.    *)
  (* Non-consuming (pure conclusion), so the resources survive.            *)
  (* ------------------------------------------------------------------- *)
  Lemma user_decode_agree (sigma_f : mstate) (va : mword 64) :
    register_lookup cur_privilege sigma_f.(sregs) = User ->
    register_lookup menvcfg sigma_f.(sregs) = MENVCFG_S ->
    reg_interp (set_reg sigma_f nextPC va).(sregs) -∗
    hw_config -∗ user_cfg C -∗
    ⌜agree_on D_u sigma_f dstateU⌝.
  Proof.
    intros Lcp Lmenv.
    iIntros "Hreg #Hhw Hcfg".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcmenv & Hsenv & Hms0 & Hss0)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hmisa0 & _)".
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv0.
    iDestruct (reg_valid_dq with "Hreg Hms0") as %Lms00.
    iDestruct (reg_valid_dq with "Hreg Hss0") as %Lss00.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iPureIntro.
    assert (Tr0 : forall (r : register) (v : type_of_register r),
              register_lookup r (set_reg sigma_f nextPC va).(sregs) = v ->
              register_beq r nextPC = false ->
              register_lookup r sigma_f.(sregs) = v).
    { intros r v Hv Hne. unfold set_reg in Hv; cbn [sregs] in Hv.
      rewrite irrelevant_register_set in Hv; [exact Hv | exact Hne]. }
    apply agree_u.
    - exact Lcp.
    - exact Lmenv.
    - apply Tr0; [exact Lsenv0 | vm_compute; reflexivity].
    - apply Tr0; [exact Lms00 | vm_compute; reflexivity].
    - apply Tr0; [exact Lss00 | vm_compute; reflexivity].
    - rewrite <- Hmisa0. apply Tr0; [exact Lmisa0 | vm_compute; reflexivity].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The postcondition body of base_exec_total_u, abstracted so the glue   *)
  (* lemmas below can each close it for one result SHAPE.  [va] is the pc,  *)
  (* the fetched-state is [sigma_f], the execute runs at [s0 := set_reg     *)
  (* sigma_f nextPC (va+4)].                                                *)
  (* ------------------------------------------------------------------- *)
  Local Notation s0 sigma_f va := (set_reg sigma_f nextPC (add_vec_int va 4)).

  Definition base_post (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (w : mword 32) (g : regfile) : iProp Σ :=
    (|={E}=>
      ∃ (instr : instruction) (r0 : ExecutionResult) (s_x : mstate)
        (g' : regfile) (va' : mword 64),
        ⌜exec (ext_decode w) sigma_f = Some (instr, sigma_f)⌝ ∗
        ⌜is_lpad_instruction instr = false⌝ ∗
        ⌜exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 4)) = Some (r0, s_x)
         \/ (exists other,
               exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 4))
                 = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 4))
               /\ exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 4)) = Some (r0, s_x))⌝ ∗
        ⌜u_result_ok r0⌝ ∗
        ⌜match r0 with ExecuteAs _ => False | _ => True end⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
           = register_lookup (R_bool minstret_increment) sigma.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C)%I.

  (* GLUE (a): state-unchanged retire / illegal / trap / enter-wait / nop.   *)
  (* Covers every family whose execute leaves s0 UNCHANGED and writes no gpr *)
  (* (ILLEGAL, ECALL/EBREAK-trap, WFI/MRET/SRET/sfence illegal, WRS,         *)
  (*  NTL/PAUSE/FENCE/FENCE.I/FENCE.TSO, ZICBOM/ZICBOZ/SSAMOSWAP illegal).    *)
  Lemma finish_unchanged (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (i : instruction) (r : ExecutionResult) (w : mword 32) :
    register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs) ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    exec (execute i) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (r, set_reg sigma_f nextPC (add_vec_int va 4)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hexec Hok Hnex.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold base_post.
    iModIntro.
    iExists i, r, (set_reg sigma_f nextPC (add_vec_int va 4)), g, (add_vec_int va 4).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdec|]. split; [exact Hlpad|].
    split; [left; exact Hexec|]. split; [exact Hok|]. split; [exact Hnex|].
    split.
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
    unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  (* GLUE (a'): state-unchanged via ONE base ExecuteAs redirect (SINVAL_VMA
     -> SFENCE_VMA -> Illegal at User, state unchanged). *)
  Lemma finish_unchanged_redirect (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (i other : instruction) (r : ExecutionResult) (w : mword 32) :
    register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs) ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    exec (execute i) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 4)) ->
    exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (r, set_reg sigma_f nextPC (add_vec_int va 4)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hex1 Hex2 Hok Hnex.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold base_post.
    iModIntro.
    iExists i, r, (set_reg sigma_f nextPC (add_vec_int va 4)), g, (add_vec_int va 4).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdec|]. split; [exact Hlpad|].
    split; [right; exists other; split; [exact Hex1|exact Hex2]|].
    split; [exact Hok|]. split; [exact Hnex|].
    split.
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
    unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  Lemma u_result_ok_retire : u_result_ok RETIRE_SUCCESS.
  Proof. unfold u_result_ok. left. reflexivity. Qed.

  (* GLUE (b): single-gpr-write retire (RETIRE_SUCCESS, gpr_write_state).     *)
  (* Covers the whole integer-compute + Zbb/Zbc/Zicond/Zimop retiring set     *)
  (* (ITYPE/RTYPE/RTYPEW/SHIFTIOP/SHIFTIWOP/ADDIW/MUL.../DIV.../REM.../UTYPE/  *)
  (*  ZBB.../CLMUL.../REV8/RORI.../ZIMOP.../ZICOND) and C_NOT/C_ZEXT_B.        *)
  Lemma finish_gprwrite (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (i : instruction) (ird : mword 5) (v : mword 64)
      (w : mword 32) :
    register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs) ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    exec (execute i) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (RETIRE_SUCCESS, gpr_write_state ird v (set_reg sigma_f nextPC (add_vec_int va 4))) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hexec.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold base_post.
    unfold gpr_write_state in Hexec |- *.
    destruct (Z.eqb (uint ird) 0) eqn:Hrd0.
    - (* rd = 0: no write, state unchanged -- reuse finish_unchanged *)
      iApply (finish_unchanged E sigma sigma_f va g i RETIRE_SUCCESS w
                Lmi Hdec Hlpad Hexec u_result_ok_retire I
                with "[Hreg Hgh Hdev] Hgpr Hnpc Hupt Hcfg").
      unfold mstate_interp. iFrame "Hreg Hgh Hdev".
    - (* rd <> 0: move the rd gpr fragment + update the auth *)
      assert (Hrdne : uint ird <> 0) by (apply Z.eqb_neq; exact Hrd0).
      iDestruct (gpr_file_acc g ird Hrdne with "Hgpr") as "[Hrd Hins]".
      iDestruct "Hrd" as (v0) "Hrd".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint ird))) v0 v with "Hreg Hrd") as "[Hreg Hrd]".
      iDestruct ("Hins" $! v with "Hrd") as "Hgpr".
      iModIntro.
      set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 4))
                     (R_bitvector_64 (gpr_of_Z (uint ird))) v).
      iExists i, RETIRE_SUCCESS, s_x, (<[Regidx ird := v]> g), (add_vec_int va 4).
      assert (LmiX : register_lookup (R_bool minstret_increment) s_x.(sregs)
                     = register_lookup (R_bool minstret_increment) sigma.(sregs)).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
      assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 4).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        apply register_lookup_set. }
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split_and!;
        first [ exact Hdec | exact Hlpad | (left; exact Hexec)
              | exact u_result_ok_retire | exact I
              | exact LmiX | exact LnpcX ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Config transport: post_fetch_cfg pins the values at sigma_f; the      *)
  (* execute runs at [s0 = set_reg sigma_f nextPC (va+4)].  cur_privilege  *)
  (* and PC are unchanged by the nextPC write.                             *)
  (* ------------------------------------------------------------------- *)
  Lemma s0_cur_privilege (sigma_f : mstate) (va : mword 64) :
    register_lookup cur_privilege sigma_f.(sregs) = User ->
    register_lookup cur_privilege (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) = User.
  Proof.
    intro H. unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [exact H | vm_compute; reflexivity].
  Qed.

  Lemma s0_PC (sigma_f : mstate) (va : mword 64) :
    register_lookup PC sigma_f.(sregs) = va ->
    register_lookup PC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) = va.
  Proof.
    intro H. unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [exact H | vm_compute; reflexivity].
  Qed.

  (* ===================================================================== *)
  (* END-TO-END DEMONSTRATION ARMS.  Each runs the full pipeline the        *)
  (* totality needs -- family execute fact + result classification + glue   *)
  (* re-establishing the frame -- for ONE representative of each of the      *)
  (* FOUR `u_result_ok` outcome classes:                                    *)
  (*   RETIRE     : ITYPE  (single-gpr-write retire)                        *)
  (*   ILLEGAL    : ILLEGAL / WFI / MRET / SRET / sfence family             *)
  (*   USER-TRAP  : ECALL  (delegated E_U_EnvCall)                          *)
  (*   ENTER-WAIT : WRS.STO / WRS.NTO                                        *)
  (* They take the fetched-state facts a proof of the totality would derive  *)
  (* from post_fetch_cfg + hw_config + user_cfg, PLUS the hart_state fact    *)
  (* [Lhs] the current spec does NOT supply (see the FRONTIER note).         *)
  (* ===================================================================== *)

  Local Notation Lmi_ty sigma sigma_f :=
    (register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs)).

  (* RETIRE class: an ITYPE (add/andi/... at U). *)

  (* ILLEGAL class: a bare ILLEGAL word (state-unchanged illegal). *)
  Lemma arm_ILLEGAL (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w wi : mword 32) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode w) sigma_f = Some (ILLEGAL wi, sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec.
    assert (Hok : u_result_ok (Illegal_Instruction tt))
      by (unfold u_result_ok; right; right; left; reflexivity).
    iApply (finish_unchanged E sigma sigma_f va g (ILLEGAL wi) (Illegal_Instruction tt) w
              Lmi Hdec eq_refl (exec_execute_ILLEGAL_U wi _) Hok I).
  Qed.

  (* USER-TRAP class: ECALL delegates to E_U_EnvCall (user_exc = true). *)
  Lemma arm_ECALL (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege sigma_f.(sregs) = User ->
    register_lookup PC sigma_f.(sregs) = va ->
    exec (ext_decode w) sigma_f = Some (ECALL tt, sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lcp Lpc Hdec.
    pose proof (exec_execute_ECALL_U (set_reg sigma_f nextPC (add_vec_int va 4)) va
                  (s0_cur_privilege sigma_f va Lcp) (s0_PC sigma_f va Lpc)) as Hexec.
    assert (Hok : u_result_ok (rv64d_types.Trap
              (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), va))).
    { unfold u_result_ok. right; left.
      exists (E_U_EnvCall tt), (zeros' 64), va. split; reflexivity. }
    iApply (finish_unchanged E sigma sigma_f va g (ECALL tt) _ w
              Lmi Hdec eq_refl Hexec Hok I).
  Qed.

  (* ENTER-WAIT class: WRS.STO / WRS.NTO park the hart WAITING. *)
  Lemma arm_WRS (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (op : wrsop) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode w) sigma_f = Some (WRS op, sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec.
    assert (Hok : u_result_ok (Enter_Wait (match op with
                        | WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end))).
    { unfold u_result_ok. right; right; right.
      eexists. split; [reflexivity|]. destruct op; [left|right]; reflexivity. }
    assert (Hnex : match Enter_Wait (match op with
                        | WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end)
                   with ExecuteAs _ => False | _ => True end) by exact I.
    iApply (finish_unchanged E sigma sigma_f va g (WRS op) _ w
              Lmi Hdec eq_refl (exec_execute_WRS op _) Hok Hnex).
  Qed.

  (* ===================================================================== *)
  (* CONFIG-FACT HELPERS.  These read config cells NON-consumingly (pure     *)
  (* conclusion, so the spatial inputs survive) so an arm can derive the     *)
  (* execute-fact side conditions and STILL hand the resources to the glue.  *)
  (* ===================================================================== *)

  (* senvcfg = 0 at any state, from user_cfg's senvcfg cell. *)
  Lemma ucfg_senvcfg (s : mstate) :
    reg_interp s.(sregs) -∗ user_cfg C -∗
    ⌜register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64)⌝.
  Proof.
    iIntros "Hreg Hcfg".
    iDestruct "Hcfg" as "(_ & _ & _ & _ & _ & _ & Hsenv & _ & _)".
    iApply (reg_valid_dq with "Hreg Hsenv").
  Qed.

  (* misa = MISA_C at any state, from hw_config's persistent misa cell. *)
  Lemma hwcfg_misa (s : mstate) :
    reg_interp s.(sregs) -∗ hw_config -∗
    ⌜register_lookup misa s.(sregs) = MISA_C⌝.
  Proof.
    iIntros "Hreg #Hhw".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hm & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %L.
    iPureIntro. rewrite L. exact Hm.
  Qed.

  (* the two extension gates the config-illegal / control-flow arms consult,
     derived from misa = MISA_C. *)
  Lemma s0_ext_S (s : mstate) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (currentlyEnabled Ext_S) s = Some (true, s).
  Proof.
    intro H. rewrite exec_currentlyEnabled_S H.
    replace (eq_vec (_get_Misa_S MISA_C) ('b"1")) with true by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Lemma s0_zca (s : mstate) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s).
  Proof.
    intro H. apply exec_currentlyEnabled_Zca. rewrite H. vm_compute; reflexivity.
  Qed.

  (* generic register transport across the nextPC := va+4 write. *)
  Lemma s0_reg (r : register) (v : type_of_register r) (sigma_f : mstate) (va : mword 64) :
    register_beq r nextPC = false ->
    register_lookup r sigma_f.(sregs) = v ->
    register_lookup r (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) = v.
  Proof.
    intros Hne H. unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [exact H | exact Hne].
  Qed.

  (* ===================================================================== *)
  (* GLUE (c): control-flow retire.  The execute writes nextPC to a TARGET   *)
  (* [tgt] (and, for JAL/JALR, one gpr [ird]).  base_post's va' is           *)
  (* existential, so [tgt] closes it directly.                               *)
  (* ===================================================================== *)

  (* nextPC-only jump (taken BTYPE): s_x = set_reg s0 nextPC tgt. *)
  Lemma finish_setpc (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (i : instruction) (tgt : mword 64) (w : mword 32) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    exec (execute i) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (RETIRE_SUCCESS,
               set_reg (set_reg sigma_f nextPC (add_vec_int va 4)) nextPC tgt) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hexec.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold base_post.
    iMod (reg_update _ nextPC (add_vec_int va 4) tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 4)) nextPC tgt).
    iExists i, RETIRE_SUCCESS, s_x, g, tgt.
    unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdec|]. split; [exact Hlpad|].
    split; [left; exact Hexec|]. split; [exact u_result_ok_retire|].
    split.
    { unfold s_x, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [| vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
    unfold s_x, set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  (* jump + gpr write (JAL / JALR): s_x = gpr_write_state ird v (set_reg s0 nextPC tgt). *)
  Lemma finish_jump_gpr (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (i : instruction) (ird : mword 5) (v tgt : mword 64)
      (w : mword 32) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    exec (execute i) (set_reg sigma_f nextPC (add_vec_int va 4))
       = Some (RETIRE_SUCCESS,
               gpr_write_state ird v
                 (set_reg (set_reg sigma_f nextPC (add_vec_int va 4)) nextPC tgt)) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hexec.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold base_post.
    iMod (reg_update _ nextPC (add_vec_int va 4) tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    unfold gpr_write_state in Hexec |- *.
    destruct (Z.eqb (uint ird) 0) eqn:Hrd0.
    - (* rd = 0: nextPC only *)
      iModIntro.
      set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 4)) nextPC tgt).
      iExists i, RETIRE_SUCCESS, s_x, g, tgt.
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hdec|]. split; [exact Hlpad|].
      split; [left; exact Hexec|]. split; [exact u_result_ok_retire|].
      split.
      { unfold s_x, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
      unfold s_x, set_reg; cbn [sregs]. apply register_lookup_set.
    - (* rd <> 0: nextPC then gpr write *)
      assert (Hrdne : uint ird <> 0) by (apply Z.eqb_neq; exact Hrd0).
      iDestruct (gpr_file_acc g ird Hrdne with "Hgpr") as "[Hrd Hins]".
      iDestruct "Hrd" as (v0) "Hrd".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint ird))) v0 v with "Hreg Hrd") as "[Hreg Hrd]".
      iDestruct ("Hins" $! v with "Hrd") as "Hgpr".
      iModIntro.
      set (s_x := set_reg (set_reg (set_reg sigma_f nextPC (add_vec_int va 4)) nextPC tgt)
                     (R_bitvector_64 (gpr_of_Z (uint ird))) v).
      iExists i, RETIRE_SUCCESS, s_x, (<[Regidx ird := v]> g), tgt.
      assert (LmiX : register_lookup (R_bool minstret_increment) s_x.(sregs)
                     = register_lookup (R_bool minstret_increment) sigma.(sregs)).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
      assert (LnpcX : register_lookup nextPC s_x.(sregs) = tgt).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        apply register_lookup_set. }
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split_and!;
        first [ exact Hdec | exact Hlpad | (left; exact Hexec)
              | exact u_result_ok_retire | exact I | exact LmiX | exact LnpcX ].
  Qed.

  (* Generic RETIRE-with-single-gpr arm: dispatches EVERY compute/Zbb/Zbc/
     Zicond/Zimop base retiring family through finish_gprwrite by applying
     its `exec_execute_<FAM>_total` fact (packaged as the `Htot` argument).  *)
  Lemma arm_gprwrite (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (i : instruction) (ird : mword 5) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode w) sigma_f = Some (i, sigma_f) ->
    is_lpad_instruction i = false ->
    (forall s : mstate, exists v : mword 64,
        exec (execute i) s = Some (RETIRE_SUCCESS, gpr_write_state ird v s)) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Htot.
    destruct (Htot (set_reg sigma_f nextPC (add_vec_int va 4))) as (v & Hexec).
    iApply (finish_gprwrite E sigma sigma_f va g i ird v w Lmi Hdec Hlpad Hexec).
  Qed.

  (* ===================================================================== *)
  (* THE RVC ANALOG.  Compressed (16-bit) execution runs at offset +2, and   *)
  (* EVERY reachable compressed instruction that goes through the RVC        *)
  (* progress composer expands via a single [ExecuteAs other] to a base      *)
  (* instruction which then produces the result.  rvc_post mirrors           *)
  (* rvc_exec_total_u's body; the finish_rvc_* glue re-establishes the frame *)
  (* for the same three result SHAPES as the base glue.                      *)
  (* ===================================================================== *)
  Local Notation s2 sigma_f va := (set_reg sigma_f nextPC (add_vec_int va 2)).

  Definition rvc_post (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (h : mword 16) (g : regfile) : iProp Σ :=
    (|={E}=>
      ∃ (instr : instruction) (r0 : ExecutionResult) (s_x : mstate)
        (g' : regfile) (va' : mword 64),
        ⌜exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f)⌝ ∗
        ⌜exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f)⌝ ∗
        ⌜exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2)) = Some (r0, s_x)
         \/ (exists other,
               exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
                 = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2))
               /\ exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 2)) = Some (r0, s_x))⌝ ∗
        ⌜u_result_ok r0⌝ ∗
        ⌜match r0 with ExecuteAs _ => False | _ => True end⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs)
           = register_lookup (R_bool minstret_increment) sigma.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = va'⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ nextPC ↦ᵣ va' ∗ user_pt_inv pt ∗ user_cfg C)%I.

  (* RVC state-unchanged (C_EBREAK -> EBREAK trap ; any ExecuteAs to a
     state-preserving base result). *)
  Lemma finish_rvc_unchanged (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr other : instruction) (r : ExecutionResult) (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (r, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Hex2 Hok Hnex.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    iModIntro.
    iExists instr, r, (set_reg sigma_f nextPC (add_vec_int va 2)), g, (add_vec_int va 2).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
    split; [right; exists other; split; [exact Hex1|exact Hex2]|]. split; [exact Hok|]. split; [exact Hnex|].
    split.
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
    unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  (* RVC single-gpr retire (compute expansions: C_LI/C_MV/C_ADD/... -> base). *)
  Lemma finish_rvc_gprwrite (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr other : instruction) (ird : mword 5) (v : mword 64)
      (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (RETIRE_SUCCESS, gpr_write_state ird v (set_reg sigma_f nextPC (add_vec_int va 2))) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Hex2.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    unfold gpr_write_state in Hex2 |- *.
    destruct (Z.eqb (uint ird) 0) eqn:Hrd0.
    - (* rd = 0 *)
      iModIntro.
      iExists instr, RETIRE_SUCCESS, (set_reg sigma_f nextPC (add_vec_int va 2)), g, (add_vec_int va 2).
      unfold mstate_interp. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
      split; [right; exists other; split; [exact Hex1|exact Hex2]|]. split; [exact u_result_ok_retire|].
      split.
      { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
      unfold set_reg; cbn [sregs]. apply register_lookup_set.
    - (* rd <> 0 *)
      assert (Hrdne : uint ird <> 0) by (apply Z.eqb_neq; exact Hrd0).
      iDestruct (gpr_file_acc g ird Hrdne with "Hgpr") as "[Hrd Hins]".
      iDestruct "Hrd" as (v0) "Hrd".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint ird))) v0 v with "Hreg Hrd") as "[Hreg Hrd]".
      iDestruct ("Hins" $! v with "Hrd") as "Hgpr".
      iModIntro.
      set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 2))
                     (R_bitvector_64 (gpr_of_Z (uint ird))) v).
      iExists instr, RETIRE_SUCCESS, s_x, (<[Regidx ird := v]> g), (add_vec_int va 2).
      assert (LmiX : register_lookup (R_bool minstret_increment) s_x.(sregs)
                     = register_lookup (R_bool minstret_increment) sigma.(sregs)).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
      assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 2).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        apply register_lookup_set. }
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split_and!;
        first [ exact Hdecc | exact Hzca
              | (right; exists other; split; [exact Hex1|exact Hex2])
              | exact u_result_ok_retire | exact I | exact LmiX | exact LnpcX ].
  Qed.

  (* RVC control-flow retire (C_JR/C_JALR -> JALR ; C_J -> JAL): the base
     jump writes nextPC to [tgt] and (JALR) one gpr. *)
  Lemma finish_rvc_jump_gpr (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr other : instruction) (ird : mword 5) (v tgt : mword 64)
      (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (RETIRE_SUCCESS,
               gpr_write_state ird v
                 (set_reg (set_reg sigma_f nextPC (add_vec_int va 2)) nextPC tgt)) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Hex2.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    iMod (reg_update _ nextPC (add_vec_int va 2) tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    unfold gpr_write_state in Hex2 |- *.
    destruct (Z.eqb (uint ird) 0) eqn:Hrd0.
    - (* rd = 0 (C_J / C_JR) *)
      iModIntro.
      set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 2)) nextPC tgt).
      iExists instr, RETIRE_SUCCESS, s_x, g, tgt.
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
      split; [right; exists other; split; [exact Hex1|exact Hex2]|]. split; [exact u_result_ok_retire|].
      split.
      { unfold s_x, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
      unfold s_x, set_reg; cbn [sregs]. apply register_lookup_set.
    - (* rd <> 0 (C_JALR) *)
      assert (Hrdne : uint ird <> 0) by (apply Z.eqb_neq; exact Hrd0).
      iDestruct (gpr_file_acc g ird Hrdne with "Hgpr") as "[Hrd Hins]".
      iDestruct "Hrd" as (v0) "Hrd".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint ird))) v0 v with "Hreg Hrd") as "[Hreg Hrd]".
      iDestruct ("Hins" $! v with "Hrd") as "Hgpr".
      iModIntro.
      set (s_x := set_reg (set_reg (set_reg sigma_f nextPC (add_vec_int va 2)) nextPC tgt)
                     (R_bitvector_64 (gpr_of_Z (uint ird))) v).
      iExists instr, RETIRE_SUCCESS, s_x, (<[Regidx ird := v]> g), tgt.
      assert (LmiX : register_lookup (R_bool minstret_increment) s_x.(sregs)
                     = register_lookup (R_bool minstret_increment) sigma.(sregs)).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
      assert (LnpcX : register_lookup nextPC s_x.(sregs) = tgt).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        apply register_lookup_set. }
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split_and!;
        first [ exact Hdecc | exact Hzca
              | (right; exists other; split; [exact Hex1|exact Hex2])
              | exact u_result_ok_retire | exact I | exact LmiX | exact LnpcX ].
  Qed.

  (* RVC DIRECT retire/illegal/trap (no ExecuteAs redirect): C_NOP / C_NTL /
     ZCMOP / C_ILLEGAL execute directly, leaving s2 unchanged. *)
  Lemma finish_rvc_direct (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr : instruction) (r : ExecutionResult) (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (r, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hexec Hok Hnex.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    iModIntro.
    iExists instr, r, (set_reg sigma_f nextPC (add_vec_int va 2)), g, (add_vec_int va 2).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
    split; [left; exact Hexec|]. split; [exact Hok|]. split; [exact Hnex|].
    split.
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
    unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  (* RVC DIRECT single-gpr retire (no ExecuteAs redirect): C_NOT / C_ZEXT_B
     (and ZCMOP when it retires a gpr write) execute directly. *)
  Lemma finish_rvc_direct_gprwrite (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr : instruction) (ird : mword 5) (v : mword 64)
      (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (RETIRE_SUCCESS, gpr_write_state ird v (set_reg sigma_f nextPC (add_vec_int va 2))) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hexec.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    unfold gpr_write_state in Hexec |- *.
    destruct (Z.eqb (uint ird) 0) eqn:Hrd0.
    - (* rd = 0 *)
      iModIntro.
      iExists instr, RETIRE_SUCCESS, (set_reg sigma_f nextPC (add_vec_int va 2)), g, (add_vec_int va 2).
      unfold mstate_interp. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
      split; [left; exact Hexec|]. split; [exact u_result_ok_retire|].
      split.
      { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
      unfold set_reg; cbn [sregs]. apply register_lookup_set.
    - (* rd <> 0 *)
      assert (Hrdne : uint ird <> 0) by (apply Z.eqb_neq; exact Hrd0).
      iDestruct (gpr_file_acc g ird Hrdne with "Hgpr") as "[Hrd Hins]".
      iDestruct "Hrd" as (v0) "Hrd".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint ird))) v0 v with "Hreg Hrd") as "[Hreg Hrd]".
      iDestruct ("Hins" $! v with "Hrd") as "Hgpr".
      iModIntro.
      set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 2))
                     (R_bitvector_64 (gpr_of_Z (uint ird))) v).
      iExists instr, RETIRE_SUCCESS, s_x, (<[Regidx ird := v]> g), (add_vec_int va 2).
      assert (LmiX : register_lookup (R_bool minstret_increment) s_x.(sregs)
                     = register_lookup (R_bool minstret_increment) sigma.(sregs)).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        rewrite irrelevant_register_set; [exact Lmi|vm_compute; reflexivity]. }
      assert (LnpcX : register_lookup nextPC s_x.(sregs) = add_vec_int va 2).
      { unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint ird)))).
        2:{ reg_ne. }
        apply register_lookup_set. }
      unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
      iPureIntro. split_and!;
        first [ exact Hdecc | exact Hzca | (left; exact Hexec)
              | exact u_result_ok_retire | exact I | exact LmiX | exact LnpcX ].
  Qed.

  (* ===================================================================== *)
  (* Zicfilp OFF at User: currentlyEnabled Ext_Zicfilp = false.  get_xLPE at *)
  (* User reads senvcfg.LPE (Ext_S enabled); senvcfg = 0 pins LPE = 0.  Feeds *)
  (* JALR's [update_elp_state] premise.  Mirrors WpMmodeLeafBase's Machine    *)
  (* [exec_cE_zicfilp_false] / WpDecode's [exec_cE_zicfilp_mSU] User branch.   *)
  (* ===================================================================== *)
  Lemma s0_zicfilp (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
  Proof.
    intros Hpriv Hmisa Hmenv Hsenv.
    unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _
              (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
                 ltac:(vm_compute; reflexivity))).
    cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv.
    match goal with |- context[_rec_get_xLPE User _ ?acc] => destruct acc end.
    cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true
      by (vm_compute; reflexivity).
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_rec_cE_S_1 (currentlyEnabled_measure Ext_Zicfilp - 1 - 1) _ s
                 ltac:(vm_compute; reflexivity))).
    cbn beta.
    replace (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) with true
      by (rewrite Hmisa; vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned s Hmenv Hsenv)).
    cbn match beta.
    match goal with |- exec (returnM ?v) s = _ =>
      replace v with false by (vm_compute; reflexivity) end.
    apply exec_returnm.
  Qed.

  Lemma u_result_ok_illegal : u_result_ok (Illegal_Instruction tt).
  Proof. unfold u_result_ok. right; right; left; reflexivity. Qed.

  Lemma u_result_ok_ebreak (v : mword 64) :
    u_result_ok (rv64d_types.Trap
      (User, make_sync_exception (E_Breakpoint Brk_Software) v, v)).
  Proof.
    unfold u_result_ok. right; left.
    exists (E_Breakpoint Brk_Software), v, v. split; [reflexivity | vm_compute; reflexivity].
  Qed.

  (* ---- bit-0 evenness for the C_J / C_BEQZ / C_BNEZ target immediates ----- *)
  (* Their base expansion's immediate is [sign_extend' K (concat_vec imm '0')]  *)
  (* -- the decoder appends a 0, so bit 0 is clear; combined with va-even this  *)
  (* discharges jump_to's target-bit0 assert.                                   *)
  Lemma access0_unsigned_gen (n : Z) (w : mword n) :
    bv_unsigned (access_vec_dec w 0) = bv_unsigned w mod 2.
  Proof.
    unfold access_vec_dec, access_mword_dec.
    unfold MachineWord.MachineWord.slice. cbv [get_word].
    rewrite bv_extract_unsigned. rewrite Z.shiftr_0_r.
    unfold bv_wrap.
    change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
    reflexivity.
  Qed.

  (* The symbolic-width cast in [concat_vec] needs the width concrete, so the
     concat bit-0 fact is proved at the two widths the C-jumps use (11, 8). *)
  Lemma bit0_concat0_11 (x : mword 11) :
    eq_vec (access_vec_dec (concat_vec x ('b"0" : mword 1)) 0) ('b"0") = true.
  Proof.
    apply eq_vec_true_iff. apply bv_eq.
    unfold access_vec_dec, access_mword_dec, concat_vec.
    cbv [to_word get_word autocast]. cbn.
    match goal with |- context[Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b) as [e2 | ne] end;
      [| exfalso; exact (ne eq_refl)].
    rewrite (TypeCasts.cast_Z_refl (H := e2)).
    unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
    unfold MachineWord.MachineWord.slice, MachineWord.MachineWord.concat, Values.to_word.
    rewrite bv_extract_unsigned.
    (erewrite bv_concat_unsigned; [ | cbn; lia ]).
    cbn. rewrite Z.shiftr_0_r. rewrite Z.lor_0_r.
    (rewrite Z.shiftl_mul_pow2; [ | lia ]).
    unfold bv_wrap, bv_modulus.
    change (2 ^ 1) with 2. change (2 ^ Z.of_N 1) with 2.
    rewrite Z_mod_mult. vm_compute; reflexivity.
  Qed.

  Lemma bit0_concat0_8 (x : mword 8) :
    eq_vec (access_vec_dec (concat_vec x ('b"0" : mword 1)) 0) ('b"0") = true.
  Proof.
    apply eq_vec_true_iff. apply bv_eq.
    unfold access_vec_dec, access_mword_dec, concat_vec.
    cbv [to_word get_word autocast]. cbn.
    match goal with |- context[Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b) as [e2 | ne] end;
      [| exfalso; exact (ne eq_refl)].
    rewrite (TypeCasts.cast_Z_refl (H := e2)).
    unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
    unfold MachineWord.MachineWord.slice, MachineWord.MachineWord.concat, Values.to_word.
    rewrite bv_extract_unsigned.
    (erewrite bv_concat_unsigned; [ | cbn; lia ]).
    cbn. rewrite Z.shiftr_0_r. rewrite Z.lor_0_r.
    (rewrite Z.shiftl_mul_pow2; [ | lia ]).
    unfold bv_wrap, bv_modulus.
    change (2 ^ 1) with 2. change (2 ^ Z.of_N 1) with 2.
    rewrite Z_mod_mult. vm_compute; reflexivity.
  Qed.

  Lemma concat0_even_11 (x : mword 11) :
    bv_unsigned (concat_vec x ('b"0" : mword 1)) mod 2 = 0.
  Proof.
    pose proof (bit0_concat0_11 x) as H.
    apply eq_vec_true_iff in H. apply (f_equal bv_unsigned) in H.
    rewrite access0_unsigned_gen in H. rewrite H. vm_compute; reflexivity.
  Qed.

  Lemma concat0_even_8 (x : mword 8) :
    bv_unsigned (concat_vec x ('b"0" : mword 1)) mod 2 = 0.
  Proof.
    pose proof (bit0_concat0_8 x) as H.
    apply eq_vec_true_iff in H. apply (f_equal bv_unsigned) in H.
    rewrite access0_unsigned_gen in H. rewrite H. vm_compute; reflexivity.
  Qed.

  Lemma even_jimm_21 (imm : mword 11) :
    bv_unsigned (sign_extend' 21 (concat_vec imm ('b"0" : mword 1))) mod 2 = 0.
  Proof.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
         MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned.
    (rewrite mod2_wrap; [ | cbn; lia ]). unfold bv_signed.
    (rewrite mod2_swrap; [ | cbn; lia ]). apply concat0_even_11.
  Qed.

  Lemma even_jimm_13 (imm : mword 8) :
    bv_unsigned (sign_extend' 13 (concat_vec imm ('b"0" : mword 1))) mod 2 = 0.
  Proof.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
         MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned.
    (rewrite mod2_wrap; [ | cbn; lia ]). unfold bv_signed.
    (rewrite mod2_swrap; [ | cbn; lia ]). apply concat0_even_8.
  Qed.

  (* One-shot iris read of the three config facts the assembly needs at the
     execute state [set_reg σf nextPC pcv]: decode agreement (so the decode
     totalities fire) + misa = MISA_C + senvcfg = 0.  Pure conclusion, so the
     [mstate_interp] survives for the finish glue. *)
  Lemma s_decode_facts (sigma_f : mstate) (pcv : mword 64) :
    register_lookup cur_privilege sigma_f.(sregs) = User ->
    register_lookup menvcfg sigma_f.(sregs) = MENVCFG_S ->
    mstate_interp (set_reg sigma_f nextPC pcv) -∗ hw_config -∗ user_cfg C -∗
    ⌜ agree_on D_u sigma_f dstateU
      /\ register_lookup misa (set_reg sigma_f nextPC pcv).(sregs) = MISA_C
      /\ register_lookup senvcfg (set_reg sigma_f nextPC pcv).(sregs)
           = (mword_of_int 0 : mword 64) ⌝.
  Proof.
    iIntros (Lcp Lmenv) "(Hreg & _ & _) #Hhw Hcfg".
    iDestruct (user_decode_agree sigma_f pcv Lcp Lmenv with "Hreg Hhw Hcfg") as %Hag.
    iDestruct (hwcfg_misa (set_reg sigma_f nextPC pcv) with "Hreg Hhw") as %Hm.
    iDestruct (ucfg_senvcfg (set_reg sigma_f nextPC pcv) with "Hreg Hcfg") as %Hs.
    iPureIntro. repeat split; assumption.
  Qed.

  (* ===================================================================== *)
  (* JUMP arms (JAL / JALR / BTYPE).  jump_to's target-bit0 premise is        *)
  (* discharged from va-even (post_fetch_cfg's is_aligned_vaddr) + the imm's   *)
  (* bit0 = 0 (decodable_u payload invariant) via the UserBits kit.            *)
  (* ===================================================================== *)
  Lemma arm_JAL (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (imm : mword 21) (ird : mword 5) :
    Lmi_ty sigma sigma_f ->
    register_lookup PC sigma_f.(sregs) = va ->
    register_lookup misa (s0 sigma_f va).(sregs) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    eq_vec (access_vec_dec imm 0) ('b"0") = true ->
    exec (ext_decode w) sigma_f = Some (JAL (imm, Regidx ird), sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lpc Lmisa Hva2 Halign Hdec.
    assert (Halign2 : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                       (sign_extend' 64 imm)) 0) ('b"0") = true).
    { rewrite (s0_PC sigma_f va Lpc).
      apply add_sext_even_64_21.
      - apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ].
      - apply wf_imm_even_21; exact Halign. }
    destruct (exec_execute_JAL_total imm ird (set_reg sigma_f nextPC (add_vec_int va 4))
                (s0_zca _ Lmisa) Halign2) as (v & Hexec).
    iApply (finish_jump_gpr E sigma sigma_f va g (JAL (imm, Regidx ird)) ird v
              (add_vec (register_lookup PC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                       (sign_extend' 64 imm)) w
              Lmi Hdec eq_refl Hexec).
  Qed.

  Lemma arm_JALR (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (imm : mword 12) (i1 ird : mword 5) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege sigma_f.(sregs) = User ->
    register_lookup misa (s0 sigma_f va).(sregs) = MISA_C ->
    register_lookup menvcfg (s0 sigma_f va).(sregs) = MENVCFG_S ->
    register_lookup senvcfg (s0 sigma_f va).(sregs) = (mword_of_int 0 : mword 64) ->
    exec (ext_decode w) sigma_f = Some (JALR (imm, Regidx i1, Regidx ird), sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lcp Lmisa Lmenv Lsenv Hdec.
    assert (Lcp0 : register_lookup cur_privilege (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) = User)
      by (apply s0_cur_privilege; exact Lcp).
    destruct (exec_execute_JALR_total imm i1 ird (set_reg sigma_f nextPC (add_vec_int va 4))
                (s0_zicfilp _ Lcp0 Lmisa Lmenv Lsenv) (s0_zca _ Lmisa)) as (v & tgt & Hexec).
    iApply (finish_jump_gpr E sigma sigma_f va g (JALR (imm, Regidx i1, Regidx ird)) ird v tgt w
              Lmi Hdec eq_refl Hexec).
  Qed.

  Lemma arm_BTYPE (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (imm : mword 13) (i2 i1 : mword 5) (op : bop) :
    Lmi_ty sigma sigma_f ->
    register_lookup PC sigma_f.(sregs) = va ->
    register_lookup misa (s0 sigma_f va).(sregs) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    eq_vec (access_vec_dec imm 0) ('b"0") = true ->
    exec (ext_decode w) sigma_f = Some (BTYPE (imm, Regidx i2, Regidx i1, op), sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lpc Lmisa Hva2 Halign Hdec.
    assert (Halign2 : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                       (sign_extend' 64 imm)) 0) ('b"0") = true).
    { rewrite (s0_PC sigma_f va Lpc).
      apply add_sext_even_64_13.
      - apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ].
      - apply wf_imm_even_13; exact Halign. }
    destruct (exec_execute_BTYPE_total imm i2 i1 op (set_reg sigma_f nextPC (add_vec_int va 4))
                (s0_zca _ Lmisa) Halign2) as (s' & Hexec & [Hs' | Hs']).
    - (* not taken: state unchanged *)
      rewrite Hs' in Hexec.
      iApply (finish_unchanged E sigma sigma_f va g (BTYPE (imm, Regidx i2, Regidx i1, op))
                RETIRE_SUCCESS w Lmi Hdec eq_refl Hexec u_result_ok_retire I).
    - (* taken: nextPC := target *)
      rewrite Hs' in Hexec.
      iApply (finish_setpc E sigma sigma_f va g (BTYPE (imm, Regidx i2, Regidx i1, op))
                (add_vec (register_lookup PC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                         (sign_extend' 64 imm)) w
                Lmi Hdec eq_refl Hexec).
  Qed.

  (* ===================================================================== *)
  (* CSR arms (CSRReg / CSRImm).  The total is Illegal (state-unchanged) OR   *)
  (* a retiring gpr-write read; FS/VS = 00 come from user_mstatus_ok.         *)
  (* ===================================================================== *)
  Lemma arm_CSRReg (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (csr : mword 12) (i1 rd : mword 5) (op : csrop) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege (s0 sigma_f va).(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus (s0 sigma_f va).(sregs)) ->
    register_lookup misa (s0 sigma_f va).(sregs) = MISA_C ->
    register_lookup menvcfg (s0 sigma_f va).(sregs) = MENVCFG_S ->
    exec (ext_decode w) sigma_f = Some (CSRReg (csr, Regidx i1, Regidx rd, op), sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lcp Hmsok Lmisa Lmenv Hdec.
    destruct Hmsok as (_ & _ & _ & Hfs & Hvs & _ & _).
    destruct (exec_execute_CSRReg_total_U csr i1 rd op
                (set_reg sigma_f nextPC (add_vec_int va 4))
                (register_lookup mstatus (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                Lcp eq_refl Hfs Hvs Lmisa Lmenv (s0_ext_S _ Lmisa))
      as (res & s' & Hexec & [ [-> ->] | [-> (v & ->)] ]).
    - iApply (finish_unchanged E sigma sigma_f va g (CSRReg (csr, Regidx i1, Regidx rd, op))
                (Illegal_Instruction tt) w Lmi Hdec eq_refl Hexec u_result_ok_illegal I).
    - iApply (finish_gprwrite E sigma sigma_f va g (CSRReg (csr, Regidx i1, Regidx rd, op))
                rd v w Lmi Hdec eq_refl Hexec).
  Qed.

  Lemma arm_CSRImm (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32) (csr : mword 12) (imm rd : mword 5) (op : csrop) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege (s0 sigma_f va).(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus (s0 sigma_f va).(sregs)) ->
    register_lookup misa (s0 sigma_f va).(sregs) = MISA_C ->
    register_lookup menvcfg (s0 sigma_f va).(sregs) = MENVCFG_S ->
    exec (ext_decode w) sigma_f = Some (CSRImm (csr, imm, Regidx rd, op), sigma_f) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.
  Proof.
    intros Lmi Lcp Hmsok Lmisa Lmenv Hdec.
    destruct Hmsok as (_ & _ & _ & Hfs & Hvs & _ & _).
    destruct (exec_execute_CSRImm_total_U csr imm rd op
                (set_reg sigma_f nextPC (add_vec_int va 4))
                (register_lookup mstatus (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs))
                Lcp eq_refl Hfs Hvs Lmisa Lmenv (s0_ext_S _ Lmisa))
      as (res & s' & Hexec & [ [-> ->] | [-> (v & ->)] ]).
    - iApply (finish_unchanged E sigma sigma_f va g (CSRImm (csr, imm, Regidx rd, op))
                (Illegal_Instruction tt) w Lmi Hdec eq_refl Hexec u_result_ok_illegal I).
    - iApply (finish_gprwrite E sigma sigma_f va g (CSRImm (csr, imm, Regidx rd, op))
                rd v w Lmi Hdec eq_refl Hexec).
  Qed.

  (* ===================================================================== *)
  (* RVC glue + jump arms.                                                   *)
  (* ===================================================================== *)
  (* generic register transport across ANY nextPC write (s0 uses +4, s2 +2). *)
  Lemma reg_nextPC_transp (r : register) (v : type_of_register r) (sigma_f : mstate)
      (x : mword 64) :
    register_beq r nextPC = false ->
    register_lookup r sigma_f.(sregs) = v ->
    register_lookup r (set_reg sigma_f nextPC x).(sregs) = v.
  Proof.
    intros Hne H. unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [exact H | exact Hne].
  Qed.

  (* RVC nextPC-only jump (taken C_BEQZ/C_BNEZ -> BTYPE): s_x = set s2 nextPC tgt. *)
  Lemma finish_rvc_setpc (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr other : instruction) (tgt : mword 64) (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    exec (execute other) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (RETIRE_SUCCESS, set_reg (set_reg sigma_f nextPC (add_vec_int va 2)) nextPC tgt) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Hex2.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    iMod (reg_update _ nextPC (add_vec_int va 2) tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    set (s_x := set_reg (set_reg sigma_f nextPC (add_vec_int va 2)) nextPC tgt).
    iExists instr, RETIRE_SUCCESS, s_x, g, tgt.
    unfold mstate_interp. fold s_x. iFrame "Hreg Hgh Hdev Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split; [exact Hdecc|]. split; [exact Hzca|].
    split; [right; exists other; split; [exact Hex1|exact Hex2]|]. split; [exact u_result_ok_retire|].
    split.
    { unfold s_x, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [| vm_compute; reflexivity].
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity]. }
    unfold s_x, set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

  (* RVC compute expansion (C_* -> base gpr-write), taking the base total in
     [forall s, exists v] form so callers pass the family total verbatim. *)
  Lemma rvc_gpr (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (instr other : instruction) (ird : mword 5) (h : mword 16) :
    Lmi_ty sigma sigma_f ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs other, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    (forall s : mstate, exists v : mword 64,
        exec (execute other) s = Some (RETIRE_SUCCESS, gpr_write_state ird v s)) ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Htot.
    destruct (Htot (set_reg sigma_f nextPC (add_vec_int va 2))) as (v & Hex2).
    iApply (finish_rvc_gprwrite E sigma sigma_f va g instr other ird v h
              Lmi Hdecc Hzca Hex1 Hex2).
  Qed.

  (* C_J -> JAL (rd = x0).  Align: va-even + the appended-0 immediate. *)
  Lemma arm_C_J (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (imm : mword 11) :
    Lmi_ty sigma sigma_f ->
    register_lookup PC sigma_f.(sregs) = va ->
    register_lookup misa (s2 sigma_f va).(sregs) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_J imm, sigma_f) ->
    mstate_interp (s2 sigma_f va) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Lpc Lmisa Hva2 Hzcaf Hdec.
    assert (Halign : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s2 sigma_f va).(sregs))
                       (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0"))))) 0)
              ('b"0") = true).
    { rewrite (reg_nextPC_transp PC va sigma_f (add_vec_int va 2) ltac:(vm_compute; reflexivity) Lpc).
      apply add_sext_even_64_21;
        [ apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ]
        | apply even_jimm_21 ]. }
    destruct (exec_execute_JAL_total (sign_extend' 21 (concat_vec imm ('b"0")))
                (zero_extend' 5 ('b"00")) (s2 sigma_f va) (s0_zca _ Lmisa) Halign) as (v & Hexec).
    iApply (finish_rvc_jump_gpr E sigma sigma_f va g (C_J imm)
              (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)) (zero_extend' 5 ('b"00")) v
              (add_vec (register_lookup PC (s2 sigma_f va).(sregs))
                       (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0"))))) h
              Lmi Hdec Hzcaf (exec_execute_C_J_U imm (s2 sigma_f va)) Hexec).
  Qed.

  (* C_JR -> JALR(0, rs1, x0) ; C_JALR -> JALR(0, rs1, ra).  No align premise
     (JALR clears bit 0); needs Zicfilp-off + Zca. *)
  Lemma arm_C_JR (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (r1 : mword 5) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege (s2 sigma_f va).(sregs) = User ->
    register_lookup misa (s2 sigma_f va).(sregs) = MISA_C ->
    register_lookup menvcfg (s2 sigma_f va).(sregs) = MENVCFG_S ->
    register_lookup senvcfg (s2 sigma_f va).(sregs) = (mword_of_int 0 : mword 64) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_JR (Regidx r1), sigma_f) ->
    mstate_interp (s2 sigma_f va) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Lcp Lmisa Lmenv Lsenv Hzcaf Hdec.
    destruct (exec_execute_JALR_total (zeros' 12) r1 (zero_extend' 5 ('b"00")) (s2 sigma_f va)
                (s0_zicfilp _ Lcp Lmisa Lmenv Lsenv) (s0_zca _ Lmisa)) as (v & tgt & Hexec).
    iApply (finish_rvc_jump_gpr E sigma sigma_f va g (C_JR (Regidx r1))
              (JALR (zeros' 12, Regidx r1, zreg)) (zero_extend' 5 ('b"00")) v tgt h
              Lmi Hdec Hzcaf (exec_execute_C_JR (Regidx r1) (s2 sigma_f va)) Hexec).
  Qed.

  Lemma arm_C_JALR (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (r1 : mword 5) :
    Lmi_ty sigma sigma_f ->
    register_lookup cur_privilege (s2 sigma_f va).(sregs) = User ->
    register_lookup misa (s2 sigma_f va).(sregs) = MISA_C ->
    register_lookup menvcfg (s2 sigma_f va).(sregs) = MENVCFG_S ->
    register_lookup senvcfg (s2 sigma_f va).(sregs) = (mword_of_int 0 : mword 64) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_JALR (Regidx r1), sigma_f) ->
    mstate_interp (s2 sigma_f va) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Lcp Lmisa Lmenv Lsenv Hzcaf Hdec.
    destruct (exec_execute_JALR_total (zeros' 12) r1 (zero_extend' 5 ('b"01")) (s2 sigma_f va)
                (s0_zicfilp _ Lcp Lmisa Lmenv Lsenv) (s0_zca _ Lmisa)) as (v & tgt & Hexec).
    iApply (finish_rvc_jump_gpr E sigma sigma_f va g (C_JALR (Regidx r1))
              (JALR (zeros' 12, Regidx r1, ra)) (zero_extend' 5 ('b"01")) v tgt h
              Lmi Hdec Hzcaf (exec_execute_C_JALR (Regidx r1) (s2 sigma_f va)) Hexec).
  Qed.

  (* C_BEQZ / C_BNEZ -> BTYPE(BEQ/BNE).  Not-taken: state unchanged; taken:
     nextPC := target (align via appended-0 immediate + va-even). *)
  Lemma arm_C_Bcc (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (instr : instruction)
      (imm : mword 8) (rsb : mword 3) (op : bop) :
    Lmi_ty sigma sigma_f ->
    register_lookup PC sigma_f.(sregs) = va ->
    register_lookup misa (s2 sigma_f va).(sregs) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (ext_decode_compressed h) sigma_f = Some (instr, sigma_f) ->
    exec (execute instr) (s2 sigma_f va)
       = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg,
                                 creg2reg_idx (Cregidx rsb), op)), s2 sigma_f va) ->
    mstate_interp (s2 sigma_f va) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.
  Proof.
    intros Lmi Lpc Lmisa Hva2 Hzcaf Hdec Hex1.
    assert (Halign : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s2 sigma_f va).(sregs))
                       (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0"))))) 0)
              ('b"0") = true).
    { rewrite (reg_nextPC_transp PC va sigma_f (add_vec_int va 2) ltac:(vm_compute; reflexivity) Lpc).
      apply add_sext_even_64_13;
        [ apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ]
        | apply even_jimm_13 ]. }
    destruct (exec_execute_BTYPE_total (sign_extend' 13 (concat_vec imm ('b"0")))
                (zero_extend' 5 ('b"00")) (zero_extend' 5 (concat_vec ('b"1") rsb)) op
                (s2 sigma_f va) (s0_zca _ Lmisa) Halign) as (s' & Hexec & [Hs' | Hs']).
    - rewrite Hs' in Hexec.
      iApply (finish_rvc_unchanged E sigma sigma_f va g instr
                (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx (Cregidx rsb), op))
                RETIRE_SUCCESS h Lmi Hdec Hzcaf Hex1 Hexec u_result_ok_retire I).
    - rewrite Hs' in Hexec.
      iApply (finish_rvc_setpc E sigma sigma_f va g instr
                (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx (Cregidx rsb), op))
                (add_vec (register_lookup PC (s2 sigma_f va).(sregs))
                         (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0"))))) h
                Lmi Hdec Hzcaf Hex1 Hexec).
  Qed.

  (* ===================================================================== *)
  (* MEMORY-FAMILY ARM INTERFACES.  These are the per-family entry points a  *)
  (* base_exec_total_u_holds / rvc_exec_total_u_holds proof dispatches to    *)
  (* for the memory families (LOAD/STORE/AMO/LOADRES/STORECON/ZICBOP and     *)
  (* the compressed loads/stores) whose Ok/Err (retire/delegated-trap)       *)
  (* classification a SIBLING file (UserMemClassify.v) builds on the         *)
  (* UserMemAccess vmem/AMO composers.  Declared here as section Variables   *)
  (* so this file stays a self-contained GREEN partial result; the parent    *)
  (* instantiates each with the sibling's proven arm.  The payload of each   *)
  (* is kept as the WHOLE decode tuple [p] (its exact rv64d_types shape) so   *)
  (* the interface is agnostic to how the sibling destructures it.           *)
  (* ===================================================================== *)
  Local Notation MiEq sigma sigma_f :=
    (register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs)).

  Variable arm_LOAD_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (imm : bits 12) (rs1 rd : regidx) (is_unsigned : bool) (width : word_width),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) sigma_f = Some (LOAD (imm, rs1, rd, is_unsigned, width), sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  Variable arm_STORE_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (imm : bits 12) (rs2 rs1 : regidx) (width : word_width),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) sigma_f = Some (STORE (imm, rs2, rs1, width), sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  Variable arm_AMO_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
    exec (ext_decode w) sigma_f = Some (AMO (op, aq, rl, rs2, rs1, width, rd), sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  Variable arm_LOADRES_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (aq rl : bool) (rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) sigma_f = Some (LOADRES (aq, rl, rs1, width, rd), sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  Variable arm_STORECON_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (aq rl : bool) (rs2 rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) sigma_f = Some (STORECON (aq, rl, rs2, rs1, width, rd), sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  Variable arm_ZICBOP_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (w : mword 32)
      (p : cbop_zicbop * regidx * bits 12),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode w) sigma_f = Some (ZICBOP p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
    base_post E sigma sigma_f va w g.

  (* -- Compressed memory families: same uniform contract, but at offset +2  *)
  (* over [ext_decode_compressed], concluding [rvc_post].  The sibling        *)
  (* instantiates each with the compressed load/store arm (which itself       *)
  (* routes through the base LOAD/STORE classification via the ExecuteAs      *)
  (* expansion at the compressed geometry).                                   *)
  Variable arm_C_LW_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LW p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LD_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LD p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LWSP_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LWSP p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LDSP_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LDSP p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SW_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SW p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SD_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SD p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SWSP_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SWSP p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SDSP_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SDSP p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LBU_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LBU p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LH_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LH p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_LHU_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LHU p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SB_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SB p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  Variable arm_C_SH_u : forall (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_SH p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post E sigma sigma_f va h g.

  (* ===================================================================== *)
  (* THE TWO EXECUTE TOTALITIES, ASSEMBLED.                                  *)
  (* Method: intro the post_fetch_cfg premises; derive the config facts at    *)
  (* the execute state; [decode_total_{u,c}_set] + [user_decode_agree] pin     *)
  (* the decoded instruction; [destruct i] + discriminate kills every non-    *)
  (* decodable constructor; each remaining family dispatches to its arm/glue.  *)
  (* Memory families route to the section Variables above.                     *)
  (* ===================================================================== *)
  Local Ltac fin lem := iApply (lem with "Hint Hgpr Hnpc Hupt Hcfg").
  Local Ltac finm lem := iApply (lem with "Hhw Hint Hgpr Hnpc Hupt Hcfg").

  Lemma base_exec_total_u_holds (E : coPset) (sigma : mstate) (va : mword 64)
      (g : regfile) :
    ⊢ base_exec_total_u C pt E sigma va g.
  Proof.
    unfold base_exec_total_u.
    iIntros (w sigma_f) "%Hcfg #Hhw Hint Hgpr Hnpc Hupt Hcfg".
    pose proof Hcfg as Hcfg_full.
    destruct Hcfg as (Lpc & Lcp & Hmsok & Lmenv & Hva2 & Lmi).
    iDestruct (s_decode_facts sigma_f (add_vec_int va 4) Lcp Lmenv with "Hint Hhw Hcfg")
      as %(Hag & Lmisa0 & Lsenv0).
    assert (Lcp0 : register_lookup cur_privilege (s0 sigma_f va).(sregs) = User)
      by (apply s0_cur_privilege; exact Lcp).
    assert (Lpc0 : register_lookup PC (s0 sigma_f va).(sregs) = va)
      by (apply s0_PC; exact Lpc).
    assert (Lmenv0 : register_lookup menvcfg (s0 sigma_f va).(sregs) = MENVCFG_S)
      by (apply (s0_reg menvcfg MENVCFG_S sigma_f va); [ vm_compute; reflexivity | exact Lmenv ]).
    assert (Hmsok0 : user_mstatus_ok (register_lookup mstatus (s0 sigma_f va).(sregs))).
    { rewrite (s0_reg mstatus (register_lookup mstatus sigma_f.(sregs)) sigma_f va
                 ltac:(vm_compute; reflexivity) eq_refl). exact Hmsok. }
    destruct (decode_total_u_set w) as (i & Hdi & Hdf).
    specialize (Hdf sigma_f Hag).
    destruct i; try (cbn in Hdi; discriminate).
    all: lazymatch type of Hdf with
    (* --- retiring compute families (arm_gprwrite + the family total) --- *)
    | _ = Some (ITYPE ?p, _) =>
        destruct p as [[[imm i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ITYPE (imm, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_ITYPE_total imm i1 ird op))
    | _ = Some (RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_RTYPE_total i2 i1 ird op))
    | _ = Some (RTYPEW ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_RTYPEW_total i2 i1 ird op))
    | _ = Some (SHIFTIOP ?p, _) =>
        destruct p as [[[shamt i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (SHIFTIOP (shamt, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_SHIFTIOP_total shamt i1 ird op))
    | _ = Some (SHIFTIWOP ?p, _) =>
        destruct p as [[[shamt i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (SHIFTIWOP (shamt, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_SHIFTIWOP_total shamt i1 ird op))
    | _ = Some (ADDIW ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ADDIW (imm, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_ADDIW_total imm i1 ird))
    | _ = Some (MUL ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (MUL (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_MUL_total i2 i1 ird op))
    | _ = Some (MULW ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (MULW (Regidx i2, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_MULW_total i2 i1 ird))
    | _ = Some (DIV ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (DIV (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Lmi Hdf eq_refl (exec_execute_DIV_total i2 i1 ird u))
    | _ = Some (DIVW ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (DIVW (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Lmi Hdf eq_refl (exec_execute_DIVW_total i2 i1 ird u))
    | _ = Some (REM ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (REM (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Lmi Hdf eq_refl (exec_execute_REM_total i2 i1 ird u))
    | _ = Some (REMW ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (REMW (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Lmi Hdf eq_refl (exec_execute_REMW_total i2 i1 ird u))
    | _ = Some (UTYPE ?p, _) =>
        destruct p as [[imm ird] op]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (UTYPE (imm, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_UTYPE_total imm ird op))
    | _ = Some (ZBB_RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ZBB_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_ZBB_RTYPE_total i2 i1 ird op))
    | _ = Some (ZBB_RTYPEW ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ZBB_RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_ZBB_RTYPEW_total i2 i1 ird op))
    | _ = Some (CLMUL ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (CLMUL (Regidx i2, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_CLMUL_total i2 i1 ird))
    | _ = Some (CLMULH ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (CLMULH (Regidx i2, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_CLMULH_total i2 i1 ird))
    | _ = Some (CLMULR ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (CLMULR (Regidx i2, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_CLMULR_total i2 i1 ird))
    | _ = Some (REV8 ?p, _) =>
        destruct p as [i1 ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (REV8 (Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_REV8_total i1 ird))
    | _ = Some (RORI ?p, _) =>
        destruct p as [[shamt i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (RORI (shamt, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_RORI_total shamt i1 ird))
    | _ = Some (RORIW ?p, _) =>
        destruct p as [[shamt i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (RORIW (shamt, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_RORIW_total shamt i1 ird))
    | _ = Some (ZIMOP_MOP_R ?p, _) =>
        destruct p as [[mop i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ZIMOP_MOP_R (mop, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_ZIMOP_MOP_R_total mop i1 ird))
    | _ = Some (ZIMOP_MOP_RR ?p, _) =>
        destruct p as [[[mop i2] i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ZIMOP_MOP_RR (mop, Regidx i2, Regidx i1, Regidx ird)) ird
              Lmi Hdf eq_refl (exec_execute_ZIMOP_MOP_RR_total mop i2 i1 ird))
    | _ = Some (ZICOND_RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite E sigma sigma_f va g w (ZICOND_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Lmi Hdf eq_refl (exec_execute_ZICOND_RTYPE_total i2 i1 ird op))
    (* --- control flow (jump arms) --- *)
    | _ = Some (JAL ?p, _) =>
        destruct p as [imm ird]; destruct ird as [ird]; cbn in Hdi;
        fin (arm_JAL E sigma sigma_f va g w imm ird Lmi Lpc Lmisa0 Hva2 Hdi Hdf)
    | _ = Some (JALR ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_JALR E sigma sigma_f va g w imm i1 ird Lmi Lcp Lmisa0 Lmenv0 Lsenv0 Hdf)
    | _ = Some (BTYPE ?p, _) =>
        destruct p as [[[imm i2] i1] op]; destruct i2 as [i2]; destruct i1 as [i1]; cbn in Hdi;
        fin (arm_BTYPE E sigma sigma_f va g w imm i2 i1 op Lmi Lpc Lmisa0 Hva2 Hdi Hdf)
    (* --- CSR arms --- *)
    | _ = Some (CSRReg ?p, _) =>
        destruct p as [[[csr i1] rd] op]; destruct i1 as [i1]; destruct rd as [rd];
        fin (arm_CSRReg E sigma sigma_f va g w csr i1 rd op Lmi Lcp0 Hmsok0 Lmisa0 Lmenv0 Hdf)
    | _ = Some (CSRImm ?p, _) =>
        destruct p as [[[csr imm] rd] op]; destruct rd as [rd];
        fin (arm_CSRImm E sigma sigma_f va g w csr imm rd op Lmi Lcp0 Hmsok0 Lmisa0 Lmenv0 Hdf)
    (* --- illegal / trap / wait / fence / nop (finish glue) --- *)
    | _ = Some (ILLEGAL ?wi, _) =>
        fin (arm_ILLEGAL E sigma sigma_f va g w wi Lmi Hdf)
    | _ = Some (ECALL ?u, _) =>
        destruct u; fin (arm_ECALL E sigma sigma_f va g w Lmi Lcp Lpc Hdf)
    | _ = Some (WRS ?op, _) =>
        fin (arm_WRS E sigma sigma_f va g w op Lmi Hdf)
    | _ = Some (EBREAK ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (EBREAK tt)
              (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va)) w
              Lmi Hdf eq_refl (exec_execute_EBREAK_U (s0 sigma_f va) va Lcp0 Lpc0)
              (u_result_ok_ebreak va) I)
    | _ = Some (MRET ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (MRET tt) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_MRET_U (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SRET ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (SRET tt) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_SRET_U (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (WFI ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (WFI tt) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_WFI_U (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_VMA ?p, _) =>
        destruct p as [i1 i2]; destruct i1 as [i1]; destruct i2 as [i2];
        fin (finish_unchanged E sigma sigma_f va g (SFENCE_VMA (Regidx i1, Regidx i2))
              (Illegal_Instruction tt) w Lmi Hdf eq_refl
              (exec_execute_SFENCE_VMA_U i1 i2 (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_W_INVAL ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (SFENCE_W_INVAL tt) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_SFENCE_W_INVAL_U (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_INVAL_IR ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (SFENCE_INVAL_IR tt) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_SFENCE_INVAL_IR_U (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SINVAL_VMA ?p, _) =>
        destruct p as [rs1 rs2]; destruct rs1 as [i1]; destruct rs2 as [i2];
        fin (finish_unchanged_redirect E sigma sigma_f va g (SINVAL_VMA (Regidx i1, Regidx i2))
              (SFENCE_VMA (Regidx i1, Regidx i2)) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_SINVAL_VMA (Regidx i1) (Regidx i2) (s0 sigma_f va))
              (exec_execute_SFENCE_VMA_U i1 i2 (s0 sigma_f va) Lcp0) u_result_ok_illegal I)
    | _ = Some (ZICBOM ?p, _) =>
        destruct p as [op i1]; destruct i1 as [i1];
        fin (finish_unchanged E sigma sigma_f va g (ZICBOM (op, Regidx i1)) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl
              (exec_execute_ZICBOM_U op i1 (s0 sigma_f va) Lcp0 Lmenv0 Lsenv0 (s0_ext_S _ Lmisa0))
              u_result_ok_illegal I)
    | _ = Some (ZICBOZ ?r, _) =>
        destruct r as [i1];
        fin (finish_unchanged E sigma sigma_f va g (ZICBOZ (Regidx i1)) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl (exec_execute_ZICBOZ_U i1 (s0 sigma_f va) Lcp0 Lmenv0 Lsenv0)
              u_result_ok_illegal I)
    | _ = Some (SSAMOSWAP ?p, _) =>
        destruct p as [[[[[aq rl] i2] i1] width] ird];
        destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged E sigma sigma_f va g
              (SSAMOSWAP (aq, rl, Regidx i2, Regidx i1, width, Regidx ird)) (Illegal_Instruction tt) w
              Lmi Hdf eq_refl
              (exec_execute_SSAMOSWAP_U aq rl i2 i1 ird width (s0 sigma_f va)
                 Lcp0 Lmenv0 Lsenv0 (s0_ext_S _ Lmisa0)) u_result_ok_illegal I)
    | _ = Some (NTL ?nt, _) =>
        fin (finish_unchanged E sigma sigma_f va g (NTL nt) RETIRE_SUCCESS w
              Lmi Hdf eq_refl (exec_execute_NTL nt (s0 sigma_f va)) u_result_ok_retire I)
    | _ = Some (PAUSE ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (PAUSE tt) RETIRE_SUCCESS w
              Lmi Hdf eq_refl (exec_execute_PAUSE (s0 sigma_f va)) u_result_ok_retire I)
    | _ = Some (FENCE_TSO ?u, _) =>
        destruct u;
        fin (finish_unchanged E sigma sigma_f va g (FENCE_TSO tt) RETIRE_SUCCESS w
              Lmi Hdf eq_refl (exec_execute_FENCE_TSO_U (s0 sigma_f va)) u_result_ok_retire I)
    | _ = Some (FENCEI ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged E sigma sigma_f va g (FENCEI (imm, Regidx i1, Regidx ird)) RETIRE_SUCCESS w
              Lmi Hdf eq_refl (exec_execute_FENCEI_U imm i1 ird (s0 sigma_f va)) u_result_ok_retire I)
    | _ = Some (FENCE ?p, _) =>
        destruct p as [[[[fm pred] succ] i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged E sigma sigma_f va g (FENCE (fm, pred, succ, Regidx i1, Regidx ird))
              RETIRE_SUCCESS w Lmi Hdf eq_refl
              (exec_execute_FENCE_total_U fm pred succ i1 ird (s0 sigma_f va) Lcp0) u_result_ok_retire I)
    (* --- memory families: the section Variables (width threaded from Hdi) --- *)
    | _ = Some (LOAD ?p, _) =>
        destruct p as [[[[imm rs1] rd] us] width]; cbn [decodable_u] in Hdi;
        finm (arm_LOAD_u E sigma sigma_f va g w imm rs1 rd us width
                Hcfg_full (width_ok1248_cases width Hdi) Hdf)
    | _ = Some (STORE ?p, _) =>
        destruct p as [[[imm rs2] rs1] width]; cbn [decodable_u] in Hdi;
        finm (arm_STORE_u E sigma sigma_f va g w imm rs2 rs1 width
                Hcfg_full (width_ok1248_cases width Hdi) Hdf)
    | _ = Some (AMO ?p, _) =>
        destruct p as [[[[[[op aq] rl] rs2] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_AMO_u E sigma sigma_f va g w op aq rl rs2 rs1 rd width
                Hcfg_full (awidth_ok_cases width Hdi) Hdf)
    | _ = Some (LOADRES ?p, _) =>
        destruct p as [[[[aq rl] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_LOADRES_u E sigma sigma_f va g w aq rl rs1 width rd
                Hcfg_full (lrsc_width_valid_cases width Hdi) Hdf)
    | _ = Some (STORECON ?p, _) =>
        destruct p as [[[[[aq rl] rs2] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_STORECON_u E sigma sigma_f va g w aq rl rs2 rs1 width rd
                Hcfg_full (lrsc_width_valid_cases width Hdi) Hdf)
    | _ = Some (ZICBOP ?p, _) =>
        finm (arm_ZICBOP_u E sigma sigma_f va g w p Hcfg_full Hdf)
    end.
  Qed.

  Lemma rvc_exec_total_u_holds (E : coPset) (sigma : mstate) (va : mword 64)
      (g : regfile) :
    ⊢ rvc_exec_total_u C pt E sigma va g.
  Proof.
    unfold rvc_exec_total_u.
    iIntros (h sigma_f) "%Hcfg #Hhw Hint Hgpr Hnpc Hupt Hcfg".
    pose proof Hcfg as Hcfg_full.
    destruct Hcfg as (Lpc & Lcp & Hmsok & Lmenv & Hva2 & Lmi).
    iDestruct (s_decode_facts sigma_f (add_vec_int va 2) Lcp Lmenv with "Hint Hhw Hcfg")
      as %(Hag & Lmisa0 & Lsenv0).
    assert (Lcp0 : register_lookup cur_privilege (s2 sigma_f va).(sregs) = User)
      by (apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lcp ]).
    assert (Lpc0 : register_lookup PC (s2 sigma_f va).(sregs) = va)
      by (apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lpc ]).
    assert (Lmenv0 : register_lookup menvcfg (s2 sigma_f va).(sregs) = MENVCFG_S)
      by (apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lmenv ]).
    assert (Lmisaf : register_lookup misa sigma_f.(sregs) = MISA_C).
    { transitivity (register_lookup misa (s2 sigma_f va).(sregs)); [ | exact Lmisa0 ].
      symmetry. apply reg_nextPC_transp; [ vm_compute; reflexivity | reflexivity ]. }
    assert (Hzcaf : exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f))
      by (apply s0_zca; exact Lmisaf).
    destruct (decode_total_c_set h) as (i & Hdi & Hdf).
    specialize (Hdf sigma_f Hag).
    destruct i; try (cbn in Hdi; discriminate).
    all: lazymatch type of Hdf with
    (* --- RVC DIRECT (no ExecuteAs) --- *)
    | _ = Some (C_NOP ?g6, _) =>
        fin (finish_rvc_direct E sigma sigma_f va g (C_NOP g6) RETIRE_SUCCESS h
              Lmi Hdf Hzcaf (exec_execute_C_NOP g6 (s2 sigma_f va)) u_result_ok_retire I)
    | _ = Some (C_NTL ?nt, _) =>
        fin (finish_rvc_direct E sigma sigma_f va g (C_NTL nt) RETIRE_SUCCESS h
              Lmi Hdf Hzcaf (exec_execute_C_NTL nt (s2 sigma_f va)) u_result_ok_retire I)
    | _ = Some (ZCMOP ?m3, _) =>
        fin (finish_rvc_direct E sigma sigma_f va g (ZCMOP m3) RETIRE_SUCCESS h
              Lmi Hdf Hzcaf (exec_execute_ZCMOP m3 (s2 sigma_f va)) u_result_ok_retire I)
    | _ = Some (C_ILLEGAL ?w16, _) =>
        fin (finish_rvc_direct E sigma sigma_f va g (C_ILLEGAL w16) (Illegal_Instruction tt) h
              Lmi Hdf Hzcaf (exec_execute_C_ILLEGAL w16 (s2 sigma_f va)) u_result_ok_illegal I)
    | _ = Some (C_NOT ?c, _) =>
        let H := fresh in destruct (exec_execute_C_NOT_total c (s2 sigma_f va)) as (? & ? & ? & H);
        fin (finish_rvc_direct_gprwrite E sigma sigma_f va g (C_NOT c) _ _ h Lmi Hdf Hzcaf H)
    | _ = Some (C_ZEXT_B ?c, _) =>
        let H := fresh in destruct (exec_execute_C_ZEXT_B_total c (s2 sigma_f va)) as (? & ? & ? & H);
        fin (finish_rvc_direct_gprwrite E sigma sigma_f va g (C_ZEXT_B c) _ _ h Lmi Hdf Hzcaf H)
    (* --- RVC compute (ExecuteAs -> base gpr-write) --- *)
    | _ = Some (C_LI ?p, _) =>
        destruct p as [imm rd]; destruct rd as [rd];
        fin (rvc_gpr E sigma sigma_f va g (C_LI (imm, Regidx rd))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_LI imm (Regidx rd) (s2 sigma_f va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ADDI))
    | _ = Some (C_LUI ?p, _) =>
        destruct p as [imm rd]; destruct rd as [rd];
        fin (rvc_gpr E sigma sigma_f va g (C_LUI (imm, Regidx rd))
              (UTYPE (sign_extend' 20 imm, Regidx rd, LUI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_LUI imm (Regidx rd) (s2 sigma_f va))
              (exec_execute_UTYPE_total (sign_extend' 20 imm) _ LUI))
    | _ = Some (C_MV ?p, _) =>
        destruct p as [rd rs2]; destruct rd as [rd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_MV (Regidx rd, Regidx r2))
              (RTYPE (Regidx r2, zreg, Regidx rd, ADD)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_MV (Regidx rd) (Regidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ ADD))
    | _ = Some (C_ADD ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_ADD (Regidx rsd, Regidx r2))
              (RTYPE (Regidx r2, Regidx rsd, Regidx rsd, ADD)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_ADD (Regidx rsd) (Regidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ ADD))
    | _ = Some (C_ADDI ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr E sigma sigma_f va g (C_ADDI (imm, Regidx rsd))
              (ITYPE (sign_extend' 12 imm, Regidx rsd, Regidx rsd, ADDI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_ADDI imm (Regidx rsd) (s2 sigma_f va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ADDI))
    | _ = Some (C_ADDI16SP ?imm, _) =>
        fin (rvc_gpr E sigma sigma_f va g (C_ADDI16SP imm)
              (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_ADDI16SP imm (s2 sigma_f va))
              (exec_execute_ITYPE_total (caddi16sp_imm imm) _ _ ADDI))
    | _ = Some (C_ADDI4SPN ?p, _) =>
        destruct p as [rdc nzimm]; destruct rdc as [rdc];
        fin (rvc_gpr E sigma sigma_f va g (C_ADDI4SPN (Cregidx rdc, nzimm))
              (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx (Cregidx rdc), ADDI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_ADDI4SPN (Cregidx rdc) nzimm (s2 sigma_f va))
              (exec_execute_ITYPE_total (caddi4spn_imm nzimm) _ _ ADDI))
    | _ = Some (C_SLLI ?p, _) =>
        destruct p as [shamt rsd]; destruct rsd as [rsd];
        fin (rvc_gpr E sigma sigma_f va g (C_SLLI (shamt, Regidx rsd))
              (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_SLLI shamt (Regidx rsd) (s2 sigma_f va))
              (exec_execute_SHIFTIOP_total shamt _ _ SLLI))
    | _ = Some (C_SRLI ?p, _) =>
        destruct p as [shamt crsd]; destruct crsd as [crsd];
        fin (rvc_gpr E sigma sigma_f va g (C_SRLI (shamt, Cregidx crsd))
              (SHIFTIOP (shamt, creg2reg_idx (Cregidx crsd), creg2reg_idx (Cregidx crsd), SRLI)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_SRLI shamt (Cregidx crsd) (s2 sigma_f va))
              (exec_execute_SHIFTIOP_total shamt _ _ SRLI))
    | _ = Some (C_SRAI ?p, _) =>
        destruct p as [shamt rsd]; destruct rsd as [rsd];
        fin (rvc_gpr E sigma sigma_f va g (C_SRAI (shamt, Cregidx rsd))
              (SHIFTIOP (shamt, creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SRAI)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_SRAI shamt (Cregidx rsd) (s2 sigma_f va))
              (exec_execute_SHIFTIOP_total shamt _ _ SRAI))
    | _ = Some (C_ANDI ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr E sigma sigma_f va g (C_ANDI (imm, Cregidx rsd))
              (ITYPE (sign_extend' 12 imm, creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), ANDI)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_ANDI imm (Cregidx rsd) (s2 sigma_f va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ANDI))
    | _ = Some (C_AND ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_AND (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), AND)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_AND (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ AND))
    | _ = Some (C_OR ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_OR (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), OR)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_OR (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ OR))
    | _ = Some (C_XOR ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_XOR (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), XOR)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_XOR (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ XOR))
    | _ = Some (C_SUB ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_SUB (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SUB)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_SUB (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPE_total _ _ _ SUB))
    | _ = Some (C_ADDW ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_ADDW (Cregidx rsd, Cregidx r2))
              (RTYPEW (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), ADDW)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_ADDW (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPEW_total _ _ _ ADDW))
    | _ = Some (C_SUBW ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr E sigma sigma_f va g (C_SUBW (Cregidx rsd, Cregidx r2))
              (RTYPEW (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SUBW)) _ h
              Lmi Hdf Hzcaf (exec_execute_C_SUBW (Cregidx rsd) (Cregidx r2) (s2 sigma_f va))
              (exec_execute_RTYPEW_total _ _ _ SUBW))
    | _ = Some (C_ADDIW ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr E sigma sigma_f va g (C_ADDIW (imm, Regidx rsd))
              (ADDIW (sign_extend' 12 imm, Regidx rsd, Regidx rsd)) _ h Lmi Hdf Hzcaf
              (exec_execute_C_ADDIW imm (Regidx rsd) (s2 sigma_f va))
              (exec_execute_ADDIW_total (sign_extend' 12 imm) _ _))
    | _ = Some (C_MUL ?p, _) =>
        destruct p as [rsdc rsc2]; destruct rsdc as [rsdc]; destruct rsc2 as [rsc2];
        let Hm := fresh in destruct (exec_execute_C_MUL (Cregidx rsdc) (Cregidx rsc2) (s2 sigma_f va)) as (mop & Hm);
        fin (rvc_gpr E sigma sigma_f va g (C_MUL (Cregidx rsdc, Cregidx rsc2))
              (MUL (creg2reg_idx (Cregidx rsc2), creg2reg_idx (Cregidx rsdc), creg2reg_idx (Cregidx rsdc), mop)) _ h
              Lmi Hdf Hzcaf Hm (exec_execute_MUL_total _ _ _ mop))
    (* --- RVC EBREAK (ExecuteAs -> trap) --- *)
    | _ = Some (C_EBREAK ?u, _) =>
        destruct u;
        fin (finish_rvc_unchanged E sigma sigma_f va g (C_EBREAK tt) (EBREAK tt)
              (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va)) h
              Lmi Hdf Hzcaf (exec_execute_C_EBREAK_U (s2 sigma_f va))
              (exec_execute_EBREAK_U (s2 sigma_f va) va Lcp0 Lpc0) (u_result_ok_ebreak va) I)
    (* --- RVC control flow (jump arms) --- *)
    | _ = Some (C_J ?imm, _) =>
        fin (arm_C_J E sigma sigma_f va g h imm Lmi Lpc Lmisa0 Hva2 Hzcaf Hdf)
    | _ = Some (C_JR ?r, _) =>
        destruct r as [r1];
        fin (arm_C_JR E sigma sigma_f va g h r1 Lmi Lcp0 Lmisa0 Lmenv0 Lsenv0 Hzcaf Hdf)
    | _ = Some (C_JALR ?r, _) =>
        destruct r as [r1];
        fin (arm_C_JALR E sigma sigma_f va g h r1 Lmi Lcp0 Lmisa0 Lmenv0 Lsenv0 Hzcaf Hdf)
    | _ = Some (C_BEQZ ?p, _) =>
        destruct p as [imm rs]; destruct rs as [rsb];
        fin (arm_C_Bcc E sigma sigma_f va g h (C_BEQZ (imm, Cregidx rsb)) imm rsb BEQ
              Lmi Lpc Lmisa0 Hva2 Hzcaf Hdf (exec_execute_C_BEQZ_U imm (Cregidx rsb) (s2 sigma_f va)))
    | _ = Some (C_BNEZ ?p, _) =>
        destruct p as [imm rs]; destruct rs as [rsb];
        fin (arm_C_Bcc E sigma sigma_f va g h (C_BNEZ (imm, Cregidx rsb)) imm rsb BNE
              Lmi Lpc Lmisa0 Hva2 Hzcaf Hdf (exec_execute_C_BNEZ imm (Cregidx rsb) (s2 sigma_f va)))
    (* --- compressed memory: the section Variables --- *)
    | _ = Some (C_LW ?p, _) => finm (arm_C_LW_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LD ?p, _) => finm (arm_C_LD_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LWSP ?p, _) => finm (arm_C_LWSP_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LDSP ?p, _) => finm (arm_C_LDSP_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SW ?p, _) => finm (arm_C_SW_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SD ?p, _) => finm (arm_C_SD_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SWSP ?p, _) => finm (arm_C_SWSP_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SDSP ?p, _) => finm (arm_C_SDSP_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LBU ?p, _) => finm (arm_C_LBU_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LH ?p, _) => finm (arm_C_LH_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_LHU ?p, _) => finm (arm_C_LHU_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SB ?p, _) => finm (arm_C_SB_u E sigma sigma_f va g h p Hcfg_full Hdf)
    | _ = Some (C_SH ?p, _) => finm (arm_C_SH_u E sigma sigma_f va g h p Hcfg_full Hdf)
    end.
  Qed.

End UserTotalU.

(* ===================================================================== *)
(*                          F R O N T I E R                                *)
(* ===================================================================== *)
(*                                                                         *)
(* DONE (all Qed, no admits; assumptions = the 5 baseline platform axioms   *)
(* only).  The two EXECUTE TOTALITIES are ASSEMBLED and CLOSED:             *)
(*   base_exec_total_u_holds : forall (arm_LOAD_u..arm_ZICBOP_u) E s va g,  *)
(*        |- base_exec_total_u C pt E s va g                                *)
(*   rvc_exec_total_u_holds  : forall (arm_C_LW_u..arm_C_SH_u) E s va g,    *)
(*        |- rvc_exec_total_u  C pt E s va g                                *)
(* The parent instantiates the memory Variables with UserMemClassify.v's    *)
(* proven arms, discharging wp_user_exec_full's Hbase/Hrvc.                 *)
(*                                                                         *)
(* Non-memory families closed IN this file:                                *)
(*  - retiring compute (ITYPE/RTYPE/.../ZICOND, 24 base) via arm_gprwrite   *)
(*    + each family's exec_execute_<FAM>_total.                             *)
(*  - illegal-at-U (MRET/SRET/WFI/SFENCE*/ZICBOM/ZICBOZ/SSAMOSWAP), traps   *)
(*    (ECALL/EBREAK), enter-wait (WRS), nop/fence (PAUSE/NTL/FENCE),        *)
(*    SINVAL redirect -- via finish_unchanged / _redirect.                  *)
(*  - JUMPS (G1, now solved): JAL/JALR/BTYPE (base) + C_J/C_JR/C_JALR/      *)
(*    C_BEQZ/C_BNEZ (rvc).  post_fetch_cfg now carries                      *)
(*    is_aligned_vaddr va 2; aligned_even + add_sext_even_64_{21,13} +      *)
(*    even_jimm_{21,13} (appended-0 immediate) discharge jump_to's target-  *)
(*    bit0 assert.  s0_zicfilp gives Zicfilp=OFF at User for JALR.          *)
(*  - CSR (G2, now solved): CSRReg/CSRImm.  FS/VS=00 come from the extended *)
(*    user_mstatus_ok inside post_fetch_cfg; exec_execute_CSR*_total_U's    *)
(*    Illegal-or-retiring-read disjunction closes via finish_unchanged /    *)
(*    finish_gprwrite.                                                      *)
(*  - RVC-direct (G3, now solved): rvc_exec_total_u's body is a DISJUNCTION *)
(*    (direct v ExecuteAs); C_NOP/C_NTL/ZCMOP/C_ILLEGAL (finish_rvc_direct) *)
(*    and C_NOT/C_ZEXT_B (finish_rvc_direct_gprwrite) take the direct arm.  *)
(*  - RVC-compute (C_LI/C_MV/C_ADD/...): ExecuteAs to base, via rvc_gpr +   *)
(*    the base total; C_EBREAK->EBREAK trap via finish_rvc_unchanged.       *)
(*                                                                         *)
(* MEMORY families are the section Variables (uniform contract):            *)
(*  base  (-> base_post, offset +4, ext_decode):                           *)
(*    arm_LOAD_u, arm_STORE_u, arm_AMO_u, arm_LOADRES_u, arm_STORECON_u,    *)
(*    arm_ZICBOP_u.                                                         *)
(*  compressed (-> rvc_post, offset +2, ext_decode_compressed):            *)
(*    arm_C_LW_u, arm_C_LD_u, arm_C_LWSP_u, arm_C_LDSP_u, arm_C_SW_u,       *)
(*    arm_C_SD_u, arm_C_SWSP_u, arm_C_SDSP_u, arm_C_LBU_u, arm_C_LH_u,      *)
(*    arm_C_LHU_u, arm_C_SB_u, arm_C_SH_u.                                  *)
(*  The sibling UserMemClassify.v must match these VERBATIM types (whole    *)
(*  rv64d_types payload tuple; MiEq + cur_privilege=User + PC=va +          *)
(*  menvcfg=MENVCFG_S + the decode fact; hw_config then the frame).         *)
(* ===================================================================== *)
