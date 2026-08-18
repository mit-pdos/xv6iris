(* ===================================================================== *)
(* UserTotalU.v -- the two U-mode EXECUTE TOTALITIES, PURE.                *)
(*                                                                         *)
(*   base_exec_total_u_holds / rvc_exec_total_u_holds  (UserClassifyAsm.v) *)
(*                                                                         *)
(* This file builds and CLOSES both totalities (Qed, no admits).  Since the *)
(* port it is Iris-FREE: [base_exec_total_u] is a [Prop], so there is no    *)
(* [mstate_interp] to move, no [gpr_file] to thread and no fancy update --  *)
(* what used to be a proofmode script per result shape is now a [split_and] *)
(* over four pure conjuncts.  Three things replace the resources:           *)
(*                                                                         *)
(*   * the CERTIFICATE.  Every execute fact now travels with its [goodmb]   *)
(*     twin (P5's catalogue, [UserExecFacts]/[UserCsr]).  The twins are     *)
(*     stated at [mm := empty] and generic in [(Dr, Dw)]; [u_gm1] below     *)
(*     lifts one to [Du_r]/[Du_w] at the hart's owned map in one            *)
(*     [goodmb_map_mono] and then picks the family out of a [first].  No    *)
(*     call site names a twin -- which is what keeps the two dispatch       *)
(*     tables' clause structure untouched.                                  *)
(*   * the POST-STATE.  [u_post_reg] is the register-only landing fact --   *)
(*     [reg_agree_on u_Dfix] off the ticked file, the tlb unmoved, the      *)
(*     bytes unmoved -- with one constructor per state SHAPE (unchanged /   *)
(*     one gpr / nextPC / nextPC+gpr).  Every [finish_*] is one of those    *)
(*     four.                                                               *)
(*   * the AMBIENT PINS.  What the arms used to read off [hw_config] /      *)
(*     [user_cfg] / [user_pt_inv] with [reg_valid_dq] arrives as            *)
(*     [UserClassifyAsm.u_exec_pins].                                       *)
(*                                                                         *)
(* The memory families remain section Variables the parent instantiates     *)
(* with UserMemClassify.v's proven arms; their contract is now pure too and *)
(* is the thing P4 codes against.                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile UserBits.
Require Import HartLift HartSpan HartGoodb HartMemRun PtBytes.
Require Import PtreeType PtTree SmodePte UptTree.
Require Import UserFrame UserBytes.
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


(* ===================================================================== *)
(* The thirteen [ExecuteAs] expansions whose [exec] fact lives in         *)
(* [WpMmodeLeafBase] (an M-mode file) and whose CERTIFICATE nobody had    *)
(* yet.  Each expansion is a bare [returnM], so each twin is one          *)
(* [goodmb_returnm].  TEMPORARY: their real home is beside the exec fact; *)
(* fold them back at the milestone rather than growing this file.         *)
(* ===================================================================== *)

Lemma goodmb_execute_C_LI (Dr Dw : register -> bool) (imm : mword 6) (rd : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_LI (imm, rd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_LI; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_LUI (Dr Dw : register -> bool) (imm : mword 6) (rd : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_LUI (imm, rd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_LUI; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_SRLI (Dr Dw : register -> bool) (shamt : mword 6) (crsd : cregidx) (s : mstate) :
  goodmb Dr Dw (execute (C_SRLI (shamt, crsd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_SRLI; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_SLLI (Dr Dw : register -> bool) (shamt : mword 6) (rsd : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_SLLI (shamt, rsd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_SLLI; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_MV (Dr Dw : register -> bool) (rd rs2 : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_MV (rd, rs2))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_MV; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_ADD (Dr Dw : register -> bool) (rsd rs2 : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_ADD (rsd, rs2))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_ADD; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_ADDI (Dr Dw : register -> bool) (imm : mword 6) (rsd : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_ADDI (imm, rsd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_ADDI; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_ADDI16SP (Dr Dw : register -> bool) (imm : mword 6) (s : mstate) :
  goodmb Dr Dw (execute (C_ADDI16SP imm)) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_ADDI16SP, caddi16sp_imm; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_ADDI4SPN (Dr Dw : register -> bool) (rdc : cregidx) (nzimm : mword 8) (s : mstate) :
  goodmb Dr Dw (execute (C_ADDI4SPN (rdc, nzimm))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_ADDI4SPN, caddi4spn_imm; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_OR (Dr Dw : register -> bool) (rsd rs2 : cregidx) (s : mstate) :
  goodmb Dr Dw (execute (C_OR (rsd, rs2))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_OR; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_AND (Dr Dw : register -> bool) (rsd rs2 : cregidx) (s : mstate) :
  goodmb Dr Dw (execute (C_AND (rsd, rs2))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_AND; cbn zeta; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_ADDIW (Dr Dw : register -> bool) (imm : mword 6) (rsd : regidx) (s : mstate) :
  goodmb Dr Dw (execute (C_ADDIW (imm, rsd))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_ADDIW; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_BNEZ (Dr Dw : register -> bool) (imm : mword 8) (rs : cregidx) (s : mstate) :
  goodmb Dr Dw (execute (C_BNEZ (imm, rs))) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_BNEZ; apply goodmb_returnm. Qed.

(* the three expansions this file proves itself (section (C) at the top) *)
Lemma goodmb_execute_ILLEGAL_U (Dr Dw : register -> bool) (w : mword 32)
    (s : mstate) :
  goodmb Dr Dw (execute (ILLEGAL w)) s ∅ = true.
Proof. apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_J_U (Dr Dw : register -> bool) (imm : mword 11)
    (s : mstate) :
  goodmb Dr Dw (execute (C_J imm)) s ∅ = true.
Proof. apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_BEQZ_U (Dr Dw : register -> bool) (imm : mword 8)
    (rs : cregidx) (s : mstate) :
  goodmb Dr Dw (execute (C_BEQZ (imm, rs))) s ∅ = true.
Proof. apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_JR (Dr Dw : register -> bool) (rs1 : regidx)
    (s : mstate) :
  goodmb Dr Dw (execute (C_JR rs1)) s ∅ = true.
Proof. unfold execute; cbn match; unfold execute_C_JR; apply goodmb_returnm. Qed.

Lemma goodmb_execute_C_JALR (Dr Dw : register -> bool) (rs1 : regidx)
    (s : mstate) :
  goodmb Dr Dw (execute (C_JALR rs1)) s ∅ = true.
Proof. apply goodmb_returnm. Qed.

(* ===================================================================== *)
(* THE EXTENSION-GATE CERTIFICATES P5 LEFT AS UNDISCHARGEABLE HYPOTHESES. *)
(*                                                                       *)
(* [goodmb_execute_JAL_total] / [_JALR_total] / [_BTYPE_total], the CSR   *)
(* pair and [_ZICBOM_U] / [_SSAMOSWAP_U] all take                         *)
(*   [goodmb Dr Dw (currentlyEnabled Ext_Zca | Ext_Zicfilp) s empty]      *)
(* as a PREMISE, and NOTHING in the tree produced one -- the gate is      *)
(* [Acc]-guarded, so neither [reflexivity] nor [vm_compute] closes it at  *)
(* a symbolic state, and mirroring [exec_currentlyEnabled_Zca] node for   *)
(* node is ~120 lines of nested [and_boolM]/[or_boolM] bookkeeping.       *)
(*                                                                       *)
(* THE CHEAP ROUTE, and it is general: a gate is READ-ONLY and reads only *)
(* [misa] / [cur_privilege] / [menvcfg] / [senvcfg] -- all of [D_u].  So  *)
(* compute the certificate ONCE at the CONCRETE decode reference state    *)
(* [dstateU], where it is [reflexivity] in 2 ms, and transport it by      *)
(* agreement.  [goodb_agree_congr] is the transport: [goodb] consults the *)
(* state only through the values of the registers it declares, so two     *)
(* files agreeing on [D] give the same answer.                            *)
(*                                                                       *)
(* Anything read-only whose read set is inside [D_u] can now be certified *)
(* the same way; that is the general shape, not a JAL/CSR special case.   *)
(* ===================================================================== *)
Lemma goodb_agree_congr (D : register -> bool) {X : Type} (m : M X)
    (s1 s2 : mstate) :
  (forall r, D r = true ->
     register_lookup r s1.(sregs) = register_lookup r s2.(sregs)) ->
  goodb D m s2 = true -> goodb D m s1 = true.
Proof.
  intros Hag. revert s1 s2 Hag.
  induction m as [y | T oc k IH]; intros s1 s2 Hag Hg; [reflexivity |].
  destruct oc; cbn [goodb] in Hg |- *; try discriminate Hg;
    try (by apply (IH _ s1 s2 Hag)).
  apply andb_prop in Hg as [HD Hk]. rewrite HD. cbn [andb].
  rewrite (Hag _ HD). apply (IH _ s1 s2 Hag). exact Hk.
Qed.

Lemma u_D_u_to_Du_r (r : register) : D_u r = true -> Du_r r = true.
Proof.
  unfold D_u. intro Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr | Hr]);
    apply register_beq_true in Hr; subst r; vm_compute; reflexivity.
Qed.

Lemma u_D_u_not_nextPC (r : register) : D_u r = true -> register_beq r nextPC = false.
Proof.
  unfold D_u. intro Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr | Hr]);
    apply register_beq_true in Hr; subst r; reflexivity.
Qed.

(* the certificate of ANY read-only stretch whose read set is inside [D_u]:
   compute it at the concrete reference state, transport by agreement. *)
Lemma u_gm_gate (s : mstate) {X : Type} (m : M X) :
  agree_on D_u s dstateU ->
  goodb D_u m dstateU = true ->
  goodmb Du_r Du_w m s ∅ = true.
Proof.
  intros Hag Hg.
  apply (goodmb_mono D_u Du_w Du_r Du_w m u_D_u_to_Du_r (fun r H => H)).
  apply goodmb_of_goodb.
  exact (goodb_agree_congr D_u m s dstateU Hag Hg).
Qed.

Lemma u_gm_zca (s : mstate) :
  agree_on D_u s dstateU ->
  goodmb Du_r Du_w (currentlyEnabled Ext_Zca) s ∅ = true.
Proof. intro Hag. apply (u_gm_gate s _ Hag). reflexivity. Qed.

Lemma u_gm_zicfilp (s : mstate) :
  agree_on D_u s dstateU ->
  goodmb Du_r Du_w (currentlyEnabled Ext_Zicfilp) s ∅ = true.
Proof. intro Hag. apply (u_gm_gate s _ Hag). reflexivity. Qed.

Lemma u_gm_extS (s : mstate) :
  agree_on D_u s dstateU ->
  goodmb Du_r Du_w (currentlyEnabled Ext_S) s ∅ = true.
Proof. intro Hag. apply (u_gm_gate s _ Hag). reflexivity. Qed.

(* ===================================================================== *)
(* THE FOOTPRINT MEMBERSHIPS AS TERMS, NOT AS A COMPUTATION.              *)
(*                                                                       *)
(* A twin's [Dr X = true] side condition used to be closed by             *)
(* [vm_compute; reflexivity], which walks a 49-element [bool_decide] over *)
(* [register] EVERY TIME -- ~5 of them per dispatch-table entry, ~170     *)
(* entries.  Paying it ONCE per register here and closing the side goal   *)
(* with [exact] is the difference between a 20-minute file and a          *)
(* 4-minute one.                                                          *)
(* ===================================================================== *)
Lemma Du_r_PC : Du_r (R_bitvector_64 PC : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_nPC : Du_r (R_bitvector_64 nextPC : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_hart : Du_r (hart_state : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_priv : Du_r (cur_privilege : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mst : Du_r (R_bitvector_64 mstatus : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_scause : Du_r (R_bitvector_64 scause : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_stval : Du_r (R_bitvector_64 stval : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_sepc : Du_r (R_bitvector_64 sepc : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_ms : Du_r (R_bitvector_64 minstret : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mi : Du_r (R_bool minstret_increment : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_cy : Du_r (R_bitvector_64 mcycle : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_ti : Du_r (R_bitvector_64 mtime : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_ip : Du_r (R_bitvector_64 mip : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_tlb : Du_r (tlb : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_misa : Du_r (R_bitvector_64 misa : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_sec : Du_r (R_bitvector_64 mseccfg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_pma : Du_r (pma_regions : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_htif : Du_r (htif_tohost_base : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_elp : Du_r (R_bitvector_1 elp : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_senv : Du_r (R_bitvector_64 senvcfg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mcnt : Du_r (R_bitvector_32 mcountinhibit : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_micfg : Du_r (R_bitvector_64 minstretcfg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_stvec : Du_r (R_bitvector_64 stvec : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mie : Du_r (R_bitvector_64 mie : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mdl : Du_r (R_bitvector_64 mideleg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_medl : Du_r (R_bitvector_64 medeleg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_menv : Du_r (R_bitvector_64 menvcfg : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mste : Du_r (R_bitvector_64 mstateen0 : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_sste : Du_r (R_bitvector_32 sstateen0 : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_mcen : Du_r (R_bitvector_32 mcounteren : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_scen : Du_r (R_bitvector_32 scounteren : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_hpm : Du_r (mhpmcounter : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_satp : Du_r (R_bitvector_64 satp : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_pcfg : Du_r (pmpcfg_n : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_r_paddr : Du_r (pmpaddr_n : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_PC : Du_w (R_bitvector_64 PC : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_nPC : Du_w (R_bitvector_64 nextPC : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_hart : Du_w (hart_state : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_priv : Du_w (cur_privilege : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_mst : Du_w (R_bitvector_64 mstatus : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_scause : Du_w (R_bitvector_64 scause : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_stval : Du_w (R_bitvector_64 stval : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_sepc : Du_w (R_bitvector_64 sepc : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_ms : Du_w (R_bitvector_64 minstret : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_mi : Du_w (R_bool minstret_increment : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_cy : Du_w (R_bitvector_64 mcycle : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_ti : Du_w (R_bitvector_64 mtime : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_ip : Du_w (R_bitvector_64 mip : register) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Du_w_tlb : Du_w (tlb : register) = true.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* THE CERTIFICATE DISPATCHER.                                            *)
(*                                                                       *)
(* Every [finish_*] now owes [goodmb Du_r Du_w (execute i) <the execute   *)
(* state> mm = true].  P5's catalogue proves exactly that, at [mm :=      *)
(* empty] and generic in [(Dr, Dw)], one lemma per family -- so the       *)
(* obligation is discharged by a HINT DATABASE, not by naming a twin at   *)
(* each of the ~130 dispatch-table entries.  That is what keeps the two   *)
(* tables' clause structure untouched by the port.                        *)
(*                                                                       *)
(* Two hints beyond the catalogue: the gpr-index side conditions          *)
(* ([Du_gpr_of_Z] / [_r] -- the one membership no computation can do,     *)
(* because an operand index is symbolic) and a [vm_compute] extern for    *)
(* the named-cell ones.  The state-side conditions ([register_lookup      *)
(* cur_privilege s = User], which MRET/SRET/FENCE's certificates need)    *)
(* are closed by [assumption] against the ambient pin.                    *)
(* ===================================================================== *)
Create HintDb u_gm.

Hint Resolve goodmb_execute_ADDIW_total : u_gm.
Hint Resolve goodmb_execute_BTYPE_total : u_gm.
Hint Resolve goodmb_execute_CLMULH_total : u_gm.
Hint Resolve goodmb_execute_CLMULR_total : u_gm.
Hint Resolve goodmb_execute_CLMUL_total : u_gm.
Hint Resolve goodmb_execute_CSRImm_total_U : u_gm.
Hint Resolve goodmb_execute_CSRReg_total_U : u_gm.
Hint Resolve goodmb_execute_C_ADDW : u_gm.
Hint Resolve goodmb_execute_C_ANDI : u_gm.
Hint Resolve goodmb_execute_C_EBREAK_U : u_gm.
Hint Resolve goodmb_execute_C_ILLEGAL : u_gm.
Hint Resolve goodmb_execute_C_MUL : u_gm.
Hint Resolve goodmb_execute_C_NOP : u_gm.
Hint Resolve goodmb_execute_C_NOT_total : u_gm.
Hint Resolve goodmb_execute_C_NTL : u_gm.
Hint Resolve goodmb_execute_C_SRAI : u_gm.
Hint Resolve goodmb_execute_C_SUB : u_gm.
Hint Resolve goodmb_execute_C_SUBW : u_gm.
Hint Resolve goodmb_execute_C_XOR : u_gm.
Hint Resolve goodmb_execute_C_ZEXT_B_total : u_gm.
Hint Resolve goodmb_execute_DIVW_total : u_gm.
Hint Resolve goodmb_execute_DIV_total : u_gm.
Hint Resolve goodmb_execute_EBREAK_U : u_gm.
Hint Resolve goodmb_execute_ECALL_U : u_gm.
Hint Resolve goodmb_execute_FENCEI_U : u_gm.
Hint Resolve goodmb_execute_FENCE_TSO_U : u_gm.
Hint Resolve goodmb_execute_FENCE_total_U : u_gm.
Hint Resolve goodmb_execute_ITYPE_total : u_gm.
Hint Resolve goodmb_execute_JALR_total : u_gm.
Hint Resolve goodmb_execute_JAL_total : u_gm.
Hint Resolve goodmb_execute_MRET_U : u_gm.
Hint Resolve goodmb_execute_MULW_total : u_gm.
Hint Resolve goodmb_execute_MUL_total : u_gm.
Hint Resolve goodmb_execute_NTL : u_gm.
Hint Resolve goodmb_execute_PAUSE : u_gm.
Hint Resolve goodmb_execute_REMW_total : u_gm.
Hint Resolve goodmb_execute_REM_total : u_gm.
Hint Resolve goodmb_execute_REV8_total : u_gm.
Hint Resolve goodmb_execute_RORIW_total : u_gm.
Hint Resolve goodmb_execute_RORI_total : u_gm.
Hint Resolve goodmb_execute_RTYPEW_total : u_gm.
Hint Resolve goodmb_execute_RTYPE_total : u_gm.
Hint Resolve goodmb_execute_SFENCE_INVAL_IR_U : u_gm.
Hint Resolve goodmb_execute_SFENCE_VMA_U : u_gm.
Hint Resolve goodmb_execute_SFENCE_W_INVAL_U : u_gm.
Hint Resolve goodmb_execute_SHIFTIOP_total : u_gm.
Hint Resolve goodmb_execute_SHIFTIWOP_total : u_gm.
Hint Resolve goodmb_execute_SINVAL_VMA : u_gm.
Hint Resolve goodmb_execute_SRET_U : u_gm.
Hint Resolve goodmb_execute_SSAMOSWAP_U : u_gm.
Hint Resolve goodmb_execute_UTYPE_total : u_gm.
Hint Resolve goodmb_execute_WFI_U : u_gm.
Hint Resolve goodmb_execute_WRS : u_gm.
Hint Resolve goodmb_execute_ZBB_RTYPEW_total : u_gm.
Hint Resolve goodmb_execute_ZBB_RTYPE_total : u_gm.
Hint Resolve goodmb_execute_ZCMOP : u_gm.
Hint Resolve goodmb_execute_ZICBOM_U : u_gm.
Hint Resolve goodmb_execute_ZICBOZ_U : u_gm.
Hint Resolve goodmb_execute_ZICOND_RTYPE_total : u_gm.
Hint Resolve goodmb_execute_ZIMOP_MOP_RR_total : u_gm.
Hint Resolve goodmb_execute_ZIMOP_MOP_R_total : u_gm.
Hint Resolve goodmb_execute_C_LI : u_gm.
Hint Resolve goodmb_execute_C_LUI : u_gm.
Hint Resolve goodmb_execute_C_SRLI : u_gm.
Hint Resolve goodmb_execute_C_SLLI : u_gm.
Hint Resolve goodmb_execute_C_MV : u_gm.
Hint Resolve goodmb_execute_C_ADD : u_gm.
Hint Resolve goodmb_execute_C_ADDI : u_gm.
Hint Resolve goodmb_execute_C_ADDI16SP : u_gm.
Hint Resolve goodmb_execute_C_ADDI4SPN : u_gm.
Hint Resolve goodmb_execute_C_OR : u_gm.
Hint Resolve goodmb_execute_C_AND : u_gm.
Hint Resolve goodmb_execute_C_ADDIW : u_gm.
Hint Resolve goodmb_execute_C_BNEZ : u_gm.
Hint Resolve goodmb_execute_ILLEGAL_U : u_gm.
Hint Resolve goodmb_execute_C_J_U : u_gm.
Hint Resolve goodmb_execute_C_BEQZ_U : u_gm.
(* the gpr side conditions FIRST and at cost 0: they are the common case,
   and the [vm_compute] externs below must never be reached at a SYMBOLIC
   index (there [bool_decide (r ∈ u_rw_list)] is stuck and the search
   stalls). *)
Hint Extern 0 (uint _ <> 0 -> Du_r _ = true) =>
  (intro; apply Du_gpr_of_Z_r; assumption) : u_gm.
Hint Extern 0 (uint _ <> 0 -> Du_w _ = true) =>
  (intro; apply Du_gpr_of_Z; assumption) : u_gm.
Hint Resolve Du_gpr_of_Z Du_gpr_of_Z_r : u_gm.
Hint Extern 2 (Du_r _ = true) => vm_compute; reflexivity : u_gm.
Hint Extern 2 (Du_w _ = true) => vm_compute; reflexivity : u_gm.

(* [goodbP] refines [goodb]: it checks the SAME nodes and, at [Ret], one
   extra leaf predicate.  Only the forward direction was proved
   ([DecodeSetU.goodbP_top]); the decode's [hval] needs this one. *)
Lemma goodbP_goodb (D : register -> bool) {X} (P : X -> bool) (m : M X)
    (s : mstate) :
  goodbP D P m s = true -> goodb D m s = true.
Proof.
  induction m as [y|T oc k IH]; intros Hm.
  - reflexivity.
  - destruct oc; cbn [goodb goodbP] in Hm |- *; try discriminate Hm;
      try (apply IH; exact Hm).
    apply andb_prop in Hm as [HD Hk]. rewrite HD. cbn. apply IH; exact Hk.
Qed.

Section UserTotalU.
  Context (pt : uptd).

  (* The two execute states, spelled EXACTLY as [UserClassifyAsm.base_post] /
     [rvc_post] spell them.  [Local Notation], not [Definition]: an
     intermediate register file behind a [Definition] is a conversion bomb
     (durable notes), and the premise's type has to be SYNTACTICALLY what the
     consumer writes. *)
  Local Notation s0r rsf va := (register_set nextPC (add_vec_int va 4) rsf).
  Local Notation s2r rsf va := (register_set nextPC (add_vec_int va 2) rsf).
  Local Notation s0 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).
  Local Notation s2 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 2) rsf) mm).

  (* ------------------------------------------------------------------- *)
  (* THE DECODE SIDE.  The decoder is read-only, so it keeps the [goodb]   *)
  (* route it always had; what is new is that [HartRunFull.run_fetch_base] *)
  (* wants an [hval], which is ONE [hval_of_goodb] off the same reference  *)
  (* state [dstateU] the catalogue is computed at.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma u_D_u_sub (r : register) : D_u r = true -> r ∈ u_Drw ∪ u_Dro.
  Proof.
    unfold D_u. intro Hr.
    repeat (apply orb_prop in Hr; destruct Hr as [Hr | Hr]);
      apply register_beq_true in Hr; subst r;
      first [ exact u_in_priv | exact u_in_menv | exact u_in_senv
            | exact u_in_mste | exact u_in_sste | exact u_in_misa ].
  Qed.

  (* the decode reference agreement, from the pin bundle *)
  Lemma u_agree_decode (rsf : regstate) (mm : PtBytes.pamap) :
    register_lookup cur_privilege rsf = User ->
    register_lookup menvcfg rsf = MENVCFG_S ->
    u_hw_pins rsf -> u_cfg_pins rsf ->
    agree_on D_u (u_state rsf mm) dstateU.
  Proof.
    intros Lcp Lmenv (Hmisa & _ & Hsenv & _) (Hmste & Hsste).
    exact (agree_u (u_state rsf mm) Lcp Lmenv Hsenv Hmste Hsste Hmisa).
  Qed.

  Lemma u_hval_base (rsf : regstate) (mm : PtBytes.pamap) (w : mword 32)
      (i : instruction) :
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode w) dstateU = Some (i, dstateU) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf.
  Proof.
    intros Hag Hd.
    exact (hval_of_goodb D_u (u_Drw ∪ u_Dro) u_Drw (ext_decode w) dstateU rsf i
             u_D_u_sub Hag (goodbP_goodb D_u decodable_u _ _ (goodbP_encdec_u w))
             Hd).
  Qed.

  Lemma u_hval_rvc (rsf : regstate) (mm : PtBytes.pamap) (h : mword 16)
      (i : instruction) :
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) dstateU = Some (i, dstateU) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) i rsf.
  Proof.
    intros Hag Hd.
    exact (hval_of_goodb D_u (u_Drw ∪ u_Dro) u_Drw (ext_decode_compressed h)
             dstateU rsf i u_D_u_sub Hag
             (goodbP_goodb D_u decodable_c _ _ (goodbP_encdec_c h)) Hd).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE POST-STATE OF A REGISTER-ONLY EXECUTE, and its four shapes.       *)
  (*                                                                       *)
  (* [reg_agree_on u_Dfix] says the execute moved none of the cells the     *)
  (* loop invariant pins; the [tlb] clause and [u_mem_step] say it moved    *)
  (* neither the TLB nor a byte.  Every base and RVC [finish_*] closes      *)
  (* exactly this, and the four constructors are the only state shapes a    *)
  (* register-only U-mode execute produces.                                *)
  (* ------------------------------------------------------------------- *)
  Definition u_post_reg (t : ptree) (mm : PtBytes.pamap) (s_x : mstate)
      (rsx : regstate) : Prop :=
    reg_agree_on u_Dfix s_x.(sregs) rsx
    /\ tlb_ok_pt (mword_of_int 0) t (register_lookup tlb s_x.(sregs))
    /\ u_mem_step pt t t mm s_x.(mem).

  (* the tlb survives every register-only write, including a write at a
     SYMBOLIC gpr index -- [register_beq] on two DIFFERENT constructors
     reduces without knowing the index *)
  Lemma u_tlb_irr (r : register) (v : type_of_register r) (rs : regstate) :
    register_beq tlb r = false ->
    register_lookup tlb (register_set r v rs) = register_lookup tlb rs.
  Proof. apply irrelevant_register_set. Qed.

  Lemma u_tlb_gpr (ird : mword 5) (v : mword 64) (s : mstate) :
    register_lookup tlb (gpr_write_state ird v s).(sregs)
      = register_lookup tlb s.(sregs).
  Proof.
    unfold gpr_write_state. destruct (Z.eqb (uint ird) 0); [reflexivity|].
    rewrite sregs_set_reg. apply u_tlb_irr. reflexivity.
  Qed.

  Lemma u_mem_gpr (ird : mword 5) (v : mword 64) (s : mstate) :
    (gpr_write_state ird v s).(mem) = s.(mem).
  Proof.
    unfold gpr_write_state. destruct (Z.eqb (uint ird) 0); [reflexivity|].
    apply mem_set_reg.
  Qed.

  Lemma u_fix_gpr_state (ird : mword 5) (v : mword 64) (s : mstate) :
    reg_agree_on u_Dfix (gpr_write_state ird v s).(sregs) s.(sregs).
  Proof.
    unfold gpr_write_state. destruct (Z.eqb (uint ird) 0) eqn:H0;
      [ apply u_fix_refl |].
    rewrite sregs_set_reg. apply u_fix_gpr, Z.eqb_neq, H0.
  Qed.

  (* THE FOUR SHAPES. *)
  Lemma u_post_id (t : ptree) (mm : PtBytes.pamap) (rsx : regstate) :
    u_exec_pins pt t rsx -> u_mem_wf pt t mm ->
    u_post_reg t mm (u_state rsx mm) rsx.
  Proof.
    intros (_ & _ & _ & Htlb) Hwf. split_and!.
    - apply u_fix_refl.
    - exact Htlb.
    - by apply u_mem_step_refl.
  Qed.

  Lemma u_post_gpr (t : ptree) (mm : PtBytes.pamap) (rsx : regstate)
      (ird : mword 5) (v : mword 64) :
    u_exec_pins pt t rsx -> u_mem_wf pt t mm ->
    u_post_reg t mm (gpr_write_state ird v (u_state rsx mm)) rsx.
  Proof.
    intros (_ & _ & _ & Htlb) Hwf. split_and!.
    - apply u_fix_gpr_state.
    - rewrite u_tlb_gpr. exact Htlb.
    - rewrite u_mem_gpr. by apply u_mem_step_refl.
  Qed.

  Lemma u_post_npc (t : ptree) (mm : PtBytes.pamap) (rsx : regstate)
      (tgt : mword 64) :
    u_exec_pins pt t rsx -> u_mem_wf pt t mm ->
    u_post_reg t mm (set_reg (u_state rsx mm) nextPC tgt) rsx.
  Proof.
    intros (_ & _ & _ & Htlb) Hwf. split_and!.
    - rewrite sregs_set_reg. apply u_fix_npc.
    - rewrite sregs_set_reg u_tlb_irr; [ exact Htlb | reflexivity ].
    - rewrite mem_set_reg. by apply u_mem_step_refl.
  Qed.

  Lemma u_post_npc_gpr (t : ptree) (mm : PtBytes.pamap) (rsx : regstate)
      (ird : mword 5) (v tgt : mword 64) :
    u_exec_pins pt t rsx -> u_mem_wf pt t mm ->
    u_post_reg t mm
      (gpr_write_state ird v (set_reg (u_state rsx mm) nextPC tgt)) rsx.
  Proof.
    intros Hp Hwf.
    destruct (u_post_npc t mm rsx tgt Hp Hwf) as (Hag & Htlb & Hst).
    split_and!.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | exact Hag ].
    - rewrite u_tlb_gpr. exact Htlb.
    - rewrite u_mem_gpr. exact Hst.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE CERTIFICATE DISPATCHER, AND WHY IT IS A [first] AND NOT AN        *)
  (* [eauto].                                                             *)
  (*                                                                      *)
  (* Every [finish_*] owes [goodmb Du_r Du_w (execute i) <the execute      *)
  (* state> mm = true] and P5's catalogue proves exactly that, one lemma   *)
  (* per family at [mm := empty].  An [eauto … with] over those ~100       *)
  (* lemmas LOOKS right and is a disaster: eauto tries [assumption] at     *)
  (* every node of its search, and the dispatch tables run inside a proof  *)
  (* whose context holds ~35 hypotheses -- MEASURED at 11-48 s per call    *)
  (* site, i.e. ~14 min for the base table alone.  The obligation needs no *)
  (* search at all: the instruction is a CONCRETE constructor, so ONE      *)
  (* [first] picks the family (a mismatched [apply] fails on the           *)
  (* constructor, instantly) and the side conditions are four fixed        *)
  (* shapes.                                                              *)
  (*                                                                      *)
  (* [u_gm_side]'s ORDER is load-bearing: the two gpr alternatives must    *)
  (* come before [vm_compute], which is stuck (and slow) at a SYMBOLIC     *)
  (* operand index.                                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma u_gm_lift0 {X : Type} (m : M X) (st : mstate) (mmx : PtBytes.pamap) :
    goodmb Du_r Du_w m st ∅ = true -> goodmb Du_r Du_w m st mmx = true.
  Proof.
    intro H. apply (goodmb_map_mono Du_r Du_w m st ∅ mmx);
      [ rewrite dom_empty_L; apply empty_subseteq | exact H ].
  Qed.

  Local Ltac u_gm_lift := apply u_gm_lift0.

  (* PLAIN [apply], deliberately.  [eapply] is more permissive and SHELVES
     the evars of a twin whose value occurs only in its premises, which the
     side-condition closer never sees.  The three such twins ([ECALL],
     [EBREAK], the CSR pair) pass their certificate EXPLICITLY at their call
     site instead -- three places, against ~95 that need none. *)
  Local Ltac u_gm_side :=
    solve [ intro; apply Du_gpr_of_Z_r; assumption
          | intro; apply Du_gpr_of_Z; assumption
          | assumption
          | first [ exact Du_r_PC
            | exact Du_r_nPC
            | exact Du_r_hart
            | exact Du_r_priv
            | exact Du_r_mst
            | exact Du_r_scause
            | exact Du_r_stval
            | exact Du_r_sepc
            | exact Du_r_ms
            | exact Du_r_mi
            | exact Du_r_cy
            | exact Du_r_ti
            | exact Du_r_ip
            | exact Du_r_tlb
            | exact Du_r_misa
            | exact Du_r_sec
            | exact Du_r_pma
            | exact Du_r_htif
            | exact Du_r_elp
            | exact Du_r_senv
            | exact Du_r_mcnt
            | exact Du_r_micfg
            | exact Du_r_stvec
            | exact Du_r_mie
            | exact Du_r_mdl
            | exact Du_r_medl
            | exact Du_r_menv
            | exact Du_r_mste
            | exact Du_r_sste
            | exact Du_r_mcen
            | exact Du_r_scen
            | exact Du_r_hpm
            | exact Du_r_satp
            | exact Du_r_pcfg
            | exact Du_r_paddr
            | exact Du_w_PC
            | exact Du_w_nPC
            | exact Du_w_hart
            | exact Du_w_priv
            | exact Du_w_mst
            | exact Du_w_scause
            | exact Du_w_stval
            | exact Du_w_sepc
            | exact Du_w_ms
            | exact Du_w_mi
            | exact Du_w_cy
            | exact Du_w_ti
            | exact Du_w_ip
            | exact Du_w_tlb ]
          (* the compressed one-operand families ([C_NOT], [C_ZEXT_B]) state
             their gpr condition as ONE forall over the creg's expansion,
             read and write together *)
          | (intros ? ?; split; intro;
             solve [ apply Du_gpr_of_Z_r; assumption
                   | apply Du_gpr_of_Z; assumption ]) ].

  (* ------------------------------------------------------------------ *)
  (* THE FAMILY DISPATCHER IS KEYED, NOT SEARCHED.                        *)
  (*                                                                      *)
  (* [first [ apply twin1 | apply twin2 | ... ]] over 79 twins pays an     *)
  (* [apply] -- i.e. a full unification, which falls back to conversion    *)
  (* on the two [execute] bodies when the first-order match fails -- once  *)
  (* per twin BEFORE the right one.  Measured: [REV8], whose twin sits at  *)
  (* position ~70, took over two minutes on its own; the whole base table  *)
  (* did not finish in 10 wall-clock minutes.  A [lazymatch] on the        *)
  (* instruction CONSTRUCTOR is a syntactic keyed lookup: it selects the   *)
  (* one twin and pays exactly one [apply].  The old chain is kept as the  *)
  (* fallback so coverage cannot regress.                                  *)
  (* ------------------------------------------------------------------ *)
  Local Ltac u_gm_fam_slow :=
    first [ apply goodmb_execute_ADDIW_total
      | apply goodmb_execute_BTYPE_total
      | apply goodmb_execute_CLMULH_total
      | apply goodmb_execute_CLMULR_total
      | apply goodmb_execute_CLMUL_total
      | apply goodmb_execute_CSRImm_total_U
      | apply goodmb_execute_CSRReg_total_U
      | apply goodmb_execute_C_ADD
      | apply goodmb_execute_C_ADDI
      | apply goodmb_execute_C_ADDI16SP
      | apply goodmb_execute_C_ADDI4SPN
      | apply goodmb_execute_C_ADDIW
      | apply goodmb_execute_C_ADDW
      | apply goodmb_execute_C_AND
      | apply goodmb_execute_C_ANDI
      | apply goodmb_execute_C_BEQZ_U
      | apply goodmb_execute_C_BNEZ
      | apply goodmb_execute_C_EBREAK_U
      | apply goodmb_execute_C_ILLEGAL
      | apply goodmb_execute_C_JALR
      | apply goodmb_execute_C_JR
      | apply goodmb_execute_C_J_U
      | apply goodmb_execute_C_LI
      | apply goodmb_execute_C_LUI
      | apply goodmb_execute_C_MUL
      | apply goodmb_execute_C_MV
      | apply goodmb_execute_C_NOP
      | apply goodmb_execute_C_NOT_total
      | apply goodmb_execute_C_NTL
      | apply goodmb_execute_C_OR
      | apply goodmb_execute_C_SLLI
      | apply goodmb_execute_C_SRAI
      | apply goodmb_execute_C_SRLI
      | apply goodmb_execute_C_SUB
      | apply goodmb_execute_C_SUBW
      | apply goodmb_execute_C_XOR
      | apply goodmb_execute_C_ZEXT_B_total
      | apply goodmb_execute_DIVW_total
      | apply goodmb_execute_DIV_total
      | apply goodmb_execute_EBREAK_U
      | apply goodmb_execute_ECALL_U
      | apply goodmb_execute_FENCEI_U
      | apply goodmb_execute_FENCE_TSO_U
      | apply goodmb_execute_FENCE_total_U
      | apply goodmb_execute_ILLEGAL_U
      | apply goodmb_execute_ITYPE_total
      | apply goodmb_execute_JALR_total
      | apply goodmb_execute_JAL_total
      | apply goodmb_execute_MRET_U
      | apply goodmb_execute_MULW_total
      | apply goodmb_execute_MUL_total
      | apply goodmb_execute_NTL
      | apply goodmb_execute_PAUSE
      | apply goodmb_execute_REMW_total
      | apply goodmb_execute_REM_total
      | apply goodmb_execute_REV8_total
      | apply goodmb_execute_RORIW_total
      | apply goodmb_execute_RORI_total
      | apply goodmb_execute_RTYPEW_total
      | apply goodmb_execute_RTYPE_total
      | apply goodmb_execute_SFENCE_INVAL_IR_U
      | apply goodmb_execute_SFENCE_VMA_U
      | apply goodmb_execute_SFENCE_W_INVAL_U
      | apply goodmb_execute_SHIFTIOP_total
      | apply goodmb_execute_SHIFTIWOP_total
      | apply goodmb_execute_SINVAL_VMA
      | apply goodmb_execute_SRET_U
      | apply goodmb_execute_SSAMOSWAP_U
      | apply goodmb_execute_UTYPE_total
      | apply goodmb_execute_WFI_U
      | apply goodmb_execute_WRS
      | apply goodmb_execute_ZBB_RTYPEW_total
      | apply goodmb_execute_ZBB_RTYPE_total
      | apply goodmb_execute_ZCMOP
      | apply goodmb_execute_ZICBOM_U
      | apply goodmb_execute_ZICBOZ_U
      | apply goodmb_execute_ZICOND_RTYPE_total
      | apply goodmb_execute_ZIMOP_MOP_RR_total
      | apply goodmb_execute_ZIMOP_MOP_R_total ].

  Local Ltac u_gm_fam :=
    lazymatch goal with
    | |- goodmb _ _ (execute (ADDIW _)) _ _ = true => apply goodmb_execute_ADDIW_total
    | |- goodmb _ _ (execute (BTYPE _)) _ _ = true => apply goodmb_execute_BTYPE_total
    | |- goodmb _ _ (execute (CLMUL _)) _ _ = true => apply goodmb_execute_CLMUL_total
    | |- goodmb _ _ (execute (CLMULH _)) _ _ = true => apply goodmb_execute_CLMULH_total
    | |- goodmb _ _ (execute (CLMULR _)) _ _ = true => apply goodmb_execute_CLMULR_total
    | |- goodmb _ _ (execute (CSRImm _)) _ _ = true => apply goodmb_execute_CSRImm_total_U
    | |- goodmb _ _ (execute (CSRReg _)) _ _ = true => apply goodmb_execute_CSRReg_total_U
    | |- goodmb _ _ (execute (C_ADD _)) _ _ = true => apply goodmb_execute_C_ADD
    | |- goodmb _ _ (execute (C_ADDI _)) _ _ = true => apply goodmb_execute_C_ADDI
    | |- goodmb _ _ (execute (C_ADDI16SP _)) _ _ = true => apply goodmb_execute_C_ADDI16SP
    | |- goodmb _ _ (execute (C_ADDI4SPN _)) _ _ = true => apply goodmb_execute_C_ADDI4SPN
    | |- goodmb _ _ (execute (C_ADDIW _)) _ _ = true => apply goodmb_execute_C_ADDIW
    | |- goodmb _ _ (execute (C_ADDW _)) _ _ = true => apply goodmb_execute_C_ADDW
    | |- goodmb _ _ (execute (C_AND _)) _ _ = true => apply goodmb_execute_C_AND
    | |- goodmb _ _ (execute (C_ANDI _)) _ _ = true => apply goodmb_execute_C_ANDI
    | |- goodmb _ _ (execute (C_BEQZ _)) _ _ = true => apply goodmb_execute_C_BEQZ_U
    | |- goodmb _ _ (execute (C_BNEZ _)) _ _ = true => apply goodmb_execute_C_BNEZ
    | |- goodmb _ _ (execute (C_EBREAK _)) _ _ = true => apply goodmb_execute_C_EBREAK_U
    | |- goodmb _ _ (execute (C_ILLEGAL _)) _ _ = true => apply goodmb_execute_C_ILLEGAL
    | |- goodmb _ _ (execute (C_J _)) _ _ = true => apply goodmb_execute_C_J_U
    | |- goodmb _ _ (execute (C_JALR _)) _ _ = true => apply goodmb_execute_C_JALR
    | |- goodmb _ _ (execute (C_JR _)) _ _ = true => apply goodmb_execute_C_JR
    | |- goodmb _ _ (execute (C_LI _)) _ _ = true => apply goodmb_execute_C_LI
    | |- goodmb _ _ (execute (C_LUI _)) _ _ = true => apply goodmb_execute_C_LUI
    | |- goodmb _ _ (execute (C_MUL _)) _ _ = true => apply goodmb_execute_C_MUL
    | |- goodmb _ _ (execute (C_MV _)) _ _ = true => apply goodmb_execute_C_MV
    | |- goodmb _ _ (execute (C_NOP _)) _ _ = true => apply goodmb_execute_C_NOP
    | |- goodmb _ _ (execute (C_NOT _)) _ _ = true => apply goodmb_execute_C_NOT_total
    | |- goodmb _ _ (execute (C_NTL _)) _ _ = true => apply goodmb_execute_C_NTL
    | |- goodmb _ _ (execute (C_OR _)) _ _ = true => apply goodmb_execute_C_OR
    | |- goodmb _ _ (execute (C_SLLI _)) _ _ = true => apply goodmb_execute_C_SLLI
    | |- goodmb _ _ (execute (C_SRAI _)) _ _ = true => apply goodmb_execute_C_SRAI
    | |- goodmb _ _ (execute (C_SRLI _)) _ _ = true => apply goodmb_execute_C_SRLI
    | |- goodmb _ _ (execute (C_SUB _)) _ _ = true => apply goodmb_execute_C_SUB
    | |- goodmb _ _ (execute (C_SUBW _)) _ _ = true => apply goodmb_execute_C_SUBW
    | |- goodmb _ _ (execute (C_XOR _)) _ _ = true => apply goodmb_execute_C_XOR
    | |- goodmb _ _ (execute (C_ZEXT_B _)) _ _ = true => apply goodmb_execute_C_ZEXT_B_total
    | |- goodmb _ _ (execute (DIV _)) _ _ = true => apply goodmb_execute_DIV_total
    | |- goodmb _ _ (execute (DIVW _)) _ _ = true => apply goodmb_execute_DIVW_total
    | |- goodmb _ _ (execute (EBREAK _)) _ _ = true => apply goodmb_execute_EBREAK_U
    | |- goodmb _ _ (execute (ECALL _)) _ _ = true => apply goodmb_execute_ECALL_U
    | |- goodmb _ _ (execute (FENCE _)) _ _ = true => apply goodmb_execute_FENCE_total_U
    | |- goodmb _ _ (execute (FENCEI _)) _ _ = true => apply goodmb_execute_FENCEI_U
    | |- goodmb _ _ (execute (FENCE_TSO _)) _ _ = true => apply goodmb_execute_FENCE_TSO_U
    | |- goodmb _ _ (execute (ILLEGAL _)) _ _ = true => apply goodmb_execute_ILLEGAL_U
    | |- goodmb _ _ (execute (ITYPE _)) _ _ = true => apply goodmb_execute_ITYPE_total
    | |- goodmb _ _ (execute (JAL _)) _ _ = true => apply goodmb_execute_JAL_total
    | |- goodmb _ _ (execute (JALR _)) _ _ = true => apply goodmb_execute_JALR_total
    | |- goodmb _ _ (execute (MRET _)) _ _ = true => apply goodmb_execute_MRET_U
    | |- goodmb _ _ (execute (MUL _)) _ _ = true => apply goodmb_execute_MUL_total
    | |- goodmb _ _ (execute (MULW _)) _ _ = true => apply goodmb_execute_MULW_total
    | |- goodmb _ _ (execute (NTL _)) _ _ = true => apply goodmb_execute_NTL
    | |- goodmb _ _ (execute (PAUSE _)) _ _ = true => apply goodmb_execute_PAUSE
    | |- goodmb _ _ (execute (REM _)) _ _ = true => apply goodmb_execute_REM_total
    | |- goodmb _ _ (execute (REMW _)) _ _ = true => apply goodmb_execute_REMW_total
    | |- goodmb _ _ (execute (REV8 _)) _ _ = true => apply goodmb_execute_REV8_total
    | |- goodmb _ _ (execute (RORI _)) _ _ = true => apply goodmb_execute_RORI_total
    | |- goodmb _ _ (execute (RORIW _)) _ _ = true => apply goodmb_execute_RORIW_total
    | |- goodmb _ _ (execute (RTYPE _)) _ _ = true => apply goodmb_execute_RTYPE_total
    | |- goodmb _ _ (execute (RTYPEW _)) _ _ = true => apply goodmb_execute_RTYPEW_total
    | |- goodmb _ _ (execute (SFENCE_INVAL_IR _)) _ _ = true => apply goodmb_execute_SFENCE_INVAL_IR_U
    | |- goodmb _ _ (execute (SFENCE_VMA _)) _ _ = true => apply goodmb_execute_SFENCE_VMA_U
    | |- goodmb _ _ (execute (SFENCE_W_INVAL _)) _ _ = true => apply goodmb_execute_SFENCE_W_INVAL_U
    | |- goodmb _ _ (execute (SHIFTIOP _)) _ _ = true => apply goodmb_execute_SHIFTIOP_total
    | |- goodmb _ _ (execute (SHIFTIWOP _)) _ _ = true => apply goodmb_execute_SHIFTIWOP_total
    | |- goodmb _ _ (execute (SINVAL_VMA _)) _ _ = true => apply goodmb_execute_SINVAL_VMA
    | |- goodmb _ _ (execute (SRET _)) _ _ = true => apply goodmb_execute_SRET_U
    | |- goodmb _ _ (execute (SSAMOSWAP _)) _ _ = true => apply goodmb_execute_SSAMOSWAP_U
    | |- goodmb _ _ (execute (UTYPE _)) _ _ = true => apply goodmb_execute_UTYPE_total
    | |- goodmb _ _ (execute (WFI _)) _ _ = true => apply goodmb_execute_WFI_U
    | |- goodmb _ _ (execute (WRS _)) _ _ = true => apply goodmb_execute_WRS
    | |- goodmb _ _ (execute (ZBB_RTYPE _)) _ _ = true => apply goodmb_execute_ZBB_RTYPE_total
    | |- goodmb _ _ (execute (ZBB_RTYPEW _)) _ _ = true => apply goodmb_execute_ZBB_RTYPEW_total
    | |- goodmb _ _ (execute (ZCMOP _)) _ _ = true => apply goodmb_execute_ZCMOP
    | |- goodmb _ _ (execute (ZICBOM _)) _ _ = true => apply goodmb_execute_ZICBOM_U
    | |- goodmb _ _ (execute (ZICBOZ _)) _ _ = true => apply goodmb_execute_ZICBOZ_U
    | |- goodmb _ _ (execute (ZICOND_RTYPE _)) _ _ = true => apply goodmb_execute_ZICOND_RTYPE_total
    | |- goodmb _ _ (execute (ZIMOP_MOP_R _)) _ _ = true => apply goodmb_execute_ZIMOP_MOP_R_total
    | |- goodmb _ _ (execute (ZIMOP_MOP_RR _)) _ _ = true => apply goodmb_execute_ZIMOP_MOP_RR_total
    | _ => u_gm_fam_slow
    end.
  Local Ltac u_gm1 := u_gm_lift; u_gm_fam; u_gm_side.

  (* the pins ride across the nextPC tick: every cell they name is not
     nextPC *)
  Lemma u_tick_reg (r : register) (rs : regstate) (va : mword 64) (n : Z) :
    register_beq r nextPC = false ->
    register_lookup r (register_set nextPC (add_vec_int va n) rs)
      = register_lookup r rs.
  Proof. apply irrelevant_register_set. Qed.

  Lemma u_pins_tick (t : ptree) (rsf : regstate) (va : mword 64) (n : Z) :
    u_exec_pins pt t rsf ->
    u_exec_pins pt t (register_set nextPC (add_vec_int va n) rsf).
  Proof.
    intros Hp.
    rewrite /u_exec_pins /u_hw_pins /u_cfg_pins /u_pt_pins in Hp |- *.
    rewrite (u_tick_reg (R_bitvector_64 misa) rsf va n eq_refl)
            (u_tick_reg (R_bitvector_64 mseccfg) rsf va n eq_refl)
            (u_tick_reg (R_bitvector_64 senvcfg) rsf va n eq_refl)
            (u_tick_reg htif_tohost_base rsf va n eq_refl)
            (u_tick_reg pma_regions rsf va n eq_refl)
            (u_tick_reg (R_bitvector_1 elp) rsf va n eq_refl)
            (u_tick_reg (R_bitvector_64 mstateen0) rsf va n eq_refl)
            (u_tick_reg (R_bitvector_32 sstateen0) rsf va n eq_refl)
            (u_tick_reg (R_bitvector_64 satp) rsf va n eq_refl)
            (u_tick_reg pmpcfg_n rsf va n eq_refl)
            (u_tick_reg pmpaddr_n rsf va n eq_refl)
            (u_tick_reg tlb rsf va n eq_refl).
    exact Hp.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE TWO INTRODUCTION FORMS.  [base_post] / [rvc_post] have nine       *)
  (* conjuncts; these are the only places that count them.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma base_post_intro (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (i : instruction) (r : ExecutionResult)
      (s_x : mstate) :
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    is_lpad_instruction i = false ->
    (exec (execute i) (s0 rsf mm va) = Some (r, s_x)
       /\ goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true
     \/ (exists other : instruction,
           exec (execute i) (s0 rsf mm va) = Some (ExecuteAs other, s0 rsf mm va)
           /\ goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true
           /\ exec (execute other) (s0 rsf mm va) = Some (r, s_x)
           /\ goodmb Du_r Du_w (execute other) (s0 rsf mm va) mm = true)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_post_reg t mm s_x (s0r rsf va) ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hlpad Hex Hok Hnex (Hag & Htlb & Hst).
    exists i, r, s_x, t. split_and!; assumption.
  Qed.

  Lemma rvc_post_intro (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (h : mword 16) (i : instruction) (r : ExecutionResult)
      (s_x : mstate) :
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) i rsf ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    (exec (execute i) (s2 rsf mm va) = Some (r, s_x)
       /\ goodmb Du_r Du_w (execute i) (s2 rsf mm va) mm = true
     \/ (exists other : instruction,
           exec (execute i) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va)
           /\ goodmb Du_r Du_w (execute i) (s2 rsf mm va) mm = true
           /\ exec (execute other) (s2 rsf mm va) = Some (r, s_x)
           /\ goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true)) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_post_reg t mm s_x (s2r rsf va) ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hdec Hhv Hzca Hex Hok Hnex (Hag & Htlb & Hst).
    exists i, r, s_x, t. split_and!; assumption.
  Qed.

  Lemma u_result_ok_retire : u_result_ok RETIRE_SUCCESS.
  Proof. unfold u_result_ok. left. reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* GLUE (a): state-unchanged retire / illegal / trap / enter-wait / nop.  *)
  (* ------------------------------------------------------------------- *)
  Lemma finish_unchanged (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i : instruction) (r : ExecutionResult) (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va) = Some (r, s0 rsf mm va) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Hexec Hok Hnex Hpins Hwf Hgm.
    apply (base_post_intro t mm rsf va w i r (s0 rsf mm va)
             Hdec Hhv Hlpad (or_introl (conj Hexec Hgm)) Hok Hnex).
    apply u_post_id; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* GLUE (a'): state-unchanged via ONE base ExecuteAs redirect. *)
  Lemma finish_unchanged_redirect (t : ptree) (mm : PtBytes.pamap)
      (rsf : regstate) (va : mword 64) (i other : instruction)
      (r : ExecutionResult) (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va) = Some (ExecuteAs other, s0 rsf mm va) ->
    exec (execute other) (s0 rsf mm va) = Some (r, s0 rsf mm va) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Hex1 Hex2 Hok Hnex Hpins Hwf Hg1 Hg2.
    apply (base_post_intro t mm rsf va w i r (s0 rsf mm va)
             Hdec Hhv Hlpad
             (or_intror (ex_intro _ other (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
             Hok Hnex).
    apply u_post_id; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* GLUE (b): single-gpr-write retire. *)
  Lemma finish_gprwrite (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i : instruction) (ird : mword 5) (v : mword 64)
      (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va)
      = Some (RETIRE_SUCCESS, gpr_write_state ird v (s0 rsf mm va)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Hexec Hpins Hwf Hgm.
    apply (base_post_intro t mm rsf va w i RETIRE_SUCCESS
             (gpr_write_state ird v (s0 rsf mm va))
             Hdec Hhv Hlpad (or_introl (conj Hexec Hgm)) u_result_ok_retire I).
    apply u_post_gpr; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* GLUE (c): control-flow retire -- nextPC only, and nextPC + one gpr. *)
  Lemma finish_setpc (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i : instruction) (tgt : mword 64) (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va)
      = Some (RETIRE_SUCCESS, set_reg (s0 rsf mm va) nextPC tgt) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Hexec Hpins Hwf Hgm.
    apply (base_post_intro t mm rsf va w i RETIRE_SUCCESS
             (set_reg (s0 rsf mm va) nextPC tgt)
             Hdec Hhv Hlpad (or_introl (conj Hexec Hgm)) u_result_ok_retire I).
    apply u_post_npc; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  Lemma finish_jump_gpr (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (i : instruction) (ird : mword 5) (v tgt : mword 64)
      (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    exec (execute i) (s0 rsf mm va)
      = Some (RETIRE_SUCCESS,
              gpr_write_state ird v (set_reg (s0 rsf mm va) nextPC tgt)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Hexec Hpins Hwf Hgm.
    apply (base_post_intro t mm rsf va w i RETIRE_SUCCESS
             (gpr_write_state ird v (set_reg (s0 rsf mm va) nextPC tgt))
             Hdec Hhv Hlpad (or_introl (conj Hexec Hgm)) u_result_ok_retire I).
    apply u_post_npc_gpr; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* the generic RETIRE-with-single-gpr arm *)
  Lemma arm_gprwrite (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (i : instruction) (ird : mword 5) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) i rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (i, u_state rsf mm) ->
    is_lpad_instruction i = false ->
    (forall s : mstate, exists v : mword 64,
        exec (execute i) s = Some (RETIRE_SUCCESS, gpr_write_state ird v s)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute i) (s0 rsf mm va) mm = true ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hlpad Htot Hpins Hwf Hgm.
    destruct (Htot (s0 rsf mm va)) as (v & Hexec).
    exact (finish_gprwrite t mm rsf va i ird v w Hhv Hdec Hlpad Hexec
             Hpins Hwf Hgm).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Register transport across the tick, at the FILE (the execute runs one *)
  (* nextPC write later than the fetch landed).                            *)
  (* ------------------------------------------------------------------- *)
  Lemma s0_cur_privilege (rsf : regstate) (va : mword 64) :
    register_lookup cur_privilege rsf = User ->
    register_lookup cur_privilege (s0r rsf va) = User.
  Proof. intro H. rewrite (u_tick_reg cur_privilege rsf va 4 eq_refl). exact H. Qed.

  Lemma s0_PC (rsf : regstate) (va : mword 64) :
    register_lookup PC rsf = va ->
    register_lookup PC (s0r rsf va) = va.
  Proof.
    intro H. rewrite (u_tick_reg (R_bitvector_64 PC) rsf va 4 eq_refl). exact H.
  Qed.

  Lemma s0_reg (r : register) (v : type_of_register r) (rsf : regstate)
      (va : mword 64) :
    register_beq r nextPC = false ->
    register_lookup r rsf = v ->
    register_lookup r (s0r rsf va) = v.
  Proof. intros Hne H. rewrite (u_tick_reg r rsf va 4 Hne). exact H. Qed.

  Lemma s2_reg (r : register) (v : type_of_register r) (rsf : regstate)
      (va : mword 64) :
    register_beq r nextPC = false ->
    register_lookup r rsf = v ->
    register_lookup r (s2r rsf va) = v.
  Proof. intros Hne H. rewrite (u_tick_reg r rsf va 2 Hne). exact H. Qed.

  (* the decode agreement rides across the tick: no cell of [D_u] is nextPC *)
  Lemma u_agree_tick (rsf : regstate) (mm : PtBytes.pamap) (va : mword 64)
      (n : Z) :
    agree_on D_u (u_state rsf mm) dstateU ->
    agree_on D_u (u_state (register_set nextPC (add_vec_int va n) rsf) mm)
      dstateU.
  Proof.
    intros Hag r Hr.
    rewrite (u_tick_reg r rsf va n (u_D_u_not_nextPC r Hr)). exact (Hag r Hr).
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


  (* ===================================================================== *)
  (* THE RVC ANALOG.  Compressed execution runs at offset +2, and every      *)
  (* reachable compressed instruction that goes through the RVC progress     *)
  (* composer expands via a single [ExecuteAs other] -- so the redirect      *)
  (* carries TWO certificates, one per execute.                              *)
  (* ===================================================================== *)

  (* RVC state-unchanged (C_EBREAK -> EBREAK trap ; any ExecuteAs to a
     state-preserving base result). *)
  Lemma finish_rvc_unchanged (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr other : instruction) (r : ExecutionResult)
      (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    exec (execute other) (s2 rsf mm va) = Some (r, s2 rsf mm va) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hex1 Hex2 Hok Hnex Hpins Hwf Hg1 Hg2.
    apply (rvc_post_intro t mm rsf va h instr r (s2 rsf mm va)
             Hdecc Hhv Hzca
             (or_intror (ex_intro _ other (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
             Hok Hnex).
    apply u_post_id; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC single-gpr retire (compute expansions: C_LI/C_MV/C_ADD/... -> base). *)
  Lemma finish_rvc_gprwrite (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr other : instruction) (ird : mword 5) (v : mword 64)
      (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    exec (execute other) (s2 rsf mm va)
      = Some (RETIRE_SUCCESS, gpr_write_state ird v (s2 rsf mm va)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hex1 Hex2 Hpins Hwf Hg1 Hg2.
    apply (rvc_post_intro t mm rsf va h instr RETIRE_SUCCESS
             (gpr_write_state ird v (s2 rsf mm va))
             Hdecc Hhv Hzca
             (or_intror (ex_intro _ other (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
             u_result_ok_retire I).
    apply u_post_gpr; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC nextPC-only jump (taken C_BEQZ/C_BNEZ -> BTYPE). *)
  Lemma finish_rvc_setpc (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr other : instruction) (tgt : mword 64)
      (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    exec (execute other) (s2 rsf mm va)
      = Some (RETIRE_SUCCESS, set_reg (s2 rsf mm va) nextPC tgt) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hex1 Hex2 Hpins Hwf Hg1 Hg2.
    apply (rvc_post_intro t mm rsf va h instr RETIRE_SUCCESS
             (set_reg (s2 rsf mm va) nextPC tgt)
             Hdecc Hhv Hzca
             (or_intror (ex_intro _ other (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
             u_result_ok_retire I).
    apply u_post_npc; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC jump + gpr write (C_J / C_JR / C_JALR -> JAL / JALR). *)
  Lemma finish_rvc_jump_gpr (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr other : instruction) (ird : mword 5)
      (v tgt : mword 64) (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    exec (execute other) (s2 rsf mm va)
      = Some (RETIRE_SUCCESS,
              gpr_write_state ird v (set_reg (s2 rsf mm va) nextPC tgt)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hex1 Hex2 Hpins Hwf Hg1 Hg2.
    apply (rvc_post_intro t mm rsf va h instr RETIRE_SUCCESS
             (gpr_write_state ird v (set_reg (s2 rsf mm va) nextPC tgt))
             Hdecc Hhv Hzca
             (or_intror (ex_intro _ other (conj Hex1 (conj Hg1 (conj Hex2 Hg2)))))
             u_result_ok_retire I).
    apply u_post_npc_gpr; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC DIRECT (no ExecuteAs redirect): C_NOP / C_NTL / ZCMOP / C_ILLEGAL. *)
  Lemma finish_rvc_direct (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr : instruction) (r : ExecutionResult)
      (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (r, s2 rsf mm va) ->
    u_result_ok r ->
    match r with ExecuteAs _ => False | _ => True end ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hexec Hok Hnex Hpins Hwf Hgm.
    apply (rvc_post_intro t mm rsf va h instr r (s2 rsf mm va)
             Hdecc Hhv Hzca (or_introl (conj Hexec Hgm)) Hok Hnex).
    apply u_post_id; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC DIRECT single-gpr retire: C_NOT / C_ZEXT_B (and ZCMOP). *)
  Lemma finish_rvc_direct_gprwrite (t : ptree) (mm : PtBytes.pamap)
      (rsf : regstate) (va : mword 64) (instr : instruction) (ird : mword 5)
      (v : mword 64) (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va)
      = Some (RETIRE_SUCCESS, gpr_write_state ird v (s2 rsf mm va)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hexec Hpins Hwf Hgm.
    apply (rvc_post_intro t mm rsf va h instr RETIRE_SUCCESS
             (gpr_write_state ird v (s2 rsf mm va))
             Hdecc Hhv Hzca (or_introl (conj Hexec Hgm)) u_result_ok_retire I).
    apply u_post_gpr; [ by apply u_pins_tick | exact Hwf ].
  Qed.

  (* RVC compute expansion, taking the base total in [forall s, exists v]
     form so callers pass the family total verbatim. *)
  Lemma rvc_gpr (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (instr other : instruction) (ird : mword 5)
      (h : mword 16) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va) = Some (ExecuteAs other, s2 rsf mm va) ->
    (forall s : mstate, exists v : mword 64,
        exec (execute other) s = Some (RETIRE_SUCCESS, gpr_write_state ird v s)) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true ->
    goodmb Du_r Du_w (execute other) (s2 rsf mm va) mm = true ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hdecc Hzca Hex1 Htot Hpins Hwf Hg1 Hg2.
    destruct (Htot (s2 rsf mm va)) as (v & Hex2).
    exact (finish_rvc_gprwrite t mm rsf va instr other ird v h Hhv Hdecc Hzca
             Hex1 Hex2 Hpins Hwf Hg1 Hg2).
  Qed.

  (* ===================================================================== *)
  (* END-TO-END ARMS, one per outcome class and one per control-flow /      *)
  (* CSR family.  Each derives its family's execute fact from the pins and  *)
  (* routes to the glue; the CERTIFICATE is discharged in place by [u_gm1], *)
  (* so no dispatch-table entry ever names a [goodmb] twin.                 *)
  (* ===================================================================== *)

  (* ILLEGAL class: a bare ILLEGAL word (state-unchanged illegal). *)
  Lemma arm_ILLEGAL (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w wi : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (ILLEGAL wi) rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (ILLEGAL wi, u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hpins Hwf.
    apply (finish_unchanged t mm rsf va (ILLEGAL wi) (Illegal_Instruction tt) w
             Hhv Hdec eq_refl (exec_execute_ILLEGAL_U wi _)
             u_result_ok_illegal I Hpins Hwf).
    u_gm1.
  Qed.

  (* USER-TRAP class: ECALL delegates to E_U_EnvCall (user_exc = true). *)
  Lemma arm_ECALL (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (ECALL tt) rsf ->
    register_lookup cur_privilege rsf = User ->
    register_lookup PC rsf = va ->
    exec (ext_decode w) (u_state rsf mm) = Some (ECALL tt, u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Lcp Lpc Hdec Hpins Hwf.
    pose proof (s0_cur_privilege rsf va Lcp) as Lcp0.
    pose proof (s0_PC rsf va Lpc) as Lpc0.
    assert (Hok : u_result_ok (rv64d_types.Trap
              (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), va))).
    { unfold u_result_ok. right; left.
      exists (E_U_EnvCall tt), (zeros' 64), va. split; reflexivity. }
    apply (finish_unchanged t mm rsf va (ECALL tt) _ w Hhv Hdec eq_refl
             (exec_execute_ECALL_U (s0 rsf mm va) va Lcp0 Lpc0) Hok I Hpins Hwf).
    (* the certificate EXPLICITLY: [goodmb_execute_ECALL_U]'s [va] occurs
       only in its premises, so the dispatcher's [apply] cannot leave it
       open and its [eapply] would shelve it. *)
    apply u_gm_lift0.
    exact (goodmb_execute_ECALL_U Du_r Du_w (s0 rsf mm va) va
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lcp0 Lpc0).
  Qed.

  (* ENTER-WAIT class: WRS.STO / WRS.NTO park the hart WAITING. *)
  Lemma arm_WRS (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (op : wrsop) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (WRS op) rsf ->
    exec (ext_decode w) (u_state rsf mm) = Some (WRS op, u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hdec Hpins Hwf.
    assert (Hok : u_result_ok (Enter_Wait (match op with
                        | WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end))).
    { unfold u_result_ok. right; right; right.
      eexists. split; [reflexivity|]. destruct op; [left|right]; reflexivity. }
    apply (finish_unchanged t mm rsf va (WRS op) _ w Hhv Hdec eq_refl
             (exec_execute_WRS op _) Hok I Hpins Hwf).
    u_gm1.
  Qed.

  Lemma s2_PC (rsf : regstate) (va : mword 64) :
    register_lookup PC rsf = va -> register_lookup PC (s2r rsf va) = va.
  Proof.
    intro H. rewrite (u_tick_reg (R_bitvector_64 PC) rsf va 2 eq_refl). exact H.
  Qed.

  (* ===================================================================== *)
  (* JUMP arms (JAL / JALR / BTYPE).                                        *)
  (* ===================================================================== *)
  Lemma arm_JAL (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (imm : mword 21) (ird : mword 5) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (JAL (imm, Regidx ird)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup PC rsf = va ->
    register_lookup misa (s0r rsf va) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    eq_vec (access_vec_dec imm 0) ('b"0") = true ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (JAL (imm, Regidx ird), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hag Lpc Lmisa Hva2 Halign Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    assert (Halign2 : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s0r rsf va)) (sign_extend' 64 imm)) 0)
              ('b"0") = true).
    { rewrite (s0_PC rsf va Lpc).
      apply add_sext_even_64_21.
      - apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ].
      - apply wf_imm_even_21; exact Halign. }
    destruct (exec_execute_JAL_total imm ird (s0 rsf mm va)
                (s0_zca (s0 rsf mm va) Lmisa) Halign2) as (v & Hexec).
    apply (finish_jump_gpr t mm rsf va (JAL (imm, Regidx ird)) ird v
             (add_vec (register_lookup PC (s0r rsf va)) (sign_extend' 64 imm)) w
             Hhv Hdec eq_refl Hexec Hpins Hwf).
    u_gm_lift.
    exact (goodmb_execute_JAL_total Du_r Du_w imm ird (s0 rsf mm va)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) (Du_gpr_of_Z ird)
             (u_gm_zca _ Hag0) (s0_zca (s0 rsf mm va) Lmisa) Halign2).
  Qed.

  Lemma arm_JALR (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (imm : mword 12) (i1 ird : mword 5) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (JALR (imm, Regidx i1, Regidx ird)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup cur_privilege rsf = User ->
    register_lookup misa (s0r rsf va) = MISA_C ->
    register_lookup menvcfg (s0r rsf va) = MENVCFG_S ->
    register_lookup senvcfg (s0r rsf va) = (mword_of_int 0 : mword 64) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (JALR (imm, Regidx i1, Regidx ird), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hag Lcp Lmisa Lmenv Lsenv Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    pose proof (s0_cur_privilege rsf va Lcp) as Lcp0.
    destruct (exec_execute_JALR_total imm i1 ird (s0 rsf mm va)
                (s0_zicfilp (s0 rsf mm va) Lcp0 Lmisa Lmenv Lsenv) (s0_zca (s0 rsf mm va) Lmisa))
      as (v & tgt & Hexec).
    apply (finish_jump_gpr t mm rsf va (JALR (imm, Regidx i1, Regidx ird)) ird v
             tgt w Hhv Hdec eq_refl Hexec Hpins Hwf).
    u_gm_lift.
    exact (goodmb_execute_JALR_total Du_r Du_w imm i1 ird (s0 rsf mm va)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             (Du_gpr_of_Z_r i1) (Du_gpr_of_Z ird)
             (u_gm_zicfilp _ Hag0)
             (s0_zicfilp (s0 rsf mm va) Lcp0 Lmisa Lmenv Lsenv)
             (u_gm_zca _ Hag0) (s0_zca (s0 rsf mm va) Lmisa)).
  Qed.

  Lemma arm_BTYPE (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (imm : mword 13) (i2 i1 : mword 5)
      (op : bop) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (BTYPE (imm, Regidx i2, Regidx i1, op)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup PC rsf = va ->
    register_lookup misa (s0r rsf va) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    eq_vec (access_vec_dec imm 0) ('b"0") = true ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (BTYPE (imm, Regidx i2, Regidx i1, op), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hag Lpc Lmisa Hva2 Halign Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    assert (Hgb : goodmb Du_r Du_w
              (execute (BTYPE (imm, Regidx i2, Regidx i1, op)))
              (s0 rsf mm va) mm = true).
    { u_gm_lift.
      apply (goodmb_execute_BTYPE_total Du_r Du_w imm i2 i1 op (s0 rsf mm va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z_r i1) (Du_gpr_of_Z_r i2)
               (u_gm_zca _ Hag0) (s0_zca (s0 rsf mm va) Lmisa)).
      rewrite (s0_PC rsf va Lpc).
      apply add_sext_even_64_13.
      - apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ].
      - apply wf_imm_even_13; exact Halign. }
    assert (Halign2 : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s0r rsf va)) (sign_extend' 64 imm)) 0)
              ('b"0") = true).
    { rewrite (s0_PC rsf va Lpc).
      apply add_sext_even_64_13.
      - apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ].
      - apply wf_imm_even_13; exact Halign. }
    destruct (exec_execute_BTYPE_total imm i2 i1 op (s0 rsf mm va)
                (s0_zca (s0 rsf mm va) Lmisa) Halign2) as (s' & Hexec & [Hs' | Hs']).
    - (* not taken: state unchanged *)
      rewrite Hs' in Hexec.
      apply (finish_unchanged t mm rsf va (BTYPE (imm, Regidx i2, Regidx i1, op))
               RETIRE_SUCCESS w Hhv Hdec eq_refl Hexec u_result_ok_retire I
               Hpins Hwf Hgb).
    - (* taken: nextPC := target *)
      rewrite Hs' in Hexec.
      apply (finish_setpc t mm rsf va (BTYPE (imm, Regidx i2, Regidx i1, op))
               (add_vec (register_lookup PC (s0r rsf va)) (sign_extend' 64 imm)) w
               Hhv Hdec eq_refl Hexec Hpins Hwf Hgb).
  Qed.

  (* ===================================================================== *)
  (* CSR arms (CSRReg / CSRImm): Illegal (state-unchanged) OR a retiring     *)
  (* gpr-write read; FS/VS = 00 come from user_mstatus_ok.                   *)
  (* ===================================================================== *)
  Lemma arm_CSRReg (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (csr : mword 12) (i1 rd : mword 5)
      (op : csrop) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (CSRReg (csr, Regidx i1, Regidx rd, op)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup cur_privilege (s0r rsf va) = User ->
    user_mstatus_ok (register_lookup mstatus (s0r rsf va)) ->
    register_lookup misa (s0r rsf va) = MISA_C ->
    register_lookup menvcfg (s0r rsf va) = MENVCFG_S ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (CSRReg (csr, Regidx i1, Regidx rd, op), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hag Lcp Hmsok Lmisa Lmenv Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    destruct Hmsok as (_ & _ & _ & Hfs & Hvs & _ & _).
    assert (Hgb : goodmb Du_r Du_w
              (execute (CSRReg (csr, Regidx i1, Regidx rd, op)))
              (s0 rsf mm va) mm = true).
    { u_gm_lift.
      exact (goodmb_execute_CSRReg_total_U Du_r Du_w csr i1 rd op (s0 rsf mm va)
               (register_lookup mstatus (s0r rsf va))
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z_r i1) (Du_gpr_of_Z rd)
               Lcp eq_refl Hfs Hvs Lmisa Lmenv
               (u_gm_extS _ Hag0) (s0_ext_S (s0 rsf mm va) Lmisa)). }
    destruct (exec_execute_CSRReg_total_U csr i1 rd op (s0 rsf mm va)
                (register_lookup mstatus (s0r rsf va))
                Lcp eq_refl Hfs Hvs Lmisa Lmenv (s0_ext_S (s0 rsf mm va) Lmisa))
      as (res & s' & Hexec & [ [-> ->] | [-> (v & ->)] ]).
    - apply (finish_unchanged t mm rsf va (CSRReg (csr, Regidx i1, Regidx rd, op))
               (Illegal_Instruction tt) w Hhv Hdec eq_refl Hexec
               u_result_ok_illegal I Hpins Hwf Hgb).
    - apply (finish_gprwrite t mm rsf va (CSRReg (csr, Regidx i1, Regidx rd, op))
               rd v w Hhv Hdec eq_refl Hexec Hpins Hwf Hgb).
  Qed.

  Lemma arm_CSRImm (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (w : mword 32) (csr : mword 12) (imm rd : mword 5)
      (op : csrop) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (CSRImm (csr, imm, Regidx rd, op)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup cur_privilege (s0r rsf va) = User ->
    user_mstatus_ok (register_lookup mstatus (s0r rsf va)) ->
    register_lookup misa (s0r rsf va) = MISA_C ->
    register_lookup menvcfg (s0r rsf va) = MENVCFG_S ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (CSRImm (csr, imm, Regidx rd, op), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hhv Hag Lcp Hmsok Lmisa Lmenv Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    destruct Hmsok as (_ & _ & _ & Hfs & Hvs & _ & _).
    assert (Hgb : goodmb Du_r Du_w
              (execute (CSRImm (csr, imm, Regidx rd, op)))
              (s0 rsf mm va) mm = true).
    { u_gm_lift.
      exact (goodmb_execute_CSRImm_total_U Du_r Du_w csr imm rd op (s0 rsf mm va)
               (register_lookup mstatus (s0r rsf va))
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z rd)
               Lcp eq_refl Hfs Hvs Lmisa Lmenv
               (u_gm_extS _ Hag0) (s0_ext_S (s0 rsf mm va) Lmisa)). }
    destruct (exec_execute_CSRImm_total_U csr imm rd op (s0 rsf mm va)
                (register_lookup mstatus (s0r rsf va))
                Lcp eq_refl Hfs Hvs Lmisa Lmenv (s0_ext_S (s0 rsf mm va) Lmisa))
      as (res & s' & Hexec & [ [-> ->] | [-> (v & ->)] ]).
    - apply (finish_unchanged t mm rsf va (CSRImm (csr, imm, Regidx rd, op))
               (Illegal_Instruction tt) w Hhv Hdec eq_refl Hexec
               u_result_ok_illegal I Hpins Hwf Hgb).
    - apply (finish_gprwrite t mm rsf va (CSRImm (csr, imm, Regidx rd, op))
               rd v w Hhv Hdec eq_refl Hexec Hpins Hwf Hgb).
  Qed.

  (* ===================================================================== *)
  (* COMPRESSED jump / branch arms.                                         *)
  (* ===================================================================== *)
  Lemma arm_C_J (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (h : mword 16) (imm : mword 11) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_J imm) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup PC rsf = va ->
    register_lookup misa (s2r rsf va) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (C_J imm, u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hag Lpc Lmisa Hva2 Hzcaf Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 2 Hag) as Hag2.
    assert (Halign : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s2r rsf va))
                 (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0"))))) 0)
              ('b"0") = true).
    { rewrite (s2_PC rsf va Lpc).
      apply add_sext_even_64_21;
        [ apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ]
        | apply even_jimm_21 ]. }
    destruct (exec_execute_JAL_total (sign_extend' 21 (concat_vec imm ('b"0")))
                (zero_extend' 5 ('b"00")) (s2 rsf mm va)
                (s0_zca (s2 rsf mm va) Lmisa) Halign) as (v & Hexec).
    apply (finish_rvc_jump_gpr t mm rsf va (C_J imm)
             (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg))
             (zero_extend' 5 ('b"00")) v
             (add_vec (register_lookup PC (s2r rsf va))
                (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0"))))) h
             Hhv Hdec Hzcaf (exec_execute_C_J_U imm (s2 rsf mm va)) Hexec
             Hpins Hwf).
    - u_gm_lift. apply goodmb_execute_C_J_U.
    - u_gm_lift.
      exact (goodmb_execute_JAL_total Du_r Du_w
               (sign_extend' 21 (concat_vec imm ('b"0")))
               (zero_extend' 5 ('b"00")) (s2 rsf mm va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z (zero_extend' 5 ('b"00")))
               (u_gm_zca _ Hag2) (s0_zca (s2 rsf mm va) Lmisa) Halign).
  Qed.

  Lemma arm_C_JR (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (h : mword 16) (r1 : mword 5) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_JR (Regidx r1)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup cur_privilege (s2r rsf va) = User ->
    register_lookup misa (s2r rsf va) = MISA_C ->
    register_lookup menvcfg (s2r rsf va) = MENVCFG_S ->
    register_lookup senvcfg (s2r rsf va) = (mword_of_int 0 : mword 64) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_JR (Regidx r1), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hag Lcp Lmisa Lmenv Lsenv Hzcaf Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 2 Hag) as Hag2.
    destruct (exec_execute_JALR_total (zeros' 12) r1 (zero_extend' 5 ('b"00"))
                (s2 rsf mm va)
                (s0_zicfilp (s2 rsf mm va) Lcp Lmisa Lmenv Lsenv)
                (s0_zca (s2 rsf mm va) Lmisa)) as (v & tgt & Hexec).
    apply (finish_rvc_jump_gpr t mm rsf va (C_JR (Regidx r1))
             (JALR (zeros' 12, Regidx r1, zreg)) (zero_extend' 5 ('b"00")) v tgt h
             Hhv Hdec Hzcaf (exec_execute_C_JR (Regidx r1) (s2 rsf mm va)) Hexec
             Hpins Hwf).
    - u_gm_lift. apply goodmb_execute_C_JR.
    - u_gm_lift.
      exact (goodmb_execute_JALR_total Du_r Du_w (zeros' 12) r1
               (zero_extend' 5 ('b"00")) (s2 rsf mm va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z_r r1) (Du_gpr_of_Z (zero_extend' 5 ('b"00")))
               (u_gm_zicfilp _ Hag2)
               (s0_zicfilp (s2 rsf mm va) Lcp Lmisa Lmenv Lsenv)
               (u_gm_zca _ Hag2) (s0_zca (s2 rsf mm va) Lmisa)).
  Qed.

  Lemma arm_C_JALR (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (h : mword 16) (r1 : mword 5) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_JALR (Regidx r1)) rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup cur_privilege (s2r rsf va) = User ->
    register_lookup misa (s2r rsf va) = MISA_C ->
    register_lookup menvcfg (s2r rsf va) = MENVCFG_S ->
    register_lookup senvcfg (s2r rsf va) = (mword_of_int 0 : mword 64) ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_JALR (Regidx r1), u_state rsf mm) ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hag Lcp Lmisa Lmenv Lsenv Hzcaf Hdec Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 2 Hag) as Hag2.
    destruct (exec_execute_JALR_total (zeros' 12) r1 (zero_extend' 5 ('b"01"))
                (s2 rsf mm va)
                (s0_zicfilp (s2 rsf mm va) Lcp Lmisa Lmenv Lsenv)
                (s0_zca (s2 rsf mm va) Lmisa)) as (v & tgt & Hexec).
    apply (finish_rvc_jump_gpr t mm rsf va (C_JALR (Regidx r1))
             (JALR (zeros' 12, Regidx r1, ra)) (zero_extend' 5 ('b"01")) v tgt h
             Hhv Hdec Hzcaf (exec_execute_C_JALR (Regidx r1) (s2 rsf mm va)) Hexec
             Hpins Hwf).
    - u_gm_lift. apply goodmb_execute_C_JALR.
    - u_gm_lift.
      exact (goodmb_execute_JALR_total Du_r Du_w (zeros' 12) r1
               (zero_extend' 5 ('b"01")) (s2 rsf mm va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z_r r1) (Du_gpr_of_Z (zero_extend' 5 ('b"01")))
               (u_gm_zicfilp _ Hag2)
               (s0_zicfilp (s2 rsf mm va) Lcp Lmisa Lmenv Lsenv)
               (u_gm_zca _ Hag2) (s0_zca (s2 rsf mm va) Lmisa)).
  Qed.

  Lemma arm_C_Bcc (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (h : mword 16) (instr : instruction)
      (imm : mword 8) (rsb : mword 3) (op : bop) :
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) instr rsf ->
    agree_on D_u (u_state rsf mm) dstateU ->
    register_lookup PC rsf = va ->
    register_lookup misa (s2r rsf va) = MISA_C ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    exec (currentlyEnabled Ext_Zca) (u_state rsf mm) = Some (true, u_state rsf mm) ->
    exec (ext_decode_compressed h) (u_state rsf mm) = Some (instr, u_state rsf mm) ->
    exec (execute instr) (s2 rsf mm va)
      = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg,
                                creg2reg_idx (Cregidx rsb), op)), s2 rsf mm va) ->
    goodmb Du_r Du_w (execute instr) (s2 rsf mm va) ∅ = true ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.
  Proof.
    intros Hhv Hag Lpc Lmisa Hva2 Hzcaf Hdec Hex1 Hg10 Hpins Hwf.
    pose proof (u_agree_tick rsf mm va 2 Hag) as Hag2.
    assert (Hg1 : goodmb Du_r Du_w (execute instr) (s2 rsf mm va) mm = true)
      by (u_gm_lift; exact Hg10).
    assert (Halign : eq_vec (access_vec_dec
              (add_vec (register_lookup PC (s2r rsf va))
                 (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0"))))) 0)
              ('b"0") = true).
    { rewrite (s2_PC rsf va Lpc).
      apply add_sext_even_64_13;
        [ apply (aligned_even va 2); [ apply Z.divide_refl | lia | exact Hva2 ]
        | apply even_jimm_13 ]. }
    assert (Hg2 : goodmb Du_r Du_w
              (execute (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg,
                               creg2reg_idx (Cregidx rsb), op)))
              (s2 rsf mm va) mm = true).
    { u_gm_lift.
      exact (goodmb_execute_BTYPE_total Du_r Du_w
               (sign_extend' 13 (concat_vec imm ('b"0")))
               (zero_extend' 5 ('b"00")) (zero_extend' 5 (concat_vec ('b"1") rsb))
               op (s2 rsf mm va)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (Du_gpr_of_Z_r (zero_extend' 5 (concat_vec ('b"1") rsb)))
               (Du_gpr_of_Z_r (zero_extend' 5 ('b"00")))
               (u_gm_zca _ Hag2) (s0_zca (s2 rsf mm va) Lmisa) Halign). }
    destruct (exec_execute_BTYPE_total (sign_extend' 13 (concat_vec imm ('b"0")))
                (zero_extend' 5 ('b"00")) (zero_extend' 5 (concat_vec ('b"1") rsb))
                op (s2 rsf mm va) (s0_zca (s2 rsf mm va) Lmisa) Halign)
      as (s' & Hexec & [Hs' | Hs']).
    - rewrite Hs' in Hexec.
      exact (finish_rvc_unchanged t mm rsf va instr
               (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg,
                       creg2reg_idx (Cregidx rsb), op))
               RETIRE_SUCCESS h Hhv Hdec Hzcaf Hex1 Hexec u_result_ok_retire I
               Hpins Hwf Hg1 Hg2).
    - rewrite Hs' in Hexec.
      exact (finish_rvc_setpc t mm rsf va instr
               (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg,
                       creg2reg_idx (Cregidx rsb), op))
               (add_vec (register_lookup PC (s2r rsf va))
                  (sign_extend' 64 (sign_extend' 13 (concat_vec imm ('b"0"))))) h
               Hhv Hdec Hzcaf Hex1 Hexec Hpins Hwf Hg1 Hg2).
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
  Variable arm_LOAD_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (imm : bits 12) (rs1 rd : regidx) (is_unsigned : bool) (width : word_width),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (LOAD (imm, rs1, rd, is_unsigned, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (LOAD (imm, rs1, rd, is_unsigned, width)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  Variable arm_STORE_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (imm : bits 12) (rs2 rs1 : regidx) (width : word_width),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (STORE (imm, rs2, rs1, width), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (STORE (imm, rs2, rs1, width)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  Variable arm_AMO_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
    exec (ext_decode w) (u_state rsf mm) = Some (AMO (op, aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (AMO (op, aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  Variable arm_LOADRES_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (LOADRES (aq, rl, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (LOADRES (aq, rl, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  Variable arm_STORECON_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs2 rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (STORECON (aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (STORECON (aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  Variable arm_ZICBOP_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (p : cbop_zicbop * regidx * bits 12),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode w) (u_state rsf mm) = Some (ZICBOP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (ZICBOP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.

  (* -- Compressed memory families: same uniform contract, but at offset +2  *)
  (* over [ext_decode_compressed], concluding [rvc_post].  The sibling        *)
  (* instantiates each with the compressed load/store arm (which itself       *)
  (* routes through the base LOAD/STORE classification via the ExecuteAs      *)
  (* expansion at the compressed geometry).                                   *)
  Variable arm_C_LW_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LW p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LW p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LD_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LD p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LD p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LWSP_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LWSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LWSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LDSP_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LDSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LDSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SW_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SW p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SW p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SD_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 5 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SD p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SD p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SWSP_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SWSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SWSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SDSP_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 6 * regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SDSP p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SDSP p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LBU_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LBU p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LBU p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LH_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LH p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LH p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_LHU_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_LHU p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_LHU p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SB_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SB p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SB p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.

  Variable arm_C_SH_u : forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (h : mword 16) (p : bits 2 * cregidx * cregidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    exec (ext_decode_compressed h) (u_state rsf mm)
      = Some (C_SH p, u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode_compressed h) (C_SH p) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    rvc_post pt t mm rsf va h.


  (* ===================================================================== *)
  (* THE TWO EXECUTE TOTALITIES, ASSEMBLED.                                  *)
  (* Method: intro the premises; derive the config facts at the execute      *)
  (* state; [decode_total_{u,c}_set] + the decode agreement pin the decoded  *)
  (* instruction AND its [hval]; [destruct i] + discriminate kills every     *)
  (* non-decodable constructor; each remaining family dispatches to its      *)
  (* arm/glue.  Memory families route to the section Variables above.        *)
  (*                                                                        *)
  (* [fin] and [finm] are now the SAME tactic -- there is no [hw_config] to  *)
  (* hand a memory arm any more -- and both end in [u_gm1], which is how a   *)
  (* dispatch-table entry discharges its family's [goodmb] obligation        *)
  (* without ever naming a twin.                                             *)
  (* ===================================================================== *)
  (* [Hpins] / [Hwf] are named by [assumption], NOT written into the tactic:
     an [Ltac] body's identifiers are resolved at DEFINITION time, where the
     proof's hypotheses do not exist yet (this is the durable notes' trap
     about a tactic notation's [constr] argument, one level down). *)
  Local Ltac fin lem := apply lem; solve [ assumption | u_gm1 ].
  Local Ltac finm lem := apply lem; solve [ assumption | u_gm1 ].

  Lemma base_exec_total_u_holds (va : mword 64) (mi : bool) :
    base_exec_total_u pt va mi.
  Proof.
    unfold base_exec_total_u.
    intros w rsf t mm Hcfg Hpins Hwf.
    pose proof Hcfg as Hcfg_full.
    destruct Hcfg as (Lpc & Lcp & Hmsok & Lmenv & Hva2 & Lmi).
    pose proof Hpins as Hpins2.
    destruct Hpins2 as (Hhwp & Hcfgp & _ & _).
    assert (Hag : agree_on D_u (u_state rsf mm) dstateU)
      by exact (u_agree_decode rsf mm Lcp Lmenv Hhwp Hcfgp).
    pose proof (u_agree_tick rsf mm va 4 Hag) as Hag0.
    destruct Hhwp as (Lmisaf & Lsecf & Lsenvf & Lhtiff & Lpmaf & Lelpf).
    assert (Lcp0 : register_lookup cur_privilege (s0r rsf va) = User)
      by (apply s0_cur_privilege; exact Lcp).
    assert (Lpc0 : register_lookup PC (s0r rsf va) = va)
      by (apply s0_PC; exact Lpc).
    assert (Lmenv0 : register_lookup menvcfg (s0r rsf va) = MENVCFG_S)
      by (apply (s0_reg menvcfg MENVCFG_S rsf va eq_refl); exact Lmenv).
    assert (Lmisa0 : register_lookup misa (s0r rsf va) = MISA_C)
      by (apply (s0_reg misa MISA_C rsf va eq_refl); exact Lmisaf).
    assert (Lsenv0 : register_lookup senvcfg (s0r rsf va)
                     = (mword_of_int 0 : mword 64))
      by (apply (s0_reg senvcfg _ rsf va eq_refl); exact Lsenvf).
    assert (Hmsok0 : user_mstatus_ok (register_lookup mstatus (s0r rsf va))).
    { rewrite (s0_reg mstatus (register_lookup mstatus rsf) rsf va eq_refl
                 eq_refl). exact Hmsok. }
    (* NOTHING WITH HEAD [goodmb] OR [exec (currentlyEnabled _)] MAY BE LEFT
       IN THE CONTEXT.  [u_gm1]'s search tries [assumption] on every goodmb
       obligation, and a hypothesis with the SAME head forces a CONVERSION
       between two big monadic terms -- [execute (MRET tt)] against
       [currentlyEnabled Ext_Zca], which is [Acc]-guarded and does not
       converge.  Measured: with the three gate certificates in context the
       base dispatch block took 812 s; the three families that need them
       (ZICBOM / ZICBOZ / SSAMOSWAP) pass them EXPLICITLY instead. *)
    destruct (decode_total_u_set w) as (i & Hdi & Hdf0).
    pose proof (u_hval_base rsf mm w i Hag (Hdf0 dstateU (fun r _ => eq_refl)))
      as Hhv.
    pose proof (Hdf0 (u_state rsf mm) Hag) as Hdf. clear Hdf0.
    destruct i; try (cbn in Hdi; discriminate).
    all: lazymatch type of Hdf with
    (* --- retiring compute families (arm_gprwrite + the family total) --- *)
    | _ = Some (ITYPE ?p, _) =>
        destruct p as [[[imm i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ITYPE (imm, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_ITYPE_total imm i1 ird op))
    | _ = Some (RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_RTYPE_total i2 i1 ird op))
    | _ = Some (RTYPEW ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_RTYPEW_total i2 i1 ird op))
    | _ = Some (SHIFTIOP ?p, _) =>
        destruct p as [[[shamt i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (SHIFTIOP (shamt, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_SHIFTIOP_total shamt i1 ird op))
    | _ = Some (SHIFTIWOP ?p, _) =>
        destruct p as [[[shamt i1] ird] op]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (SHIFTIWOP (shamt, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_SHIFTIWOP_total shamt i1 ird op))
    | _ = Some (ADDIW ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ADDIW (imm, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_ADDIW_total imm i1 ird))
    | _ = Some (MUL ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (MUL (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_MUL_total i2 i1 ird op))
    | _ = Some (MULW ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (MULW (Regidx i2, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_MULW_total i2 i1 ird))
    | _ = Some (DIV ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (DIV (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Hhv Hdf eq_refl (exec_execute_DIV_total i2 i1 ird u))
    | _ = Some (DIVW ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (DIVW (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Hhv Hdf eq_refl (exec_execute_DIVW_total i2 i1 ird u))
    | _ = Some (REM ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (REM (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Hhv Hdf eq_refl (exec_execute_REM_total i2 i1 ird u))
    | _ = Some (REMW ?p, _) =>
        destruct p as [[[i2 i1] ird] u]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (REMW (Regidx i2, Regidx i1, Regidx ird, u)) ird
              Hhv Hdf eq_refl (exec_execute_REMW_total i2 i1 ird u))
    | _ = Some (UTYPE ?p, _) =>
        destruct p as [[imm ird] op]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (UTYPE (imm, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_UTYPE_total imm ird op))
    | _ = Some (ZBB_RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ZBB_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_ZBB_RTYPE_total i2 i1 ird op))
    | _ = Some (ZBB_RTYPEW ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ZBB_RTYPEW (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_ZBB_RTYPEW_total i2 i1 ird op))
    | _ = Some (CLMUL ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (CLMUL (Regidx i2, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_CLMUL_total i2 i1 ird))
    | _ = Some (CLMULH ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (CLMULH (Regidx i2, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_CLMULH_total i2 i1 ird))
    | _ = Some (CLMULR ?p, _) =>
        destruct p as [[i2 i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (CLMULR (Regidx i2, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_CLMULR_total i2 i1 ird))
    | _ = Some (REV8 ?p, _) =>
        destruct p as [i1 ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (REV8 (Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_REV8_total i1 ird))
    | _ = Some (RORI ?p, _) =>
        destruct p as [[shamt i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (RORI (shamt, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_RORI_total shamt i1 ird))
    | _ = Some (RORIW ?p, _) =>
        destruct p as [[shamt i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (RORIW (shamt, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_RORIW_total shamt i1 ird))
    | _ = Some (ZIMOP_MOP_R ?p, _) =>
        destruct p as [[mop i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ZIMOP_MOP_R (mop, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_ZIMOP_MOP_R_total mop i1 ird))
    | _ = Some (ZIMOP_MOP_RR ?p, _) =>
        destruct p as [[[mop i2] i1] ird]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ZIMOP_MOP_RR (mop, Regidx i2, Regidx i1, Regidx ird)) ird
              Hhv Hdf eq_refl (exec_execute_ZIMOP_MOP_RR_total mop i2 i1 ird))
    | _ = Some (ZICOND_RTYPE ?p, _) =>
        destruct p as [[[i2 i1] ird] op]; destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_gprwrite t mm rsf va w (ZICOND_RTYPE (Regidx i2, Regidx i1, Regidx ird, op)) ird
              Hhv Hdf eq_refl (exec_execute_ZICOND_RTYPE_total i2 i1 ird op))
    (* --- control flow (jump arms) --- *)
    | _ = Some (JAL ?p, _) =>
        destruct p as [imm ird]; destruct ird as [ird]; cbn in Hdi;
        fin (arm_JAL t mm rsf va w imm ird Hhv Hag Lpc Lmisa0 Hva2 Hdi Hdf)
    | _ = Some (JALR ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (arm_JALR t mm rsf va w imm i1 ird Hhv Hag Lcp Lmisa0 Lmenv0 Lsenv0 Hdf)
    | _ = Some (BTYPE ?p, _) =>
        destruct p as [[[imm i2] i1] op]; destruct i2 as [i2]; destruct i1 as [i1]; cbn in Hdi;
        fin (arm_BTYPE t mm rsf va w imm i2 i1 op Hhv Hag Lpc Lmisa0 Hva2 Hdi Hdf)
    (* --- CSR arms --- *)
    | _ = Some (CSRReg ?p, _) =>
        destruct p as [[[csr i1] rd] op]; destruct i1 as [i1]; destruct rd as [rd];
        fin (arm_CSRReg t mm rsf va w csr i1 rd op Hhv Hag Lcp0 Hmsok0 Lmisa0 Lmenv0 Hdf)
    | _ = Some (CSRImm ?p, _) =>
        destruct p as [[[csr imm] rd] op]; destruct rd as [rd];
        fin (arm_CSRImm t mm rsf va w csr imm rd op Hhv Hag Lcp0 Hmsok0 Lmisa0 Lmenv0 Hdf)
    (* --- illegal / trap / wait / fence / nop (finish glue) --- *)
    | _ = Some (ILLEGAL ?wi, _) =>
        fin (arm_ILLEGAL t mm rsf va w wi Hhv Hdf)
    | _ = Some (ECALL ?u, _) =>
        destruct u; fin (arm_ECALL t mm rsf va w Hhv Lcp Lpc Hdf)
    | _ = Some (WRS ?op, _) =>
        fin (arm_WRS t mm rsf va w op Hhv Hdf)
    | _ = Some (EBREAK ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (EBREAK tt)
              (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va)) w
              Hhv Hdf eq_refl (exec_execute_EBREAK_U (s0 rsf mm va) va Lcp0 Lpc0)
              (u_result_ok_ebreak va) I Hpins Hwf
              (u_gm_lift0 _ (s0 rsf mm va) mm
                 (goodmb_execute_EBREAK_U Du_r Du_w (s0 rsf mm va) va
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    Lcp0 Lpc0)))
    | _ = Some (MRET ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (MRET tt) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_MRET_U (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SRET ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (SRET tt) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_SRET_U (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (WFI ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (WFI tt) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_WFI_U (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_VMA ?p, _) =>
        destruct p as [i1 i2]; destruct i1 as [i1]; destruct i2 as [i2];
        fin (finish_unchanged t mm rsf va (SFENCE_VMA (Regidx i1, Regidx i2))
              (Illegal_Instruction tt) w Hhv Hdf eq_refl
              (exec_execute_SFENCE_VMA_U i1 i2 (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_W_INVAL ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (SFENCE_W_INVAL tt) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_SFENCE_W_INVAL_U (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SFENCE_INVAL_IR ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (SFENCE_INVAL_IR tt) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_SFENCE_INVAL_IR_U (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (SINVAL_VMA ?p, _) =>
        destruct p as [rs1 rs2]; destruct rs1 as [i1]; destruct rs2 as [i2];
        fin (finish_unchanged_redirect t mm rsf va (SINVAL_VMA (Regidx i1, Regidx i2))
              (SFENCE_VMA (Regidx i1, Regidx i2)) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_SINVAL_VMA (Regidx i1) (Regidx i2) (s0 rsf mm va))
              (exec_execute_SFENCE_VMA_U i1 i2 (s0 rsf mm va) Lcp0) u_result_ok_illegal I)
    | _ = Some (ZICBOM ?p, _) =>
        destruct p as [op i1]; destruct i1 as [i1];
        fin (finish_unchanged t mm rsf va (ZICBOM (op, Regidx i1)) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl
              (exec_execute_ZICBOM_U op i1 (s0 rsf mm va) Lcp0 Lmenv0 Lsenv0 (s0_ext_S (s0 rsf mm va) Lmisa0))
              u_result_ok_illegal I Hpins Hwf
              (u_gm_lift0 _ (s0 rsf mm va) mm
                 (goodmb_execute_ZICBOM_U Du_r Du_w op i1 (s0 rsf mm va)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) Lcp0 Lmenv0 Lsenv0
                    (u_gm_extS _ Hag0) (s0_ext_S (s0 rsf mm va) Lmisa0))))
    | _ = Some (ZICBOZ ?r, _) =>
        destruct r as [i1];
        fin (finish_unchanged t mm rsf va (ZICBOZ (Regidx i1)) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl (exec_execute_ZICBOZ_U i1 (s0 rsf mm va) Lcp0 Lmenv0 Lsenv0)
              u_result_ok_illegal I Hpins Hwf
              (u_gm_lift0 _ (s0 rsf mm va) mm
                 (goodmb_execute_ZICBOZ_U Du_r Du_w i1 (s0 rsf mm va)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) Lcp0 Lmenv0 Lsenv0)))
    | _ = Some (SSAMOSWAP ?p, _) =>
        destruct p as [[[[[aq rl] i2] i1] width] ird];
        destruct i2 as [i2]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged t mm rsf va
              (SSAMOSWAP (aq, rl, Regidx i2, Regidx i1, width, Regidx ird)) (Illegal_Instruction tt) w
              Hhv Hdf eq_refl
              (exec_execute_SSAMOSWAP_U aq rl i2 i1 ird width (s0 rsf mm va)
                 Lcp0 Lmenv0 Lsenv0 (s0_ext_S (s0 rsf mm va) Lmisa0))
              u_result_ok_illegal I Hpins Hwf
              (u_gm_lift0 _ (s0 rsf mm va) mm
                 (goodmb_execute_SSAMOSWAP_U Du_r Du_w aq rl i2 i1 ird width
                    (s0 rsf mm va)
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) Lcp0 Lmenv0 Lsenv0
                    (u_gm_extS _ Hag0) (s0_ext_S (s0 rsf mm va) Lmisa0))))
    | _ = Some (NTL ?nt, _) =>
        fin (finish_unchanged t mm rsf va (NTL nt) RETIRE_SUCCESS w
              Hhv Hdf eq_refl (exec_execute_NTL nt (s0 rsf mm va)) u_result_ok_retire I)
    | _ = Some (PAUSE ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (PAUSE tt) RETIRE_SUCCESS w
              Hhv Hdf eq_refl (exec_execute_PAUSE (s0 rsf mm va)) u_result_ok_retire I)
    | _ = Some (FENCE_TSO ?u, _) =>
        destruct u;
        fin (finish_unchanged t mm rsf va (FENCE_TSO tt) RETIRE_SUCCESS w
              Hhv Hdf eq_refl (exec_execute_FENCE_TSO_U (s0 rsf mm va)) u_result_ok_retire I)
    | _ = Some (FENCEI ?p, _) =>
        destruct p as [[imm i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged t mm rsf va (FENCEI (imm, Regidx i1, Regidx ird)) RETIRE_SUCCESS w
              Hhv Hdf eq_refl (exec_execute_FENCEI_U imm i1 ird (s0 rsf mm va)) u_result_ok_retire I)
    | _ = Some (FENCE ?p, _) =>
        destruct p as [[[[fm pred] succ] i1] ird]; destruct i1 as [i1]; destruct ird as [ird];
        fin (finish_unchanged t mm rsf va (FENCE (fm, pred, succ, Regidx i1, Regidx ird))
              RETIRE_SUCCESS w Hhv Hdf eq_refl
              (exec_execute_FENCE_total_U fm pred succ i1 ird (s0 rsf mm va) Lcp0) u_result_ok_retire I)
    (* --- memory families: the section Variables (width threaded from Hdi) --- *)
    | _ = Some (LOAD ?p, _) =>
        destruct p as [[[[imm rs1] rd] us] width]; cbn [decodable_u] in Hdi;
        finm (arm_LOAD_u t mm rsf va mi w imm rs1 rd us width
                Hcfg_full Hag (width_ok1248_cases width Hdi) Hdf)
    | _ = Some (STORE ?p, _) =>
        destruct p as [[[imm rs2] rs1] width]; cbn [decodable_u] in Hdi;
        finm (arm_STORE_u t mm rsf va mi w imm rs2 rs1 width
                Hcfg_full Hag (width_ok1248_cases width Hdi) Hdf)
    | _ = Some (AMO ?p, _) =>
        destruct p as [[[[[[op aq] rl] rs2] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_AMO_u t mm rsf va mi w op aq rl rs2 rs1 rd width
                Hcfg_full Hag (awidth_ok_cases width Hdi) Hdf)
    | _ = Some (LOADRES ?p, _) =>
        destruct p as [[[[aq rl] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_LOADRES_u t mm rsf va mi w aq rl rs1 width rd
                Hcfg_full Hag (lrsc_width_valid_cases width Hdi) Hdf)
    | _ = Some (STORECON ?p, _) =>
        destruct p as [[[[[aq rl] rs2] rs1] width] rd]; cbn [decodable_u] in Hdi;
        finm (arm_STORECON_u t mm rsf va mi w aq rl rs2 rs1 width rd
                Hcfg_full Hag (lrsc_width_valid_cases width Hdi) Hdf)
    | _ = Some (ZICBOP ?p, _) =>
        finm (arm_ZICBOP_u t mm rsf va mi w p Hcfg_full Hag Hdf Hhv)
    end.
  Qed.

  Lemma rvc_exec_total_u_holds (va : mword 64) (mi : bool) :
    rvc_exec_total_u pt va mi.
  Proof.
    unfold rvc_exec_total_u.
    intros h rsf t mm Hcfg Hpins Hwf.
    pose proof Hcfg as Hcfg_full.
    destruct Hcfg as (Lpc & Lcp & Hmsok & Lmenv & Hva2 & Lmi).
    pose proof Hpins as Hpins2.
    destruct Hpins2 as (Hhwp & Hcfgp & _ & _).
    assert (Hag : agree_on D_u (u_state rsf mm) dstateU)
      by exact (u_agree_decode rsf mm Lcp Lmenv Hhwp Hcfgp).
    pose proof (u_agree_tick rsf mm va 2 Hag) as Hag0.
    destruct Hhwp as (Lmisaf & Lsecf & Lsenvf & Lhtiff & Lpmaf & Lelpf).
    assert (Lcp0 : register_lookup cur_privilege (s2r rsf va) = User)
      by (apply (s2_reg cur_privilege User rsf va eq_refl); exact Lcp).
    assert (Lpc0 : register_lookup PC (s2r rsf va) = va)
      by (apply (s2_reg (R_bitvector_64 PC) va rsf va eq_refl); exact Lpc).
    assert (Lmenv0 : register_lookup menvcfg (s2r rsf va) = MENVCFG_S)
      by (apply (s2_reg menvcfg MENVCFG_S rsf va eq_refl); exact Lmenv).
    assert (Lmisa0 : register_lookup misa (s2r rsf va) = MISA_C)
      by (apply (s2_reg misa MISA_C rsf va eq_refl); exact Lmisaf).
    assert (Lsenv0 : register_lookup senvcfg (s2r rsf va)
                     = (mword_of_int 0 : mword 64))
      by (apply (s2_reg senvcfg _ rsf va eq_refl); exact Lsenvf).
    assert (Hmsok0 : user_mstatus_ok (register_lookup mstatus (s2r rsf va))).
    { rewrite (s2_reg mstatus (register_lookup mstatus rsf) rsf va eq_refl
                 eq_refl). exact Hmsok. }
    assert (Hzcaf : exec (currentlyEnabled Ext_Zca) (u_state rsf mm)
                    = Some (true, u_state rsf mm))
      by exact (s0_zca (u_state rsf mm) Lmisaf).
    destruct (decode_total_c_set h) as (i & Hdi & Hdf0).
    pose proof (u_hval_rvc rsf mm h i Hag (Hdf0 dstateU (fun r _ => eq_refl)))
      as Hhv.
    pose proof (Hdf0 (u_state rsf mm) Hag) as Hdf. clear Hdf0.
    destruct i; try (cbn in Hdi; discriminate).
    all: lazymatch type of Hdf with
    (* --- RVC DIRECT (no ExecuteAs) --- *)
    | _ = Some (C_NOP ?g6, _) =>
        fin (finish_rvc_direct t mm rsf va (C_NOP g6) RETIRE_SUCCESS h
              Hhv Hdf Hzcaf (exec_execute_C_NOP g6 (s2 rsf mm va)) u_result_ok_retire I)
    | _ = Some (C_NTL ?nt, _) =>
        fin (finish_rvc_direct t mm rsf va (C_NTL nt) RETIRE_SUCCESS h
              Hhv Hdf Hzcaf (exec_execute_C_NTL nt (s2 rsf mm va)) u_result_ok_retire I)
    | _ = Some (ZCMOP ?m3, _) =>
        fin (finish_rvc_direct t mm rsf va (ZCMOP m3) RETIRE_SUCCESS h
              Hhv Hdf Hzcaf (exec_execute_ZCMOP m3 (s2 rsf mm va)) u_result_ok_retire I)
    | _ = Some (C_ILLEGAL ?w16, _) =>
        fin (finish_rvc_direct t mm rsf va (C_ILLEGAL w16) (Illegal_Instruction tt) h
              Hhv Hdf Hzcaf (exec_execute_C_ILLEGAL w16 (s2 rsf mm va)) u_result_ok_illegal I)
    | _ = Some (C_NOT ?c, _) =>
        let H := fresh in destruct (exec_execute_C_NOT_total c (s2 rsf mm va)) as (? & ? & ? & H);
        fin (finish_rvc_direct_gprwrite t mm rsf va (C_NOT c) _ _ h Hhv Hdf Hzcaf H)
    | _ = Some (C_ZEXT_B ?c, _) =>
        let H := fresh in destruct (exec_execute_C_ZEXT_B_total c (s2 rsf mm va)) as (? & ? & ? & H);
        fin (finish_rvc_direct_gprwrite t mm rsf va (C_ZEXT_B c) _ _ h Hhv Hdf Hzcaf H)
    (* --- RVC compute (ExecuteAs -> base gpr-write) --- *)
    | _ = Some (C_LI ?p, _) =>
        destruct p as [imm rd]; destruct rd as [rd];
        fin (rvc_gpr t mm rsf va (C_LI (imm, Regidx rd))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_LI imm (Regidx rd) (s2 rsf mm va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ADDI))
    | _ = Some (C_LUI ?p, _) =>
        destruct p as [imm rd]; destruct rd as [rd];
        fin (rvc_gpr t mm rsf va (C_LUI (imm, Regidx rd))
              (UTYPE (sign_extend' 20 imm, Regidx rd, LUI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_LUI imm (Regidx rd) (s2 rsf mm va))
              (exec_execute_UTYPE_total (sign_extend' 20 imm) _ LUI))
    | _ = Some (C_MV ?p, _) =>
        destruct p as [rd rs2]; destruct rd as [rd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_MV (Regidx rd, Regidx r2))
              (RTYPE (Regidx r2, zreg, Regidx rd, ADD)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_MV (Regidx rd) (Regidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ ADD))
    | _ = Some (C_ADD ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_ADD (Regidx rsd, Regidx r2))
              (RTYPE (Regidx r2, Regidx rsd, Regidx rsd, ADD)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_ADD (Regidx rsd) (Regidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ ADD))
    | _ = Some (C_ADDI ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr t mm rsf va (C_ADDI (imm, Regidx rsd))
              (ITYPE (sign_extend' 12 imm, Regidx rsd, Regidx rsd, ADDI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_ADDI imm (Regidx rsd) (s2 rsf mm va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ADDI))
    | _ = Some (C_ADDI16SP ?imm, _) =>
        fin (rvc_gpr t mm rsf va (C_ADDI16SP imm)
              (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_ADDI16SP imm (s2 rsf mm va))
              (exec_execute_ITYPE_total (caddi16sp_imm imm) _ _ ADDI))
    | _ = Some (C_ADDI4SPN ?p, _) =>
        destruct p as [rdc nzimm]; destruct rdc as [rdc];
        fin (rvc_gpr t mm rsf va (C_ADDI4SPN (Cregidx rdc, nzimm))
              (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx (Cregidx rdc), ADDI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_ADDI4SPN (Cregidx rdc) nzimm (s2 rsf mm va))
              (exec_execute_ITYPE_total (caddi4spn_imm nzimm) _ _ ADDI))
    | _ = Some (C_SLLI ?p, _) =>
        destruct p as [shamt rsd]; destruct rsd as [rsd];
        fin (rvc_gpr t mm rsf va (C_SLLI (shamt, Regidx rsd))
              (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_SLLI shamt (Regidx rsd) (s2 rsf mm va))
              (exec_execute_SHIFTIOP_total shamt _ _ SLLI))
    | _ = Some (C_SRLI ?p, _) =>
        destruct p as [shamt crsd]; destruct crsd as [crsd];
        fin (rvc_gpr t mm rsf va (C_SRLI (shamt, Cregidx crsd))
              (SHIFTIOP (shamt, creg2reg_idx (Cregidx crsd), creg2reg_idx (Cregidx crsd), SRLI)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_SRLI shamt (Cregidx crsd) (s2 rsf mm va))
              (exec_execute_SHIFTIOP_total shamt _ _ SRLI))
    | _ = Some (C_SRAI ?p, _) =>
        destruct p as [shamt rsd]; destruct rsd as [rsd];
        fin (rvc_gpr t mm rsf va (C_SRAI (shamt, Cregidx rsd))
              (SHIFTIOP (shamt, creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SRAI)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_SRAI shamt (Cregidx rsd) (s2 rsf mm va))
              (exec_execute_SHIFTIOP_total shamt _ _ SRAI))
    | _ = Some (C_ANDI ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr t mm rsf va (C_ANDI (imm, Cregidx rsd))
              (ITYPE (sign_extend' 12 imm, creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), ANDI)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_ANDI imm (Cregidx rsd) (s2 rsf mm va))
              (exec_execute_ITYPE_total (sign_extend' 12 imm) _ _ ANDI))
    | _ = Some (C_AND ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_AND (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), AND)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_AND (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ AND))
    | _ = Some (C_OR ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_OR (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), OR)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_OR (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ OR))
    | _ = Some (C_XOR ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_XOR (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), XOR)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_XOR (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ XOR))
    | _ = Some (C_SUB ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_SUB (Cregidx rsd, Cregidx r2))
              (RTYPE (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SUB)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_SUB (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPE_total _ _ _ SUB))
    | _ = Some (C_ADDW ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_ADDW (Cregidx rsd, Cregidx r2))
              (RTYPEW (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), ADDW)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_ADDW (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPEW_total _ _ _ ADDW))
    | _ = Some (C_SUBW ?p, _) =>
        destruct p as [rsd rs2]; destruct rsd as [rsd]; destruct rs2 as [r2];
        fin (rvc_gpr t mm rsf va (C_SUBW (Cregidx rsd, Cregidx r2))
              (RTYPEW (creg2reg_idx (Cregidx r2), creg2reg_idx (Cregidx rsd), creg2reg_idx (Cregidx rsd), SUBW)) _ h
              Hhv Hdf Hzcaf (exec_execute_C_SUBW (Cregidx rsd) (Cregidx r2) (s2 rsf mm va))
              (exec_execute_RTYPEW_total _ _ _ SUBW))
    | _ = Some (C_ADDIW ?p, _) =>
        destruct p as [imm rsd]; destruct rsd as [rsd];
        fin (rvc_gpr t mm rsf va (C_ADDIW (imm, Regidx rsd))
              (ADDIW (sign_extend' 12 imm, Regidx rsd, Regidx rsd)) _ h Hhv Hdf Hzcaf
              (exec_execute_C_ADDIW imm (Regidx rsd) (s2 rsf mm va))
              (exec_execute_ADDIW_total (sign_extend' 12 imm) _ _))
    | _ = Some (C_MUL ?p, _) =>
        destruct p as [rsdc rsc2]; destruct rsdc as [rsdc]; destruct rsc2 as [rsc2];
        let Hm := fresh in destruct (exec_execute_C_MUL (Cregidx rsdc) (Cregidx rsc2) (s2 rsf mm va)) as (mop & Hm);
        fin (rvc_gpr t mm rsf va (C_MUL (Cregidx rsdc, Cregidx rsc2))
              (MUL (creg2reg_idx (Cregidx rsc2), creg2reg_idx (Cregidx rsdc), creg2reg_idx (Cregidx rsdc), mop)) _ h
              Hhv Hdf Hzcaf Hm (exec_execute_MUL_total _ _ _ mop))
    (* --- RVC EBREAK (ExecuteAs -> trap) --- *)
    | _ = Some (C_EBREAK ?u, _) =>
        destruct u;
        fin (finish_rvc_unchanged t mm rsf va (C_EBREAK tt) (EBREAK tt)
              (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va)) h
              Hhv Hdf Hzcaf (exec_execute_C_EBREAK_U (s2 rsf mm va))
              (exec_execute_EBREAK_U (s2 rsf mm va) va Lcp0 Lpc0) (u_result_ok_ebreak va) I)
    (* --- RVC control flow (jump arms) --- *)
    | _ = Some (C_J ?imm, _) =>
        fin (arm_C_J t mm rsf va h imm Hhv Hag Lpc Lmisa0 Hva2 Hzcaf Hdf)
    | _ = Some (C_JR ?r, _) =>
        destruct r as [r1];
        fin (arm_C_JR t mm rsf va h r1 Hhv Hag Lcp0 Lmisa0 Lmenv0 Lsenv0 Hzcaf Hdf)
    | _ = Some (C_JALR ?r, _) =>
        destruct r as [r1];
        fin (arm_C_JALR t mm rsf va h r1 Hhv Hag Lcp0 Lmisa0 Lmenv0 Lsenv0 Hzcaf Hdf)
    | _ = Some (C_BEQZ ?p, _) =>
        destruct p as [imm rs]; destruct rs as [rsb];
        fin (arm_C_Bcc t mm rsf va h (C_BEQZ (imm, Cregidx rsb)) imm rsb BEQ
              Hhv Hag Lpc Lmisa0 Hva2 Hzcaf Hdf (exec_execute_C_BEQZ_U imm (Cregidx rsb) (s2 rsf mm va))
              (goodmb_execute_C_BEQZ_U Du_r Du_w imm (Cregidx rsb) (s2 rsf mm va)))
    | _ = Some (C_BNEZ ?p, _) =>
        destruct p as [imm rs]; destruct rs as [rsb];
        fin (arm_C_Bcc t mm rsf va h (C_BNEZ (imm, Cregidx rsb)) imm rsb BNE
              Hhv Hag Lpc Lmisa0 Hva2 Hzcaf Hdf (exec_execute_C_BNEZ imm (Cregidx rsb) (s2 rsf mm va))
              (goodmb_execute_C_BNEZ Du_r Du_w imm (Cregidx rsb) (s2 rsf mm va)))
    (* --- compressed memory: the section Variables --- *)
    | _ = Some (C_LW ?p, _) => finm (arm_C_LW_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LD ?p, _) => finm (arm_C_LD_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LWSP ?p, _) => finm (arm_C_LWSP_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LDSP ?p, _) => finm (arm_C_LDSP_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SW ?p, _) => finm (arm_C_SW_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SD ?p, _) => finm (arm_C_SD_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SWSP ?p, _) => finm (arm_C_SWSP_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SDSP ?p, _) => finm (arm_C_SDSP_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LBU ?p, _) => finm (arm_C_LBU_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LH ?p, _) => finm (arm_C_LH_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_LHU ?p, _) => finm (arm_C_LHU_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SB ?p, _) => finm (arm_C_SB_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    | _ = Some (C_SH ?p, _) => finm (arm_C_SH_u t mm rsf va mi h p Hcfg_full Hag Hdf Hhv)
    end.
  Qed.

End UserTotalU.
