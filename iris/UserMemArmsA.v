(* ====================================================================== *)
(* UserMemArmsA.v -- the THREE ATOMIC memory arms: LR, SC and AMO.        *)
(*                                                                        *)
(* Package P4b, the last three of [UserTotalU]'s frozen nineteen.  They    *)
(* differ from LOAD / STORE in exactly one structural way, and it is worth *)
(* stating up front because it is what shapes every lemma below:           *)
(*                                                                        *)
(*   AN ATOMIC ACCESS IS NEVER SPLIT ACROSS A PAGE; IT IS REFUSED.         *)
(*                                                                        *)
(* [plat_misaligned_exception] returns [None] for an ordinary load or      *)
(* store -- the model then SPLITS the access on the page boundary, which   *)
(* is why [UserMemArmsBase]'s engine is a trichotomy crossed with          *)
(* [in_one_page_dec] -- but for a reserved / conditional / atomic access   *)
(* ([res = true]) it returns [Some AccessFault], and the access faults     *)
(* before any translation happens ([UserMemAccess.plat_misaligned_lrsc]).  *)
(* So the atomic arms' case tree is SMALLER than the data arms':           *)
(*                                                                        *)
(*   misaligned          -> E_Load_Access_Fault / E_SAMO_Access_Fault,     *)
(*                          state untouched, no walk at all;              *)
(*   aligned + mapped    -> one page by construction ([in_one_page_aligned] *)
(*                          at [(k | 4096)]), so ONE walk, no straddle;    *)
(*   aligned + unmapped  -> the ordinary translate fault.                  *)
(*                                                                        *)
(* Everything else is [UserMemArmsBase]'s recipe verbatim: the access half *)
(* is [UserMemCert]'s pure composers ([u_lr_pure] / [u_sc_pure] /          *)
(* [u_amo_pure]), the execute half is [UserMemArms]' pairs, and the seam   *)
(* is [UserMemTotal.finish_mem_base].                                      *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.xv6iris_extras Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Require Import WpGpr.
Require Import HartLift HartSpan HartMemRun HartMemAsm PtBytes.
Require Import PtreeType PtTree.
Require Import UserFrame UserBytes.
Require Import UserPtTree UserExec UserClassifyAsm.
Require Import UserExecFacts UserMemArms UserMemAccess UserMemPt UserMemMis.
Require Import UserTotalU UserMemTotal UserMemClassify UserMemArmsBase.
Local Open Scope Z_scope.
Import Defs.

Require Import WpDecodeBridge DecodeTotalU.
Require Import UserMemCert MemAccessGen CommonWalk.
(* the width-16 (AMOCAS.Q) execute layer: [wpair_state], the pair-register
   reductions and the two width-16 AMO pairs *)
Require Import UserMemClassifyAmo.
Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* 0. THE LOADRES EXECUTE PAIR AT A SYMBOLIC [rd].                         *)
(*                                                                        *)
(* [UserMemArms]' [exec_execute_LOADRES_u_ok] pins [uint rd <> 0], so an   *)
(* arm built on it would owe an [rd = x0] duplicate of its whole case      *)
(* tree.  This is the same shape fix [UserMemArmsBase] made for LOAD:      *)
(* [UserExecFacts.gpr_write_state] already carries the x0 case, so ONE     *)
(* pair covers both and the certificate's footprint obligation becomes the *)
(* CONDITIONAL [Du_gpr_of_Z], which is what [goodmb_wX_bits_gpr] wants.    *)
(* ---------------------------------------------------------------------- *)
Lemma exec_execute_LOADRES_u_retire (aq rl : bool) (rs1 rd : mword 5)
    (width : Z) (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data))
          aq (andb aq rl) true) s = Some (Ok data, s') ->
  exec (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS, gpr_write_state rd (sign_extend' 64 data) s').
Proof.
  intros Hw Hvr.
  change (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)))
    with (execute_LOADRES aq rl (Regidx rs1) width (Regidx rd)).
  unfold execute_LOADRES. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (sign_extend' 64 data)) s'
                = Some (tt, gpr_write_state rd (sign_extend' 64 data) s'))
    by (rewrite (exec_wX_bits_gpr rd (sign_extend' 64 data) s'); reflexivity).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_returnM.
Qed.

Lemma goodmb_execute_LOADRES_u_retire (Dr Dw : register -> bool)
    (aq rl : bool) (rs1 rd : mword 5) (width : Z)
    (data : mword (8 * width)) (s s' : mstate) mm :
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (width <=? xlen_bytes) = true ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data))
          aq (andb aq rl) true) s = Some (Ok data, s') ->
  goodmb Dr Dw (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data))
          aq (andb aq rl) true) s mm = true ->
  goodmb Dr Dw (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))) s mm = true.
Proof.
  intros HDrd Hw Hvr Hgvr.
  change (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)))
    with (execute_LOADRES aq rl (Regidx rs1) width (Regidx rd)).
  unfold execute_LOADRES. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  assert (Hgass : goodmb Dr Dw (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s mm
                 = true) by reflexivity.
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgass Hass).
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgvr Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (sign_extend' 64 data)) s'
                = Some (tt, gpr_write_state rd (sign_extend' 64 data) s'))
    by (rewrite (exec_wX_bits_gpr rd (sign_extend' 64 data) s'); reflexivity).
  erewrite (gm_bind0 _ _ _ _ _ _ _ (goodmb_wX_bits_gpr Dr Dw rd _ s' mm HDrd) Hw2).
  apply goodmb_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* 0b. THE STORECON EXECUTE PAIR AT A SYMBOLIC [rd] -- the same shape fix.  *)
(*                                                                        *)
(* [UserMemArms]' [exec_execute_STORECON_u_ok] pins [uint rd <> 0] too, so  *)
(* without this the SC arm would owe an [rd = x0] duplicate of its whole    *)
(* case tree.  The extra step over LOADRES is the [cancel_reservation]      *)
(* between the [wX] and the [returnM]: it is a TERM axiom                   *)
(* ([ResvAxioms.cancel_reservation_term]), so it moves neither state nor    *)
(* certificate.                                                            *)
(* ---------------------------------------------------------------------- *)
Lemma exec_execute_STORECON_u_retire (aq rl : bool) (rs2 rs1 rd : mword 5)
    (width : Z) (b : bool) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  exec (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s
    = Some (Ok b, s') ->
  exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            gpr_write_state rd (zero_extend' 64 (bool_bit_forwards (negb b))) s').
Proof.
  intros Hw Hvw.
  change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_STORECON. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd)
                        (zero_extend' 64 (bool_bit_forwards (negb b)))) s'
                = Some (tt, gpr_write_state rd
                              (zero_extend' 64 (bool_bit_forwards (negb b))) s'))
    by (rewrite (exec_wX_bits_gpr rd
                   (zero_extend' 64 (bool_bit_forwards (negb b))) s'); reflexivity).
  assert (Hwc : exec (Defs.bind0 (wX_bits (Regidx rd)
                        (zero_extend' 64 (bool_bit_forwards (negb b))))
                        (cancel_reservation tt)) s'
                = Some (tt, gpr_write_state rd
                              (zero_extend' 64 (bool_bit_forwards (negb b))) s')).
  { rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_cancel_reservation. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc). apply exec_returnM.
Qed.

Lemma goodmb_execute_STORECON_u_retire (Dr Dw : register -> bool)
    (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z) (b : bool)
    (s s' : mstate) mm :
  (uint rs2 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint rs2))) = true) ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  (width <=? xlen_bytes) = true ->
  exec (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s
    = Some (Ok b, s') ->
  goodmb Dr Dw (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s mm = true ->
  goodmb Dr Dw (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    s mm = true.
Proof.
  intros HDrs2 HDrd Hw Hvw Hgvw.
  change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_STORECON. rewrite Hw.
  assert (Hass : exec (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  assert (Hgass : goodmb Dr Dw (assert_exp' true
                   "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s mm
                 = true) by reflexivity.
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgass Hass).
  erewrite gm_bind; [ | apply goodmb_rX_bits_gpr, HDrs2 | apply (exec_rX_bits_gpr rs2 s) ].
  erewrite (gm_bind _ _ _ _ _ _ _ _ Hgvw Hvw). cbn match.
  assert (Hgw2 : goodmb Dr Dw (wX_bits (Regidx rd)
                   (zero_extend' 64 (bool_bit_forwards (negb b)))) s' mm = true)
    by exact (goodmb_wX_bits_gpr Dr Dw rd _ s' mm HDrd).
  assert (Hw2 : exec (wX_bits (Regidx rd)
                        (zero_extend' 64 (bool_bit_forwards (negb b)))) s'
                = Some (tt, gpr_write_state rd
                              (zero_extend' 64 (bool_bit_forwards (negb b))) s'))
    by (rewrite (exec_wX_bits_gpr rd
                   (zero_extend' 64 (bool_bit_forwards (negb b))) s'); reflexivity).
  assert (Hwc : exec (Defs.bind0 (wX_bits (Regidx rd)
                        (zero_extend' 64 (bool_bit_forwards (negb b))))
                        (cancel_reservation tt)) s'
                = Some (tt, gpr_write_state rd
                              (zero_extend' 64 (bool_bit_forwards (negb b))) s')).
  { rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_cancel_reservation. }
  assert (Hgwc : goodmb Dr Dw (Defs.bind0 (wX_bits (Regidx rd)
                        (zero_extend' 64 (bool_bit_forwards (negb b))))
                        (cancel_reservation tt)) s' mm = true).
  { erewrite (gm_bind0 _ _ _ _ _ _ _ Hgw2 Hw2).
    apply (goodmb_cancel_reservation Dr Dw). }
  erewrite (gm_bind0 _ _ _ _ _ _ _ Hgwc Hwc). apply goodmb_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* THE THREE ACCESS-TYPE DISEQUALITIES [u_pmlen_pure] ASKS FOR.            *)
(*                                                                        *)
(* [vm_compute] CANNOT decide them at a symbolic [aq]/[rl] (or [op]): the  *)
(* generated [generic_neq] is a positive-indexed decision procedure over   *)
(* the whole [MemoryAccessType] tag, and the tag of [LoadReserved (aq, rl, *)
(* Data)] is not closed until the booleans are.  ONE [destruct] in front   *)
(* is the whole fix -- the same shape as the AMO PMA brick's (worklist     *)
(* section 15) -- and the arms then hand these in by name instead of       *)
(* carrying an [ltac:] that silently fails to reduce.                      *)
(* ---------------------------------------------------------------------- *)
Lemma u_neq_lr (aq rl : bool) :
  generic_neq (LoadReserved (aq, rl, Data)) (InstructionFetch tt) = true /\
  generic_neq (LoadReserved (aq, rl, Data)) (Load PageTableEntry) = true /\
  generic_neq (LoadReserved (aq, rl, Data)) (Store PageTableEntry) = true.
Proof. destruct aq, rl; split_and!; vm_compute; reflexivity. Qed.

Lemma u_neq_sc (aq rl : bool) :
  generic_neq (StoreConditional (aq, rl, Data)) (InstructionFetch tt) = true /\
  generic_neq (StoreConditional (aq, rl, Data)) (Load PageTableEntry) = true /\
  generic_neq (StoreConditional (aq, rl, Data)) (Store PageTableEntry) = true.
Proof. destruct aq, rl; split_and!; vm_compute; reflexivity. Qed.

Lemma u_neq_amo (op : amoop) (aq rl : bool) :
  generic_neq (Atomic (op, aq, rl, Data, Data)) (InstructionFetch tt) = true /\
  generic_neq (Atomic (op, aq, rl, Data, Data)) (Load PageTableEntry) = true /\
  generic_neq (Atomic (op, aq, rl, Data, Data)) (Store PageTableEntry) = true.
Proof. destruct op, aq, rl; split_and!; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 0c. THE TWO-GPR LANDING.                                                *)
(*                                                                        *)
(* AMOCAS.Q writes rd AND rd+1 ([UserMemClassifyAmo.wpair_state]).  Every   *)
(* landing fact the tier had was a ONE-write form -- [u_fix_gpr_state] /    *)
(* [u_tlb_gpr] / [u_mem_gpr], all over [gpr_write_state] -- and the         *)
(* one-write form is NOT an instance of the pair form: [wpair_state] is     *)
(* guarded on the OUTSIDE by [generic_neq (Regidx rd) zreg], which          *)
(* [gpr_write_state] has no counterpart for.  So these are SIBLINGS, not a  *)
(* generalization, and no landed arm changes.  The footprint side           *)
(* conditions need nothing new: [Du_gpr_of_Z] / [_r] are already index-     *)
(* generic, so they apply at [add_vec_int rd 1] unchanged.                  *)
(* ---------------------------------------------------------------------- *)
Lemma u_fix_wpair_state (rd : mword 5) (data : mword (64 * 2)) (s : mstate) :
  reg_agree_on u_Dfix (wpair_state rd data s).(sregs) s.(sregs).
Proof.
  unfold wpair_state.
  destruct (generic_neq (Regidx rd) zreg); [ | apply u_fix_refl ]. cbv zeta.
  destruct (Z.eqb (uint rd) 0) eqn:H0;
    destruct (Z.eqb (uint (add_vec_int rd 1)) 0) eqn:H1.
  - apply u_fix_refl.
  - rewrite sregs_set_reg. apply u_fix_gpr, Z.eqb_neq, H1.
  - rewrite sregs_set_reg. apply u_fix_gpr, Z.eqb_neq, H0.
  - eapply u_fix_trans.
    + rewrite sregs_set_reg. apply u_fix_gpr, Z.eqb_neq, H1.
    + rewrite sregs_set_reg. apply u_fix_gpr, Z.eqb_neq, H0.
Qed.

Lemma u_tlb_wpair (rd : mword 5) (data : mword (64 * 2)) (s : mstate) :
  register_lookup tlb (wpair_state rd data s).(sregs)
    = register_lookup tlb s.(sregs).
Proof.
  unfold wpair_state.
  destruct (generic_neq (Regidx rd) zreg); [ | reflexivity ]. cbv zeta.
  destruct (Z.eqb (uint rd) 0); destruct (Z.eqb (uint (add_vec_int rd 1)) 0).
  - reflexivity.
  - rewrite sregs_set_reg. apply u_tlb_irr. reflexivity.
  - rewrite sregs_set_reg. apply u_tlb_irr. reflexivity.
  - rewrite sregs_set_reg.
    etransitivity; [ apply u_tlb_irr; reflexivity | ].
    rewrite sregs_set_reg. apply u_tlb_irr. reflexivity.
Qed.

Lemma u_mem_wpair (rd : mword 5) (data : mword (64 * 2)) (s : mstate) :
  (wpair_state rd data s).(mem) = s.(mem).
Proof.
  unfold wpair_state.
  destruct (generic_neq (Regidx rd) zreg); [ | reflexivity ]. cbv zeta.
  destruct (Z.eqb (uint rd) 0); destruct (Z.eqb (uint (add_vec_int rd 1)) 0);
    repeat rewrite mem_set_reg; reflexivity.
Qed.

(* [UserMemArms]' AMO post-state IS [gpr_write_state]; the two names differ
   only in where the [regval_into_reg] coercion is spelled. *)
Lemma wgpr_is_gpr_write (rd : mword 5) (v : mword 64) (s : mstate) :
  wgpr_state rd v s = gpr_write_state rd v s.
Proof. reflexivity. Qed.

Section UserMemArmsA.
  Context (pt : uptd).

  Local Notation s0r rsf va := (register_set nextPC (add_vec_int va 4) rsf).
  Local Notation s0 rsf mm va :=
    (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).
  (* the AMO effective address, spelled EXACTLY as [execute_AMO] builds it
     (offset [zeros' 64], off the TICKED file) -- a Notation, not a
     Definition: an intermediate address behind a Definition is a conversion
     bomb against the execute lemmas' premises *)
  Local Notation eav rsf mm va ir1 :=
    (add_vec (if Z.eqb (uint ir1) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir1)))
                     (u_state (register_set nextPC (add_vec_int va 4) rsf) mm).(sregs))
             (zeros' 64)).

  (* ------------------------------------------------------------------- *)
  (* 1. THE TRANSLATION-EXCEPTION FLAVOURS, at the three atomic accesses.  *)
  (* [translationException] maps LoadReserved to the LOAD page fault and   *)
  (* StoreConditional / Atomic to the SAMO one (rv64d.v l.24511 ff).       *)
  (* ------------------------------------------------------------------- *)
  Lemma u_texc_lr (aq rl : bool) (s : mstate) :
    exec (translationException (LoadReserved (aq, rl, Data)) (PTW_Invalid_Addr tt)) s
      = Some (E_Load_Page_Fault tt, s)
    /\ exec (translationException (LoadReserved (aq, rl, Data)) (PTW_Invalid_PTE tt)) s
      = Some (E_Load_Page_Fault tt, s)
    /\ exec (translationException (LoadReserved (aq, rl, Data)) (PTW_No_Permission tt)) s
      = Some (E_Load_Page_Fault tt, s).
  Proof. split_and!; unfold translationException; cbn match; apply exec_returnm. Qed.

  Lemma u_texc_sc (aq rl : bool) (s : mstate) :
    exec (translationException (StoreConditional (aq, rl, Data)) (PTW_Invalid_Addr tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (StoreConditional (aq, rl, Data)) (PTW_Invalid_PTE tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (StoreConditional (aq, rl, Data)) (PTW_No_Permission tt)) s
      = Some (E_SAMO_Page_Fault tt, s).
  Proof. split_and!; unfold translationException; cbn match; apply exec_returnm. Qed.

  Lemma u_texc_amo (op : amoop) (aq rl : bool) (s : mstate) :
    exec (translationException (Atomic (op, aq, rl, Data, Data)) (PTW_Invalid_Addr tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (Atomic (op, aq, rl, Data, Data)) (PTW_Invalid_PTE tt)) s
      = Some (E_SAMO_Page_Fault tt, s)
    /\ exec (translationException (Atomic (op, aq, rl, Data, Data)) (PTW_No_Permission tt)) s
      = Some (E_SAMO_Page_Fault tt, s).
  Proof.
    split_and!; unfold translationException; destruct op; cbn match;
      apply exec_returnm.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 2. THE LR ACCESS: [translate_and_read_value] at the reserved access.  *)
  (* [UserMemCert.u_tarv_page]'s twin -- same two-step composition, the    *)
  (* LOAD composer replaced by [u_lr_pure].                               *)
  (* ------------------------------------------------------------------- *)
  Lemma u_tarv_lr (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (w va : mword 64) (aq rl : bool) :
    0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    ud_um pt !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved (aq, rl, Data)) w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    exists (dv : mword (8 * k)) (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree),
      exec (translate_and_read_value (Virtaddr va) k (LoadReserved (aq, rl, Data))
              aq (andb aq rl) true) (u_state rs mm)
        = Some (Ok (Physaddr (u_walk_pa w va), dv), u_state rs' mm') /\
      goodmb Du_r Du_w
        (translate_and_read_value (Virtaddr va) k (LoadReserved (aq, rl, Data))
           aq (andb aq rl) true) (u_state rs mm) mm = true /\
      u_tlb_only rs rs' /\
      tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
      u_mem_step pt t t' mm mm'.
  Proof.
    intros Hk Hk8 Hkdvd Huintk Hal Hl Hleaf Hcanon Hcfg Hpins Hwf.
    destruct (u_lr_pure pt t mm rs k w va aq rl aq (andb aq rl)
                Hk Hk8 Hkdvd Huintk Hal (mem_flags_ok_amo aq rl)
                Hl Hleaf Hcanon Hcfg Hpins Hwf)
      as (dv & rs' & mm' & t' & Htr & Htrg & Hmr & Hmrg & Hfile & Htlbok' & Hstep
          & Hcfg' & Hpins' & Hwf').
    exists dv, rs', mm', t'. split_and!;
      [ exact (exec_translate_and_read_value_gen k va (u_walk_pa w va)
                 (LoadReserved (aq, rl, Data)) aq (andb aq rl) true PBMT_PMA dv
                 (u_state rs mm) (u_state rs' mm') (u_state rs' mm') Htr Hmr)
      | | exact (u_tlb_only_land rs rs' Hfile) | exact Htlbok' | exact Hstep ].
    apply (goodmb_translate_and_read_value_gen Du_r Du_w k va (u_walk_pa w va)
             (LoadReserved (aq, rl, Data)) aq (andb aq rl) true PBMT_PMA dv
             (u_state rs mm) (u_state rs' mm') (u_state rs' mm') mm Htr Htrg Hmr).
    rewrite (goodmb_dom Du_r Du_w _ (u_state rs' mm') mm mm').
    - exact Hmrg.
    - symmetry. exact (u_mem_step_dom pt t t' mm mm' Hwf Hstep).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 3. THE LR CASE TREE, at the [vmem_read_addr] level.                  *)
  (* Three arms, not seven: an unaligned reserved access is REFUSED, so    *)
  (* there is no straddle to consider (see the file header).              *)
  (* ------------------------------------------------------------------- *)
  Lemma u_vmem_read_lr_pure (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) (aq rl : bool) :
    0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    (exists (dv : mword (8 * k)) (rs' : regstate) (mm' : PtBytes.pamap)
            (t' : ptree),
        exec (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data))
                aq (andb aq rl) true) (u_state rs mm)
          = Some (Ok dv, u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data))
                aq (andb aq rl) true) (u_state rs mm) mm = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm')
    \/ (exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree)
               (e : ExceptionType) (xv pcx : mword 64),
        exec (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data))
                aq (andb aq rl) true) (u_state rs mm)
          = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
                  u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data))
                aq (andb aq rl) true) (u_state rs mm) mm = true
        /\ user_exc e = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm').
  Proof.
    intros Hk Hk8 Hkdvd Huintk Hcfg Hpins Hwf.
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & Hacc & _ & _).
    pose proof Hpins as (_ & _ & _ & Htlb0).
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal; last first.
    - (* MISALIGNED: refused before any walk, state untouched *)
      right. exists rs, mm, t, (E_Load_Access_Fault tt), va,
             (register_lookup PC rs).
      split_and!;
        [ exact (exec_vmem_read_addr_misaligned_lr va (register_lookup PC rs) k
                   aq rl aq (andb aq rl) User (u_state rs mm) Hal Lcp eq_refl)
        | exact (goodmb_vmem_read_addr_misaligned_lr Du_r Du_w va
                   (register_lookup PC rs) k aq rl aq (andb aq rl) User
                   (u_state rs mm) mm ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hal Lcp eq_refl)
        | vm_compute; reflexivity
        | exact (u_tlb_only_refl rs) | exact Htlb0
        | exact (u_mem_step_refl pt t mm Hwf) ].
    - (* ALIGNED: one page by construction, so one walk *)
      assert (Hin : in_one_page va k)
        by exact (in_one_page_aligned va k Hk Hkdvd Hal).
      pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin)
        as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) (k, 0) mm Hsp) as Hspg.
      assert (Heff : exec (effectivePrivilege (LoadReserved (aq, rl, Data))
                       (register_lookup mstatus (u_state rs mm).(sregs))
                       (register_lookup cur_privilege (u_state rs mm).(sregs)))
                       (u_state rs mm) = Some (User, u_state rs mm)).
      { rewrite u_state_sregs Lcp.
        exact (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
                 (register_lookup mstatus rs) User (u_state rs mm) Lmprv). }
      assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (LoadReserved (aq, rl, Data))
                        (register_lookup mstatus (u_state rs mm).(sregs))
                        (register_lookup cur_privilege (u_state rs mm).(sregs)))
                        (u_state rs mm) mm = true).
      { rewrite u_state_sregs Lcp.
        exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                 (LoadReserved (aq, rl, Data)) (register_lookup mstatus rs) User
                 (u_state rs mm) mm Lmprv). }
      pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
      pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
      destruct (data_classify (LoadReserved (aq, rl, Data)) (ud_tfp pt) (ud_um pt) va
                  (or_intror (or_intror (or_intror
                     (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))
                  Hacc)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + destruct (u_tarv_lr t mm rs k w va aq rl Hk Hk8 Hkdvd Huintk Hal
                    Hum Hok Hcanon Hcfg Hpins Hwf)
          as (dv & rs' & mm' & t' & Htrv & Htrvg & Honly & Htlbok & Hstep).
        left. exists dv, rs', mm', t'. split_and!;
          [ exact (exec_vmem_read_addr_intra k va (u_walk_pa w va) dv
                     (LoadReserved (aq, rl, Data)) aq (andb aq rl) true User Sv39
                     (u_state rs mm) (u_state rs' mm') Hk Hsp (or_introl Hal)
                     Heff Htm Htrv
                     (fun _ => exec_load_reservation _ k (u_state rs' mm')))
          | exact (goodmb_vmem_read_addr_intra Du_r Du_w k va (u_walk_pa w va) dv
                     (LoadReserved (aq, rl, Data)) aq (andb aq rl) true User Sv39
                     (u_state rs mm) (u_state rs' mm') mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_introl Hal) Heff Heffg Htm Htmg Htrv Htrvg)
          | exact Honly | exact Htlbok | exact Hstep ].
      + destruct (u_fault_pair pt t mm rs (LoadReserved (aq, rl, Data))
                    (E_Load_Page_Fault tt) va
                    (or_intror (or_intror (or_intror
                       (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))
                    (proj1 (u_texc_lr aq rl (u_state rs mm)))
                    (proj1 (proj2 (u_texc_lr aq rl (u_state rs mm))))
                    (proj2 (proj2 (u_texc_lr aq rl (u_state rs mm))))
                    Hfault Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
        assert (Htrv : exec (translate_and_read_value (Virtaddr va) k
                          (LoadReserved (aq, rl, Data)) aq (andb aq rl) true)
                          (u_state rs mm)
                        = Some (Err (rv64d_types.Trap (User,
                                       make_sync_exception (E_Load_Page_Fault tt) va,
                                       register_lookup PC rs)), u_state rs mm))
          by exact (exec_translate_and_read_value_err k va
                      (LoadReserved (aq, rl, Data)) aq (andb aq rl) true
                      (E_Load_Page_Fault tt) _ (u_state rs mm) (u_state rs mm)
                      Htr Hme).
        assert (Htrvg : goodmb Du_r Du_w (translate_and_read_value (Virtaddr va) k
                          (LoadReserved (aq, rl, Data)) aq (andb aq rl) true)
                          (u_state rs mm) mm = true)
          by exact (goodmb_translate_and_read_value_err Du_r Du_w k va
                      (LoadReserved (aq, rl, Data)) aq (andb aq rl) true
                      (E_Load_Page_Fault tt) _ (u_state rs mm) (u_state rs mm) mm
                      Htrg Htr Hmeg Hme).
        right. exists rs, mm, t, (E_Load_Page_Fault tt), va,
               (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_read_addr_intra_err k va _
                     (LoadReserved (aq, rl, Data)) aq (andb aq rl) true User Sv39
                     (u_state rs mm) (u_state rs mm) Hk Hsp (or_introl Hal)
                     Heff Htm Htrv)
          | exact (goodmb_vmem_read_addr_intra_err Du_r Du_w k va _
                     (LoadReserved (aq, rl, Data)) aq (andb aq rl) true User Sv39
                     (u_state rs mm) (u_state rs mm) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_introl Hal) Heff Heffg Htm Htmg Htrv Htrvg)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 4. THE LR EXECUTE-LEVEL CLOSERS, and the arm.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma arm_lr_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (aq rl : bool) (rs1 rd : mword 5) (width : Z)
      (data : mword (8 * width)) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOADRES (aq, rl, Regidx rs1, width, Regidx rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)) rsf ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data))
            aq (andb aq rl) true) (s0 rsf mm va) = Some (Ok data, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (zeros' 64) width
            (LoadReserved (aq, rl, Data)) aq (andb aq rl) true)
            (s0 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)) RETIRE_SUCCESS w
             (gpr_write_state rd (sign_extend' 64 data) (u_state rs' mm'))
             Hdec Hhv eq_refl).
    - exact (exec_execute_LOADRES_u_retire aq rl rs1 rd width data
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOADRES_u_retire Du_r Du_w aq rl rs1 rd width data
               (s0 rsf mm va) (u_state rs' mm') mm (Du_gpr_of_Z rd) Hwok Hvr Hvg).
    - exact u_ok_retire.
    - exact I.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | ].
      rewrite u_state_sregs. exact Hland.
    - rewrite u_tlb_gpr u_state_sregs. exact Htlb.
    - rewrite u_mem_gpr u_state_mem. exact Hst.
  Qed.

  Lemma arm_lr_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (aq rl : bool) (rs1 rd : mword 5) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOADRES (aq, rl, Regidx rs1, width, Regidx rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)) rsf ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data))
            aq (andb aq rl) true) (s0 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_read (Regidx rs1) (zeros' 64) width
            (LoadReserved (aq, rl, Data)) aq (andb aq rl) true)
            (s0 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hue Hvr Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) w
             (u_state rs' mm') Hdec Hhv eq_refl).
    - exact (exec_execute_LOADRES_u_err aq rl rs1 rd width _
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvr).
    - exact (goodmb_execute_LOADRES_u_err Du_r Du_w aq rl rs1 rd width _
               (s0 rsf mm va) (u_state rs' mm') mm Hwok Hvr Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* THE ARM.  [UserTotalU]'s frozen [arm_LOADRES_u], proved. *)
  Lemma arm_LOADRES_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs1 : regidx) (width : word_width) (rd : regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (LOADRES (aq, rl, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (LOADRES (aq, rl, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hpfc Hag Hwid Hdec Hhv Hpins Hwf.
    destruct rs1 as [ir1]. destruct rd as [ird].
    assert (Hk : 0 < width) by (destruct Hwid as [-> | ->]; lia).
    assert (Hk8 : width <= 8) by (destruct Hwid as [-> | ->]; lia).
    assert (Hwok : (width <=? xlen_bytes) = true)
      by (destruct Hwid as [-> | ->]; vm_compute; reflexivity).
    assert (Hkdvd : (width | 4096))
      by (destruct Hwid as [-> | ->]; [exists 1024 | exists 512]; reflexivity).
    assert (Huintk : uint (to_bits 64 width) = width)
      by (destruct Hwid as [-> | ->]; vm_compute; reflexivity).
    pose proof (u_data_cfg_tick rsf va 4
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 4 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (LoadReserved (aq, rl, Data))
                     (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                     (s0 rsf mm va) = Some (User, s0 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data)) _ User
                  (s0 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w (effectivePrivilege (LoadReserved (aq, rl, Data))
                      (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                      (s0 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                  (LoadReserved (aq, rl, Data)) _ User (s0 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure pt t mm mm (s0r rsf va) (LoadReserved (aq, rl, Data))
                (proj1 (u_neq_lr aq rl)) (proj1 (proj2 (u_neq_lr aq rl)))
                (proj2 (proj2 (u_neq_lr aq rl))) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s0r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s0r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_read_lr_pure t mm (s0r rsf va) width
                (add_vec (if Z.eqb (uint ir1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir1)))
                                 (s0 rsf mm va).(sregs))
                         (zeros' 64))
                aq rl Hk Hk8 Hkdvd Huintk Hcfg Hpins' Hwf)
      as [ (dv & rs' & mm' & t' & Hvr & Hvrg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvr & Hvrg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_lr_retire t t' mm mm' rsf rs' va w aq rl ir1 ird width dv
               Hdec Hhv Hwok);
        [ exact (exec_vmem_read_u ir1 (zeros' 64) width
                   (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Ok dv)
                   (s0 rsf mm va) (u_state rs' mm') Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w ir1 (zeros' 64) width
                   (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Ok dv)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_lr_trap t t' mm mm' rsf rs' va w aq rl ir1 ird width e xv pcx
               Hdec Hhv Hwok Hue);
        [ exact (exec_vmem_read_u ir1 (zeros' 64) width
                   (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') Lcp Heff Hpml Htm Hvr)
        | exact (goodmb_vmem_read_u Du_r Du_w ir1 (zeros' 64) width
                   (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvr Hvrg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 5. THE SC CASE TREE, at the [vmem_write_addr] level.                  *)
  (*                                                                     *)
  (* Three arms, exactly as LR's -- but the RETIRING arm carries a BOOL    *)
  (* the tier cannot pin.  [vmem_write_addr] at [StoreConditional]        *)
  (* branches on [match_reservation paddr] AFTER the walk, and the two     *)
  (* branches call different things: held -> [mem_write_ea] then           *)
  (* [mem_write_value]; lost -> [phys_access_check] alone, with nothing    *)
  (* written.  The reservation is machine state no arm owns, so the arm    *)
  (* needs BOTH certificates -- which is what [u_sc_pure]'s fourth pair    *)
  (* supplies -- and the outcome stays existential in [b], exactly as      *)
  (* [UserMemArmsBase.u_vmem_write_pure]'s already is.  The post map       *)
  (* differs between the branches, so the [u_mem_step] handed out is the   *)
  (* one for the branch taken.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma u_vmem_write_sc_pure (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
      (k : Z) (va : mword 64) (dat : mword (8 * k)) (aq rl : bool) :
    0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k -> vmem_width k ->
    u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_wf pt t mm ->
    (exists (b : bool) (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree),
        exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data))
                (andb aq rl) rl true) (u_state rs mm)
          = Some (Ok b, u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data))
                (andb aq rl) rl true) (u_state rs mm) mm = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm')
    \/ (exists (rs' : regstate) (mm' : PtBytes.pamap) (t' : ptree)
               (e : ExceptionType) (xv pcx : mword 64),
        exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data))
                (andb aq rl) rl true) (u_state rs mm)
          = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
                  u_state rs' mm')
        /\ goodmb Du_r Du_w
             (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data))
                (andb aq rl) rl true) (u_state rs mm) mm = true
        /\ user_exc e = true
        /\ u_tlb_only rs rs'
        /\ tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs')
        /\ u_mem_step pt t t' mm mm').
  Proof.
    intros Hk Hk8 Hkdvd Huintk Hvwid Hcfg Hpins Hwf.
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & Hacc & _ & _).
    pose proof Hpins as (_ & _ & _ & Htlb0).
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal; last first.
    - (* MISALIGNED: refused before any walk, state untouched *)
      right. exists rs, mm, t, (E_SAMO_Access_Fault tt), va,
             (register_lookup PC rs).
      split_and!;
        [ exact (exec_vmem_write_addr_misaligned_sc va (register_lookup PC rs) k dat
                   aq rl (andb aq rl) rl User (u_state rs mm) Hal Lcp eq_refl)
        | exact (goodmb_vmem_write_addr_misaligned_sc Du_r Du_w va
                   (register_lookup PC rs) k dat aq rl (andb aq rl) rl User
                   (u_state rs mm) mm ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hal Lcp eq_refl)
        | vm_compute; reflexivity
        | exact (u_tlb_only_refl rs) | exact Htlb0
        | exact (u_mem_step_refl pt t mm Hwf) ].
    - (* ALIGNED: one page by construction, so one walk *)
      assert (Hin : in_one_page va k)
        by exact (in_one_page_aligned va k Hk Hkdvd Hal).
      pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin)
        as Hsp.
      pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                    (u_state rs mm) (u_state rs mm) (k, 0) mm Hsp) as Hspg.
      pose proof (u_effectivePrivilege_pure (StoreConditional (aq, rl, Data))
                    rs mm Hcfg) as Heff.
      pose proof (u_goodmb_effectivePrivilege_pure (StoreConditional (aq, rl, Data))
                    rs mm mm Hcfg) as Heffg.
      pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
      pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
      destruct (data_classify (StoreConditional (aq, rl, Data)) (ud_tfp pt)
                  (ud_um pt) va
                  (or_intror (or_intror (or_intror (or_intror
                     (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))))
                  Hacc)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + destruct (u_sc_pure pt t mm rs k w va
                    (autocast (T := mword) (subrange_vec_dec dat (8 * k - 1) 0))
                    aq rl (andb aq rl) rl
                    Hk Hk8 Hkdvd Huintk Hal (wr_flags_ok_amo aq rl)
                    Hum Hok Hcanon Hcfg Hpins Hwf)
          as (rs' & mm' & mm2 & t' & Htr & Htrg & Hea & Heag0 & Hwv & Hwvg0
              & Hpace & Hpacg0 & Hfile & Htlbok & Hstep & Hstep2 & Hcfg' & Hpins').
        (* the three post-walk certificates read back at the STARTING map *)
        assert (Heag : goodmb Du_r Du_w
                  (mem_write_ea (Physaddr (u_walk_pa w va)) k
                     (StoreConditional (aq, rl, Data)) PBMT_PMA (andb aq rl) rl true)
                  (u_state rs' mm') mm = true)
          by (rewrite <- (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep); exact Heag0).
        assert (Hwvg : goodmb Du_r Du_w
                  (mem_write_value (Physaddr (u_walk_pa w va)) k
                     (autocast (T := mword) (subrange_vec_dec dat (8 * k - 1) 0))
                     (StoreConditional (aq, rl, Data)) PBMT_PMA (andb aq rl) rl true)
                  (u_state rs' mm') mm = true)
          by (rewrite <- (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep); exact Hwvg0).
        assert (Hpacg : goodmb Du_r Du_w
                  (phys_access_check (StoreConditional (aq, rl, Data)) PBMT_PMA User
                     (Physaddr (u_walk_pa w va)) k true) (u_state rs' mm') mm = true)
          by (rewrite <- (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep); exact Hpacg0).
        pose proof (u_effectivePrivilege_pure (StoreConditional (aq, rl, Data))
                      rs' mm' Hcfg') as Heff'.
        pose proof (u_goodmb_effectivePrivilege_pure (StoreConditional (aq, rl, Data))
                      rs' mm' mm Hcfg') as Heff'g.
        pose proof (exec_vmem_write_addr_sc k va (u_walk_pa w va) dat aq rl
                      (andb aq rl) rl User User Sv39 pma_ok_aligned
                      (u_state rs mm) (u_state rs' mm') (u_state rs' mm2)
                      Hvwid Hal Heff Htm Htr Hea Hwv Heff' Hpace) as Hvwa.
        pose proof (goodmb_vmem_write_addr_sc Du_r Du_w k va (u_walk_pa w va) dat
                      aq rl (andb aq rl) rl User User Sv39 pma_ok_aligned
                      (u_state rs mm) (u_state rs' mm') (u_state rs' mm2) mm
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      Hvwid Hal Heff Heffg Htm Htmg Htr Htrg Hea Heag Hwv Hwvg
                      Heff' Heff'g Hpace Hpacg) as Hvwag.
        left.
        (* [destruct] substitutes the scrutinee in [Hvwa] as well as in the
           goal, so the branch's [if] is already a redex here -- do NOT
           [rewrite Hmr in Hvwa], the LHS is gone by then. *)
        destruct (match_reservation (bits_of_physaddr (Physaddr (u_walk_pa w va))))
          eqn:Hmr; cbn match in Hvwa.
        * exists true, rs', mm2, t'. split_and!;
            [ exact Hvwa | exact Hvwag | exact (u_tlb_only_land rs rs' Hfile)
            | exact Htlbok | exact Hstep2 ].
        * exists false, rs', mm', t'. split_and!;
            [ exact Hvwa | exact Hvwag | exact (u_tlb_only_land rs rs' Hfile)
            | exact Htlbok | exact Hstep ].
      + destruct (u_fault_pair pt t mm rs (StoreConditional (aq, rl, Data))
                    (E_SAMO_Page_Fault tt) va
                    (or_intror (or_intror (or_intror (or_intror
                       (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))))
                    (proj1 (u_texc_sc aq rl (u_state rs mm)))
                    (proj1 (proj2 (u_texc_sc aq rl (u_state rs mm))))
                    (proj2 (proj2 (u_texc_sc aq rl (u_state rs mm))))
                    Hfault Hcfg Hpins Hwf) as (Htr & Htrg & Hme & Hmeg).
        right. exists rs, mm, t, (E_SAMO_Page_Fault tt), va,
               (register_lookup PC rs).
        split_and!;
          [ exact (exec_vmem_write_addr_intra_terr k va dat
                     (StoreConditional (aq, rl, Data)) (andb aq rl) rl true
                     (E_SAMO_Page_Fault tt) _ User Sv39
                     (u_state rs mm) (u_state rs mm)
                     Hk Hsp (or_introl Hal) Heff Htm Htr Hme)
          | exact (goodmb_vmem_write_addr_intra_terr Du_r Du_w k va dat
                     (StoreConditional (aq, rl, Data)) (andb aq rl) rl true
                     (E_SAMO_Page_Fault tt) _ User Sv39
                     (u_state rs mm) (u_state rs mm) mm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     Hk Hsp Hspg (or_introl Hal) Heff Heffg Htm Htmg
                     Htr Htrg Hme Hmeg)
          | vm_compute; reflexivity
          | exact (u_tlb_only_refl rs) | exact Htlb0
          | exact (u_mem_step_refl pt t mm Hwf) ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 6. THE SC EXECUTE-LEVEL CLOSERS, and the arm.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma arm_sc_retire (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z) (b : bool) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd),
              u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)) rsf ->
    (width <=? xlen_bytes) = true ->
    exec (vmem_write (Regidx rs1) (zeros' 64) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) (s0 rsf mm va)
      = Some (Ok b, u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (zeros' 64) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (StoreConditional (aq, rl, Data)) (andb aq rl) rl true)
            (s0 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))
             RETIRE_SUCCESS w
             (gpr_write_state rd (zero_extend' 64 (bool_bit_forwards (negb b)))
                (u_state rs' mm'))
             Hdec Hhv eq_refl).
    - exact (exec_execute_STORECON_u_retire aq rl rs2 rs1 rd width b
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORECON_u_retire Du_r Du_w aq rl rs2 rs1 rd width b
               (s0 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) (Du_gpr_of_Z rd) Hwok Hvw Hvg).
    - exact u_ok_retire.
    - exact I.
    - eapply u_fix_trans; [ apply u_fix_gpr_state | ].
      rewrite u_state_sregs. exact Hland.
    - rewrite u_tlb_gpr u_state_sregs. exact Htlb.
    - rewrite u_mem_gpr u_state_mem. exact Hst.
  Qed.

  Lemma arm_sc_trap (t t' : ptree) (mm mm' : PtBytes.pamap)
      (rsf rs' : regstate) (va : mword 64) (w : mword 32)
      (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
      (e : ExceptionType) (xv pcx : mword 64) :
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd),
              u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)) rsf ->
    (width <=? xlen_bytes) = true ->
    user_exc e = true ->
    exec (vmem_write (Regidx rs1) (zeros' 64) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) (s0 rsf mm va)
      = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)),
              u_state rs' mm') ->
    goodmb Du_r Du_w (vmem_write (Regidx rs1) (zeros' 64) width
            (autocast (T := mword) (subrange_vec_dec
               (if Z.eqb (uint rs2) 0 then zero_reg
                else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                       (s0r rsf va))
               (Z.sub (Z.mul width 8) 1) 0))
            (StoreConditional (aq, rl, Data)) (andb aq rl) rl true)
            (s0 rsf mm va) mm = true ->
    reg_agree_on u_Dfix rs' (s0r rsf va) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
    u_mem_step pt t t' mm mm' ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hdec Hhv Hwok Hue Hvw Hvg Hland Htlb Hst.
    apply (finish_mem_base pt t t' mm rsf va
             (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))
             (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) w
             (u_state rs' mm') Hdec Hhv eq_refl).
    - exact (exec_execute_STORECON_u_err aq rl rs2 rs1 rd width _
               (s0 rsf mm va) (u_state rs' mm') Hwok Hvw).
    - exact (goodmb_execute_STORECON_u_err Du_r Du_w aq rl rs2 rs1 rd width _
               (s0 rsf mm va) (u_state rs' mm') mm
               (fun H => Du_gpr_of_Z_r rs2 H) Hwok Hvw Hvg).
    - exact (u_ok_trap e xv pcx Hue).
    - exact I.
    - rewrite u_state_sregs. exact Hland.
    - rewrite u_state_sregs. exact Htlb.
    - rewrite u_state_mem. exact Hst.
  Qed.

  (* THE ARM.  [UserTotalU]'s frozen [arm_STORECON_u], proved. *)
  Lemma arm_STORECON_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs2 rs1 : regidx) (width : word_width) (rd : regidx) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (STORECON (aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (STORECON (aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hpfc Hag Hwid Hdec Hhv Hpins Hwf.
    destruct rs2 as [ir2]. destruct rs1 as [ir1]. destruct rd as [ird].
    assert (Hk : 0 < width) by (destruct Hwid as [-> | ->]; lia).
    assert (Hk8 : width <= 8) by (destruct Hwid as [-> | ->]; lia).
    assert (Hwok : (width <=? xlen_bytes) = true)
      by (destruct Hwid as [-> | ->]; vm_compute; reflexivity).
    assert (Hkdvd : (width | 4096))
      by (destruct Hwid as [-> | ->]; [exists 1024 | exists 512]; reflexivity).
    assert (Huintk : uint (to_bits 64 width) = width)
      by (destruct Hwid as [-> | ->]; vm_compute; reflexivity).
    assert (Hvwid : vmem_width width)
      by (destruct Hwid as [-> | ->];
          [ right; right; left | right; right; right ]; reflexivity).
    pose proof (u_data_cfg_tick rsf va 4
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 4 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    assert (Heff : exec (effectivePrivilege (StoreConditional (aq, rl, Data))
                     (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                     (s0 rsf mm va) = Some (User, s0 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data)) _ User
                  (s0 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w
                      (effectivePrivilege (StoreConditional (aq, rl, Data))
                        (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                      (s0 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                  (StoreConditional (aq, rl, Data)) _ User (s0 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure pt t mm mm (s0r rsf va) (StoreConditional (aq, rl, Data))
                (proj1 (u_neq_sc aq rl)) (proj1 (proj2 (u_neq_sc aq rl)))
                (proj2 (proj2 (u_neq_sc aq rl))) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s0r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s0r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (u_vmem_write_sc_pure t mm (s0r rsf va) width
                (add_vec (if Z.eqb (uint ir1) 0 then zero_reg
                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir1)))
                                 (s0 rsf mm va).(sregs))
                         (zeros' 64))
                (autocast (T := mword) (subrange_vec_dec
                   (if Z.eqb (uint ir2) 0 then zero_reg
                    else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir2)))
                           (s0r rsf va))
                   (Z.sub (Z.mul width 8) 1) 0))
                aq rl Hk Hk8 Hkdvd Huintk Hvwid Hcfg Hpins' Hwf)
      as [ (b & rs' & mm' & t' & Hvw & Hvwg & Honly & Htlbok & Hstep)
         | (rs' & mm' & t' & e & xv & pcx & Hvw & Hvwg & Hue & Honly & Htlbok & Hstep) ].
    - apply (arm_sc_retire t t' mm mm' rsf rs' va w aq rl ir2 ir1 ird width b
               Hdec Hhv Hwok);
        [ exact (exec_vmem_write_u ir1 (zeros' 64) width _
                   (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Ok b)
                   (s0 rsf mm va) (u_state rs' mm') Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w ir1 (zeros' 64) width _
                   (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Ok b)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
    - apply (arm_sc_trap t t' mm mm' rsf rs' va w aq rl ir2 ir1 ird width e xv pcx
               Hdec Hhv Hwok Hue);
        [ exact (exec_vmem_write_u ir1 (zeros' 64) width _
                   (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') Lcp Heff Hpml Htm Hvw)
        | exact (goodmb_vmem_write_u Du_r Du_w ir1 (zeros' 64) width _
                   (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Err _)
                   (s0 rsf mm va) (u_state rs' mm') mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hvw Hvwg)
        | exact (u_fix_of_tlb_only _ _ Honly)
        | exact Htlbok | exact Hstep ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* 7. THE AMO ARM.                                                      *)
  (*                                                                     *)
  (* THE ONLY ARM WITH NO [vmem_*] LEVEL.  [execute_AMO] inlines the       *)
  (* read-modify-write -- its own alignment check, the translate, the      *)
  (* effective-address announcement, the read, the per-op result, the      *)
  (* AMOCAS guard, the write and the [wX] -- so [UserMemArms]' five        *)
  (* execute pairs take the composer's facts DIRECTLY and the arm's case   *)
  (* tree runs at [execute].  It is still LR's three-arm tree (misaligned  *)
  (* / aligned+mapped / aligned+faulting), crossed with two further        *)
  (* splits inside the mapped arm:                                        *)
  (*                                                                     *)
  (*   the AMOCAS GUARD [op = AMOCAS && loaded <> rd] -- a boolean, not a  *)
  (*     case on the op: a mismatch writes rd and stores NOTHING;          *)
  (*   the WIDTH -- 16 takes the rs2/rd operands as register PAIRS         *)
  (*     ([UserMemClassifyAmo]'s width-16 layer) and lands on              *)
  (*     [wpair_state], hence section 0c's two-gpr landing.                *)
  (*                                                                     *)
  (* The mem-level aq/rl are NOT the access type's: the leaf reads at      *)
  (* [(aq, aq && rl)] and writes at [(aq && rl, rl)].                      *)
  (* ------------------------------------------------------------------- *)
  Lemma arm_AMO_u (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide) :
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
    exec (ext_decode w) (u_state rsf mm)
      = Some (AMO (op, aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w)
      (AMO (op, aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w.
  Proof.
    intros Hpfc Hag Hwid Hdec Hhv Hpins Hwf.
    destruct rs2 as [ir2]. destruct rs1 as [ir1]. destruct rd as [ird].
    pose proof Hwf as (md0 & _ & _ & _ & _ & _ & Hacc & _ & _).
    assert (Hk : 0 < width)
      by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]]; lia).
    assert (Hk16 : width <= 16)
      by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]]; lia).
    assert (Hw2 : (width <=? Z.mul xlen_bytes 2) = true)
      by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity).
    assert (Hkdvd : (width | 4096))
      by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]];
          [exists 4096 | exists 2048 | exists 1024 | exists 512 | exists 256];
          reflexivity).
    assert (Huintk : uint (to_bits 64 width) = width)
      by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity).
    pose proof (u_data_cfg_tick rsf va 4
                  (u_data_cfg_of_post_fetch rsf mm va mi Hpfc)) as Hcfg.
    pose proof (u_pins_tick pt t rsf va 4 Hpins) as Hpins'.
    pose proof Hcfg as (Lcp & Lms & Lmenv).
    destruct Lms as (_ & Lmprv & _).
    pose proof Hpins' as (_ & _ & _ & Htlb0).
    assert (Heff : exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data))
                     (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                     (s0 rsf mm va) = Some (User, s0 rsf mm va))
      by exact (exec_effectivePrivilege_mprv0 (Atomic (op, aq, rl, Data, Data)) _ User
                  (s0 rsf mm va) Lmprv).
    assert (Heffg : goodmb Du_r Du_w
                      (effectivePrivilege (Atomic (op, aq, rl, Data, Data))
                         (register_lookup mstatus (s0 rsf mm va).(sregs)) User)
                      (s0 rsf mm va) mm = true)
      by exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                  (Atomic (op, aq, rl, Data, Data)) _ User (s0 rsf mm va) mm Lmprv).
    destruct (u_pmlen_pure pt t mm mm (s0r rsf va) (Atomic (op, aq, rl, Data, Data))
                (proj1 (u_neq_amo op aq rl)) (proj1 (proj2 (u_neq_amo op aq rl)))
                (proj2 (proj2 (u_neq_amo op aq rl))) Hcfg Hpins') as (Hpml & Hpmlg).
    pose proof (u_translationMode_pure pt t (s0r rsf va) mm Hcfg Hpins') as Htm.
    pose proof (u_goodmb_translationMode_pure pt t (s0r rsf va) mm mm Hcfg Hpins')
      as Htmg.
    destruct (is_aligned_vaddr (Virtaddr (eav rsf mm va ir1)) width) eqn:Hal;
      last first.
    - (* MISALIGNED: refused before any walk, state untouched *)
      apply (finish_mem_base pt t t mm rsf va
               (AMO (op, aq, rl, Regidx ir2, Regidx ir1, width, Regidx ird))
               (rv64d_types.Trap (User,
                  make_sync_exception (E_SAMO_Access_Fault tt) (eav rsf mm va ir1),
                  register_lookup PC (s0r rsf va))) w
               (s0 rsf mm va) Hdec Hhv eq_refl).
      + exact (exec_execute_AMO_u_misaligned op aq rl ir2 ir1 ird width
                 (register_lookup PC (s0r rsf va)) Sv39 (s0 rsf mm va)
                 Hw2 Lcp Heff Hpml Htm eq_refl Hal).
      + exact (goodmb_execute_AMO_u_misaligned Du_r Du_w op aq rl ir2 ir1 ird width
                 (register_lookup PC (s0r rsf va)) Sv39 (s0 rsf mm va) mm
                 (fun H => Du_gpr_of_Z_r ir1 H)
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity)
                 Hw2 Lcp Heff Heffg Hpml Hpmlg Htm Htmg eq_refl Hal).
      + exact (u_ok_trap (E_SAMO_Access_Fault tt) _ _
                 ltac:(vm_compute; reflexivity)).
      + exact I.
      + rewrite u_state_sregs. apply u_fix_refl.
      + rewrite u_state_sregs. exact Htlb0.
      + rewrite u_state_mem. exact (u_mem_step_refl pt t mm Hwf).
    - (* ALIGNED: one page by construction, so one walk *)
      destruct (data_classify (Atomic (op, aq, rl, Data, Data)) (ud_tfp pt)
                  (ud_um pt) (eav rsf mm va ir1)
                  (or_intror (or_intror (or_intror (or_intror (or_intror
                     (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl))))))))
                  Hacc)
        as [ (wp & Hum & Hok & Hcanon) | Hfault ].
      + (* MAPPED *)
        destruct (u_amo_pure pt t mm (s0r rsf va) width wp (eav rsf mm va ir1)
                    op aq rl Hk Hk16 Hkdvd Huintk Hal Hum Hok Hcanon
                    Hcfg Hpins' Hwf)
          as (dv & rs' & mm' & t' & Htr & Htrg & Hea & Heag & Hrdm & Hgrdm
              & Hwrite & Hfile & Htlbok & Hstep & Hcfg' & Hpins'').
        (* the post-walk certificates read back at the STARTING map *)
        rewrite (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep) in Heag.
        rewrite (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep) in Hgrdm.
        assert (Hland : reg_agree_on u_Dfix rs' (s0r rsf va))
          by exact (u_fix_of_tlb_only _ _ (u_tlb_only_land _ _ Hfile)).
        assert (Hcase : (width <=? xlen_bytes) = true \/ width = 16)
          by (destruct Hwid as [-> | [-> | [-> | [-> | ->]]]];
              [ left | left | left | left | right ]; reflexivity).
        destruct Hcase as [Hwle | Hw16].
        * (* widths 1/2/4/8: rs2 and rd are single registers *)
          pose proof (exec_rX_bits_gpr ird (u_state rs' mm')) as Hrdv.
          destruct (andb (generic_eq op AMOCAS)
                      (neq_vec (autocast (T := mword) dv : bits (width * 8))
                         (trunc (Z.mul (__id width) 8)
                            (if Z.eqb (uint ird) 0 then zero_reg
                             else register_lookup
                                    (R_bitvector_64 (gpr_of_Z (uint ird)))
                                    (u_state rs' mm').(sregs))))) eqn:Hguard.
          -- (* AMOCAS, COMPARE MISMATCH: rd := the loaded value, no store *)
             apply (finish_mem_base pt t t' mm rsf va
                      (AMO (op, aq, rl, Regidx ir2, Regidx ir1, width, Regidx ird))
                      RETIRE_SUCCESS w
                      (wgpr_state ird
                         (sign_extend' 64
                            (autocast (T := mword) dv : bits (width * 8)))
                         (u_state rs' mm')) Hdec Hhv eq_refl).
             ++ exact (exec_execute_AMO_u_cas_ne op aq rl ir2 ir1 ird width
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         dv _ Sv39 (s0 rsf mm va) (u_state rs' mm')
                         Hwle Hw2 Hrdv Hguard Lcp Heff Hpml Htm Hal Htr Hea Hrdm).
             ++ exact (goodmb_execute_AMO_u_cas_ne Du_r Du_w op aq rl ir2 ir1 ird
                         width (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         dv _ Sv39 (s0 rsf mm va) (u_state rs' mm') mm
                         (fun H => Du_gpr_of_Z_r ir1 H)
                         (fun H => Du_gpr_of_Z_r ir2 H)
                         (fun H => Du_gpr_of_Z_r ird H) (Du_gpr_of_Z ird)
                         ltac:(vm_compute; reflexivity)
                         ltac:(vm_compute; reflexivity)
                         Hwle Hw2 Hrdv Hguard Lcp Heff Heffg Hpml Hpmlg Htm Htmg
                         Hal Htr Htrg Hea Heag Hrdm Hgrdm).
             ++ exact u_ok_retire.
             ++ exact I.
             ++ eapply u_fix_trans; [ apply u_fix_gpr_state | ].
                rewrite u_state_sregs. exact Hland.
             ++ rewrite u_tlb_gpr u_state_sregs. exact Htlbok.
             ++ rewrite u_mem_gpr u_state_mem. exact Hstep.
          -- (* the RMW stores (every non-CAS op, and a matching AMOCAS) *)
             (* [u_amo_pure] offers the write at ANY value, so the value has
                to be NAMED here -- [destruct (Hwrite _)] will not leave it as
                an evar.  It is the model's per-op result, transcribed. *)
             pose (rs2v := trunc (Z.mul (__id width) 8)
                     (if Z.eqb (uint ir2) 0 then zero_reg
                      else register_lookup (R_bitvector_64 (gpr_of_Z (uint ir2)))
                             (u_state rs' mm').(sregs)) : bits (width * 8)).
             pose (lcv := autocast (T := mword) dv : bits (width * 8)).
             destruct (Hwrite (sign_extend' (Z.mul 8 (__id width))
                        (match op with
                         | AMOSWAP => rs2v | AMOADD => add_vec rs2v lcv
                         | AMOXOR => xor_vec rs2v lcv | AMOAND => and_vec rs2v lcv
                         | AMOOR => or_vec rs2v lcv
                         | AMOMIN => if zopz0zI_s rs2v lcv then rs2v else lcv
                         | AMOMAX => if zopz0zK_s rs2v lcv then rs2v else lcv
                         | AMOMINU => if zopz0zI_u rs2v lcv then rs2v else lcv
                         | AMOMAXU => if zopz0zK_u rs2v lcv then rs2v else lcv
                         | AMOCAS => rs2v end)))
               as (mm2 & Hwv & Hwvg & Hstep2).
             apply (finish_mem_base pt t t' mm rsf va
                      (AMO (op, aq, rl, Regidx ir2, Regidx ir1, width, Regidx ird))
                      RETIRE_SUCCESS w
                      (wgpr_state ird
                         (sign_extend' 64
                            (autocast (T := mword) dv : bits (width * 8)))
                         (u_state rs' mm2)) Hdec Hhv eq_refl).
             ++ exact (exec_execute_AMO_u_store op aq rl ir2 ir1 ird width
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         dv _ Sv39 (s0 rsf mm va) (u_state rs' mm') (u_state rs' mm2)
                         Hwle Hw2 Hrdv Hguard Lcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv).
             ++ rewrite (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep) in Hwvg.
                exact (goodmb_execute_AMO_u_store Du_r Du_w op aq rl ir2 ir1 ird
                         width (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         dv _ Sv39 (s0 rsf mm va) (u_state rs' mm') (u_state rs' mm2)
                         mm
                         (fun H => Du_gpr_of_Z_r ir1 H)
                         (fun H => Du_gpr_of_Z_r ir2 H)
                         (fun H => Du_gpr_of_Z_r ird H) (Du_gpr_of_Z ird)
                         ltac:(vm_compute; reflexivity)
                         ltac:(vm_compute; reflexivity)
                         Hwle Hw2 Hrdv Hguard Lcp Heff Heffg Hpml Hpmlg Htm Htmg
                         Hal Htr Htrg Hea Heag Hrdm Hgrdm Hwv Hwvg).
             ++ exact u_ok_retire.
             ++ exact I.
             ++ eapply u_fix_trans; [ apply u_fix_gpr_state | ].
                rewrite u_state_sregs. exact Hland.
             ++ rewrite u_tlb_gpr u_state_sregs. exact Htlbok.
             ++ rewrite u_mem_gpr u_state_mem. exact Hstep2.
        * (* width 16 (AMOCAS.Q): rs2 and rd are register PAIRS *)
          subst width.
          destruct (exec_rX_pair_bits_gpr ir2 (u_state rs' mm')) as (rp & Hrp).
          destruct (exec_rX_pair_bits_gpr ird (u_state rs' mm')) as (rpd & Hrpd).
          destruct (andb (generic_eq op AMOCAS)
                      (neq_vec (autocast (T := mword) dv : bits (16 * 8))
                         (trunc (Z.mul (__id 16) 8) rpd))) eqn:Hguard.
          -- (* AMOCAS.Q, COMPARE MISMATCH *)
             apply (finish_mem_base pt t t' mm rsf va
                      (AMO (op, aq, rl, Regidx ir2, Regidx ir1, 16, Regidx ird))
                      RETIRE_SUCCESS w
                      (wpair_state ird
                         (sign_extend' (Z.mul 64 2)
                            (autocast (T := mword) dv : bits (16 * 8)))
                         (u_state rs' mm')) Hdec Hhv eq_refl).
             ++ exact (exec_execute_AMO_u_cas_ne_16 op aq rl ir2 ir1 ird
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         rp rpd dv Sv39 (s0 rsf mm va) (u_state rs' mm')
                         Lcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm).
             ++ exact (goodmb_execute_AMO_u_cas_ne_16 Du_r Du_w op aq rl ir2 ir1 ird
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         rp rpd dv Sv39 (s0 rsf mm va) (u_state rs' mm') mm
                         (fun H => Du_gpr_of_Z_r ir1 H)
                         (fun H => Du_gpr_of_Z_r ir2 H)
                         (fun H => Du_gpr_of_Z_r (add_vec_int ir2 1) H)
                         (fun H => Du_gpr_of_Z_r ird H)
                         (fun H => Du_gpr_of_Z_r (add_vec_int ird 1) H)
                         (Du_gpr_of_Z ird) (Du_gpr_of_Z (add_vec_int ird 1))
                         ltac:(vm_compute; reflexivity)
                         ltac:(vm_compute; reflexivity)
                         Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hal Htr Htrg
                         Hrp Hrpd Hguard Hea Heag Hrdm Hgrdm).
             ++ exact u_ok_retire.
             ++ exact I.
             ++ eapply u_fix_trans; [ apply u_fix_wpair_state | ].
                rewrite u_state_sregs. exact Hland.
             ++ rewrite u_tlb_wpair u_state_sregs. exact Htlbok.
             ++ rewrite u_mem_wpair u_state_mem. exact Hstep.
          -- (* AMOCAS.Q that stores *)
             pose (rs2v := trunc (Z.mul (__id 16) 8) rp : bits (16 * 8)).
             pose (lcv := autocast (T := mword) dv : bits (16 * 8)).
             destruct (Hwrite (sign_extend' (Z.mul 8 (__id 16))
                        (match op with
                         | AMOSWAP => rs2v | AMOADD => add_vec rs2v lcv
                         | AMOXOR => xor_vec rs2v lcv | AMOAND => and_vec rs2v lcv
                         | AMOOR => or_vec rs2v lcv
                         | AMOMIN => if zopz0zI_s rs2v lcv then rs2v else lcv
                         | AMOMAX => if zopz0zK_s rs2v lcv then rs2v else lcv
                         | AMOMINU => if zopz0zI_u rs2v lcv then rs2v else lcv
                         | AMOMAXU => if zopz0zK_u rs2v lcv then rs2v else lcv
                         | AMOCAS => rs2v end)))
               as (mm2 & Hwv & Hwvg & Hstep2).
             apply (finish_mem_base pt t t' mm rsf va
                      (AMO (op, aq, rl, Regidx ir2, Regidx ir1, 16, Regidx ird))
                      RETIRE_SUCCESS w
                      (wpair_state ird
                         (sign_extend' (Z.mul 64 2)
                            (autocast (T := mword) dv : bits (16 * 8)))
                         (u_state rs' mm2)) Hdec Hhv eq_refl).
             ++ exact (exec_execute_AMO_u_store_16 op aq rl ir2 ir1 ird
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         rp rpd dv Sv39 (s0 rsf mm va) (u_state rs' mm')
                         (u_state rs' mm2)
                         Lcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm Hwv).
             ++ rewrite (u_goodmb_step pt t t' mm mm' _ _ Hwf Hstep) in Hwvg.
                exact (goodmb_execute_AMO_u_store_16 Du_r Du_w op aq rl ir2 ir1 ird
                         (Physaddr (u_walk_pa wp (eav rsf mm va ir1))) PBMT_PMA
                         rp rpd dv Sv39 (s0 rsf mm va) (u_state rs' mm')
                         (u_state rs' mm2) mm
                         (fun H => Du_gpr_of_Z_r ir1 H)
                         (fun H => Du_gpr_of_Z_r ir2 H)
                         (fun H => Du_gpr_of_Z_r (add_vec_int ir2 1) H)
                         (fun H => Du_gpr_of_Z_r ird H)
                         (fun H => Du_gpr_of_Z_r (add_vec_int ird 1) H)
                         (Du_gpr_of_Z ird) (Du_gpr_of_Z (add_vec_int ird 1))
                         ltac:(vm_compute; reflexivity)
                         ltac:(vm_compute; reflexivity)
                         Lcp Heff Heffg Hpml Hpmlg Htm Htmg Hal Htr Htrg
                         Hrp Hrpd Hguard Hea Heag Hrdm Hgrdm Hwv Hwvg).
             ++ exact u_ok_retire.
             ++ exact I.
             ++ eapply u_fix_trans; [ apply u_fix_wpair_state | ].
                rewrite u_state_sregs. exact Hland.
             ++ rewrite u_tlb_wpair u_state_sregs. exact Htlbok.
             ++ rewrite u_mem_wpair u_state_mem. exact Hstep2.
      + (* UNMAPPED / DENIED: the ordinary translate fault *)
        destruct (u_fault_pair pt t mm (s0r rsf va)
                    (Atomic (op, aq, rl, Data, Data)) (E_SAMO_Page_Fault tt)
                    (eav rsf mm va ir1)
                    (or_intror (or_intror (or_intror (or_intror (or_intror
                       (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl))))))))
                    (proj1 (u_texc_amo op aq rl (s0 rsf mm va)))
                    (proj1 (proj2 (u_texc_amo op aq rl (s0 rsf mm va))))
                    (proj2 (proj2 (u_texc_amo op aq rl (s0 rsf mm va))))
                    Hfault Hcfg Hpins' Hwf) as (Htr & Htrg & _ & _).
        apply (finish_mem_base pt t t mm rsf va
                 (AMO (op, aq, rl, Regidx ir2, Regidx ir1, width, Regidx ird))
                 (rv64d_types.Trap (User,
                    make_sync_exception (E_SAMO_Page_Fault tt) (eav rsf mm va ir1),
                    register_lookup PC (s0r rsf va))) w
                 (s0 rsf mm va) Hdec Hhv eq_refl).
        * exact (exec_execute_AMO_u_translate_err op aq rl ir2 ir1 ird width
                   (E_SAMO_Page_Fault tt) (register_lookup PC (s0r rsf va)) Sv39
                   (s0 rsf mm va) (s0 rsf mm va)
                   Hw2 Lcp Heff Hpml Htm Lcp eq_refl Hal Htr).
        * exact (goodmb_execute_AMO_u_translate_err Du_r Du_w op aq rl ir2 ir1 ird
                   width (E_SAMO_Page_Fault tt) (register_lookup PC (s0r rsf va))
                   Sv39 (s0 rsf mm va) (s0 rsf mm va) mm
                   (fun H => Du_gpr_of_Z_r ir1 H)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)
                   Hw2 Lcp Heff Heffg Hpml Hpmlg Htm Htmg Lcp eq_refl Hal
                   Htr Htrg).
        * exact (u_ok_trap (E_SAMO_Page_Fault tt) _ _
                   ltac:(vm_compute; reflexivity)).
        * exact I.
        * rewrite u_state_sregs. apply u_fix_refl.
        * rewrite u_state_sregs. exact Htlb0.
        * rewrite u_state_mem. exact (u_mem_step_refl pt t mm Hwf).
  Qed.

End UserMemArmsA.

(* ====================================================================== *)
(* THE CONTRACT CHECK, MECHANICAL.                                        *)
(*                                                                        *)
(* Worklist section 15's rule: an arm's signature is long enough that a    *)
(* silent mismatch with [UserTotalU]'s frozen [Variable] would surface     *)
(* only at [ProofUser]'s instantiation, hundreds of files later.  Each     *)
(* [Definition] below states that [Variable]'s body COPIED VERBATIM and    *)
(* inhabits it with the arm, so the check is a typing judgement rather     *)
(* than an eye comparison.  They cost nothing at run time and are the      *)
(* cheapest possible regression test for the interface.                    *)
(* ====================================================================== *)
Definition arm_LOADRES_u_contract (pt : uptd) :
  forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (LOADRES (aq, rl, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (LOADRES (aq, rl, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w
  := arm_LOADRES_u pt.

Definition arm_STORECON_u_contract (pt : uptd) :
  forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (aq rl : bool) (rs2 rs1 : regidx) (width : word_width) (rd : regidx),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 4 \/ width = 8) ->
    exec (ext_decode w) (u_state rsf mm) = Some (STORECON (aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (STORECON (aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w
  := arm_STORECON_u pt.

Definition arm_AMO_u_contract (pt : uptd) :
  forall (t : ptree) (mm : PtBytes.pamap) (rsf : regstate)
      (va : mword 64) (mi : bool) (w : mword 32)
      (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide),
    post_fetch_cfg (u_state rsf mm) va mi ->
    agree_on D_u (u_state rsf mm) dstateU ->
    (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
    exec (ext_decode w) (u_state rsf mm) = Some (AMO (op, aq, rl, rs2, rs1, width, rd), u_state rsf mm) ->
    hval (u_Drw ∪ u_Dro) u_Drw rsf (ext_decode w) (AMO (op, aq, rl, rs2, rs1, width, rd)) rsf ->
    u_exec_pins pt t rsf -> u_mem_wf pt t mm ->
    base_post pt t mm rsf va w
  := arm_AMO_u pt.
