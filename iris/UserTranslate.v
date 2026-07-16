(* UserTranslate.v -- the translateAddr layer over [upt_inv] (UserPt.v):
   worklist item 1 of the user-execution development (see CLAUDE.md).

   GOAL (the one caller-facing interface, absorbing TLB hit-vs-miss): for an
   access [acc] at virtual address [va] from a user-phase machine state, the
   model's [translateAddr (Virtaddr va) acc] takes exactly one of

     - Ok  : [va]'s vpn is mapped, the leaf check passes and no A/D update
             is needed.  Output pa = [u_walk_pa (um_pte0 e) va] (covered by
             [u_data] via [upt_data_cov]); output state = the input with the
             tlb slot holding [um_tlb_ent vpn e] -- UNIFORMLY presented as
             the filled vector (on a hit the fill is the identity), so
             callers never split on hit/miss ([upt_tlb_ok_fill] re-seals);
     - Err : non-canonical va, unmapped vpn ([upt_unmapped_walk_fault]),
             leaf check denied ([upt_denied_walk_fault]), or A/D update
             needed (Svade: menvcfg.ADUE = 0) -- the access page-faults with
             NO state change, feeding the trap arm of the step obligation.

   This file currently holds the first pure bricks (the mode dispatch that
   every translateAddr reduction begins with); the per-access wrappers land
   on top of CommonWalk's [exec_translate_walk_user{,_nomatch,_err}].       *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGprCsrwB.
Require Import SmodePte KptPt SmodeCore.
Require Import CommonWalk UserPt.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The mode dispatch: at User with SXL = 64 and satp.Mode = Sv39, the   *)
(* MMU is in Sv39 -- the head of every translateAddr reduction.            *)
(* ===================================================================== *)

Lemma exec_get_satp_39 (satp0 : mword 64) s :
  register_lookup satp s.(sregs) = satp0 ->
  exec (get_satp 39) s = Some (autocast (T := mword) satp0, s).
Proof.
  intro Hsatp.
  unfold get_satp.
  assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                        "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
  { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
      by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  change (Z.eqb 39 32) with false. cbn match.
  unfold autocast_m.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
  rewrite Hsatp. apply exec_returnm.
Qed.

Lemma exec_satp_mode_width_39 s :
  exec (satp_mode_width_forwards Sv39) s = Some (39, s).
Proof. cbn. apply exec_returnm. Qed.

Lemma exec_assert_vmem431 s :
  exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s).
Proof.
  replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  unfold assert_exp'. cbn match. apply exec_returnm.
Qed.

Lemma exec_translationMode_U_sv39 (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  exec (translationMode User) s = Some (Sv39, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  change (generic_eq User Machine) with false. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  assert (Hae : exec (Defs.assert_exp' (Z.geb xlen 64) "sys/vmem.sail:254.25-254.26") s
                = Some (eq_refl, s)).
  { replace (Z.geb xlen 64) with true by (vm_compute; reflexivity).
    unfold assert_exp'. cbn match. apply exec_returnm. }
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hmb : exec L s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hmb).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §2 The FETCH translateAddr wrappers at User/Sv39.  The shared head:     *)
(* catch_early_return -> effectivePrivilege (= User for a fetch) ->        *)
(* translationMode (Sv39) -> not a shadow-stack access -> width/satp ->    *)
(* the canonicality test -> the mxr/do_sum mstatus reads -> translate.     *)
(* ===================================================================== *)

Local Ltac utr_head Hcp HSXL Hsatp Hmode :=
  unfold translateAddr;
  rewrite exec_catch_early_return;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus _));
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege _));
  rewrite Hcp;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ _));
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 _ _ HSXL Hsatp Hmode));
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch _));
  unfold Defs.bind0;
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity);
  rewrite execR_bind; rewrite execR_returnR; cbn match;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_satp_mode_width_39 _));
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_get_satp_39 _ _ Hsatp));
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_vmem431 _)).

(* non-canonical va: faults BEFORE the TLB or the walk; no state change,
   no memory reads, no TLB/menvcfg dependence *)
Lemma exec_translateAddr_fetch_u_noncanonical (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Err (E_Fetch_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hcanon.
  utr_head Hcp HSXL Hsatp Hmode.
  rewrite Hcanon. cbn match.
  assert (Hte : exec (translationException (InstructionFetch tt) (PTW_Invalid_Addr tt)) s
                = Some (E_Fetch_Page_Fault tt, s)).
  { unfold translationException. cbn match. apply exec_returnm. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* the walk FAULTS (invalid PTE / permission denied / A-bit needs update):
   TLB lookup misses (given), the walk errs (given), the fetch page-faults
   with NO state change.  [Hte] discharges per concrete PTW error by
   [unfold translationException; cbn match; apply exec_returnm]. *)
Lemma exec_translateAddr_fetch_u_fault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (InstructionFetch tt) User
          (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
          (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
          root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (InstructionFetch tt) f) s
    = Some (E_Fetch_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Err (E_Fetch_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
  utr_head Hcp HSXL Hsatp Hmode.
  rewrite Hcanon. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_err vpn (InstructionFetch tt) User _ _
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (InstructionFetch tt) User
                   _ _ (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* the walk SUCCEEDS from an empty slot: TLB miss -> 3-level walk (owned
   PTE reads) -> fill.  State change: the slot at [tlb_hash 39 vpn] gains
   the level-0 [u_walk_entry]. *)
Lemma exec_translateAddr_fetch_u_walk
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (va satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
  (forall mxr do_sum s0, exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (InstructionFetch tt) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va), PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  utr_head Hcp HSXL Hsatp Hmode.
  rewrite Hcanon. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user vpn root pte2 pte1 pte0 (InstructionFetch tt) User _ _
                H2i H2nl H1i H1nl H0i H0nl (Hchk0 _ _) H0N
                (mword_of_int 0) menvcfg0 tlbvec s
                Hmisa Htlb Hvec Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* same, from a COLLIDING slot (a resident non-matching entry) *)
Lemma exec_translateAddr_fetch_u_walk_nomatch
    (ent' : TLB_Entry)
    (vpn : mword 27) (root : mword 44) (pte2 pte1 pte0 : mword 64)
    (va satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                     (ext_bits_of_PTE pte2)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                     (ext_bits_of_PTE pte1)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true ->
  (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0)) s0 = Some (false, s0)) ->
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false ->
  (forall mxr do_sum s0, exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                     (ext_bits_of_PTE pte0) tt) s0 = Some (PTE_Check_Success tt, s0)) ->
  eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) vpn) = false ->
  update_PTE_Bits (autocast (T := mword) pte0 : mword 64) (InstructionFetch tt) = None ->
  exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s = Some (Ok pte2, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9))) 8) s = Some (Ok pte1, s) ->
  exec (read_pte (Physaddr (u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0))) 8) s = Some (Ok pte0, s) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (u_walk_pa pte0 va), PBMT_PMA, init_ext_ptw),
            set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                             (Some (u_walk_entry vpn pte2 pte1 pte0 (mword_of_int 0))))).
Proof.
  intros H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N Hmisa Hcp HSXL Hsatp Hmode Hasid Hppn
         Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE Hcanon Hvpn_def.
  utr_head Hcp HSXL Hsatp Hmode.
  rewrite Hcanon. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
    replace vpnx with vpn by (symmetry; exact Hvpn_def);
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_nomatch vpn root pte2 pte1 pte0 (InstructionFetch tt) User _ _
                H2i H2nl H1i H1nl H0i H0nl (Hchk0 _ _) H0N
                (mword_of_int 0) menvcfg0 ent' tlbvec s
                Hmisa Htlb Hvec Hnm Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
  cbn match.
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §3 Frame-level fetch-fault facts over [upt_inv]'s pieces: fetching      *)
(* from an unmapped or fetch-denied page faults with NO state change.      *)
(* The mxr/do_sum the walk runs at are the goal's concrete mstatus         *)
(* expressions; both fault lemmas are insensitive to them.                 *)
(* ===================================================================== *)
Section UserTranslateIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma upt_translateAddr_fetch_unmapped (pt : upt) (vpn : mword 27)
      (va usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) :
    pt.(u_map) !! vpn = None ->
    upt_unmapped_spec pt ->
    upt_tlb_ok pt.(u_map) tlbvec ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    register_lookup satp σ.(sregs) = usatp ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    upt_satp_ok pt usatp ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_slots_own pt.(u_slots) -∗
    ⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
       = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hfwf Hok Lpriv LSXL Lsatp Ltlb (Hmode & Hasid & Hppn)
             Hcanon Hvpn_def HA Hord HR Hcov Hpter) "#Hhw Hint Hslots".
    iDestruct (upt_unmapped_walk_fault pt vpn (InstructionFetch tt)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus σ.(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus σ.(sregs))) ('b"1"))
                 σ Hvpn Hfwf HA Hord HR Hcov Hpter
                 with "Hhw Hint Hslots") as %Hwalk.
    iPureIntro.
    assert (Hte : exec (translationException (InstructionFetch tt) (PTW_Invalid_PTE tt)) σ
                  = Some (E_Fetch_Page_Fault tt, σ)).
    { unfold translationException. cbn match. apply exec_returnm. }
    exact (exec_translateAddr_fetch_u_fault vpn pt.(u_root) (PTW_Invalid_PTE tt) va usatp σ
             Lpriv LSXL Lsatp Hmode Hasid Hppn
             (upt_lookup_TLB_unmapped pt.(u_map) vpn tlbvec σ Hvpn Hok Ltlb)
             Hwalk Hte Hcanon Hvpn_def).
  Qed.

  (* a MAPPED pc page whose leaf DENIES instruction fetch (X = 0 or U = 0,
     e.g. the trampoline).  Needs the vpn to also MISS the TLB -- which the
     caller has when the resident entry does not match ([upt_tlb_ok] +
     [um_tlb_ent_match_inj] handle residency in the composed trichotomy;
     if the vpn's own entry IS resident, the hit path replays the stored
     leaf's check and faults there instead -- future hit-path lemma). *)
  Lemma upt_translateAddr_fetch_denied (pt : upt) (vpn : mword 27) (e : umap_ent)
      (va usatp : mword 64) (σ : mstate) :
    pt.(u_map) !! vpn = Some e ->
    upt_map_spec pt ->
    upte_check_denied (InstructionFetch tt)
      (eq_vec (_get_Mstatus_MXR (register_lookup mstatus σ.(sregs))) ('b"1"))
      (eq_vec (_get_Mstatus_SUM (register_lookup mstatus σ.(sregs))) ('b"1"))
      (um_pte0 e) ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ) ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    register_lookup satp σ.(sregs) = usatp ->
    upt_satp_ok pt usatp ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_slots_own pt.(u_slots) -∗
    ⌜exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
       = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hspec Hden Hlk Lpriv LSXL Lsatp (Hmode & Hasid & Hppn)
             Hcanon Hvpn_def HA Hord HR Hcov Hpter) "#Hhw Hint Hslots".
    iDestruct (upt_denied_walk_fault pt vpn e (InstructionFetch tt)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus σ.(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus σ.(sregs))) ('b"1"))
                 σ Hvpn Hspec Hden HA Hord HR Hcov Hpter
                 with "Hhw Hint Hslots") as %Hwalk.
    iPureIntro.
    assert (Hte : exec (translationException (InstructionFetch tt) (PTW_No_Permission tt)) σ
                  = Some (E_Fetch_Page_Fault tt, σ)).
    { unfold translationException. cbn match. apply exec_returnm. }
    exact (exec_translateAddr_fetch_u_fault vpn pt.(u_root) (PTW_No_Permission tt) va usatp σ
             Lpriv LSXL Lsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def).
  Qed.

End UserTranslateIris.
