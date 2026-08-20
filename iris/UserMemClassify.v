(* ====================================================================== *)
(* UserMemClassify.v -- THE U-MODE MEMORY-FAMILY ARMS, PURE.               *)
(*                                                                        *)
(* Package P4b (claude-notes/projects/user-tier-port.md sections 9 and 14).*)
(* [UserTotalU] declares the nineteen memory arms as section [Variable]s   *)
(* with a frozen contract -- decode facts + [u_exec_pins] + [u_mem_wf] in, *)
(* [UserClassifyAsm.base_post] / [rvc_post] out -- and this file is where   *)
(* they are proved.                                                        *)
(*                                                                        *)
(* WHAT WENT, AND WHY IT COULD NOT STAY.  The pre-port file was ~4 600     *)
(* lines, almost all of it Iris composers ([mem_read_total],               *)
(* [mem_exec_load_k], the LR/SC engines, [rvc_finish_mem], ...) that       *)
(* consumed [mstate_interp] / [gen_heap_interp] / [utlb_inv_pt] /          *)
(* [udata_own] ONLY TO LEARN WHAT MEMORY HELD.  Under per-node stepping    *)
(* the hart HOLDS those bytes, the arms' contract is a pure [Prop], and an  *)
(* arm has no interpretation authority to hand such a composer -- so the    *)
(* whole apparatus is not merely redundant, it is unusable.  Its content    *)
(* survives in three places, each strictly more general: the certificates   *)
(* in [UserMemPt]/[UserMemAccess]/[UserMemMis]/[UserMemArms] (P4a), the     *)
(* pure translate/access composers in [UserMemCert] and [UserFaultCert],    *)
(* and the two closers in [UserMemTotal].  What is kept here is exactly     *)
(* the file's PURE content -- the classification of a runtime address into  *)
(* mapped / faulting ([data_classify]), the page-straddle decision          *)
(* ([in_one_page_dec]), the two translate-fault vmem reductions and the      *)
(* U-mode pointer-masking probes -- plus the arms themselves.               *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
(* for ssreflect's [rewrite /x] and [by]; nothing in this file is an [iProp] *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import UserBits.
Require Import SmodeCore.
Require Import UptTree UserPtTree.
Require Import UserExecFacts.
Require Import UserMemAccess UserMemMis.
Require Import TrampPt KptTree.
Require Import Pt4kWalk.
Require Import RiscvModelBytes.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_vmem_read_addr_translate_err (width : Z) (va pc : mword 64) (e : ExceptionType)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (priv : Privilege) (s s' : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e va, pc)), s').
Proof.
  intros Hw Halign Heff Htm Htr Hcp Hpc.
  apply (exec_vmem_read_addr_intra_err width va _ acc aq rl res ep md s s'
           (vmem_width_pos _ Hw)
           (exec_split_on_page_boundary_aligned va width s Hw Halign)
           (or_introl Halign) Heff Htm).
  unfold translate_and_read_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_memory_exception va pc e priv s' Hcp Hpc)).
  cbn match. apply exec_returnM.
Qed.

Lemma exec_vmem_write_addr_translate_err (width : Z) (va pc : mword 64) (e : ExceptionType)
    (data : mword (8*width)) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (ep : Privilege) (md : SATPMode) (priv : Privilege) (s s' : mstate) :
  vmem_width width ->
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_write_addr (Virtaddr va) width data acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e va, pc)), s').
Proof.
  intros Hw Halign Heff Htm Htr Hcp Hpc.
  exact (exec_vmem_write_addr_intra_terr width va data acc aq rl res e _ ep md s s'
           (vmem_width_pos _ Hw)
           (exec_split_on_page_boundary_aligned va width s Hw Halign)
           (or_introl Halign) Heff Htm Htr
           (exec_memory_exception va pc e priv s' Hcp Hpc)).
Qed.

Lemma exec_is_pmm_applicable_u (acc : MemoryAccessType mem_payload) (s : mstate) :
  generic_neq acc (InstructionFetch tt) = true ->
  generic_neq acc (Load PageTableEntry) = true ->
  generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable acc User) s = Some (true, s).
Proof.
  intros Hif Hlp Hsp Hmxr. unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)). rewrite Hif. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)). rewrite Hlp. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)). rewrite Hsp. cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq User Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite Hmxr. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor). cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmm_u_disabled (s : mstate) :
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (get_pmm User) s = Some (PMM_Disabled, s).
Proof.
  intros Hmisa Hmenv Hsenv. unfold get_pmm. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)).
  rewrite Hmisa.
  replace (eq_vec (_get_Misa_S MISA_C) ('b"1")) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_pinned s Hmenv Hsenv)).
  match goal with |- exec (returnM ?x) s = _ =>
    replace x with PMM_Disabled by (vm_compute; reflexivity) end.
  apply exec_returnM.
Qed.

Lemma exec_get_pmlen_u (acc : MemoryAccessType mem_payload) (s : mstate) :
  generic_neq acc (InstructionFetch tt) = true ->
  generic_neq acc (Load PageTableEntry) = true ->
  generic_neq acc (Store PageTableEntry) = true ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
  exec (get_pmlen acc User) s = Some (0, s).
Proof.
  intros Hif Hlp Hsp Hmxr Hmisa Hmenv Hsenv. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_u acc s Hif Hlp Hsp Hmxr)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmm_u_disabled s Hmisa Hmenv Hsenv)).
  apply exec_returnM.
Qed.

Definition u_data_ok (acc : MemoryAccessType mem_payload)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  exists w, um !! svpn_of va = Some w
            /\ uleaf_ok acc w
            /\ neq_vec (bits_of_virtaddr (Virtaddr va))
                 (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                    (Z.sub 39 1) 0)) = false.

Lemma data_classify (acc : MemoryAccessType mem_payload) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  u_acc acc ->
  upt_acc_wf um ->
  u_data_ok acc um va \/ u_fault_flavor acc tfp um va.
Proof.
  intros Hacc Hwf.
  unfold u_data_ok, u_fault_flavor.
  destruct (neq_vec (bits_of_virtaddr (Virtaddr va))
              (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                 (Z.sub 39 1) 0))) eqn:Hcn.
  - (* non-canonical *)
    right. left. reflexivity.
  - (* canonical *)
    destruct (decide (svpn_of va = tramp_vpn)) as [Het | Hnt].
    + right. right. right. split; [reflexivity|].
      exists pte_tramp. split.
      * unfold upt_leaf_at. left. split; [exact Het | reflexivity].
      * exact (uleaf_denied_tramp acc).
    + destruct (decide (svpn_of va = tf_vpn)) as [Hetf | Hntf].
      * right. right. right. split; [reflexivity|].
        exists (pte_tf tfp). split.
        -- unfold upt_leaf_at. right. left. split; [exact Hetf | reflexivity].
        -- exact (uleaf_denied_tf tfp acc).
      * destruct (um !! svpn_of va) as [w|] eqn:Hm.
        -- destruct (Hwf (svpn_of va) w Hm acc Hacc) as [Hok | Hden].
           ++ left. exists w. split; [reflexivity | split; [exact Hok | reflexivity]].
           ++ right. right. right. split; [reflexivity|].
              exists w. split.
              ** unfold upt_leaf_at. right. right. exact Hm.
              ** exact Hden.
        -- right. right. left. split; [reflexivity|]. split; [reflexivity|].
           split; [exact Hnt | exact Hntf].
Qed.

Definition cfg_okR (s : mstate) : Prop :=
  register_lookup misa s.(sregs) = MISA_C /\
  register_lookup menvcfg s.(sregs) = MENVCFG_S /\
  register_lookup htif_tohost_base s.(sregs) = None /\
  register_lookup cur_privilege s.(sregs) = User /\
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" /\
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false /\
  pma_allows_all (register_lookup pma_regions s.(sregs)).

Lemma cfg_okR_pres (s s' : mstate) :
  (s'.(sregs) = s.(sregs) \/ exists tv, s'.(sregs) = register_set tlb tv s.(sregs)) ->
  cfg_okR s -> cfg_okR s'.
Proof.
  intros Hd (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold cfg_okR.
  assert (Tr : forall r : register, register_beq r tlb = false ->
            register_lookup r s'.(sregs) = register_lookup r s.(sregs)).
  { intros r Hne. destruct Hd as [Heq | (tv & Heq)]; rewrite Heq;
      [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
  rewrite (Tr misa ltac:(vm_compute; reflexivity)).
  rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)).
  rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)).
  rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)).
  rewrite (Tr mstatus ltac:(vm_compute; reflexivity)).
  rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)).
  repeat split; assumption.
Qed.

Lemma in_one_page_dec (va : mword 64) (W : Z) :
  {in_one_page va W} + {~ in_one_page va W}.
Proof. unfold in_one_page. apply Z_le_dec. Qed.


Lemma zext5_concat1_3_unsigned (x : mword 1) (y : mword 3) :
  bv_unsigned (zero_extend' 5 (concat_vec x y) : mword 5)
  = bv_unsigned x * 8 + bv_unsigned y.
Proof.
  unfold zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (1 + 3)) (1 + 3)) as [e2 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e2)).
  unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned; [| cbn; lia].
  erewrite bv_concat_unsigned; [| cbn; lia].
  change (Z.of_N (MachineWord.MachineWord.Z_idx 3)) with 3.
  rewrite Z.shiftl_mul_pow2; [| lia].
  pose proof (bv_unsigned_in_range _ y) as Hy. unfold bv_modulus in Hy.
  change (MachineWord.MachineWord.Z_idx 3) with 3%N in Hy.
  change (Z.of_N 3%N) with 3 in Hy.
  change (2 ^ 3) with 8 in Hy.
  replace (bv_unsigned x * 2 ^ 3) with (bv_unsigned x * 8); [| lia].
  apply Z_lor_disjoint_add.
  change 8 with (2 ^ 3).
  apply Z_land_shift_low; [lia | change (2 ^ 3) with 8; exact Hy].
Qed.

Lemma creg_nz (i : mword 3) : uint (zero_extend' 5 (concat_vec ('b"1") i)) <> 0.
Proof.
  rewrite uint_unsigned_n. rewrite zext5_concat1_3_unsigned.
  change (bv_unsigned ('b"1" : mword 1)) with 1.
  pose proof (bv_unsigned_in_range _ i) as Hi.
  intro H. change (1 * 8) with 8 in H.
  pose proof (proj1 Hi) as H0.
  assert (He : bv_unsigned i = -8).
  { apply (Z.add_cancel_l _ _ 8). rewrite H. reflexivity. }
  rewrite He in H0. apply Z.leb_le in H0. vm_compute in H0. discriminate.
Qed.
