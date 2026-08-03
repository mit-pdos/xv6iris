(* ===================================================================== *)
(* UserMemClassify.v -- worklist item (B2): the MEMORY-family half of the  *)
(* U-mode execute totalities.                                              *)
(*                                                                         *)
(* Builds the va-generic Ok/Err data-access DISJUNCTION composer (the data *)
(* analog of the fetch classification user_pt_fetch_instr / _fetch_fault)  *)
(* and, on top of it, one arm lemma per MEMORY family that produces the    *)
(* totality's post body (base_post / rvc_post).                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile.
Require Import WpGpr UserBits.
Require Import SmodeCore.
Require Import UptTree UserPtTree UserExec UserCompute UserClassify.
Require Import UserExecFacts UserMemArms WpMmodeLeafBase.
Require Import WpGprCsrwC.
Require Import UserMemAccess UserMemPt.
Require Import TrampPt KptTree UserTranslate.
Require Import UserTotalU Pt4kWalk.
Require Import RiscvModelBytes CommonWalk WpLoad MemAmo4.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 The MISSING vmem PRIMITIVE: a translateAddr FAULT reduces to a       *)
(*    vmem_read_addr / vmem_write_addr Err (delegated Trap).  The existing *)
(*    UserMemAccess Err reductions all assume translate = Ok and the       *)
(*    mem_read / mem_write fails; here translate itself faults (the        *)
(*    page-fault path the fault head utlb_inv_pt_translateAddr_u_fault     *)
(*    produces).  A trimmed twin of exec_vmem_read_addr_aligned_err: the   *)
(*    single aligned iteration takes the [Err (e,_)] branch of the loop    *)
(*    body's translate match -> memory_exception -> early_return.          *)
(* ===================================================================== *)

Lemma exec_vmem_read_addr_translate_err (width : Z) (va pc : mword 64) (e : ExceptionType)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool) (priv : Privilege) (s s' : mstate) :
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) acc) s
    = Some (Err (e, tt), s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_read_addr (Virtaddr va) width acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros Halign Htr Hcp Hpc.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * width)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite (misaligned_order_split 1).
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s'))
  end.
  { unfold Defs.untilMT. destruct (Defs.Zwf_guarded _) as [accf]. cbn [Defs.untilMT'].
    destruct (Z_ge_dec _ 0) as [Hge|Hge]; [| cbn in Hge; exfalso; lia ].
    match goal with |- context [ Defs.bind ?bd ?k ] =>
      assert (Hbody : execR bd s = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
    { cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
      match goal with |- execR (Defs.bind ?mm ?post) s' = _ =>
        assert (Hmrm : execR mm s' = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
      { match goal with
        | |- context [ memory_exception (Virtaddr ?vv) e ] =>
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception vv pc e priv s' Hcp Hpc))
        end. cbn match.
        rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
      rewrite execR_bind. rewrite Hmrm. reflexivity. }
    rewrite execR_bind. rewrite Hbody. reflexivity. }
  rewrite execR_bind. rewrite Hu. reflexivity.
Qed.

Lemma exec_vmem_write_addr_translate_err (width : Z) (va pc : mword 64) (e : ExceptionType)
    (data : mword (8 * width)) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (priv : Privilege) (s s' : mstate) :
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) acc) s
    = Some (Err (e, tt), s') ->
  register_lookup cur_privilege s'.(sregs) = priv ->
  register_lookup PC s'.(sregs) = pc ->
  exec (vmem_write_addr (Virtaddr va) width data acc aq rl res) s
    = Some (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc)), s').
Proof.
  intros Halign Htr Hcp Hpc.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite (misaligned_order_split 1).
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s'))
  end.
  { unfold Defs.untilMT. destruct (Defs.Zwf_guarded _) as [accf]. cbn [Defs.untilMT'].
    destruct (Z_ge_dec _ 0) as [Hge|Hge]; [| cbn in Hge; exfalso; lia ].
    match goal with |- context [ Defs.bind ?bd ?k ] =>
      assert (Hbody : execR bd s = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
    { cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
      match goal with |- execR (Defs.bind ?mm ?post) s' = _ =>
        assert (Hmrm : execR mm s' = Some (inl (Err (Trap (priv, make_sync_exception e
                        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))), s')) end.
      { match goal with
        | |- context [ memory_exception (Virtaddr ?vv) e ] =>
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception vv pc e priv s' Hcp Hpc))
        end. cbn match.
        rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
      rewrite execR_bind. rewrite Hmrm. reflexivity. }
    rewrite execR_bind. rewrite Hbody. reflexivity. }
  rewrite execR_bind. rewrite Hu. reflexivity.
Qed.

(* ===================================================================== *)
(* §1 The FAULT (Err) half of the va-generic data-access composer, over   *)
(*    utlb_inv_pt -- the data analog of user_pt_fetch_fault (UserFetchPt). *)
(*    At an ALIGNED va whose translation faults (non-canonical / unmapped  *)
(*    / denied -- packaged by u_fault_flavor), the data access delegates a  *)
(*    User trap: vmem_read_addr / vmem_write_addr = Err (Trap (User, page   *)
(*    fault, pc)), state UNCHANGED (a fault writes nothing), the invariant  *)
(*    merely borrowed.  Load -> E_Load_Page_Fault, Store -> E_SAMO_Page_    *)
(*    Fault (all three PTW errors collapse to the page fault for these      *)
(*    accesses: PTW_No_Permission is NOT PTW_No_Access, so it maps through  *)
(*    the [_] arm of translationException).                                 *)
(* ===================================================================== *)
Section DataFaultComposers.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_read_addr_load_err (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pc : mword 64) (width : Z) (σ : mstate) :
    u_fault_flavor (Load Data) tfp um va ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_read_addr (Virtaddr va) width (Load Data) false false false) σ
      = Some (Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (Load Data) uroot tfp um va
                 (E_Load_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (Load Data)
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (Load Data) σ (or_intror (or_introl eq_refl)))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (Load Data)) σ
                   = Some (Err (E_Load_Page_Fault tt, tt), σ)).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))
        with (add_vec_int va (0 * width)).
      rewrite avi0. exact Htr. }
    assert (Hva : add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width) = va).
    { change (bits_of_virtaddr (Virtaddr va)) with va. apply avi0. }
    transitivity (Some ((Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt)
       (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))
       : result (mword (8 * width)) ExecutionResult), σ)).
    { exact (exec_vmem_read_addr_translate_err width va pc (E_Load_Page_Fault tt)
               (Load Data) false false false User σ σ Halign Htr' Lcp Lpc). }
    rewrite Hva. reflexivity.
  Qed.

  Lemma user_pt_vmem_write_addr_store_err (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pc : mword 64) (width : Z)
      (data : mword (8 * width)) (σ : mstate) :
    u_fault_flavor (Store Data) tfp um va ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_write_addr (Virtaddr va) width data (Store Data) false false false) σ
      = Some (Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (Store Data) uroot tfp um va
                 (E_SAMO_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (Store Data)
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (Store Data) σ
                    (or_intror (or_intror (or_introl eq_refl))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (Store Data)) σ
                   = Some (Err (E_SAMO_Page_Fault tt, tt), σ)).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))
        with (add_vec_int va (0 * width)).
      rewrite avi0. exact Htr. }
    assert (Hva : add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width) = va).
    { change (bits_of_virtaddr (Virtaddr va)) with va. apply avi0. }
    transitivity (Some ((Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt)
       (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))
       : result bool ExecutionResult), σ)).
    { exact (exec_vmem_write_addr_translate_err width va pc (E_SAMO_Page_Fault tt)
               data (Store Data) false false false User σ σ Halign Htr' Lcp Lpc). }
    rewrite Hva. reflexivity.
  Qed.

End DataFaultComposers.

(* ===================================================================== *)
(* §2 The [get_pmlen acc User = 0] BRIDGE (the concrete blocker flagged in *)
(*    the prior FRONTIER).  The U-mode memory bridges exec_vmem_{read,     *)
(*    write}_u (UserMemArms.v) demand [exec (get_pmlen acc User) s =       *)
(*    Some (0,s)].  Under the xv6 pins this holds: is_pmm_applicable needs  *)
(*    MXR=0 (from user_mstatus_ok); get_pmm User -> currentlyEnabled Ext_S  *)
(*    (=true, misa.S=1) -> read_senvcfg -> _get_SEnvcfg_PMM of the pinned   *)
(*    senvcfg=0 value = PMM_Disabled -> pmlen 0.                            *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* §3 The DATA ADDRESS CLASSIFICATION -- the data analog of fetch_classify *)
(*    (UserActiveClass.v).  For any access [acc] user execution can issue  *)
(*    and any runtime address [va], either [va] is user-mapped with a      *)
(*    leaf that PASSES the check (Ok / retire path) or it faults           *)
(*    (u_fault_flavor: non-canonical / unmapped / denied -- the Err path). *)
(*    This is the total case-split every memory arm routes on.             *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* §4 [translationMode User = Sv39] extracted from utlb_inv_pt.  The satp  *)
(*    value lives inside the invariant (Sv39-pinned); this reads it        *)
(*    NON-consumingly (pure conclusion, invariant handed back) so the      *)
(*    bridge exec_vmem_{read,write}_u's translationMode premise is         *)
(*    dischargeable while the composer still gets the invariant.           *)
(* ===================================================================== *)
Section TranslationModeU.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma utlb_inv_pt_translationMode_U (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (s : mstate) :
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    reg_interp s.(sregs) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translationMode User) s = Some (Sv39, s)⌝ ∗
    reg_interp s.(sregs) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros HSXL. iIntros "Hri Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmaw & Ht & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iSplitR.
    { iPureIntro. exact (exec_translationMode_U_sv39 usatp s HSXL Hsatpv Hmode). }
    iFrame "Hri".
    iExists usatp, tlbvec, t. iFrame "Hsatp Htlb Ht Hpmp". iPureIntro; tauto.
  Qed.

End TranslationModeU.

(* ===================================================================== *)
(* §5 The ALIGNED Ok/Err DISJUNCTION composer, width-generic, over        *)
(*    user_pt_inv -- the single reusable "Ok/Err split" every memory arm   *)
(*    routes on at an aligned runtime address.  Case-splits data_classify  *)
(*    (Load/Store Data): u_data_ok -> the UserMemAccess Ok composer        *)
(*    (retire path, state moved by TLB fill / write); u_fault_flavor ->    *)
(*    the *_err composer above (delegated User page-fault trap, state      *)
(*    unchanged).  Section mirrors UserMemAccessGeneric's k-context; the   *)
(*    width instances follow.                                              *)
(* ===================================================================== *)
Section AlignedClassify.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_plain : forall (addr : mword 64) (data : mword (8 * k)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  Lemma user_pt_vmem_read_addr_load_classify (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (va pc : mword 64) (σ : mstate) :
    upt_acc_wf um ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (dvv : mword (8 * k)) (σ' : mstate),
       ⌜exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false) σ
         = Some (Ok dvv, σ')⌝ ∗
       ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
       ⌜(σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
       reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (⌜exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false) σ
         = Some (Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), σ)⌝ ∗
       reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros Hwf Hcov Hal Hmisa Hmenv Hhtif Lpc Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    destruct (data_classify (Load Data) tfp um va (or_intror (or_introl eq_refl)) Hwf)
      as [ (w & Hum & Hok & Hcanon) | Hfault ].
    - iMod (user_pt_vmem_read_addr_load k Hk Hk8 Hkdvd Huintk Hread_plain
              uroot tfp um data w va σ
              Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
              with "Hri Hgh Hinv Hdata")
        as (dvv σ') "(%Hvr & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
      iModIntro. iLeft. iExists dvv, σ'. iFrame "Hri Hgh Hinv Hdata".
      iPureIntro. split; [exact Hvr | split; [exact Hmdev | exact Hsregs]].
    - iDestruct (user_pt_vmem_read_addr_load_err uroot tfp um va pc k σ
                   Hfault Hal Lpc Hhtif Hcp HSXL Hmprv Hall with "Hri Hgh Hinv") as %Herr.
      iModIntro. iRight. iFrame "Hri Hgh Hinv Hdata". iPureIntro. exact Herr.
  Qed.

  Lemma user_pt_vmem_write_addr_store_classify (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (va pc : mword 64) (dat : mword (8 * k)) (σ : mstate) :
    let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*k-1) (8*0*k))
              : mword (8 * k) in
    upt_acc_wf um ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (w : mword 64) (σ' : mstate),
       ⌜exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false) σ
         = Some (Ok true, MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) wv) σ'.(mdev))⌝ ∗
       ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
       ⌜(σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
       reg_interp σ'.(sregs) ∗
       gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) wv) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (⌜exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false) σ
         = Some (Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)), σ)⌝ ∗
       reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros wv Hwf Hcov Hal Hmisa Hmenv Hhtif Lpc Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    destruct (data_classify (Store Data) tfp um va
                (or_intror (or_intror (or_introl eq_refl))) Hwf)
      as [ (w & Hum & Hok & Hcanon) | Hfault ].
    - iMod (user_pt_vmem_write_addr_store k Hk Hk8 Hkdvd Huintk Hwrite_plain
              uroot tfp um data w va dat σ
              Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
              with "Hri Hgh Hinv Hdata")
        as (σ') "(%Hvw & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
      iModIntro. iLeft. iExists w, σ'. iFrame "Hri Hgh Hinv Hdata".
      iPureIntro. split; [exact Hvw | split; [exact Hmdev | exact Hsregs]].
    - iDestruct (user_pt_vmem_write_addr_store_err uroot tfp um va pc k dat σ
                   Hfault Hal Lpc Hhtif Hcp HSXL Hmprv Hall with "Hri Hgh Hinv") as %Herr.
      iModIntro. iRight. iFrame "Hri Hgh Hinv Hdata". iPureIntro. exact Herr.
  Qed.

End AlignedClassify.

(* the width instances (the names the memory arms consume) *)
Section AlignedClassifyInstances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition user_pt_vmem_read_addr_load_classify_1 :=
    user_pt_vmem_read_addr_load_classify 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) exec_read_ram_plain_1.

  Definition user_pt_vmem_write_addr_store_classify_1 :=
    user_pt_vmem_write_addr_store_classify 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) exec_write_ram_plain_1.

End AlignedClassifyInstances.

(* ===================================================================== *)
(* §6 The MISALIGNED SPLIT-WITH-FAULT read composer -- the misaligned-axis *)
(*    analog of data_classify for plain LOAD.  A misaligned plain load does *)
(*    NOT fault outright; the model SPLITS it into [N] chunks of [bytes]    *)
(*    each and faults at the FIRST straddled chunk whose translate faults.  *)
(*    [vmem_read_split_fault]: J good chunks (folded via [gbody]) then the  *)
(*    J-th chunk translate-faults ([fbody]) -> the untilMT loop early-      *)
(*    returns the User trap; state at the fault point.  Reuses the existing *)
(*    all-mapped split machinery (split_body/split_var/split_cond_false)    *)
(*    for the good prefix.                                                  *)
(* ===================================================================== *)
Lemma execR_bind_inl {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s s' (r : R) :
  execR m s = Some (inl r, s') -> execR (Defs.bind m f) s = Some (inl r, s').
Proof. intro H. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_untilMT'_fault {R Vars} (limit:Z) (vars:Vars) cond body s s' (r:R)
    (acc:Acc (Zwf 0) limit) :
  (limit >= 0)%Z ->
  execR (body vars) s = Some (inl r, s') ->
  execR (Defs.untilMT' limit vars cond body acc) s = Some (inl r, s').
Proof.
  intros Hlim Hb. destruct acc as [af]. cbn [Defs.untilMT'].
  destruct (Z_ge_dec limit 0) as [Hge|Hge]; [|lia].
  rewrite execR_bind. rewrite Hb. reflexivity.
Qed.

Lemma execR_untilMT'_chain_fault {R Vars}
    (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars) :
  forall (J:nat)(v:nat->Vars)(st:nat->mstate)(r:R)(limit0:Z)(acc:Acc (Zwf 0) limit0),
  (limit0 >= Z.of_nat J)%Z ->
  (forall k,(k<J)%nat -> execR (body (v k)) (st k) = Some (inr (v (S k)), st (S k))) ->
  (forall k,(k<J)%nat -> execR (cond (v (S k))) (st (S k)) = Some (inr false, st (S k))) ->
  execR (body (v J)) (st J) = Some (inl r, st (S J)) ->
  execR (Defs.untilMT' limit0 (v 0%nat) cond body acc) (st 0%nat) = Some (inl r, st (S J)).
Proof.
  intros J. induction J as [|J' IH]; intros v st r limit0 acc Hlim Hbody Hcondf HbodyF.
  - apply (execR_untilMT'_fault limit0 (v 0%nat) cond body (st 0%nat) (st 1%nat) r acc);
      [lia | exact HbodyF].
  - edestruct (execR_untilMT'_step limit0 (v 0%nat) (v 1%nat) cond body (st 0%nat) (st 1%nat) acc)
      as [acc' Hstep].
    + lia.
    + apply (Hbody 0%nat); lia.
    + apply (Hcondf 0%nat); lia.
    + rewrite Hstep.
      apply (IH (fun k => v (S k)) (fun k => st (S k)) r (limit0-1) acc').
      * lia.
      * intros k Hk. apply (Hbody (S k)); lia.
      * intros k Hk. apply (Hcondf (S k)); lia.
      * exact HbodyF.
Qed.

Section SplitFaultRead.
  Context (width bytes : Z) (va pc : mword 64) (acc : MemoryAccessType mem_payload)
          (aq rl : bool) (e : ExceptionType).
  Context (N J : nat) (pa : nat -> mword 64) (val : nat -> mword (8*bytes)) (st : nat -> mstate).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes) (HJ : (J < N)%nat).
  Context (Hwidth : Z.of_nat N * bytes = width).
  Notation vbits := (bits_of_virtaddr (Virtaddr va)).
  Notation RES := (result (mword (8*width)) ExecutionResult).
  Notation n := (Z.of_nat N).

  Hypothesis Htr : forall k, (k < J)%nat ->
    exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat k * bytes))) acc) (st k)
      = Some (Ok (Physaddr (pa k), PBMT_PMA, init_ext_ptw), st (S k)).
  Hypothesis Hmr : forall k, (k < J)%nat ->
    exec (mem_read acc PBMT_PMA (Physaddr (pa k)) bytes aq rl false) (st (S k))
      = Some (Ok (val k), st (S k)).
  Hypothesis HtrF : exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat J * bytes))) acc) (st J)
      = Some (Err (e, tt), st (S J)).
  Hypothesis HcpF : register_lookup cur_privilege (st (S J)).(sregs) = User.
  Hypothesis HpcF : register_lookup PC (st (S J)).(sregs) = pc.

  Notation trapval := ((Err (rv64d_types.Trap (User, make_sync_exception e
     (add_vec_int vbits (Z.of_nat J * bytes)), pc))) : RES).

  (* good body step, k<J (reproof of split_body_step with the narrower bound) *)
  Lemma gbody (k : nat) : (k < J)%nat ->
    execR (split_body width bytes va acc aq rl N (split_var bytes N val k)) (st k)
      = Some (inr (split_var bytes N val (S k)), st (S k)).
  Proof.
    intros Hk. unfold split_body, split_var.
    replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min k (N-1)) with k by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st k) = Some (@eq_refl bool true, st k)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr k Hk)).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mrm ?post) (st (S k)) = _ =>
      assert (Hmrm : execR mrm (st (S k)) = Some (inr (data_seq bytes N val (S k)), st (S k)))
    end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (Hmr k Hk)). cbn match.
      rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt (st (S k)))).
      cbn [data_seq]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
    destruct (Z.eqb (Z.of_nat k) (n-1)) eqn:Eq; cbn match;
      rewrite execR_returnR_fwd; do 3 f_equal; unfold split_var.
    - apply Z.eqb_eq in Eq.
      replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
      replace (Nat.min (S k) (N-1)) with k by lia. reflexivity.
    - apply Z.eqb_neq in Eq.
      replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.min (S k) (N-1)) with (S k) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
  Qed.

  (* fault body step at J: translate faults -> loop body early-returns the trap *)
  Lemma fbody :
    execR (split_body width bytes va acc aq rl N (split_var bytes N val J)) (st J)
      = Some (inl trapval, st (S J)).
  Proof.
    unfold split_body, split_var.
    replace (Nat.eqb J N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min J (N-1)) with J by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st J) = Some (@eq_refl bool true, st J)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ HtrF).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mm ?post) (st (S J)) = _ =>
      assert (Hmrm : execR mm (st (S J)) = Some (inl trapval, st (S J)))
    end.
    { match goal with
      | |- context [ memory_exception (Virtaddr ?vv) e ] =>
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception vv pc e User (st (S J)) HcpF HpcF))
      end. cbn match.
      rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
    rewrite execR_bind. rewrite Hmrm. reflexivity.
  Qed.


  Lemma split_loop_fault :
    execR (Defs.untilMT (zeros' (8 * n * bytes), false, 0%Z)
             (fun '(data, finished, i) => n)
             (fun '(data, finished, i) => returnR RES finished)
             (split_body width bytes va acc aq rl N)) (st 0%nat)
      = Some (inl trapval, st (S J)).
  Proof.
    rewrite <- (split_var0 bytes N val HN Hbytes).
    unfold Defs.untilMT.
    set (L := (fun '(data, finished, i) => n) (split_var bytes N val 0%nat)).
    assert (HL : L = n) by (unfold L; rewrite (split_var0 bytes N val HN Hbytes); reflexivity).
    clearbody L. rewrite HL.
    apply (execR_untilMT'_chain_fault (fun '(data, finished, i) => returnR RES finished)
             (split_body width bytes va acc aq rl N) J (split_var bytes N val) st trapval n _).
    - lia.
    - intros k Hk. apply gbody; exact Hk.
    - intros k Hk. apply split_cond_false; lia.
    - apply fbody.
  Qed.

  Lemma vmem_read_split_fault :
    is_aligned_vaddr (Virtaddr va) width = false ->
    is_amo_access acc = false ->
    is_vector_access acc = false ->
    exec (split_misaligned (Virtaddr va) width) (st 0%nat) = Some ((n, bytes), st 0%nat) ->
    exec (vmem_read_addr (Virtaddr va) width acc aq rl false) (st 0%nat)
      = Some (trapval, st (S J)).
  Proof.
    intros Hnal Hamo Hvec Hsplit.
    unfold vmem_read_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    match goal with
    | |- context [ Defs.bind0 ?g (Defs.liftR (split_misaligned (Virtaddr va) width)) ] =>
        set (GRD := g)
    end.
    assert (Hg : execR GRD (st 0%nat) = Some (inr tt, st 0%nat)).
    { unfold GRD.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_plat_misaligned_loadstore_none acc (st 0%nat) Hamo Hvec)).
      cbn match. apply execR_returnR_fwd. }
    assert (Hinner : execR (Defs.bind0 GRD (liftR (split_misaligned (Virtaddr va) width))) (st 0%nat)
                     = Some (inr (n, bytes), st 0%nat)).
    { rewrite (execR_bind0_Some _ _ _ _ Hg).
      rewrite execR_liftR. rewrite Hsplit. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_split. cbn match.
    rewrite (execR_bind_inl _ _ _ _ _ split_loop_fault). reflexivity.
  Qed.

End SplitFaultRead.

(* ===================================================================== *)
(* §7 The MISALIGNED SPLIT-WITH-FAULT write composer -- the STORE analog   *)
(*    of §6.  Same shape: J good chunks (translate+ea+value succeed, folded *)
(*    via [wgbody]) then chunk J translate-faults ([wfbody]) -> the untilMT *)
(*    write loop early-returns the User trap.                              *)
(* ===================================================================== *)
Section SplitFaultWrite.
  Context (width bytes : Z) (va pc : mword 64) (dat : mword (8*width)) (e : ExceptionType).
  Context (N J : nat) (pa : nat -> mword 64) (sk : nat -> bool) (stt st : nat -> mstate).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes) (HJ : (J < N)%nat).
  Context (Hwidth : Z.of_nat N * bytes = width).
  Notation vbits := (bits_of_virtaddr (Virtaddr va)).
  Notation RES := (result bool ExecutionResult).
  Notation n := (Z.of_nat N).

  Hypothesis Htr : forall k, (k < J)%nat ->
    exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat k * bytes))) (Store Data)) (st k)
      = Some (Ok (Physaddr (pa k), PBMT_PMA, init_ext_ptw), stt k).
  Hypothesis Hea : forall k, (k < J)%nat ->
    exec (mem_write_ea (Physaddr (pa k)) bytes false false false) (stt k) = Some (Ok tt, stt k).
  Hypothesis Hwv : forall k, (k < J)%nat ->
    exec (mem_write_value (Physaddr (pa k)) bytes (wv width bytes dat k) (Store Data) PBMT_PMA false false false) (stt k)
      = Some (Ok (sk k), st (S k)).
  Hypothesis HtrF : exec (translateAddr (Virtaddr (add_vec_int vbits (Z.of_nat J * bytes))) (Store Data)) (st J)
      = Some (Err (e, tt), st (S J)).
  Hypothesis HcpF : register_lookup cur_privilege (st (S J)).(sregs) = User.
  Hypothesis HpcF : register_lookup PC (st (S J)).(sregs) = pc.

  Notation trapvalW := ((Err (rv64d_types.Trap (User, make_sync_exception e
     (add_vec_int vbits (Z.of_nat J * bytes)), pc))) : RES).

  Lemma wgbody (k : nat) : (k < J)%nat ->
    execR (write_body width bytes va dat N (write_var N sk k)) (st k)
      = Some (inr (write_var N sk (S k)), st (S k)).
  Proof.
    intros Hk. unfold write_body, write_var.
    replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min k (N-1)) with k by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st k) = Some (@eq_refl bool true, st k)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr k Hk)).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mrm ?post) (stt k) = _ =>
      assert (Hmrm : execR mrm (stt k) = Some (inr (ws_seq sk (S k)), st (S k)))
    end.
    { assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") (stt k) = Some (tt, stt k)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") : Defs.monadR RES exception unit) (stt k) = Some (inr tt, stt k))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      rewrite (execR_bind0_Some _ _ _ _ Hscm).
      rewrite (execR_liftR_seq _ _ _ _ _ (Hea k Hk)). cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ (Hwv k Hk)). cbn match.
      cbn [ws_seq]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
    destruct (Z.eqb (Z.of_nat k) (n-1)) eqn:Eq; cbn match;
      rewrite execR_returnR_fwd; do 3 f_equal; unfold write_var.
    - apply Z.eqb_eq in Eq.
      replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
      replace (Nat.min (S k) (N-1)) with k by lia. reflexivity.
    - apply Z.eqb_neq in Eq.
      replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.min (S k) (N-1)) with (S k) by lia.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
  Qed.

  Lemma wfbody :
    execR (write_body width bytes va dat N (write_var N sk J)) (st J)
      = Some (inl trapvalW, st (S J)).
  Proof.
    unfold write_body, write_var.
    replace (Nat.eqb J N) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.min J (N-1)) with J by lia.
    cbn match.
    assert (Hass : exec (assert_exp' true "loop dummy assert") (st J) = Some (@eq_refl bool true, st J)) by reflexivity.
    rewrite (execR_liftR_seq _ _ _ _ _ Hass).
    rewrite (execR_liftR_seq _ _ _ _ _ HtrF).
    cbn match.
    match goal with
    | |- execR (Defs.bind ?mm ?post) (st (S J)) = _ =>
      assert (Hmrm : execR mm (st (S J)) = Some (inl trapvalW, st (S J)))
    end.
    { match goal with
      | |- context [ memory_exception (Virtaddr ?vv) e ] =>
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception vv pc e User (st (S J)) HcpF HpcF))
      end. cbn match.
      rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
    rewrite execR_bind. rewrite Hmrm. reflexivity.
  Qed.

  Lemma write_loop_fault :
    execR (Defs.untilMT (false, 0%Z, true)
             (fun '(finished, i, write_success) => n)
             (fun '(finished, i, write_success) => returnR RES finished)
             (write_body width bytes va dat N)) (st 0%nat)
      = Some (inl trapvalW, st (S J)).
  Proof.
    rewrite <- (write_var0 bytes N sk HN Hbytes).
    unfold Defs.untilMT.
    set (L := (fun '(finished, i, write_success) => n) (write_var N sk 0%nat)).
    assert (HL : L = n) by (unfold L; rewrite (write_var0 bytes N sk HN Hbytes); reflexivity).
    clearbody L. rewrite HL.
    apply (execR_untilMT'_chain_fault (fun '(finished, i, write_success) => returnR RES finished)
             (write_body width bytes va dat N) J (write_var N sk) st trapvalW n _).
    - lia.
    - intros k Hk. apply wgbody; exact Hk.
    - intros k Hk. apply write_cond_false; lia.
    - apply wfbody.
  Qed.

  Lemma vmem_write_split_fault :
    is_aligned_vaddr (Virtaddr va) width = false ->
    exec (split_misaligned (Virtaddr va) width) (st 0%nat) = Some ((n, bytes), st 0%nat) ->
    exec (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) (st 0%nat)
      = Some (trapvalW, st (S J)).
  Proof.
    intros Hnal Hsplit.
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    rewrite Hnal. cbn [Riscv.rv64d.not negb].
    match goal with
    | |- context [ Defs.bind0 ?g (Defs.liftR (split_misaligned (Virtaddr va) width)) ] =>
        set (GRD := g)
    end.
    assert (Hg : execR GRD (st 0%nat) = Some (inr tt, st 0%nat)).
    { unfold GRD.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_plat_misaligned_loadstore_none (Store Data) (st 0%nat) eq_refl eq_refl)).
      cbn match. apply execR_returnR_fwd. }
    assert (Hinner : execR (Defs.bind0 GRD (liftR (split_misaligned (Virtaddr va) width))) (st 0%nat)
                     = Some (inr (n, bytes), st 0%nat)).
    { rewrite (execR_bind0_Some _ _ _ _ Hg).
      rewrite execR_liftR. rewrite Hsplit. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_split. cbn match.
    rewrite (execR_bind_inl _ _ _ _ _ write_loop_fault). reflexivity.
  Qed.

End SplitFaultWrite.

(* ===================================================================== *)
(* §8 The MISALIGNED per-chunk-leaf READ classify FOLD -- the iris side of *)
(*    the total misaligned read classify.  Folds the split chunks [0,M):   *)
(*    at each chunk data_classify decides mapped-ok (run user_pt_load_data_ *)
(*    g at THAT chunk's own leaf -- handles cross-page straddling, unlike   *)
(*    split_load_fold's single-leaf assumption) or fault; returns either    *)
(*    ALL-good (translate+read facts for every chunk) or first-fault-at-j   *)
(*    (good prefix facts + u_fault_flavor at chunk j).  Feeds the all-good  *)
(*    split composer (retire) / the §6 vmem_read_split_fault (trap).        *)
(* ===================================================================== *)
Section MisReadClassify.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)) (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hread_plain : forall (addr : mword 64) (ww : mword (8 * bytes)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N bytes)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte ww j)) ->
      exec (read_ram rv64d_types.Read_plain (Physaddr addr) bytes false) s = Some ((ww, default_meta), s)).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa) (va : mword 64).
  Context (Hwf : upt_acc_wf um) (Hcov : udata_cov um data).

  Notation cva k := (add_vec_int va (Z.of_nat k * bytes)).

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

  Context (σ0 : mstate).

  Fixpoint sst (k : nat) : mstate :=
    match k with
    | O => σ0
    | S k' =>
      match exec (translateAddr (Virtaddr (cva k')) (Load Data)) (sst k') with
      | Some (Ok (Physaddr _, _, _), s') => s'
      | _ => sst k'
      end
    end.
  Definition spaR (k : nat) : mword 64 :=
    match exec (translateAddr (Virtaddr (cva k)) (Load Data)) (sst k) with
    | Some (Ok (Physaddr p, _, _), _) => p
    | _ => zeros' 64
    end.
  Definition svalR (k : nat) : mword (8 * bytes) :=
    match exec (mem_read (Load Data) PBMT_PMA (Physaddr (spaR k)) bytes false false false) (sst (S k)) with
    | Some (Ok v, _) => v
    | _ => zeros' (8 * bytes)
    end.

  Lemma read_classify_fold (M : nat) :
    (forall k, (k < M)%nat -> is_aligned_vaddr (Virtaddr (cva k)) bytes = true) ->
    cfg_okR σ0 ->
    reg_interp σ0.(sregs) -∗ gen_heap_interp σ0.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ( (⌜forall k, (k < M)%nat ->
         exec (translateAddr (Virtaddr (cva k)) (Load Data)) (sst k)
           = Some (Ok (Physaddr (spaR k), PBMT_PMA, init_ext_ptw), sst (S k))⌝ ∗
       ⌜forall k, (k < M)%nat ->
         exec (mem_read (Load Data) PBMT_PMA (Physaddr (spaR k)) bytes false false false) (sst (S k))
           = Some (Ok (svalR k), sst (S k))⌝ ∗
       ⌜(sst M).(mdev) = σ0.(mdev)⌝ ∗ ⌜cfg_okR (sst M)⌝ ∗
       ⌜register_lookup (R_bool minstret_increment) (sst M).(sregs)
          = register_lookup (R_bool minstret_increment) σ0.(sregs)⌝ ∗
       ⌜register_lookup nextPC (sst M).(sregs) = register_lookup nextPC σ0.(sregs)⌝ ∗
       reg_interp (sst M).(sregs) ∗ gen_heap_interp (sst M).(mem) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data)
     ∨ (∃ j : nat, ⌜(j < M)%nat⌝ ∗
         ⌜forall k, (k < j)%nat ->
           exec (translateAddr (Virtaddr (cva k)) (Load Data)) (sst k)
             = Some (Ok (Physaddr (spaR k), PBMT_PMA, init_ext_ptw), sst (S k))⌝ ∗
         ⌜forall k, (k < j)%nat ->
           exec (mem_read (Load Data) PBMT_PMA (Physaddr (spaR k)) bytes false false false) (sst (S k))
             = Some (Ok (svalR k), sst (S k))⌝ ∗
         ⌜u_fault_flavor (Load Data) tfp um (cva j)⌝ ∗
         ⌜cfg_okR (sst j)⌝ ∗ ⌜(sst j).(mdev) = σ0.(mdev)⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) (sst j).(sregs)
            = register_lookup (R_bool minstret_increment) σ0.(sregs)⌝ ∗
         ⌜register_lookup nextPC (sst j).(sregs) = register_lookup nextPC σ0.(sregs)⌝ ∗
         reg_interp (sst j).(sregs) ∗ gen_heap_interp (sst j).(mem) ∗
         utlb_inv_pt uroot tfp um ∗ udata_own data))%I.
  Proof.
    induction M as [|M' IH]; intros Hal Hcfg; iIntros "Hri Hgh Hinv Hdata".
    - iModIntro. iLeft. iFrame. iPureIntro.
      split; [intros; lia|]. split; [intros; lia|].
      split; [reflexivity|]. split; [exact Hcfg|]. split; [reflexivity|]. reflexivity.
    - iMod (IH ltac:(intros; apply Hal; lia) Hcfg with "Hri Hgh Hinv Hdata") as "[HAll | HF]".
      + iDestruct "HAll" as "(%Htr & %Hmr & %Hmdev & %Hcfg' & %Hmi & %Hnpc & Hri & Hgh & Hinv & Hdata)".
        destruct (data_classify (Load Data) tfp um (cva M') (or_intror (or_introl eq_refl)) Hwf)
          as [ (w & Hum & Hok & Hcanon) | Hfault ].
        * pose proof Hcfg' as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & Hmprv & Hall).
          iMod (user_pt_load_data_g bytes Hb Hb8 Hbdvd Huintb Hread_plain
                  uroot tfp um data w (cva M') (sst M')
                  Hum Hok Hcov (Hal M' ltac:(lia)) Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
                  with "Hri Hgh Hinv Hdata")
            as (dv σ') "(%Htr0 & %Hmr0 & %Hmdev0 & %Hsregs & Hri & Hgh & Hinv & Hdata)".
          assert (Hstep : sst (S M') = σ').
          { cbn [sst]. rewrite Htr0. reflexivity. }
          assert (Hspa : spaR M' = u_walk_pa w (cva M')).
          { unfold spaR. rewrite Htr0. reflexivity. }
          assert (Hsval : svalR M' = dv).
          { unfold svalR. rewrite Hspa. rewrite Hstep. rewrite Hmr0. reflexivity. }
          assert (Ttr : forall r : register, register_beq r tlb = false ->
                    register_lookup r σ'.(sregs) = register_lookup r (sst M').(sregs)).
          { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
              [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
          iModIntro. iLeft. rewrite Hstep. iFrame.
          iPureIntro. split; [| split; [| split; [| split; [| split]]]].
          -- intros k Hk. destruct (Nat.eq_dec k M') as [->|Hne].
             ++ rewrite Hspa Hstep. exact Htr0.
             ++ apply Htr; lia.
          -- intros k Hk. destruct (Nat.eq_dec k M') as [->|Hne].
             ++ rewrite Hspa Hsval Hstep. exact Hmr0.
             ++ apply Hmr; lia.
          -- rewrite Hmdev0. exact Hmdev.
          -- exact (cfg_okR_pres (sst M') σ' Hsregs Hcfg').
          -- rewrite (Ttr (R_bool minstret_increment) ltac:(vm_compute; reflexivity)). exact Hmi.
          -- rewrite (Ttr nextPC ltac:(vm_compute; reflexivity)). exact Hnpc.
        * iModIntro. iRight. iExists M'.
          iFrame. iPureIntro. split; [lia|]. split; [exact Htr|]. split; [exact Hmr|].
          split; [exact Hfault|]. split; [exact Hcfg'|]. split; [exact Hmdev|].
          split; [exact Hmi|]. exact Hnpc.
      + iDestruct "HF" as (j) "(%Hj & %Htr & %Hmr & %Hfl & %Hcfgj & %Hmdevj & %Hmij & %Hnpcj & Hri & Hgh & Hinv & Hdata)".
        iModIntro. iRight. iExists j. iFrame. iPureIntro.
        split; [lia|]. split; [exact Htr|]. split; [exact Hmr|]. split; [exact Hfl|].
        split; [exact Hcfgj|]. split; [exact Hmdevj|]. split; [exact Hmij|]. exact Hnpcj.
  Qed.

End MisReadClassify.

(* ===================================================================== *)
(* §10 The TOTAL MISALIGNED read composer: fold [0,N) (§8) then either the *)
(*     all-good split (§5-style exec_vmem_read_addr_misaligned_split, Ok)  *)
(*     or the first-fault split (§6 vmem_read_split_fault, Err via the     *)
(*     fault head at chunk j).  Takes the split fact as a hypothesis (the  *)
(*     ctz split-derivation supplies it).                                  *)
(* ===================================================================== *)
Section MisReadTotal.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)) (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hread_plain : forall (addr : mword 64) (ww : mword (8 * bytes)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N bytes)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte ww j)) ->
      exec (read_ram rv64d_types.Read_plain (Physaddr addr) bytes false) s = Some ((ww, default_meta), s)).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa).
  Context (Hwf : upt_acc_wf um) (Hcov : udata_cov um data).

  Notation cva va k := (add_vec_int va (Z.of_nat k * bytes)).

  Lemma mem_read_misaligned_total (W : Z) (N : nat) (va : mword 64) (s : mstate) :
    (1 <= N)%nat -> Z.of_nat N * bytes = W ->
    is_aligned_vaddr (Virtaddr va) W = false ->
    exec (split_misaligned (Virtaddr va) W) s = Some ((Z.of_nat N, bytes), s) ->
    (forall k, (k < N)%nat -> is_aligned_vaddr (Virtaddr (cva va k)) bytes = true) ->
    cfg_okR s ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (dvv : mword (8 * W)) (σ' : mstate),
        ⌜exec (vmem_read_addr (Virtaddr va) W (Load Data) false false false) s = Some (Ok dvv, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pc : mword 64),
        ⌜exec (vmem_read_addr (Virtaddr va) W (Load Data) false false false) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pc)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros HN Hwidth Hnal Hsplit Halk Hcfg.
    iIntros "Hreg Hgh Hutlb Hudata".
    iMod (read_classify_fold bytes Hb Hb8 Hbdvd Huintb Hread_plain uroot tfp um data va Hwf Hcov s N Halk Hcfg
            with "Hreg Hgh Hutlb Hudata") as "[HAll | HF]".
    - iDestruct "HAll" as "(%Htr & %Hmr & %Hmdev & %Hcfgn & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      destruct (exec_vmem_read_addr_misaligned_split W bytes va (Load Data) false false N
                  (spaR bytes va s) (svalR bytes va s) (sst bytes va s)
                  HN Hb Htr Hmr Hnal eq_refl eq_refl Hsplit) as (dvv & Hvr).
      iModIntro. iLeft. iExists dvv, (sst bytes va s N).
      iFrame "Hreg Hgh Hutlb Hudata". iPureIntro. split; [exact Hvr |]. split; [exact Hmdev|].
      split; [exact Hmi | exact Hnpc].
    - iDestruct "HF" as (j) "(%Hj & %Htr & %Hmr & %Hfl & %Hcfgj & %Hmdevj & %Hmij & %Hnpcj & Hreg & Hgh & Hutlb & Hudata)".
      pose proof Hcfgj as (Hmisaj & Hmenvj & Hhtifj & Hcpj & HSXLj & HMPRVj & Hpmaj).
      iDestruct (utlb_inv_pt_translateAddr_u_fault (Load Data) uroot tfp um (cva va j)
                   (E_Load_Page_Fault tt) (sst bytes va s j) Hfl Hhtifj Hcpj HSXLj
                   (exec_effectivePrivilege_mprv0 (Load Data)
                      (register_lookup mstatus (sst bytes va s j).(sregs)) User (sst bytes va s j) HMPRVj)
                   (exec_is_shadow_stack_u_acc (Load Data) (sst bytes va s j) (or_intror (or_introl eq_refl)))
                   Hpmaj
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   with "Hreg Hgh Hutlb") as %Htrf.
      set (pcj := register_lookup PC (sst bytes va s j).(sregs)).
      assert (Hstepj : sst bytes va s (S j) = sst bytes va s j).
      { cbn [sst]. fold (cva va j).
        change (bits_of_virtaddr (Virtaddr va)) with va in Htrf.
        rewrite Htrf. reflexivity. }
      assert (HtrF : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (Z.of_nat j * bytes))) (Load Data)) (sst bytes va s j)
                     = Some (Err (E_Load_Page_Fault tt, tt), sst bytes va s (S j))).
      { change (bits_of_virtaddr (Virtaddr va)) with va. rewrite Hstepj. exact Htrf. }
      assert (HcpF : register_lookup cur_privilege (sst bytes va s (S j)).(sregs) = User)
        by (rewrite Hstepj; exact Hcpj).
      assert (HpcF : register_lookup PC (sst bytes va s (S j)).(sregs) = pcj)
        by (rewrite Hstepj; reflexivity).
      pose proof (vmem_read_split_fault W bytes va pcj (Load Data) false false (E_Load_Page_Fault tt)
                    N j (spaR bytes va s) (svalR bytes va s) (sst bytes va s)
                    HN Hb Hj Htr Hmr HtrF HcpF HpcF Hnal eq_refl eq_refl Hsplit) as Hvr.
      rewrite Hstepj in Hvr.
      iModIntro. iRight.
      iExists (sst bytes va s j), (E_Load_Page_Fault tt),
        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (Z.of_nat j * bytes)), pcj.
      iFrame "Hreg Hgh Hutlb Hudata". iPureIntro.
      split; [exact Hvr |]. split; [reflexivity |]. split; [exact Hmdevj|].
      split; [exact Hmij | exact Hnpcj].
  Qed.

End MisReadTotal.

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

(* ===================================================================== *)
(* §11 The ctz split-derivation: for a misaligned va of width W in {2,4,8}, *)
(*     reduce split_misaligned to the concrete chunk count/size (bytes =    *)
(*     2^ctz(va), N = W/bytes) + per-chunk alignment.  count_trailing_zeros *)
(*     is characterized via a foreach_Z_down' suffix invariant.            *)
(* ===================================================================== *)
Lemma shiftr_mod2_testbit (x i : Z) : 0 <= i ->
  (Z.shiftr x i) mod 2 = Z.b2z (Z.testbit x i).
Proof.
  intros Hi.
  rewrite Zmod_odd.
  rewrite <- Z.bit0_odd.
  rewrite Z.shiftr_spec; [| lia].
  replace (0 + i) with i; [| lia].
  destruct (Z.testbit x i); reflexivity.
Qed.

Lemma access_unsigned_64 (w : mword 64) (i : Z) : 0 <= i ->
  bv_unsigned (access_vec_dec w i) = Z.b2z (Z.testbit (bv_unsigned w) i).
Proof.
  intros Hi.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice.
  cbv [get_word].
  rewrite bv_extract_unsigned.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  replace (Z.of_N (MachineWord.MachineWord.Z_idx i)) with i.
  2:{ unfold MachineWord.MachineWord.Z_idx. rewrite Z2N.id; [| lia]. reflexivity. }
  apply shiftr_mod2_testbit; lia.
Qed.

Lemma bvu_moi1 : bv_unsigned (mword_of_int 1 : mword 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma allowed_misaligned_false (a : mword 64) (W : Z) :
  (W = 2 \/ W = 4 \/ W = 8) -> allowed_misaligned a W 0 = false.
Proof.
  intros HW. unfold allowed_misaligned.
  destruct HW as [ -> | [ -> | -> ] ]; reflexivity.
Qed.

Section WithVa.
Variable va : mword 64.

Definition body (i r : Z) : Z :=
  if eq_vec (access_vec_dec va i) (mword_of_int 1) then i else r.

Lemma body_eq (i r : Z) :
  body i r = (if eq_vec (access_vec_dec va i) (mword_of_int 1) then i else r).
Proof. reflexivity. Qed.

Lemma bit_set (i : Z) : 0 <= i ->
  Z.testbit (bv_unsigned va) i = true ->
  eq_vec (access_vec_dec va i) (mword_of_int 1) = true.
Proof.
  intros Hi Hb. apply eq_vec_true_iff. apply bv_eq.
  rewrite access_unsigned_64; [| lia]. rewrite Hb. rewrite bvu_moi1. reflexivity.
Qed.

Lemma bit_clear (i : Z) : 0 <= i ->
  Z.testbit (bv_unsigned va) i = false ->
  eq_vec (access_vec_dec va i) (mword_of_int 1) = false.
Proof.
  intros Hi Hb. apply eq_vec_false_iff. intro Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite access_unsigned_64 in Heq; [| lia]. rewrite Hb in Heq.
  rewrite bvu_moi1 in Heq. simpl in Heq. discriminate.
Qed.

Lemma fold_low_clear : forall (n : nat) (off r : Z),
  (forall j, 0 <= j <= 63 + off -> eq_vec (access_vec_dec va j) (mword_of_int 1) = false) ->
  foreach_Z_down' 63 0 1 off n r body = r.
Proof.
  induction n as [|n IH]; intros off r Hclear.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)); reflexivity.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)) as [Hg|Hg]; [ | reflexivity ].
    apply Z.leb_le in Hg.
    rewrite body_eq.
    rewrite (Hclear (63 + off)); [ | lia ].
    cbn match.
    apply IH. intros j Hj. apply Hclear. lia.
Qed.

Lemma fold_gives_k : forall (n : nat) (off k : Z),
  0 <= k <= 63 + off ->
  n = S (Z.to_nat (63 + off)) ->
  Z.testbit (bv_unsigned va) k = true ->
  (forall j, 0 <= j < k -> Z.testbit (bv_unsigned va) j = false) ->
  forall (r : Z), foreach_Z_down' 63 0 1 off n r body = k.
Proof.
  induction n as [|n IH]; intros off k Hk Hn Hset Hlow r.
  - discriminate Hn.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)) as [Hg|Hg].
    2:{ apply Z.leb_gt in Hg. lia. }
    apply Z.leb_le in Hg.
    injection Hn as Hn'.
    destruct (Z.eq_dec k (63 + off)) as [Hkeq|Hkne].
    + rewrite body_eq.
      rewrite <- Hkeq.
      rewrite (bit_set k ltac:(lia) Hset).
      cbn match.
      apply fold_low_clear.
      intros j Hj. apply bit_clear; [ lia | apply Hlow; lia ].
    + rewrite body_eq.
      apply IH.
      * lia.
      * rewrite Hn'.
        replace (63 + (off - 1)) with (62 + off); [| lia].
        replace (63 + off) with (Z.succ (62 + off)); [| lia].
        rewrite Z2Nat.inj_succ; [| lia]. reflexivity.
      * exact Hset.
      * exact Hlow.
Qed.

Lemma ctz_val (k : Z) :
  0 <= k <= 63 ->
  Z.testbit (bv_unsigned va) k = true ->
  (forall j, 0 <= j < k -> Z.testbit (bv_unsigned va) j = false) ->
  count_trailing_zeros va = k.
Proof.
  intros Hk Hset Hlow.
  transitivity (foreach_Z_down' 63 0 1 0 64 64 body).
  { unfold count_trailing_zeros, foreach_Z_down. reflexivity. }
  apply (fold_gives_k 64 0 k).
  - lia.
  - reflexivity.
  - exact Hset.
  - exact Hlow.
Qed.

Lemma low_bits_zero_mod (m : nat) :
  (forall j, 0 <= j < Z.of_nat m -> Z.testbit (bv_unsigned va) j = false) ->
  bv_unsigned va mod (2 ^ Z.of_nat m) = 0.
Proof.
  intros H.
  apply (proj1 (Z.bits_inj_iff' (bv_unsigned va mod 2 ^ Z.of_nat m) 0)).
  intros i Hi. rewrite Z.bits_0.
  destruct (Z.lt_ge_cases i (Z.of_nat m)) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low; [| lia]. apply H. lia.
  - rewrite Z.mod_pow2_bits_high; [| lia]. reflexivity.
Qed.

Lemma chunk_aligned (bytes j : Z) :
  0 < bytes -> (bytes | 4096) -> 0 <= j < 4096 ->
  bv_unsigned va mod bytes = 0 -> j mod bytes = 0 ->
  is_aligned_vaddr (Virtaddr (add_vec_int va j)) bytes = true.
Proof.
  intros Hb Hdvd Hj Hva Hjm.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite (uint_unsigned_n _).
  rewrite Z.rem_mod_nonneg;
    [ | pose proof (bv_unsigned_in_range _ (add_vec_int va j)); lia | exact Hb ].
  rewrite (Znumtheory.Zmod_div_mod bytes 4096 _ Hb ltac:(lia) Hdvd).
  pose proof (uint_add_vec_int_mod4096 va j Hj) as Hm.
  rewrite !(uint_unsigned_n _) in Hm.
  rewrite Hm.
  rewrite <- (Znumtheory.Zmod_div_mod bytes 4096 _ Hb ltac:(lia) Hdvd).
  rewrite Z.add_mod; [| lia].
  rewrite Hva. rewrite Hjm. rewrite Z.add_0_l. apply Zmod_0_l.
Qed.

Lemma exec_split (W k : Z) (s : mstate) :
  is_aligned_vaddr (Virtaddr va) W = false ->
  allowed_misaligned va W 0 = false ->
  count_trailing_zeros va = k ->
  Z.eqb W (Z.quot W (pow2 k) * pow2 k) = true ->
  exec (split_misaligned (Virtaddr va) W) s
    = Some ((Z.quot W (pow2 k), pow2 k), s).
Proof.
  intros Hmis Hallow Hctz Hguard.
  unfold split_misaligned.
  unfold sys_misaligned_allowed_within_exp, sys_misaligned_byte_by_byte.
  cbn zeta.
  change (bits_of_virtaddr (Virtaddr va)) with va.
  rewrite Hmis.
  rewrite Hallow.
  cbn [orb].
  cbn match.
  rewrite Hctz.
  rewrite Hguard.
  erewrite exec_bind_Some.
  2:{ unfold assert_exp'. cbn match. apply exec_returnm. }
  cbn beta. apply exec_returnm.
Qed.

Lemma assemble (W k bytes num : Z) (Nn : nat) (s : mstate) :
  is_aligned_vaddr (Virtaddr va) W = false ->
  allowed_misaligned va W 0 = false ->
  count_trailing_zeros va = k ->
  bv_unsigned va mod bytes = 0 ->
  bytes = pow2 k ->
  num = Z.quot W bytes ->
  Z.of_nat Nn = num ->
  (1 <= Nn)%nat ->
  0 < bytes -> bytes < W -> W <= 8 ->
  (bytes | 4096) ->
  uint (to_bits 64 bytes) = bytes ->
  Z.of_nat Nn * bytes = W ->
  Z.eqb W (num * bytes) = true ->
  exists (N : nat) (bytes0 : Z),
    (1 <= N)%nat /\ Z.of_nat N * bytes0 = W /\ 0 < bytes0 /\ bytes0 < W /\
    (bytes0 | 4096) /\ uint (to_bits 64 bytes0) = bytes0 /\
    exec (split_misaligned (Virtaddr va) W) s = Some ((Z.of_nat N, bytes0), s) /\
    (forall k0, (k0 < N)%nat ->
       is_aligned_vaddr (Virtaddr (add_vec_int va (Z.of_nat k0 * bytes0))) bytes0 = true).
Proof.
  intros Hmis Hallow Hctz Hvamod Hbytes Hnum HN HNn Hbpos HbltW HWle Hdvd Hub HNbW Hguard.
  exists Nn, bytes.
  split; [ exact HNn |].
  split; [ exact HNbW |].
  split; [ exact Hbpos |].
  split; [ exact HbltW |].
  split; [ exact Hdvd |].
  split; [ exact Hub |].
  split.
  { rewrite HN. rewrite Hnum. rewrite Hbytes.
    apply (exec_split W k s Hmis Hallow Hctz).
    rewrite <- Hbytes. rewrite <- Hnum. exact Hguard. }
  { intros k0 Hk0. apply chunk_aligned.
    - exact Hbpos.
    - exact Hdvd.
    - assert (Hk0z : Z.of_nat k0 < Z.of_nat Nn) by (apply inj_lt; exact Hk0).
      assert (Hk0nn : 0 <= Z.of_nat k0) by apply Nat2Z.is_nonneg.
      split.
      + nia.
      + nia.
    - exact Hvamod.
    - apply Z.mod_mul. lia. }
Qed.

End WithVa.

Lemma split_misaligned_derive (W : Z) (va : mword 64) (s : mstate) :
  (W = 2 \/ W = 4 \/ W = 8) ->
  is_aligned_vaddr (Virtaddr va) W = false ->
  exists (N : nat) (bytes : Z),
    (1 <= N)%nat /\ Z.of_nat N * bytes = W /\ 0 < bytes /\ bytes < W /\
    (bytes | 4096) /\ uint (to_bits 64 bytes) = bytes /\
    exec (split_misaligned (Virtaddr va) W) s = Some ((Z.of_nat N, bytes), s) /\
    (forall k, (k < N)%nat ->
       is_aligned_vaddr (Virtaddr (add_vec_int va (Z.of_nat k * bytes))) bytes = true).
Proof.
  intros HW Halign.
  pose proof (allowed_misaligned_false va W HW) as Hallow.
  assert (HWpos : 0 < W) by (destruct HW as [ -> | [ -> | -> ] ]; lia).
  assert (Hmodne : bv_unsigned va mod W <> 0).
  { unfold is_aligned_vaddr in Halign. apply Z.eqb_neq in Halign.
    rewrite (uint_unsigned_n _) in Halign.
    rewrite Z.rem_mod_nonneg in Halign;
      [ exact Halign | pose proof (bv_unsigned_in_range _ va); lia | exact HWpos ]. }
  destruct HW as [ -> | [ -> | -> ] ].
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 2 0 1 2 2%nat s).
      * exact Halign.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * apply Z.mod_1_r.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + exfalso. apply Hmodne. change 2 with (2 ^ Z.of_nat 1).
      apply low_bits_zero_mod. intros j Hj.
      assert (j = 0) as -> by lia. exact E0.
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 4 0 1 4 4%nat s).
      * exact Halign.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * apply Z.mod_1_r.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + destruct (Z.testbit (bv_unsigned va) 1) eqn:E1.
      * apply (assemble va 4 1 2 2 2%nat s).
        -- exact Halign.
        -- exact Hallow.
        -- apply ctz_val; [ lia | exact E1 | intros j Hj; assert (j = 0) as -> by lia; exact E0 ].
        -- change 2 with (2 ^ Z.of_nat 1). apply low_bits_zero_mod.
           intros j Hj. assert (j = 0) as -> by lia. exact E0.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- exists 2048; vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
      * exfalso. apply Hmodne. change 4 with (2 ^ Z.of_nat 2).
        apply low_bits_zero_mod. intros j Hj.
        assert (j = 0 \/ j = 1) as [ -> | -> ] by lia; [ exact E0 | exact E1 ].
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 8 0 1 8 8%nat s).
      * exact Halign.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * apply Z.mod_1_r.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + destruct (Z.testbit (bv_unsigned va) 1) eqn:E1.
      * apply (assemble va 8 1 2 4 4%nat s).
        -- exact Halign.
        -- exact Hallow.
        -- apply ctz_val; [ lia | exact E1 | intros j Hj; assert (j = 0) as -> by lia; exact E0 ].
        -- change 2 with (2 ^ Z.of_nat 1). apply low_bits_zero_mod.
           intros j Hj. assert (j = 0) as -> by lia. exact E0.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- exists 2048; vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
      * destruct (Z.testbit (bv_unsigned va) 2) eqn:E2.
        -- apply (assemble va 8 2 4 2 2%nat s).
           ++ exact Halign.
           ++ exact Hallow.
           ++ apply ctz_val; [ lia | exact E2
              | intros j Hj; assert (j = 0 \/ j = 1) as [ -> | -> ] by lia; [ exact E0 | exact E1 ] ].
           ++ change 4 with (2 ^ Z.of_nat 2). apply low_bits_zero_mod.
              intros j Hj. assert (j = 0 \/ j = 1) as [ -> | -> ] by lia; [ exact E0 | exact E1 ].
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ exists 1024; vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
        -- exfalso. apply Hmodne. change 8 with (2 ^ Z.of_nat 3).
           apply low_bits_zero_mod. intros j Hj.
           assert (j = 0 \/ j = 1 \/ j = 2) as [ -> | [ -> | -> ] ] by lia;
             [ exact E0 | exact E1 | exact E2 ].
Qed.



(* ===================================================================== *)
(* §12 The TOTAL read classify (aligned §5 / misaligned §10+split_deriv),  *)
(*     the width-k LOAD engine (mem_exec_core), and the compressed LOAD    *)
(*     arms C_LH/C_LHU/C_LW/C_LD (each: ExecuteAs to a base LOAD at literal *)
(*     width, engine, rvc_post).                                           *)
(* ===================================================================== *)
Lemma pow2_le8 (b : Z) : 0 < b -> b < 8 -> (b | 4096) -> b = 1 \/ b = 2 \/ b = 4.
Proof.
  intros Hpos Hlt Hdvd.
  assert (Hb : b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  destruct Hdvd as [q Hq].
  destruct Hb as [H|[H|[H|[H|[H|[H|H]]]]]]; subst b;
    try (left; reflexivity); try (right; left; reflexivity);
    try (right; right; reflexivity); exfalso; lia.
Qed.


(* ===================================================================== *)
(* §11a SHARED GLUE for the memory arms.                                   *)
(*                                                                         *)
(*  Every memory arm -- base (+4) and compressed (+2) alike -- opens by     *)
(*  transporting post_fetch_cfg's facts (plus hw_config's misa/pma/htif and *)
(*  user_cfg's senvcfg) across the [set_reg _ nextPC (va+n)] that the fetch *)
(*  left behind, and closes by re-packing the engine's Ok/Err result into   *)
(*  base_post / rvc_post.  Both halves are instruction-size generic, so ONE *)
(*  prologue lemma serves n=2 and n=4 and one closer serves every           *)
(*  compressed arm (base_finish_mem, in §BaseMemArms, is its +4 twin).      *)
(* ===================================================================== *)
Section MemArmGlue.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma u_result_ok_trap (e : ExceptionType) (xv pcx : mword 64) :
    user_exc e = true ->
    u_result_ok (rv64d_types.Trap (User, make_sync_exception e xv, pcx)).
  Proof. intro Hue. unfold u_result_ok. right; left. exists e, xv, pcx. split; [reflexivity | exact Hue]. Qed.

  (* The seven config premises EVERY mem_exec_* engine takes, named once.  *)
  Definition u_engine_cfg (s : mstate) : Prop :=
    register_lookup cur_privilege s.(sregs) = User
    /\ user_mstatus_ok (register_lookup mstatus s.(sregs))
    /\ register_lookup misa s.(sregs) = MISA_C
    /\ register_lookup menvcfg s.(sregs) = MENVCFG_S
    /\ register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64)
    /\ register_lookup htif_tohost_base s.(sregs) = None
    /\ pma_allows_all (register_lookup pma_regions s.(sregs)).

  (* PROLOGUE.  Pure conclusion, so the caller keeps its mstate_interp and  *)
  (* user_cfg -- one line replaces the arms' 25-line transport block.       *)
  Lemma post_fetch_uconfig (C : ucfg) (n : Z) (sigma_f : mstate) (va : mword 64)
      (mi : bool) :
    post_fetch_cfg sigma_f va mi ->
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va n)) -∗
    hw_config -∗ user_cfg C -∗
    ⌜u_engine_cfg (set_reg sigma_f nextPC (add_vec_int va n))
     /\ register_lookup PC (set_reg sigma_f nextPC (add_vec_int va n)).(sregs) = va
     /\ exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f)
     /\ register_lookup (R_bool minstret_increment) sigma_f.(sregs) = mi⌝.
  Proof.
    intros (Lpc & Lcp & Hmsok & Lmenv & Hva2 & Lmi).
    iIntros "(Hreg & Hgh & Hdev) #Hhw Hcfg".
    iDestruct (hwcfg_misa (set_reg sigma_f nextPC (add_vec_int va n))
                 with "Hreg Hhw") as %Hmisa.
    iDestruct (ucfg_senvcfg C (set_reg sigma_f nextPC (add_vec_int va n))
                 with "Hreg Hcfg") as %Hsenv.
    iPoseProof "Hhw" as (misa0 msec0 pmar0 elp0)
      "(#Hmisac & _ & #Hpmac & #Hhtifc & _ & _ & _ & _ & _ & %Hpmaall & _ & _ & _ & _ & %Hmisaeq & _)".
    iDestruct (reg_valid_dq with "Hreg Hhtifc") as %Hhtif.
    iDestruct (reg_valid_dq with "Hreg Hpmac") as %Hpmav.
    assert (Lmisaf : register_lookup misa sigma_f.(sregs) = MISA_C).
    { rewrite <- Hmisa. symmetry.
      apply reg_nextPC_transp; [ vm_compute; reflexivity | reflexivity ]. }
    iPureIntro. unfold u_engine_cfg. split_and!.
    - apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lcp ].
    - rewrite (reg_nextPC_transp mstatus (register_lookup mstatus sigma_f.(sregs))
                 sigma_f (add_vec_int va n) ltac:(vm_compute; reflexivity) eq_refl).
      exact Hmsok.
    - exact Hmisa.
    - apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lmenv ].
    - exact Hsenv.
    - exact Hhtif.
    - rewrite Hpmav; exact Hpmaall.
    - apply reg_nextPC_transp; [ vm_compute; reflexivity | exact Lpc ].
    - exact (s0_zca sigma_f Lmisaf).
    - exact Lmi.
  Qed.

  (* EPILOGUE (compressed).  The missing member of UserTotalU's finish_rvc_* *)
  (* family: an ExecuteAs redirect whose base instruction lands in a NEW     *)
  (* state s_x with a possibly-updated gpr map g'.                          *)
  Lemma rvc_finish_mem (C : ucfg) (pt : uptd)
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64) (h : mword 16)
      (g g' : regfile) (ci bi : instruction) (r0 : ExecutionResult) (s_x : mstate) :
    register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs) ->
    exec (ext_decode_compressed h) sigma_f = Some (ci, sigma_f) ->
    exec (currentlyEnabled Ext_Zca) sigma_f = Some (true, sigma_f) ->
    exec (execute ci) (set_reg sigma_f nextPC (add_vec_int va 2))
       = Some (ExecuteAs bi, set_reg sigma_f nextPC (add_vec_int va 2)) ->
    exec (execute bi) (set_reg sigma_f nextPC (add_vec_int va 2)) = Some (r0, s_x) ->
    u_result_ok r0 ->
    match r0 with ExecuteAs _ => False | _ => True end ->
    register_lookup (R_bool minstret_increment) s_x.(sregs)
       = register_lookup (R_bool minstret_increment)
           (set_reg sigma_f nextPC (add_vec_int va 2)).(sregs) ->
    register_lookup nextPC s_x.(sregs)
       = register_lookup nextPC (set_reg sigma_f nextPC (add_vec_int va 2)).(sregs) ->
    mstate_interp s_x -∗ gpr_file g' -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
    user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Lmi Hdecc Hzca Hex1 Hex2 Hok Hnex Hmi Hnpc.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold rvc_post.
    iModIntro. iExists ci, r0, s_x, g', (add_vec_int va 2).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split_and!.
    - exact Hdecc.
    - exact Hzca.
    - right. exists bi. split; [exact Hex1 | exact Hex2].
    - exact Hok.
    - exact Hnex.
    - rewrite Hmi. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity].
    - rewrite Hnpc. unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

End MemArmGlue.

Section MemReadTotal.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma mem_read_total (k : Z)
      (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k)
      (Hread_plain_k : forall (addr : mword 64) (w : mword (8 * k)) s,
         dev_addr addr = false ->
         (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
         exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (Hwf : upt_acc_wf um) (Hcov : udata_cov um data)
      (va pc : mword 64) (s : mstate) :
    cfg_okR s -> register_lookup PC s.(sregs) = pc ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (dvv : mword (8 * k)) (σ' : mstate),
        ⌜exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false) s = Some (Ok dvv, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗ ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros Hcfg Lpc.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & HMPRV & Hpma).
    iIntros "Hreg Hgh Hutlb Hudata".
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    - (* aligned: the §5 classify *)
      iMod (user_pt_vmem_read_addr_load_classify k Hk Hk8 Hkdvd Huintk Hread_plain_k
              uroot tfp um data va pc s Hwf Hcov Hal Hmisa Hmenv Hhtif Lpc Hcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
      + iDestruct "HOk" as (dvv σ') "(%Hvr & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        iModIntro. iLeft. iExists dvv, σ'. iFrame. iPureIntro.
        split; [exact Hvr |]. split; [exact Hmdev|].
        split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
      + iDestruct "HErr" as "(%Herr & Hreg & Hgh & Hutlb & Hudata)".
        iModIntro. iRight. iExists s, (E_Load_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - (* misaligned: split then the total misaligned composer *)
      destruct (split_misaligned_derive k va s HkW Hal)
        as (N & bytes & HN & Hwidth & Hbpos & Hblt & Hbdvd & Huintb & Hsplit & Halk).
      assert (Hblt8 : bytes < 8) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; lia).
      destruct (pow2_le8 bytes Hbpos Hblt8 Hbdvd) as [Hbe|[Hbe|Hbe]]; subst bytes.
      + iMod (mem_read_misaligned_total 1 ltac:(lia) ltac:(lia) ltac:(exists 4096; reflexivity)
                ltac:(vm_compute; reflexivity) exec_read_ram_plain_1 uroot tfp um data Hwf Hcov
                k N va s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (dvv σ') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists dvv, σ'. iFrame. iPureIntro. split; [exact Hvr |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
      + iMod (mem_read_misaligned_total 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity)
                ltac:(vm_compute; reflexivity) exec_read_ram_plain_2 uroot tfp um data Hwf Hcov
                k N va s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (dvv σ') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists dvv, σ'. iFrame. iPureIntro. split; [exact Hvr |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
      + iMod (mem_read_misaligned_total 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
                ltac:(vm_compute; reflexivity) exec_read_ram_plain_4 uroot tfp um data Hwf Hcov
                k N va s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (dvv σ') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists dvv, σ'. iFrame. iPureIntro. split; [exact Hvr |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
  Qed.


  Lemma mem_exec_load_k (pt : uptd) (k : Z)
      (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k)
      (Hread_plain_k : forall (addr : mword 64) (w : mword (8 * k)) s,
         dev_addr addr = false ->
         (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
         exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (g : regfile) (s : mstate) :
    uint rd <> 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (v : mword 64) (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file (<[Regidx rd := v]> g) ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Hrd Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Load Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    assert (Hcfg : cfg_okR s).
    { unfold cfg_okR. repeat split; assumption. }
    iMod (mem_read_total k Hk Hk8 Hkdvd Huintk Hread_plain_k HkW
            pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) Hwf Hcov va
            (register_lookup PC s.(sregs)) s Hcfg eq_refl with "Hreg Hgh Hutlb Hudata")
      as "[HOk | HErr]".
    - iDestruct "HOk" as (dvv sig') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) k (Load Data) false false false) s = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data) false false false Sv39 (Ok dvv) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvr. }
      assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; vm_compute; reflexivity).
      pose proof (exec_execute_LOAD_u_ok imm rs1 rd is_unsigned k dvv s sig' Hkle Hrd Hvread) as Hexec.
      iDestruct (gpr_file_acc g rd Hrd with "Hgpr") as "[Hrdf Hins]".
      iDestruct "Hrdf" as (v0) "Hrdf".
      set (nv := regval_into_reg (extend_value is_unsigned dvv)).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
      iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
      iModIntro. iLeft. set (s_x := set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
      iExists nv, s_x.
      iSplitR; [ iPureIntro; unfold s_x, nv; exact Hexec |].
      assert (Tr : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                register_lookup r s_x.(sregs) = register_lookup r sig'.(sregs)).
      { intros r Hne. unfold s_x, set_reg; cbn [sregs]. apply irrelevant_register_set; exact Hne. }
      iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
      iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
      { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) k (Load Data) false false false) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data) false false false Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; vm_compute; reflexivity).
      pose proof (exec_execute_LOAD_u_err imm rs1 rd is_unsigned k (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s sig' Hkle Hvread) as Hexec.
      iModIntro. iRight. iExists e, xv, pcx, sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hue |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End MemReadTotal.

(* ===================================================================== *)
(* §9 Compressed-register nonzero + width-1 memory ARMS.  A cregidx maps   *)
(*    to x8..x15, so the compressed load/store rd/rs1 is never x0 -- the    *)
(*    rd<>0 premise of exec_execute_LOAD_u_ok holds by construction.        *)
(* ===================================================================== *)


Lemma exec_execute_LOAD_u_ok_rd0 (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
    (width : Z) (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd = 0 ->
  exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) width (Load Data) false false false) s
    = Some (Ok data, s') ->
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hw Hrd Hvr.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, width)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned width).
  unfold execute_LOAD. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (extend_value is_unsigned data)) s' = Some (tt, s')).
  { rewrite (exec_wX_bits_gpr rd (extend_value is_unsigned data) s').
    rewrite (proj2 (Z.eqb_eq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_returnm.
Qed.

Section MemArmsU.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Local Notation uroot := (pt.(ud_root)).
  Local Notation utfp := (pt.(ud_tfp)).
  Local Notation uum := (pt.(ud_um)).
  Local Notation udat := (pt.(ud_data)).

  Lemma mem_exec_load_1 (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (g : regfile) (pc : mword 64) (s : mstate) :
    uint rd <> 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    register_lookup PC s.(sregs) = pc ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (v : mword 64) (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file (<[Regidx rd := v]> g) ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (va : mword 64),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e va, pc), s)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        mstate_interp s ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Hrd Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Lpc Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    (* translationMode = Sv39 (non-consuming) *)
    iDestruct (utlb_inv_pt_translationMode_U uroot utfp uum s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    (* get_pmlen (Load Data) User s = 0 *)
    assert (Hpml : exec (get_pmlen (Load Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption;
        try (vm_compute; reflexivity). }
    (* effectivePrivilege (Load Data) mstatus User s = User *)
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    (* classify at width 1 (always aligned) *)
    iMod (user_pt_vmem_read_addr_load_classify_1 uroot utfp uum udat va pc s
            Hwf Hcov (is_aligned_vaddr_1 va) Hmisa Hmenv Hhtif Lpc Lcp HSXL HMPRV Hpma
            with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
    - iDestruct "HOk" as (dvv sig') "(%Hvr & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      (* bridge: vmem_read *)
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) 1 (Load Data) false false false) s
                       = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) 1 (Load Data) false false false Sv39
                 (Ok dvv) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvr. }
      pose proof (exec_execute_LOAD_u_ok imm rs1 rd is_unsigned 1 dvv s sig'
                    eq_refl Hrd Hvread) as Hexec.
      (* gpr write *)
      iDestruct (gpr_file_acc g rd Hrd with "Hgpr") as "[Hrdf Hins]".
      iDestruct "Hrdf" as (v0) "Hrdf".
      set (nv := regval_into_reg (extend_value is_unsigned dvv)).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
      iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
      iModIntro. iLeft.
      set (s_x := set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
      iExists nv, s_x.
      iSplitR.
      { iPureIntro. unfold s_x, nv. exact Hexec. }
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iSplitR.
      { iPureIntro. unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint rd)))).
        2:{ reg_ne. }
        apply Tr. vm_compute; reflexivity. }
      iSplitR.
      { iPureIntro. unfold s_x, set_reg; cbn [sregs].
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))).
        2:{ reg_ne. }
        apply Tr. vm_compute; reflexivity. }
      unfold mstate_interp.
      iSplitL "Hreg Hgh Hdev".
      { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh".
        rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as "(%Herr & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) 1 (Load Data) false false false) s
                       = Some (Err (rv64d_types.Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), s)).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) 1 (Load Data) false false false Sv39
                 (Err _) s s Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_LOAD_u_err imm rs1 rd is_unsigned 1
                    (rv64d_types.Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)) s s
                    eq_refl Hvread) as Hexec.
      iModIntro. iRight.
      iExists (E_Load_Page_Fault tt), va.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; reflexivity |].
      unfold mstate_interp. iFrame "Hreg Hgh Hdev Hgpr Hutlb Hudata".
      iPureIntro; split; assumption.
  Qed.

  (* rd = 0 companion of mem_exec_load_1: the width-1 load with an x0
     destination retires without a gpr write (used by base LB/LBU x0). *)
  Lemma mem_exec_load_1_rd0 (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (g : regfile) (pc : mword 64) (s : mstate) :
    uint rd = 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    register_lookup PC s.(sregs) = pc ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (va : mword 64),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e va, pc), s)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        mstate_interp s ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Hrd Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Lpc Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U uroot utfp uum s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Load Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    iMod (user_pt_vmem_read_addr_load_classify_1 uroot utfp uum udat va pc s
            Hwf Hcov (is_aligned_vaddr_1 va) Hmisa Hmenv Hhtif Lpc Lcp HSXL HMPRV Hpma
            with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
    - iDestruct "HOk" as (dvv sig') "(%Hvr & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) 1 (Load Data) false false false) s
                       = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) 1 (Load Data) false false false Sv39
                 (Ok dvv) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvr. }
      pose proof (exec_execute_LOAD_u_ok_rd0 imm rs1 rd is_unsigned 1 dvv s sig'
                    eq_refl Hrd Hvread) as Hexec.
      iModIntro. iLeft. iExists sig'.
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iSplitR; [ iPureIntro; exact Hexec |].
      iSplitR; [ iPureIntro; apply Tr; vm_compute; reflexivity |].
      iSplitR; [ iPureIntro; apply Tr; vm_compute; reflexivity |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
      { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as "(%Herr & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) 1 (Load Data) false false false) s
                       = Some (Err (rv64d_types.Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), s)).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) 1 (Load Data) false false false Sv39
                 (Err _) s s Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_LOAD_u_err imm rs1 rd is_unsigned 1
                    (rv64d_types.Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)) s s
                    eq_refl Hvread) as Hexec.
      iModIntro. iRight. iExists (E_Load_Page_Fault tt), va.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; reflexivity |].
      unfold mstate_interp. iFrame "Hreg Hgh Hdev Hgpr Hutlb Hudata".
      iPureIntro; split; assumption.
  Qed.

End MemArmsU.

Lemma exec_execute_C_LBU_U (uimm : mword 2) (rdc rsc1 : cregidx) (s : mstate) :
  exec (execute (C_LBU (uimm, rdc, rsc1))) s
    = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx rsc1, creg2reg_idx rdc, true, 1)), s).
Proof. apply exec_returnm. Qed.

Lemma arm_C_LBU_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_LBU p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[uimm rdc] rsc1]. destruct rdc as [i0]. destruct rsc1 as [i1].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s2 := set_reg sigma_f nextPC (add_vec_int va 2)).
  iDestruct (post_fetch_uconfig C 2 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp2 & Hmsok2 & Hmisa2 & Lmenv2 & Hsenv2 & Hhtif2 & Hpma2) & Lpc2 & Hzcaf & Lmi).
  iMod (mem_exec_load_1 pt (zero_extend' 12 uimm)
          (zero_extend' 5 (concat_vec ('b"1") i1))
          (zero_extend' 5 (concat_vec ('b"1") i0)) true g va s2
          (creg_nz i0) Lcp2 Hmsok2 Hmisa2 Lmenv2 Hsenv2 Hhtif2 Lpc2 Hpma2
          with "Hint Hgpr Hupt") as "[HOk | HErr]".
  - iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
    iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
              (C_LBU (uimm, Cregidx i0, Cregidx i1))
              (LOAD (zero_extend' 12 uimm, creg2reg_idx (Cregidx i1),
                     creg2reg_idx (Cregidx i0), true, 1))
              RETIRE_SUCCESS s_x Lmi Hdec Hzcaf
              (exec_execute_C_LBU_U uimm (Cregidx i0) (Cregidx i1) s2) Hexec
              u_result_ok_retire I Hmi Hnpceq
              with "Hint Hgpr Hnpc Hupt Hcfg").
  - iDestruct "HErr" as (e vaX) "(%Hexec & %Hue & Hint & Hgpr & Hupt)".
    iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
              (C_LBU (uimm, Cregidx i0, Cregidx i1))
              (LOAD (zero_extend' 12 uimm, creg2reg_idx (Cregidx i1),
                     creg2reg_idx (Cregidx i0), true, 1))
              (rv64d_types.Trap (User, make_sync_exception e vaX, va)) s2 Lmi Hdec Hzcaf
              (exec_execute_C_LBU_U uimm (Cregidx i0) (Cregidx i1) s2) Hexec
              (u_result_ok_trap e vaX va Hue) I eq_refl eq_refl
              with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

Section MemArmsU2.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (pt : uptd).

  Lemma mem_exec_store_1 (imm : mword 12) (rs2 rs1 : mword 5)
      (g : regfile) (pc : mword 64) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    register_lookup PC s.(sregs) = pc ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (s_x : mstate),
        ⌜exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (va : mword 64),
        ⌜exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e va, pc), s)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        mstate_interp s ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Lpc Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Store Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    set (dat := autocast (T:=mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul 1 8) 1) 0) : mword (8 * 1)).
    iMod (user_pt_vmem_write_addr_store_classify_1 pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) va pc dat s
            Hwf Hcov (is_aligned_vaddr_1 va) Hmisa Hmenv Hhtif Lpc Lcp HSXL HMPRV Hpma
            with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
    - iDestruct "HOk" as (w sig') "(%Hvw & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      set (s_x := MState sig'.(sregs) (write_bytes sig'.(mem) (u_walk_pa w va) (Z.to_N 1)
                    (autocast (T:=mword) (subrange_vec_dec dat (8 * (0 + 1) * 1 - 1) (8 * 0 * 1)) : mword (8 * 1))) sig'.(mdev)).
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) 1 dat (Store Data) false false false) s
                        = Some (Ok true, s_x)).
      { apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) 1 dat (Store Data) false false false Sv39
                 (Ok true) s s_x Lcp Heff Hpml Htm).
        fold va. exact Hvw. }
      pose proof (exec_execute_STORE_u_ok imm rs2 rs1 1 true s s_x eq_refl) as Hexec0.
      assert (Hexec : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s = Some (RETIRE_SUCCESS, s_x)).
      { apply Hexec0. fold dat. exact Hvwrite. }
      iModIntro. iLeft. iExists s_x.
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iSplitR; [ iPureIntro; exact Hexec |].
      iSplitR.
      { iPureIntro. unfold s_x; cbn [sregs]. apply Tr. vm_compute; reflexivity. }
      iSplitR.
      { iPureIntro. unfold s_x; cbn [sregs]. apply Tr. vm_compute; reflexivity. }
      unfold mstate_interp.
      iSplitL "Hreg Hgh Hdev".
      { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as "(%Herr & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) 1 dat (Store Data) false false false) s
                        = Some (Err (rv64d_types.Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)), s)).
      { apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) 1 dat (Store Data) false false false Sv39
                 (Err _) s s Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_STORE_u_err imm rs2 rs1 1
                    (rv64d_types.Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)) s s
                    eq_refl) as Hexec0.
      assert (Hexec : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
                      = Some (rv64d_types.Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc), s)).
      { apply Hexec0. fold dat. exact Hvwrite. }
      iModIntro. iRight. iExists (E_SAMO_Page_Fault tt), va.
      iSplitR; [iPureIntro; exact Hexec |]. iSplitR; [iPureIntro; reflexivity |].
      unfold mstate_interp. iFrame "Hreg Hgh Hdev Hgpr Hutlb Hudata".
      iPureIntro; split; assumption.
  Qed.

End MemArmsU2.

Lemma exec_execute_C_SB_U (uimm : mword 2) (rsc1 rsc2 : cregidx) (s : mstate) :
  exec (execute (C_SB (uimm, rsc1, rsc2))) s
    = Some (ExecuteAs (STORE (zero_extend' 12 uimm, creg2reg_idx rsc2, creg2reg_idx rsc1, 1)), s).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SB_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SB p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[uimm rsc1] rsc2]. destruct rsc1 as [i1]. destruct rsc2 as [i2].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s2 := set_reg sigma_f nextPC (add_vec_int va 2)).
  iDestruct (post_fetch_uconfig C 2 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp2 & Hmsok2 & Hmisa2 & Lmenv2 & Hsenv2 & Hhtif2 & Hpma2) & Lpc2 & Hzcaf & Lmi).
  iMod (mem_exec_store_1 pt (zero_extend' 12 uimm)
          (zero_extend' 5 (concat_vec ('b"1") i2))
          (zero_extend' 5 (concat_vec ('b"1") i1)) g va s2
          Lcp2 Hmsok2 Hmisa2 Lmenv2 Hsenv2 Hhtif2 Lpc2 Hpma2
          with "Hint Hgpr Hupt") as "[HOk | HErr]".
  - iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
    iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
              (C_SB (uimm, Cregidx i1, Cregidx i2))
              (STORE (zero_extend' 12 uimm, creg2reg_idx (Cregidx i2), creg2reg_idx (Cregidx i1), 1))
              RETIRE_SUCCESS s_x Lmi Hdec Hzcaf
              (exec_execute_C_SB_U uimm (Cregidx i1) (Cregidx i2) s2) Hexec
              u_result_ok_retire I Hmi Hnpceq
              with "Hint Hgpr Hnpc Hupt Hcfg").
  - iDestruct "HErr" as (e vaX) "(%Hexec & %Hue & Hint & Hgpr & Hupt)".
    iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
              (C_SB (uimm, Cregidx i1, Cregidx i2))
              (STORE (zero_extend' 12 uimm, creg2reg_idx (Cregidx i2), creg2reg_idx (Cregidx i1), 1))
              (rv64d_types.Trap (User, make_sync_exception e vaX, va)) s2 Lmi Hdec Hzcaf
              (exec_execute_C_SB_U uimm (Cregidx i1) (Cregidx i2) s2) Hexec
              (u_result_ok_trap e vaX va Hue) I eq_refl eq_refl
              with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* ===================================================================== *)
(* §13 The STORE mirror of the read pipeline (§8-§12): write_classify_fold  *)
(*     (dual-state sstS-after-write / sttS-after-translate + free           *)
(*     exec_mem_write_ea_g), mem_write_misaligned_total, mem_write_total     *)
(*     (aligned §5 store classify / misaligned split), mem_exec_store_k      *)
(*     engine (no gpr write; store absorbed by udata_own), and the          *)
(*     compressed STORE arms C_SW/C_SD/C_SH/C_SWSP/C_SDSP.                    *)
(* ===================================================================== *)
Unset Keyed Unification.

Section MisWriteClassify.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)) (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hwrite_plain : forall (addr : mword 64) (dd : mword (8 * bytes)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) bytes dd tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N bytes) dd) s.(mdev))).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa).
  Context (Hwf : upt_acc_wf um) (Hcov : udata_cov um data).
  Context (W : Z) (va : mword 64) (dat : mword (8 * W)).
  Context (σ0 : mstate).

  Notation cva k := (add_vec_int va (Z.of_nat k * bytes)).

  Definition wchunk (k' : nat) (s : mstate) : mstate :=
    match exec (translateAddr (Virtaddr (cva k')) (Store Data)) s with
    | Some (Ok (Physaddr p, _, _), stt) =>
        match exec (mem_write_value (Physaddr p) bytes (wv W bytes dat k') (Store Data) PBMT_PMA false false false) stt with
        | Some (Ok _, s'') => s'' | _ => stt end
    | _ => s end.
  Fixpoint sstS (k : nat) : mstate :=
    match k with O => σ0 | S k' => wchunk k' (sstS k') end.
  Definition sttS (k : nat) : mstate :=
    match exec (translateAddr (Virtaddr (cva k)) (Store Data)) (sstS k) with
    | Some (Ok (Physaddr _, _, _), stt) => stt | _ => sstS k end.
  Definition spaS (k : nat) : mword 64 :=
    match exec (translateAddr (Virtaddr (cva k)) (Store Data)) (sstS k) with
    | Some (Ok (Physaddr p, _, _), _) => p | _ => zeros' 64 end.

  Lemma write_classify_fold (M : nat) :
    (forall k, (k < M)%nat -> is_aligned_vaddr (Virtaddr (cva k)) bytes = true) ->
    cfg_okR σ0 ->
    reg_interp σ0.(sregs) -∗ gen_heap_interp σ0.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ( (⌜forall k, (k < M)%nat ->
         exec (translateAddr (Virtaddr (cva k)) (Store Data)) (sstS k)
           = Some (Ok (Physaddr (spaS k), PBMT_PMA, init_ext_ptw), sttS k)⌝ ∗
       ⌜forall k, (k < M)%nat ->
         exec (mem_write_ea (Physaddr (spaS k)) bytes false false false) (sttS k)
           = Some (Ok tt, sttS k)⌝ ∗
       ⌜forall k, (k < M)%nat ->
         exec (mem_write_value (Physaddr (spaS k)) bytes (wv W bytes dat k) (Store Data) PBMT_PMA false false false) (sttS k)
           = Some (Ok true, sstS (S k))⌝ ∗
       ⌜(sstS M).(mdev) = σ0.(mdev)⌝ ∗ ⌜cfg_okR (sstS M)⌝ ∗
       ⌜register_lookup (R_bool minstret_increment) (sstS M).(sregs) = register_lookup (R_bool minstret_increment) σ0.(sregs)⌝ ∗
       ⌜register_lookup nextPC (sstS M).(sregs) = register_lookup nextPC σ0.(sregs)⌝ ∗
       reg_interp (sstS M).(sregs) ∗ gen_heap_interp (sstS M).(mem) ∗
       utlb_inv_pt uroot tfp um ∗ udata_own data)
     ∨ (∃ j : nat, ⌜(j < M)%nat⌝ ∗
         ⌜forall k, (k < j)%nat ->
           exec (translateAddr (Virtaddr (cva k)) (Store Data)) (sstS k)
             = Some (Ok (Physaddr (spaS k), PBMT_PMA, init_ext_ptw), sttS k)⌝ ∗
         ⌜forall k, (k < j)%nat ->
           exec (mem_write_ea (Physaddr (spaS k)) bytes false false false) (sttS k)
             = Some (Ok tt, sttS k)⌝ ∗
         ⌜forall k, (k < j)%nat ->
           exec (mem_write_value (Physaddr (spaS k)) bytes (wv W bytes dat k) (Store Data) PBMT_PMA false false false) (sttS k)
             = Some (Ok true, sstS (S k))⌝ ∗
         ⌜u_fault_flavor (Store Data) tfp um (cva j)⌝ ∗
         ⌜cfg_okR (sstS j)⌝ ∗ ⌜(sstS j).(mdev) = σ0.(mdev)⌝ ∗
         ⌜register_lookup (R_bool minstret_increment) (sstS j).(sregs) = register_lookup (R_bool minstret_increment) σ0.(sregs)⌝ ∗
         ⌜register_lookup nextPC (sstS j).(sregs) = register_lookup nextPC σ0.(sregs)⌝ ∗
         reg_interp (sstS j).(sregs) ∗ gen_heap_interp (sstS j).(mem) ∗
         utlb_inv_pt uroot tfp um ∗ udata_own data))%I.
  Proof.
    induction M as [|M' IH]; intros Hal Hcfg; iIntros "Hri Hgh Hinv Hdata".
    - iModIntro. iLeft. iFrame. iPureIntro.
      split; [intros; lia|]. split; [intros; lia|]. split; [intros; lia|].
      split; [reflexivity|]. split; [exact Hcfg|]. split; [reflexivity|]. reflexivity.
    - iMod (IH ltac:(intros; apply Hal; lia) Hcfg with "Hri Hgh Hinv Hdata") as "[HAll | HF]".
      + iDestruct "HAll" as "(%Htr & %Hea & %Hwvf & %Hmdev & %Hcfg' & %Hmi & %Hnpc & Hri & Hgh & Hinv & Hdata)".
        destruct (data_classify (Store Data) tfp um (cva M') (or_intror (or_intror (or_introl eq_refl))) Hwf)
          as [ (w & Hum & Hok & Hcanon) | Hfault ].
        * pose proof Hcfg' as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & Hmprv & Hall).
          iMod (user_pt_store_data_g bytes Hb Hb8 Hbdvd Huintb Hwrite_plain
                  uroot tfp um data w (cva M') (wv W bytes dat M') (sstS M')
                  Hum Hok Hcov (Hal M' ltac:(lia)) Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
                  with "Hri Hgh Hinv Hdata")
            as (σ') "(%Htr0 & %Hwv0 & %Hmdev0 & %Hsregs & Hri & Hgh & Hinv & Hdata)".
          assert (Hstt : sttS M' = σ').
          { unfold sttS. rewrite Htr0. reflexivity. }
          assert (Hspa : spaS M' = u_walk_pa w (cva M')).
          { unfold spaS. rewrite Htr0. reflexivity. }
          assert (Hstep : sstS (S M') = MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w (cva M')) (Z.to_N bytes) (wv W bytes dat M')) σ'.(mdev)).
          { cbn [sstS]. unfold wchunk. rewrite Htr0. rewrite Hwv0. reflexivity. }
          assert (Ttr : forall r : register, register_beq r tlb = false ->
                    register_lookup r σ'.(sregs) = register_lookup r (sstS M').(sregs)).
          { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
              [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
          iModIntro. iLeft.
          set (X := sstS (S M')).
          assert (HXm : X = MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w (cva M')) (Z.to_N bytes) (wv W bytes dat M')) σ'.(mdev)).
          { unfold X. exact Hstep. }
          rewrite HXm. iFrame.
          iPureIntro. split; [| split; [| split; [| split; [| split; [| split]]]]].
          -- intros k Hk. destruct (Nat.eq_dec k M') as [->|Hne].
             ++ rewrite Hspa Hstt. exact Htr0.
             ++ apply Htr; lia.
          -- intros k Hk. destruct (Nat.eq_dec k M') as [->|Hne].
             ++ rewrite Hspa Hstt. apply exec_mem_write_ea_g.
             ++ apply Hea; lia.
          -- intros k Hk. destruct (Nat.eq_dec k M') as [->|Hne].
             ++ rewrite Hspa Hstt Hstep. exact Hwv0.
             ++ apply Hwvf; lia.
          -- cbn [mdev]. rewrite Hmdev0. exact Hmdev.
          -- cbn [sregs].
             exact (cfg_okR_pres (sstS M') σ' Hsregs Hcfg').
          -- cbn [sregs].
             rewrite (Ttr (R_bool minstret_increment) ltac:(vm_compute; reflexivity)). exact Hmi.
          -- cbn [sregs].
             rewrite (Ttr nextPC ltac:(vm_compute; reflexivity)). exact Hnpc.
        * iModIntro. iRight. iExists M'.
          iFrame. iPureIntro. split; [lia|]. split; [exact Htr|]. split; [exact Hea|]. split; [exact Hwvf|].
          split; [exact Hfault|]. split; [exact Hcfg'|]. split; [exact Hmdev|].
          split; [exact Hmi|]. exact Hnpc.
      + iDestruct "HF" as (j) "(%Hj & %Htr & %Hea & %Hwvf & %Hfl & %Hcfgj & %Hmdevj & %Hmij & %Hnpcj & Hri & Hgh & Hinv & Hdata)".
        iModIntro. iRight. iExists j. iFrame. iPureIntro.
        split; [lia|]. split; [exact Htr|]. split; [exact Hea|]. split; [exact Hwvf|]. split; [exact Hfl|].
        split; [exact Hcfgj|]. split; [exact Hmdevj|]. split; [exact Hmij|]. exact Hnpcj.
  Qed.

End MisWriteClassify.


Lemma ws_seq_true (N : nat) : ws_seq (fun _ => true) N = true.
Proof. induction N as [|N IH]; [reflexivity | cbn [ws_seq]; rewrite IH; reflexivity]. Qed.

Section MemWriteTot.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (bytes : Z).
  Context (Hb : 0 < bytes) (Hb8 : bytes <= 8) (Hbdvd : (bytes | 4096)) (Huintb : uint (to_bits 64 bytes) = bytes).
  Context (Hwrite_plain : forall (addr : mword 64) (dd : mword (8 * bytes)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) bytes dd tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N bytes) dd) s.(mdev))).
  Context (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa).
  Context (Hwf : upt_acc_wf um) (Hcov : udata_cov um data).

  Notation cvaW va k := (add_vec_int va (Z.of_nat k * bytes)).

  Lemma mem_write_misaligned_total (W : Z) (N : nat) (va : mword 64) (dat : mword (8 * W)) (s : mstate) :
    (1 <= N)%nat -> Z.of_nat N * bytes = W ->
    is_aligned_vaddr (Virtaddr va) W = false ->
    exec (split_misaligned (Virtaddr va) W) s = Some ((Z.of_nat N, bytes), s) ->
    (forall k, (k < N)%nat -> is_aligned_vaddr (Virtaddr (cvaW va k)) bytes = true) ->
    cfg_okR s ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (σ' : mstate),
        ⌜exec (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s = Some (Ok true, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pc : mword 64),
        ⌜exec (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pc)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros HN Hwidth Hnal Hsplit Halk Hcfg.
    iIntros "Hreg Hgh Hutlb Hudata".
    iMod (write_classify_fold bytes Hb Hb8 Hbdvd Huintb Hwrite_plain uroot tfp um data Hwf Hcov
            W va dat s N Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HAll | HF]".
    - iDestruct "HAll" as "(%Htr & %Hea & %Hwvf & %Hmdev & %Hcfgn & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      pose proof (exec_vmem_write_addr_misaligned_split W bytes va dat N
                    (spaS bytes W va dat s) (fun _ => true) (sttS bytes W va dat s) (sstS bytes W va dat s)
                    HN Hb Htr Hea Hwvf Hnal Hsplit) as Hvw.
      rewrite ws_seq_true in Hvw.
      iModIntro. iLeft. iExists (sstS bytes W va dat s N).
      iFrame "Hreg Hgh Hutlb Hudata". iPureIntro. split; [exact Hvw |]. split; [exact Hmdev|].
      split; [exact Hmi | exact Hnpc].
    - iDestruct "HF" as (j) "(%Hj & %Htr & %Hea & %Hwvf & %Hfl & %Hcfgj & %Hmdevj & %Hmij & %Hnpcj & Hreg & Hgh & Hutlb & Hudata)".
      pose proof Hcfgj as (Hmisaj & Hmenvj & Hhtifj & Hcpj & HSXLj & HMPRVj & Hpmaj).
      iDestruct (utlb_inv_pt_translateAddr_u_fault (Store Data) uroot tfp um (cvaW va j)
                   (E_SAMO_Page_Fault tt) (sstS bytes W va dat s j) Hfl Hhtifj Hcpj HSXLj
                   (exec_effectivePrivilege_mprv0 (Store Data)
                      (register_lookup mstatus (sstS bytes W va dat s j).(sregs)) User (sstS bytes W va dat s j) HMPRVj)
                   (exec_is_shadow_stack_u_acc (Store Data) (sstS bytes W va dat s j) (or_intror (or_intror (or_introl eq_refl))))
                   Hpmaj
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   with "Hreg Hgh Hutlb") as %Htrf.
      set (pcj := register_lookup PC (sstS bytes W va dat s j).(sregs)).
      assert (Hstepsj : sstS bytes W va dat s (S j) = sstS bytes W va dat s j).
      { cbn [sstS]. unfold wchunk.
        change (bits_of_virtaddr (Virtaddr va)) with va in Htrf.
        rewrite Htrf. reflexivity. }
      assert (HtrF : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (Z.of_nat j * bytes))) (Store Data)) (sstS bytes W va dat s j)
                     = Some (Err (E_SAMO_Page_Fault tt, tt), sstS bytes W va dat s (S j))).
      { change (bits_of_virtaddr (Virtaddr va)) with va. rewrite Hstepsj. exact Htrf. }
      assert (HcpF : register_lookup cur_privilege (sstS bytes W va dat s (S j)).(sregs) = User)
        by (rewrite Hstepsj; exact Hcpj).
      assert (HpcF : register_lookup PC (sstS bytes W va dat s (S j)).(sregs) = pcj)
        by (rewrite Hstepsj; reflexivity).
      pose proof (vmem_write_split_fault W bytes va pcj dat (E_SAMO_Page_Fault tt)
                    N j (spaS bytes W va dat s) (fun _ => true) (sttS bytes W va dat s) (sstS bytes W va dat s)
                    HN Hb Hj Htr Hea Hwvf HtrF HcpF HpcF Hnal Hsplit) as Hvw.
      rewrite Hstepsj in Hvw.
      iModIntro. iRight.
      iExists (sstS bytes W va dat s j), (E_SAMO_Page_Fault tt),
        (add_vec_int (bits_of_virtaddr (Virtaddr va)) (Z.of_nat j * bytes)), pcj.
      iFrame "Hreg Hgh Hutlb Hudata". iPureIntro.
      split; [exact Hvw |]. split; [reflexivity |]. split; [exact Hmdevj|].
      split; [exact Hmij | exact Hnpcj].
  Qed.

End MemWriteTot.

Section MemWriteTotalDisp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_write_total (k : Z)
      (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k)
      (Hwrite_plain_k : forall (addr : mword 64) (dd : mword (8 * k)) s,
         dev_addr addr = false ->
         exec (write_ram rv64d_types.Write_plain (Physaddr addr) k dd tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) dd) s.(mdev)))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (Hwf : upt_acc_wf um) (Hcov : udata_cov um data)
      (va pc : mword 64) (dat : mword (8 * k)) (s : mstate) :
    cfg_okR s -> register_lookup PC s.(sregs) = pc ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (σ' : mstate),
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false) s = Some (Ok true, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (Store Data) false false false) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗ ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros Hcfg Lpc.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & HMPRV & Hpma).
    iIntros "Hreg Hgh Hutlb Hudata".
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    - iMod (user_pt_vmem_write_addr_store_classify k Hk Hk8 Hkdvd Huintk Hwrite_plain_k
              uroot tfp um data va pc dat s Hwf Hcov Hal Hmisa Hmenv Hhtif Lpc Hcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
      + iDestruct "HOk" as (w σ') "(%Hvw & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        iModIntro. iLeft.
        iExists (MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k)
                   (autocast (T := mword) (subrange_vec_dec dat (8 * (0 + 1) * k - 1) (8 * 0 * k)))) σ'.(mdev)).
        cbn [sregs mem mdev]. iFrame. iPureIntro.
        split; [exact Hvw |]. split; [exact Hmdev|].
        split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
      + iDestruct "HErr" as "(%Herr & Hreg & Hgh & Hutlb & Hudata)".
        iModIntro. iRight. iExists s, (E_SAMO_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - destruct (split_misaligned_derive k va s HkW Hal)
        as (N & bytes & HN & Hwidth & Hbpos & Hblt & Hbdvd & Huintb & Hsplit & Halk).
      assert (Hblt8 : bytes < 8) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; lia).
      destruct (pow2_le8 bytes Hbpos Hblt8 Hbdvd) as [Hbe|[Hbe|Hbe]]; subst bytes.
      + iMod (mem_write_misaligned_total 1 ltac:(lia) ltac:(lia) ltac:(exists 4096; reflexivity)
                ltac:(vm_compute; reflexivity) exec_write_ram_plain_1 uroot tfp um data Hwf Hcov
                k N va dat s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (σ') "(%Hvw & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists σ'. iFrame. iPureIntro. split; [exact Hvw |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
      + iMod (mem_write_misaligned_total 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity)
                ltac:(vm_compute; reflexivity) exec_write_ram_plain_2 uroot tfp um data Hwf Hcov
                k N va dat s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (σ') "(%Hvw & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists σ'. iFrame. iPureIntro. split; [exact Hvw |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
      + iMod (mem_write_misaligned_total 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
                ltac:(vm_compute; reflexivity) exec_write_ram_plain_4 uroot tfp um data Hwf Hcov
                k N va dat s HN Hwidth Hal Hsplit Halk Hcfg with "Hreg Hgh Hutlb Hudata") as "[HOk | HErr]".
        * iDestruct "HOk" as (σ') "(%Hvw & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iLeft. iExists σ'. iFrame. iPureIntro. split; [exact Hvw |]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
        * iDestruct "HErr" as (σ' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
          iModIntro. iRight. iExists σ', e, xv, pcx. iFrame. iPureIntro. split; [exact Herr|]. split; [exact Hue|]. split; [exact Hmdev|]. split; [exact Hmi | exact Hnpc].
  Qed.

End MemWriteTotalDisp.

Section MemStoreEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_store_k (pt : uptd) (k : Z)
      (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k)
      (Hwrite_plain_k : forall (addr : mword 64) (dd : mword (8 * k)) s,
         dev_addr addr = false ->
         exec (write_ram rv64d_types.Write_plain (Physaddr addr) k dd tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) dd) s.(mdev)))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (imm : mword 12) (rs2 rs1 : mword 5)
      (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (s_x : mstate),
        ⌜exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Store Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    set (dat := autocast (T:=mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul k 8) 1) 0) : mword (8 * k)).
    assert (Hcfg : cfg_okR s). { unfold cfg_okR. repeat split; assumption. }
    assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; vm_compute; reflexivity).
    iMod (mem_write_total k Hk Hk8 Hkdvd Huintk Hwrite_plain_k HkW
            pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) Hwf Hcov va
            (register_lookup PC s.(sregs)) dat s Hcfg eq_refl with "Hreg Hgh Hutlb Hudata")
      as "[HOk | HErr]".
    - iDestruct "HOk" as (sig') "(%Hvw & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) k dat (Store Data) false false false) s = Some (Ok true, sig')).
      { apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k dat (Store Data) false false false Sv39 (Ok true) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvw. }
      pose proof (exec_execute_STORE_u_ok imm rs2 rs1 k true s sig' Hkle) as Hexec0.
      assert (Hexec : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s = Some (RETIRE_SUCCESS, sig')).
      { apply Hexec0. fold dat. exact Hvwrite. }
      iModIntro. iLeft. iExists sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (sign_extend' 64 imm) k dat (Store Data) false false false) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k dat (Store Data) false false false Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_STORE_u_err imm rs2 rs1 k (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s sig' Hkle) as Hexec0.
      assert (Hexec : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), sig')).
      { apply Hexec0. fold dat. exact Hvwrite. }
      iModIntro. iRight. iExists e, xv, pcx, sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hue |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End MemStoreEngine.

(* ===================================================================== *)
(* §14 SP-loads (C_LWSP/C_LDSP): rd is a full regidx that CAN be 0.  The    *)
(*     rd=0 path retires WITHOUT a gpr write (wX x0 = no-op):               *)
(*     exec_execute_LOAD_u_ok_rd0 + mem_exec_load_k_rd0.  The arm dispatches *)
(*     on uint rd =? 0 to the rd0 engine (no write) or mem_exec_load_k.     *)
(* ===================================================================== *)
Section MemLoadRd0.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_load_k_rd0 (pt : uptd) (k : Z)
      (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k)
      (Hread_plain_k : forall (addr : mword 64) (w : mword (8 * k)) s,
         dev_addr addr = false ->
         (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
         exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool)
      (g : regfile) (s : mstate) :
    uint rd = 0 ->
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Hrd Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Load Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (sign_extend' 64 imm)).
    assert (Hcfg : cfg_okR s). { unfold cfg_okR. repeat split; assumption. }
    assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|[Hkv|Hkv]]; subst k; vm_compute; reflexivity).
    iMod (mem_read_total k Hk Hk8 Hkdvd Huintk Hread_plain_k HkW
            pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) Hwf Hcov va
            (register_lookup PC s.(sregs)) s Hcfg eq_refl with "Hreg Hgh Hutlb Hudata")
      as "[HOk | HErr]".
    - iDestruct "HOk" as (dvv sig') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) k (Load Data) false false false) s = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data) false false false Sv39 (Ok dvv) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvr. }
      pose proof (exec_execute_LOAD_u_ok_rd0 imm rs1 rd is_unsigned k dvv s sig' Hkle Hrd Hvread) as Hexec.
      iModIntro. iLeft. iExists sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (sign_extend' 64 imm) k (Load Data) false false false) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data) false false false Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_LOAD_u_err imm rs1 rd is_unsigned k (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s sig' Hkle Hvread) as Hexec.
      iModIntro. iRight. iExists e, xv, pcx, sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hue |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End MemLoadRd0.

(* ===================================================================== *)
(* §14a WHOLE-ARM GENERICS.  mem_exec_store_k/mem_exec_load_k(_rd0) are      *)
(*     already instruction-size generic in k -- the only thing that varied  *)
(*     across the 11 k-width compressed arms (C_SW/SD/SH/SWSP/SDSP,          *)
(*     C_LH/LHU/LW/LD/LWSP/LDSP) was the concrete instruction, offset and    *)
(*     width baked into each arm's forwarding step.  Abstracting that over  *)
(*     a `forall st, exec (execute ci) st = Some (ExecuteAs base, st)`       *)
(*     hypothesis collapses all of them to ONE store lemma and ONE load     *)
(*     lemma (the load one internalizing the rd=0/rd<>0 split so it also    *)
(*     covers the two SP-relative loads).  arm_C_LBU_u/_C_SB_u stay outside *)
(*     (width-1 engines, whose Err shape differs -- see the module header). *)
(* ===================================================================== *)
Section MemArmGenericK.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma arm_c_store_u (C : ucfg) (pt : uptd) (E : coPset) (sigma sigma_f : mstate)
      (va : mword 64) (g : regfile) (h : mword 16) (ci : instruction)
      (k : Z) (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096))
      (Huintk : uint (to_bits 64 k) = k)
      (Hwrite_plain_k : forall (addr : mword 64) (dd : mword (8 * k)) s,
         dev_addr addr = false ->
         exec (write_ram rv64d_types.Write_plain (Physaddr addr) k dd tt) s
         = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) dd) s.(mdev)))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (off : mword 12) (rs2 rs1 : mword 5) :
    (forall st : mstate, exec (execute ci) st
        = Some (ExecuteAs (STORE (off, Regidx rs2, Regidx rs1, k)), st)) ->
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (ci, sigma_f) ->
    hw_config -∗ mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hforward Hcfg Hdec.
    iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
    set (s2 := set_reg sigma_f nextPC (add_vec_int va 2)).
    iDestruct (post_fetch_uconfig C 2 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
      as %((Lcp2 & Hmsok2 & Hmisa2 & Lmenv2 & Hsenv2 & Hhtif2 & Hpma2) & Lpc2 & Hzcaf & Lmi).
    iMod (mem_exec_store_k pt k Hk Hk8 Hkdvd Huintk Hwrite_plain_k HkW
            off rs2 rs1 g s2
            Lcp2 Hmsok2 Hmisa2 Lmenv2 Hsenv2 Hhtif2 Hpma2
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    - iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
                ci (STORE (off, Regidx rs2, Regidx rs1, k))
                RETIRE_SUCCESS s_x Lmi Hdec Hzcaf
                (Hforward s2) Hexec
                u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    - iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (rvc_finish_mem C pt E sigma sigma_f va h g _
                ci (STORE (off, Regidx rs2, Regidx rs1, k))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x Lmi Hdec Hzcaf
                (Hforward s2) Hexec
                (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  Qed.

  Lemma arm_c_load_u (C : ucfg) (pt : uptd) (E : coPset) (sigma sigma_f : mstate)
      (va : mword 64) (g : regfile) (h : mword 16) (ci : instruction)
      (k : Z) (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096))
      (Huintk : uint (to_bits 64 k) = k)
      (Hread_plain_k : forall (addr : mword 64) (w : mword (8 * k)) s,
         dev_addr addr = false ->
         (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
         exec (read_ram rv64d_types.Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s))
      (HkW : k = 2 \/ k = 4 \/ k = 8)
      (off : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) :
    (forall st : mstate, exec (execute ci) st
        = Some (ExecuteAs (LOAD (off, Regidx rs1, Regidx rd, is_unsigned, k)), st)) ->
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (ci, sigma_f) ->
    hw_config -∗ mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hforward Hcfg Hdec.
    iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
    set (s2 := set_reg sigma_f nextPC (add_vec_int va 2)).
    iDestruct (post_fetch_uconfig C 2 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
      as %((Lcp2 & Hmsok2 & Hmisa2 & Lmenv2 & Hsenv2 & Hhtif2 & Hpma2) & Lpc2 & Hzcaf & Lmi).
    destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
    - apply Z.eqb_eq in Hrd0.
      iMod (mem_exec_load_k_rd0 pt k Hk Hk8 Hkdvd Huintk Hread_plain_k HkW
              off rs1 rd is_unsigned g s2
              Hrd0 Lcp2 Hmsok2 Hmisa2 Lmenv2 Hsenv2 Hhtif2 Hpma2
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      + iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (rvc_finish_mem C pt E sigma sigma_f va h g g
                  ci (LOAD (off, Regidx rs1, Regidx rd, is_unsigned, k))
                  RETIRE_SUCCESS s_x Lmi Hdec Hzcaf
                  (Hforward s2) Hexec
                  u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (rvc_finish_mem C pt E sigma sigma_f va h g g
                  ci (LOAD (off, Regidx rs1, Regidx rd, is_unsigned, k))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x Lmi Hdec Hzcaf
                  (Hforward s2) Hexec
                  (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
    - apply Z.eqb_neq in Hrd0.
      iMod (mem_exec_load_k pt k Hk Hk8 Hkdvd Huintk Hread_plain_k HkW
              off rs1 rd is_unsigned g s2
              Hrd0 Lcp2 Hmsok2 Hmisa2 Lmenv2 Hsenv2 Hhtif2 Hpma2
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      + iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (rvc_finish_mem C pt E sigma sigma_f va h g (<[Regidx rd := v]> g)
                  ci (LOAD (off, Regidx rs1, Regidx rd, is_unsigned, k))
                  RETIRE_SUCCESS s_x Lmi Hdec Hzcaf
                  (Hforward s2) Hexec
                  u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (rvc_finish_mem C pt E sigma sigma_f va h g g
                  ci (LOAD (off, Regidx rs1, Regidx rd, is_unsigned, k))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x Lmi Hdec Hzcaf
                  (Hforward s2) Hexec
                  (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
  Qed.

  Lemma exec_execute_C_LH_U (uimm : mword 2) (rdc rsc1 : cregidx) (st : mstate) :
    exec (execute (C_LH (uimm, rdc, rsc1))) st
      = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx rsc1, creg2reg_idx rdc, false, 2)), st).
  Proof. apply exec_returnm. Qed.

  Lemma arm_C_LH_u (C : ucfg) (pt : uptd)
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LH p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hcfg Hdec.
    destruct p as [[uimm rdc] rsc1]. destruct rdc as [i0]. destruct rsc1 as [i1].
    iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LH (uimm, Cregidx i0, Cregidx i1)) 2
              ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 (or_introl eq_refl)
              (zero_extend' 12 uimm) (zero_extend' 5 (concat_vec ('b"1") i1))
              (zero_extend' 5 (concat_vec ('b"1") i0)) false
              (exec_execute_C_LH_U uimm (Cregidx i0) (Cregidx i1)) Hcfg Hdec).
  Qed.

  Lemma exec_execute_C_LHU_U (uimm : mword 2) (a b : cregidx) (st : mstate) :
    exec (execute (C_LHU (uimm, a, b))) st
      = Some (ExecuteAs (LOAD (zero_extend' 12 uimm, creg2reg_idx b, creg2reg_idx a, true, 2)), st).
  Proof. apply exec_returnm. Qed.

  Lemma arm_C_LHU_u (C : ucfg) (pt : uptd)
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LHU p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hcfg Hdec.
    destruct p as [[uimm rdc] rsc1]. destruct rsc1 as [i1]. destruct rdc as [i0].
    iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LHU (uimm, Cregidx i0, Cregidx i1)) 2
              ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 (or_introl eq_refl)
              (zero_extend' 12 uimm) (zero_extend' 5 (concat_vec ('b"1") i1))
              (zero_extend' 5 (concat_vec ('b"1") i0)) true
              (exec_execute_C_LHU_U uimm (Cregidx i0) (Cregidx i1)) Hcfg Hdec).
  Qed.

  Lemma exec_execute_C_LW_U (uimm : mword 5) (a b : cregidx) (st : mstate) :
    exec (execute (C_LW (uimm, a, b))) st
      = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")), creg2reg_idx a, creg2reg_idx b, false, 4)), st).
  Proof. apply exec_returnm. Qed.

  Lemma arm_C_LW_u (C : ucfg) (pt : uptd)
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LW p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hcfg Hdec.
    destruct p as [[uimm rsc] rdc]. destruct rsc as [i1]. destruct rdc as [i0].
    iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LW (uimm, Cregidx i1, Cregidx i0)) 4
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 (or_intror (or_introl eq_refl))
              (zero_extend' 12 (concat_vec uimm ('b"00"))) (zero_extend' 5 (concat_vec ('b"1") i1))
              (zero_extend' 5 (concat_vec ('b"1") i0)) false
              (exec_execute_C_LW_U uimm (Cregidx i1) (Cregidx i0)) Hcfg Hdec).
  Qed.

  Lemma exec_execute_C_LD_U (uimm : mword 5) (a b : cregidx) (st : mstate) :
    exec (execute (C_LD (uimm, a, b))) st
      = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), creg2reg_idx a, creg2reg_idx b, false, 8)), st).
  Proof. apply exec_returnm. Qed.

  Lemma arm_C_LD_u (C : ucfg) (pt : uptd)
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
      (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
    post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
    exec (ext_decode_compressed h) sigma_f = Some (C_LD p, sigma_f) ->
    hw_config -∗
    mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
    gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
    rvc_post C pt E sigma sigma_f va h g.
  Proof.
    intros Hcfg Hdec.
    destruct p as [[uimm rsc] rdc]. destruct rsc as [i1]. destruct rdc as [i0].
    iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LD (uimm, Cregidx i1, Cregidx i0)) 8
              ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 (or_intror (or_intror eq_refl))
              (zero_extend' 12 (concat_vec uimm ('b"000"))) (zero_extend' 5 (concat_vec ('b"1") i1))
              (zero_extend' 5 (concat_vec ('b"1") i0)) false
              (exec_execute_C_LD_U uimm (Cregidx i1) (Cregidx i0)) Hcfg Hdec).
  Qed.

End MemArmGenericK.

Lemma exec_execute_C_SW_U (uimm : mword 5) (a b : cregidx) (st : mstate) :
  exec (execute (C_SW (uimm, a, b))) st
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"00")), creg2reg_idx b, creg2reg_idx a, 4)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SW_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SW p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[uimm rsc1] rsc2]. destruct rsc1 as [i1]. destruct rsc2 as [i2].
  iApply (arm_c_store_u C pt E sigma sigma_f va g h (C_SW (uimm, Cregidx i1, Cregidx i2)) 4
            ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
            exec_write_ram_plain_4 (or_intror (or_introl eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"00"))) (zero_extend' 5 (concat_vec ('b"1") i2))
            (zero_extend' 5 (concat_vec ('b"1") i1))
            (exec_execute_C_SW_U uimm (Cregidx i1) (Cregidx i2)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_SD_U (uimm : mword 5) (a b : cregidx) (st : mstate) :
  exec (execute (C_SD (uimm, a, b))) st
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), creg2reg_idx b, creg2reg_idx a, 8)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SD_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 5 * cregidx * cregidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SD p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[uimm rsc1] rsc2]. destruct rsc1 as [i1]. destruct rsc2 as [i2].
  iApply (arm_c_store_u C pt E sigma sigma_f va g h (C_SD (uimm, Cregidx i1, Cregidx i2)) 8
            ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
            exec_write_ram_plain_8 (or_intror (or_intror eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"000"))) (zero_extend' 5 (concat_vec ('b"1") i2))
            (zero_extend' 5 (concat_vec ('b"1") i1))
            (exec_execute_C_SD_U uimm (Cregidx i1) (Cregidx i2)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_SH_U (uimm : mword 2) (a b : cregidx) (st : mstate) :
  exec (execute (C_SH (uimm, a, b))) st
    = Some (ExecuteAs (STORE (zero_extend' 12 uimm, creg2reg_idx b, creg2reg_idx a, 2)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SH_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 2 * cregidx * cregidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SH p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[uimm rsc1] rsc2]. destruct rsc1 as [i1]. destruct rsc2 as [i2].
  iApply (arm_c_store_u C pt E sigma sigma_f va g h (C_SH (uimm, Cregidx i1, Cregidx i2)) 2
            ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
            exec_write_ram_plain_2 (or_introl eq_refl)
            (zero_extend' 12 uimm) (zero_extend' 5 (concat_vec ('b"1") i2))
            (zero_extend' 5 (concat_vec ('b"1") i1))
            (exec_execute_C_SH_U uimm (Cregidx i1) (Cregidx i2)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_SWSP_U (uimm : mword 6) (rs2 : regidx) (st : mstate) :
  exec (execute (C_SWSP (uimm, rs2))) st
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"00")), rs2, sp, 4)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SWSP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 6 * regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SWSP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [uimm rs2]. destruct rs2 as [r2].
  iApply (arm_c_store_u C pt E sigma sigma_f va g h (C_SWSP (uimm, Regidx r2)) 4
            ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
            exec_write_ram_plain_4 (or_intror (or_introl eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"00"))) r2 (zero_extend' 5 ('b"10"))
            (exec_execute_C_SWSP_U uimm (Regidx r2)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_SDSP_U (uimm : mword 6) (rs2 : regidx) (st : mstate) :
  exec (execute (C_SDSP (uimm, rs2))) st
    = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), rs2, sp, 8)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_SDSP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 6 * regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_SDSP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [uimm rs2]. destruct rs2 as [r2].
  iApply (arm_c_store_u C pt E sigma sigma_f va g h (C_SDSP (uimm, Regidx r2)) 8
            ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
            exec_write_ram_plain_8 (or_intror (or_intror eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"000"))) r2 (zero_extend' 5 ('b"10"))
            (exec_execute_C_SDSP_U uimm (Regidx r2)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_LWSP_U (uimm : mword 6) (rd : regidx) (st : mstate) :
  exec (execute (C_LWSP (uimm, rd))) st
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")), sp, rd, false, 4)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_LWSP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 6 * regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_LWSP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [uimm rd]. destruct rd as [r].
  iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LWSP (uimm, Regidx r)) 4
            ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_plain_4 (or_intror (or_introl eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"00"))) (zero_extend' 5 ('b"10")) r false
            (exec_execute_C_LWSP_U uimm (Regidx r)) Hcfg Hdec).
Qed.

Lemma exec_execute_C_LDSP_U (uimm : mword 6) (rd : regidx) (st : mstate) :
  exec (execute (C_LDSP (uimm, rd))) st
    = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, rd, false, 8)), st).
Proof. apply exec_returnm. Qed.

Lemma arm_C_LDSP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (h : mword 16) (p : bits 6 * regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode_compressed h) sigma_f = Some (C_LDSP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 2)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 2 -∗ user_pt_inv pt -∗ user_cfg C -∗
  rvc_post C pt E sigma sigma_f va h g.
Proof.
  intros Hcfg Hdec.
  destruct p as [uimm rd]. destruct rd as [r].
  iApply (arm_c_load_u C pt E sigma sigma_f va g h (C_LDSP (uimm, Regidx r)) 8
            ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_plain_8 (or_intror (or_intror eq_refl))
            (zero_extend' 12 (concat_vec uimm ('b"000"))) (zero_extend' 5 ('b"10")) r false
            (exec_execute_C_LDSP_U uimm (Regidx r)) Hcfg Hdec).
Qed.

(* ===================================================================== *)
(*                          F R O N T I E R                                *)
(* ===================================================================== *)
(*                                                                         *)
(* ALL 13 COMPRESSED ARMS CLOSED (Qed, axiom-clean, type-matching          *)
(* UserTotalU's Variables; plugging them into rvc_exec_total_u_holds       *)
(* yields the fully-discharged  |- rvc_exec_total_u C pt E s v g):          *)
(*   LOADS: arm_C_LBU_u/_C_LH_u/_C_LHU_u/_C_LW_u/_C_LD_u (cregidx, rd<>0    *)
(*     via creg_nz), arm_C_LWSP_u/_C_LDSP_u (sp base; rd can be 0 -> §14    *)
(*     rd0 no-write path).                                                  *)
(*   STORES: arm_C_SB_u/_C_SH_u/_C_SW_u/_C_SD_u (cregidx), arm_C_SWSP_u/    *)
(*     _C_SDSP_u (sp base) -- §13 store mirror, no gpr write.               *)
(*                                                                         *)
(* THE PIPELINE (reusable): §8-§12 read (fold, ctz split-derivation §11,    *)
(* total classify, mem_exec_load_k engine) + §13 store mirror              *)
(* (write_classify_fold, mem_write_total, mem_exec_store_k) + §14 rd0.      *)
(* Any width k in {2,4,8}: total classify = case va aligned (§5 classify_k) *)
(* / misaligned (split_misaligned_derive gives (N,bytes); the fold folds    *)
(* the chunks -> all-good split retire / first-fault trap).                 *)
(*                                                                         *)
(* BASE arms (the 6 base memory Variables, separate future step): need the  *)
(* decode-width refinement in DecodeSetU (decodable_u does NOT constrain the *)
(* LOAD/STORE/... width; strengthen the memory cases to carry the width     *)
(* boolean, re-prove decode_total_u_set, thread into UserTotalU).           *)
(*                                                                         *)
(* PROVEN ABOVE (all Qed, no admits/axioms; compiles green against the     *)
(* current .vo tree):                                                      *)
(*                                                                         *)
(*  (1) exec_vmem_read_addr_translate_err / exec_vmem_write_addr_translate_*)
(*      _err -- the genuinely MISSING vmem primitive: a translateAddr Err  *)
(*      (page-fault) reduces to vmem_read_addr / vmem_write_addr = Err      *)
(*      (delegated Trap).  Every pre-existing UserMemAccess Err reduction   *)
(*      assumes translate = Ok and the mem_read/write fails; the page-fault *)
(*      path (which the fault head produces) had no vmem-level reduction.   *)
(*      A trimmed twin of exec_vmem_read_addr_aligned_err (the single       *)
(*      aligned iteration takes the [Err (e,_)] branch of the loop body's   *)
(*      translate match).                                                   *)
(*                                                                         *)
(*  (2) user_pt_vmem_read_addr_load_err / user_pt_vmem_write_addr_store_err *)
(*      -- the Err (FAULT) half of the va-generic data-access composer over *)
(*      utlb_inv_pt, the data analog of user_pt_fetch_fault (UserFetchPt).  *)
(*      Given an ALIGNED va whose translation faults (u_fault_flavor:       *)
(*      non-canonical / unmapped / denied), delivers the delegated User     *)
(*      trap  vmem_{read,write}_addr = Err (Trap (User, E_{Load,SAMO}_Page_ *)
(*      Fault, pc)), state unchanged.  Key fact used: for Load/Store Data   *)
(*      ALL THREE PTW errors collapse to the page fault (PTW_No_Permission  *)
(*      is not PTW_No_Access, so it takes the [_] arm of translationExcep-  *)
(*      tion), so the single-[e] fault head utlb_inv_pt_translateAddr_u_    *)
(*      fault fires.                                                        *)
(*                                                                         *)
(* The Ok (RETIRE) half of the composer already exists and is green:        *)
(*   user_pt_vmem_read_addr_load{,_8/_4/_2/_1}  (UserMemAccess.v)           *)
(*   user_pt_vmem_write_addr_store{,_8/_4/_2/_1}                            *)
(* so the va-generic Ok/Err DISJUNCTION is a case-split on the address      *)
(* classification (the data analog of fetch_classify, UserActiveClass.v):   *)
(*   u_data_ok acc um va  \/  u_fault_flavor acc tfp um va                  *)
(* -- route the first to user_pt_vmem_{read,write}_addr_{load,store} (Ok),  *)
(*    the second to the *_err composers above (Err).                        *)
(*                                                                         *)
(*  (3) [get_pmlen acc User = 0] BRIDGE (§2) -- exec_is_pmm_applicable_u /   *)
(*      exec_get_pmm_u_disabled / exec_get_pmlen_u.  The concrete blocker    *)
(*      the prior FRONTIER flagged, now CLOSED: is_pmm_applicable acc User   *)
(*      = true from MXR=0 (or_boolM's second disjunct); get_pmm User ->      *)
(*      currentlyEnabled Ext_S (=true, misa.S) -> read_senvcfg -> pinned     *)
(*      senvcfg=0 -> PMM_Disabled -> pmlen 0.  Generic over acc (takes the   *)
(*      three generic_neq facts, each a vm_compute at the call site).        *)
(*                                                                         *)
(*  (4) u_data_ok + data_classify (§3) -- the DATA analog of fetch_classify: *)
(*      any [acc] in [u_acc], any va, is either u_data_ok (mapped+ok+        *)
(*      canonical, the Ok/retire path) or u_fault_flavor (the Err/trap       *)
(*      path).  The total case-split every memory arm routes on.             *)
(*                                                                         *)
(*  (5) utlb_inv_pt_translationMode_U (§4) -- reads the Sv39-pinned satp     *)
(*      from utlb_inv_pt NON-consumingly, discharging the bridge's           *)
(*      [translationMode User = Sv39] premise while the invariant survives.  *)
(*                                                                         *)
(*  (6) user_pt_vmem_{read_addr_load,write_addr_store}_classify (§5),        *)
(*      width-generic + the 8 width instances (_classify_{8,4,2,1}) -- the   *)
(*      reusable ALIGNED Ok/Err DISJUNCTION composer.  ONE case-split on     *)
(*      data_classify: u_data_ok -> the UserMemAccess Ok composer; fault ->  *)
(*      the (2) *_err composer.  This is "build the Ok/Err split once" --     *)
(*      every LOAD/STORE arm consumes exactly these at each width.           *)
(*                                                                         *)
(* REMAINING (the arms themselves -- the reframe + two genuinely-new         *)
(* sub-layers; the classifier and bridge ingredients above are all green):  *)
(*                                                                         *)
(*  (A) The vmem_read / vmem_write BRIDGE CHAINING into an arm: apply        *)
(*      exec_vmem_read_u / _write_u (UserMemArms.v) at [s0 = set_reg         *)
(*      sigma_f nextPC (va+4)] with cur_privilege=User, effectivePrivilege=  *)
(*      User (exec_effectivePrivilege_mprv0 + MPRV=0), get_pmlen=0 (the (3)  *)
(*      BRIDGE), translationMode=Sv39 (the (5) extraction) -- reducing the   *)
(*      execute's [vmem_read (Regidx rs1) offset ...] to the [vmem_read_addr *)
(*      (rX rs1 + offset) ...] the (6) classifier delivers.  All ingredients *)
(*      are green; this is bookkeeping over the s0-transported config pins.  *)
(*                                                                         *)
(*  (B) The six base ARMS (arm_LOAD_u/_STORE_u/_AMO_u/_LOADRES_u/           *)
(*      _STORECON_u/_ZICBOP_u -> base_post) and the compressed arms         *)
(*      (arm_C_*_u -> rvc_post, each via ExecuteAs to a base LOAD/STORE).   *)
(*      Each: compute the runtime va = rs1val+offset, classify (Ok/Err),    *)
(*      apply the family execute fact (UserMemArms.v exec_execute_*_u_ok /   *)
(*      _err -- Ok IS the retire, Err IS the delegated trap), then reframe  *)
(*      into base_post/rvc_post.  The reframe is finish_gprwrite-shaped     *)
(*      (UserTotalU.v) but over the MOVED post-composer state (tlb-fill for *)
(*      loads, mem write for stores); dev_interp carries through unchanged  *)
(*      (sigma'.(mdev) = sigma.(mdev), reported by every composer).         *)
(*                                                                         *)
(*      SIGNATURE: the sibling's Variable arm_LOAD_u (UserTotalU.v) takes    *)
(*      the FOUR split config premises (MiEq ; cur_privilege=User ; PC=va ;  *)
(*      menvcfg=MENVCFG_S) NOT the whole post_fetch_cfg; but those four do   *)
(*      NOT carry the mstatus pins (MPRV=0 / MXR=0 / SXL) the Ok/Err/get_    *)
(*      pmlen composers need.  Since post_fetch_cfg (UserExec.v) is now      *)
(*      EXTENDED to carry the full user_mstatus_ok (the B1 spec gap is       *)
(*      CLOSED), the arms should take the WHOLE post_fetch_cfg as one        *)
(*      premise and destruct it for cur_privilege / mstatus pins / va-2-     *)
(*      align / menvcfg / MiEq -- i.e. the task's contract:                  *)
(*                                                                         *)
(*        arm_LOAD_u (E : coPset) (sigma sigma_f : mstate) (va : mword 64)  *)
(*            (g : regfile) (w : mword 32)                    *)
(*            (p : bits 12 * regidx * regidx * bool * word_width) :          *)
(*          post_fetch_cfg sigma_f va                                        *)
(*            (register_lookup (R_bool minstret_increment) sigma.(sregs)) -> *)
(*          exec (ext_decode w) sigma_f = Some (LOAD p, sigma_f) ->          *)
(*          hw_config -∗                                                     *)
(*          mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗     *)
(*          gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗                      *)
(*          user_pt_inv pt -∗ user_cfg C -∗ base_post E sigma sigma_f va w g *)
(*                                                                         *)
(*      (The sibling's four-premise Variable will need updating to this      *)
(*      post_fetch_cfg shape -- flagged for the parent to reconcile.)  The   *)
(*      width in [p] must additionally be shown in {1,2,4,8} from the decode *)
(*      (a decoder-width lemma) so the execute's [width<=?xlen_bytes] assert *)
(*      passes and the (6) classifier at the matching width applies.         *)
(*                                                                         *)
(*  DONE THIS ROUND (§6/§7 above, all Qed, no admits):                       *)
(*    * vmem_read_split_fault / vmem_write_split_fault -- the split-WITH-     *)
(*      FAULT composers: a misaligned plain LOAD/STORE whose J-th straddled  *)
(*      chunk translate-faults early-returns the User trap (J good chunks    *)
(*      folded via gbody/wgbody through the existing split_body machinery,   *)
(*      then fbody/wfbody at chunk J).  Supporting generic loop bricks:      *)
(*      execR_bind_inl, execR_untilMT'_fault, execR_untilMT'_chain_fault.    *)
(*      These are the misaligned-axis analog of data_classify's Err half --  *)
(*      the "one substantial missing layer" the prior frontier flagged.      *)
(*                                                                         *)
(*  (C) sub-layers the arms still need (built on §6/§7):                      *)
(*      * TOTAL misaligned read/write classify: combine the all-mapped split *)
(*        composer (retire, all chunks u_data_ok) with §6/§7 (fault at the   *)
(*        first bad chunk) via a decidable first-bad-chunk search + a PARTIAL *)
(*        fold (reuse split_load_fold / split_store_fold with N:=J to build  *)
(*        the good-prefix Htr/Hmr and state chain, then the fault head       *)
(*        utlb_inv_pt_translateAddr_u_fault at chunk J supplies HtrF).  This  *)
(*        is now bookkeeping over EXISTING bricks -- no new loop machinery.   *)
(*      * LR/SC/AMO Ok composers: LR needs LoadReserved-Data / res=true and  *)
(*        SC/AMO their own acc; the (6) classifier is hardcoded to Load/     *)
(*        Store Data / res=false, so LR/SC/AMO need acc/res-specific Ok      *)
(*        composers (user_pt_vmem_read_addr_lr_{4,8} / _sc_{4,8} already      *)
(*        exist in UserMemAccess.v for the aligned case; they still need     *)
(*        wrapping in a data_classify split like (6)).  LR/SC/AMO FAULT on   *)
(*        misalignment (exec_vmem_read_addr_misaligned_lr / _sc,             *)
(*        exec_execute_AMO_u_misaligned) so they need NO split -- only the   *)
(*        aligned Ok / translate-fault / misalign-fault three-way.           *)
(*                                                                         *)
(*  (D) ZICBOP (prefetch): execute_ZICBOP runs a real translateAddr and     *)
(*      ALWAYS retires (a prefetch fault is suppressed to a nop-retire in    *)
(*      the model); no gpr write -- a finish_unchanged-shaped reframe once   *)
(*      the translate Ok/Err absorption (either branch retires) is threaded. *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  BASE memory arms (offset +4, ext_decode): LOAD / STORE / ZICBOP /      *)
(*  AMO / LOADRES / STORECON.  Each concludes base_post directly (the LEFT  *)
(*  direct-execute disjunct -- no ExecuteAs).  The width is threaded from   *)
(*  the refined decodable_u (DecodeSetU) via UserTotalU's dispatch.         *)
(* ===================================================================== *)

Section BaseMemArms.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* Shared closer: the engine's (retire | delegated trap) result -> base_post. *)
  Lemma base_finish_mem
      (E : coPset) (sigma sigma_f : mstate) (va : mword 64) (w : mword 32)
      (g g' : regfile) (instr : instruction) (r0 : ExecutionResult)
      (s_x : mstate) :
    register_lookup (R_bool minstret_increment) sigma_f.(sregs)
       = register_lookup (R_bool minstret_increment) sigma.(sregs) ->
    exec (ext_decode w) sigma_f = Some (instr, sigma_f) ->
    is_lpad_instruction instr = false ->
    exec (execute instr) (set_reg sigma_f nextPC (add_vec_int va 4)) = Some (r0, s_x) ->
    u_result_ok r0 ->
    match r0 with ExecuteAs _ => False | _ => True end ->
    register_lookup (R_bool minstret_increment) s_x.(sregs)
       = register_lookup (R_bool minstret_increment) (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) ->
    register_lookup nextPC s_x.(sregs)
       = register_lookup nextPC (set_reg sigma_f nextPC (add_vec_int va 4)).(sregs) ->
    mstate_interp s_x -∗ gpr_file g' -∗ nextPC ↦ᵣ add_vec_int va 4 -∗
    user_pt_inv pt -∗ user_cfg C -∗
    base_post C pt E sigma sigma_f va w g.
  Proof.
    intros Lmi Hdec Hlpad Hexec Hok Hnex Hmi Hnpc.
    iIntros "Hint Hgpr Hnpc Hupt Hcfg". unfold base_post.
    iModIntro. iExists instr, r0, s_x, g', (add_vec_int va 4).
    iFrame "Hint Hgpr Hnpc Hupt Hcfg".
    iPureIntro. split_and!.
    - exact Hdec.
    - exact Hlpad.
    - left; exact Hexec.
    - exact Hok.
    - exact Hnex.
    - rewrite Hmi. unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity].
    - rewrite Hnpc. unfold set_reg; cbn [sregs]. apply register_lookup_set.
  Qed.

End BaseMemArms.

Lemma arm_LOAD_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (imm : bits 12) (rs1 rd : regidx) (is_unsigned : bool) (width : word_width) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
  exec (ext_decode w) sigma_f = Some (LOAD (imm, rs1, rd, is_unsigned, width), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs1 as [rs1]. destruct rd as [rd].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & Lpc0 & _ & Lmi).
  (* dispatch on width, then rd = 0 / rd <> 0 *)
  destruct Hwidth as [Hw|[Hw|[Hw|Hw]]]; subst width.
  - (* width 1 *)
    destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
    + apply Z.eqb_eq in Hrd0.
      iMod (mem_exec_load_1_rd0 pt imm rs1 rd is_unsigned g va s0
              Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Lpc0 Hpma0 with "Hint Hgpr Hupt")
        as "[HOk | HErr]".
      * iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv) "(%Hexec & %Hue & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))
                  (rv64d_types.Trap (User, make_sync_exception e xv, va)) s0
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv va Hue) I
                  eq_refl eq_refl with "Hint Hgpr Hnpc Hupt Hcfg").
    + apply Z.eqb_neq in Hrd0.
      iMod (mem_exec_load_1 pt imm rs1 rd is_unsigned g va s0
              Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Lpc0 Hpma0 with "Hint Hgpr Hupt")
        as "[HOk | HErr]".
      * iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g (<[Regidx rd := v]> g)
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv) "(%Hexec & %Hue & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))
                  (rv64d_types.Trap (User, make_sync_exception e xv, va)) s0
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv va Hue) I
                  eq_refl eq_refl with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 2 *)
    destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
    + apply Z.eqb_eq in Hrd0.
      iMod (mem_exec_load_k_rd0 pt 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_2 (or_introl eq_refl)
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
    + apply Z.eqb_neq in Hrd0.
      iMod (mem_exec_load_k pt 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_2 (or_introl eq_refl)
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g (<[Regidx rd := v]> g)
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 4 *)
    destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
    + apply Z.eqb_eq in Hrd0.
      iMod (mem_exec_load_k_rd0 pt 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_4 (or_intror (or_introl eq_refl))
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
    + apply Z.eqb_neq in Hrd0.
      iMod (mem_exec_load_k pt 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_4 (or_intror (or_introl eq_refl))
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g (<[Regidx rd := v]> g)
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 8 *)
    destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
    + apply Z.eqb_eq in Hrd0.
      iMod (mem_exec_load_k_rd0 pt 8 ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_8 (or_intror (or_intror eq_refl))
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
    + apply Z.eqb_neq in Hrd0.
      iMod (mem_exec_load_k pt 8 ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity)
              ltac:(vm_compute; reflexivity) exec_read_ram_plain_8 (or_intror (or_intror eq_refl))
              imm rs1 rd is_unsigned g s0 Hrd0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
              with "Hint Hgpr Hupt") as "[HOk | HErr]".
      * iDestruct "HOk" as (v s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g (<[Regidx rd := v]> g)
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8)) RETIRE_SUCCESS s_x
                  Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
      * iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
        iApply (base_finish_mem C pt E sigma sigma_f va w g g
                  (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8))
                  (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                  Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                  with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

Lemma arm_STORE_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (imm : bits 12) (rs2 rs1 : regidx) (width : word_width) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 1 \/ width = 2 \/ width = 4 \/ width = 8) ->
  exec (ext_decode w) sigma_f = Some (STORE (imm, rs2, rs1, width), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs2 as [rs2]. destruct rs1 as [rs1].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & Lpc0 & _ & Lmi).
  destruct Hwidth as [Hw|[Hw|[Hw|Hw]]]; subst width.
  - (* width 1 *)
    iMod (mem_exec_store_1 pt imm rs2 rs1 g va s0
            Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Lpc0 Hpma0 with "Hint Hgpr Hupt")
      as "[HOk | HErr]".
    + iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 1)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv) "(%Hexec & %Hue & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 1))
                (rv64d_types.Trap (User, make_sync_exception e xv, va)) s0
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv va Hue) I
                eq_refl eq_refl with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 2 *)
    iMod (mem_exec_store_k pt 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity)
            ltac:(vm_compute; reflexivity) exec_write_ram_plain_2 (or_introl eq_refl)
            imm rs2 rs1 g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 2)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 2))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 4 *)
    iMod (mem_exec_store_k pt 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
            ltac:(vm_compute; reflexivity) exec_write_ram_plain_4 (or_intror (or_introl eq_refl))
            imm rs2 rs1 g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 4)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 4))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 8 *)
    iMod (mem_exec_store_k pt 8 ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity)
            ltac:(vm_compute; reflexivity) exec_write_ram_plain_8 (or_intror (or_intror eq_refl))
            imm rs2 rs1 g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 8)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORE (imm, Regidx rs2, Regidx rs1, 8))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* ===================================================================== *)
(* LR / SC base memory arms (aq/rl-generic).                              *)
(* ===================================================================== *)

(* ---- Part A: kinds-generic reserved read_ram leaves ---- *)
Lemma exec_read_ram_resv_kinds_4 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 32) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 4 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 4 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_read_ram_resv_kinds_8 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 64) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 8 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 8 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 8) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

(* ---- Part B: aq/rl-generic reserved checked_mem_read / mem_read (LR) ---- *)
Lemma exec_checked_mem_read_lr_g4 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (LoadReserved Data) pbmt User (Physaddr addr) 4 aq (andb aq rl) true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  unfold checked_mem_read.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 4 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 4 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 4 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                    (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
    { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hrk as (rk & Hrke & Hrkv).
    rewrite (exec_bind_Some _ _ _ _ _ Hrke).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resv_kinds_4 rk addr w s Hrkv Hdev Hbytes)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 4 true) s
                   = Some (Some (E_Load_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 4 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 4 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_lr_g8 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (LoadReserved Data) pbmt User (Physaddr addr) 8 aq (andb aq rl) true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  unfold checked_mem_read.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 8 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 8 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 8 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                    (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
    { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hrk as (rk & Hrke & Hrkv).
    rewrite (exec_bind_Some _ _ _ _ _ Hrke).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resv_kinds_8 rk addr w s Hrkv Hdev Hbytes)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (LoadReserved Data) pbmt User (Physaddr addr) 8 true) s
                   = Some (Some (E_Load_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_lr addr 8 s HA Hord Hrange HR)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_lr_g 8 addr pbmt region s Hmatch Halign Hread)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_mem_read_lr_g4 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (LoadReserved Data) pbmt (Physaddr addr) 4 aq (andb aq rl) true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_g4 aq rl pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved Data) pbmt User (Physaddr addr) 4 aq (andb aq rl) true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s)).
  { unfold mem_read_priv_meta.
    destruct aq; [ destruct rl |];
      (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
       rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
       destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
       cbn match; apply exec_returnM). }
  rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
    cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
Qed.

Lemma exec_mem_read_lr_g8 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (LoadReserved Data) pbmt (Physaddr addr) 8 aq (andb aq rl) true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_g8 aq rl pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved Data) pbmt User (Physaddr addr) 8 aq (andb aq rl) true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (E_Load_Access_Fault tt)), s)).
  { unfold mem_read_priv_meta.
    destruct aq; [ destruct rl |];
      (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
       rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
       destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
       cbn match; apply exec_returnM). }
  rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone);
    cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
Qed.

(* ---- Part C: aq/rl-generic LR aligned-Ok composers ---- *)
Section LRComposersG.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_read_addr_lr_g4 (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ' : mstate,
      ⌜(exists dvv : mword 32,
          exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved Data) aq (andb aq rl) true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved Data) aq (andb aq rl) true) σ
            = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved Data) σ
               (or_intror (or_intror (or_intror (or_introl eq_refl))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 4 ltac:(lia) ltac:(exists 1024; reflexivity) um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4)
      as (region & Hpmam & _ & Hrd & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 4 (Z.to_nat 4 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmio : exec (within_mmio_readable (Physaddr pa) 4) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 4 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 4 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa 4 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmr := exec_mem_read_lr_g4 aq rl PBMT_PMA pa region dv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
             Hpmam (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal) Hrd
             Hmmio (addr_is_ram_not_dev _ Hram0) Hbytes
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4))) (LoadReserved Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)).
      rewrite avi0. exact Htr. }
    destruct (exec_vmem_read_addr_lr_disj 4 va pa (register_lookup PC σ'.(sregs)) dv
                aq (andb aq rl) User (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr' Hmr
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl)
      as [Hret | Hflt].
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; left; exact Hret | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

  Lemma user_pt_vmem_read_addr_lr_g8 (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ' : mstate,
      ⌜(exists dvv : mword 64,
          exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved Data) aq (andb aq rl) true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved Data) aq (andb aq rl) true) σ
            = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved Data) σ
               (or_intror (or_intror (or_intror (or_introl eq_refl))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 8 ltac:(lia) ltac:(exists 512; reflexivity) um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8)
      as (region & Hpmam & _ & Hrd & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 8 (Z.to_nat 8 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmio : exec (within_mmio_readable (Physaddr pa) 8) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 8 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 8 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa 8 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmr := exec_mem_read_lr_g8 aq rl PBMT_PMA pa region dv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
             Hpmam (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal) Hrd
             Hmmio (addr_is_ram_not_dev _ Hram0) Hbytes
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8))) (LoadReserved Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)).
      rewrite avi0. exact Htr. }
    destruct (exec_vmem_read_addr_lr_disj 8 va pa (register_lookup PC σ'.(sregs)) dv
                aq (andb aq rl) User (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr' Hmr
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl)
      as [Hret | Hflt].
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; left; exact Hret | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End LRComposersG.

(* ---- Part D: LR translate-fault composer (aq/rl-generic, width-generic) ---- *)
Section LRFaultComposer.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_read_addr_lr_err (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pc : mword 64) (width : Z) (σ : mstate) :
    u_fault_flavor (LoadReserved Data) tfp um va ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_read_addr (Virtaddr va) width (LoadReserved Data) aq (andb aq rl) true) σ
      = Some (Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (LoadReserved Data) uroot tfp um va
                 (E_Load_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (LoadReserved Data)
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (LoadReserved Data) σ
                    (or_intror (or_intror (or_intror (or_introl eq_refl)))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (LoadReserved Data)) σ
                   = Some (Err (E_Load_Page_Fault tt, tt), σ)).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))
        with (add_vec_int va (0 * width)).
      rewrite avi0. exact Htr. }
    assert (Hva : add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width) = va).
    { change (bits_of_virtaddr (Virtaddr va)) with va. apply avi0. }
    transitivity (Some ((Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt)
       (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))
       : result (mword (8 * width)) ExecutionResult), σ)).
    { exact (exec_vmem_read_addr_translate_err width va pc (E_Load_Page_Fault tt)
               (LoadReserved Data) aq (andb aq rl) true User σ σ Halign Htr' Lcp Lpc). }
    rewrite Hva. reflexivity.
  Qed.

End LRFaultComposer.

(* ---- Part E: LOADRES rd=0 execute ---- *)
Lemma exec_execute_LOADRES_u_ok_rd0 (aq rl : bool) (rs1 rd : mword 5) (width : Z)
    (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd = 0 ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved Data) aq (andb aq rl) true) s
    = Some (Ok data, s') ->
  exec (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd))) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hw Hrd Hvr.
  change (execute (LOADRES (aq, rl, Regidx rs1, width, Regidx rd)))
    with (execute_LOADRES aq rl (Regidx rs1) width (Regidx rd)).
  unfold execute_LOADRES. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:43.28-43.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ Hvr). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (sign_extend' 64 data)) s' = Some (tt, s')).
  { rewrite (exec_wX_bits_gpr rd (sign_extend' 64 data) s').
    rewrite (proj2 (Z.eqb_eq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_returnm.
Qed.

(* ---- Part F: LR total classify (width-generic) + engine ---- *)
Section LREngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_read_lr_total (k : Z) (aq rl : bool)
      (HkW : k = 4 \/ k = 8)
      (Hlr_ok : forall (aq0 rl0 : bool) (uroot0 tfp0 : mword 44)
          (um0 : gmap (mword 27) (mword 64)) (data0 : gset Arch.pa)
          (w0 va0 : mword 64) (σ0 : mstate),
          um0 !! svpn_of va0 = Some w0 ->
          uleaf_ok (LoadReserved Data) w0 ->
          udata_cov um0 data0 ->
          is_aligned_vaddr (Virtaddr va0) k = true ->
          neq_vec (bits_of_virtaddr (Virtaddr va0))
             (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub 39 1) 0)) = false ->
          register_lookup misa σ0.(sregs) = MISA_C ->
          register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
          register_lookup htif_tohost_base σ0.(sregs) = None ->
          register_lookup cur_privilege σ0.(sregs) = User ->
          _get_Mstatus_SXL (register_lookup mstatus σ0.(sregs)) = 'b"10" ->
          eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ0.(sregs))) ('b"1") = false ->
          pma_allows_all (register_lookup pma_regions σ0.(sregs)) ->
          reg_interp σ0.(sregs) -∗ gen_heap_interp σ0.(mem) -∗
          utlb_inv_pt uroot0 tfp0 um0 -∗ udata_own data0 ==∗
          ∃ σ0' : mstate,
            ⌜(exists dvv : mword (8 * k),
                exec (vmem_read_addr (Virtaddr va0) k (LoadReserved Data) aq0 (andb aq0 rl0) true) σ0
                  = Some (Ok dvv, σ0'))
             \/ exec (vmem_read_addr (Virtaddr va0) k (LoadReserved Data) aq0 (andb aq0 rl0) true) σ0
                  = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va0,
                                     register_lookup PC σ0.(sregs))), σ0')⌝ ∗
            ⌜σ0'.(mdev) = σ0.(mdev)⌝ ∗
            ⌜(σ0'.(sregs) = σ0.(sregs) \/
              exists tv, σ0'.(sregs) = register_set tlb tv σ0.(sregs))%type⌝ ∗
            reg_interp σ0'.(sregs) ∗ gen_heap_interp σ0'.(mem) ∗
            utlb_inv_pt uroot0 tfp0 um0 ∗ udata_own data0)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (Hwf : upt_acc_wf um) (Hcov : udata_cov um data)
      (va pc : mword 64) (s : mstate) :
    cfg_okR s -> register_lookup PC s.(sregs) = pc ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (dvv : mword (8 * k)) (σ' : mstate),
        ⌜exec (vmem_read_addr (Virtaddr va) k (LoadReserved Data) aq (andb aq rl) true) s = Some (Ok dvv, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_read_addr (Virtaddr va) k (LoadReserved Data) aq (andb aq rl) true) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗ ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros Hcfg Lpc.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & HMPRV & Hpma).
    iIntros "Hreg Hgh Hutlb Hudata".
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    - destruct (data_classify (LoadReserved Data) tfp um va
                  (or_intror (or_intror (or_intror (or_introl eq_refl)))) Hwf)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + iMod (Hlr_ok aq rl uroot tfp um data w va s
                Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL HMPRV Hpma
                with "Hreg Hgh Hutlb Hudata")
          as (σ') "(%Hdisj & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        destruct Hdisj as [ (dvv & Hok') | Herr ].
        * iModIntro. iLeft. iExists dvv, σ'. iFrame. iPureIntro.
          split; [exact Hok' |]. split; [exact Hmdev|].
          split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
        * iModIntro. iRight. iExists σ', (E_Load_Access_Fault tt), va, pc.
          iFrame. iPureIntro. rewrite Lpc in Herr. split; [exact Herr |].
          split; [vm_compute; reflexivity |]. split; [exact Hmdev|].
          split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
      + iDestruct (user_pt_vmem_read_addr_lr_err aq rl uroot tfp um va pc k s
                     Hfault Hal Lpc Hhtif Hcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Herr.
        iModIntro. iRight. iExists s, (E_Load_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - iModIntro. iRight. iExists s, (E_Load_Access_Fault tt), va, pc.
      iFrame. iPureIntro.
      split; [ exact (exec_vmem_read_addr_misaligned_lr va pc k aq (andb aq rl) User s Hal Hcp Lpc) |].
      split; [vm_compute; reflexivity |]. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  Qed.

End LREngine.

(* ---- Part G: LR execute engine ---- *)
Section LRExecEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_lr_k (pt : uptd) (k : Z) (aq rl : bool)
      (HkW : k = 4 \/ k = 8)
      (Hlr_ok : forall (aq0 rl0 : bool) (uroot0 tfp0 : mword 44)
          (um0 : gmap (mword 27) (mword 64)) (data0 : gset Arch.pa)
          (w0 va0 : mword 64) (σ0 : mstate),
          um0 !! svpn_of va0 = Some w0 ->
          uleaf_ok (LoadReserved Data) w0 ->
          udata_cov um0 data0 ->
          is_aligned_vaddr (Virtaddr va0) k = true ->
          neq_vec (bits_of_virtaddr (Virtaddr va0))
             (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub 39 1) 0)) = false ->
          register_lookup misa σ0.(sregs) = MISA_C ->
          register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
          register_lookup htif_tohost_base σ0.(sregs) = None ->
          register_lookup cur_privilege σ0.(sregs) = User ->
          _get_Mstatus_SXL (register_lookup mstatus σ0.(sregs)) = 'b"10" ->
          eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ0.(sregs))) ('b"1") = false ->
          pma_allows_all (register_lookup pma_regions σ0.(sregs)) ->
          reg_interp σ0.(sregs) -∗ gen_heap_interp σ0.(mem) -∗
          utlb_inv_pt uroot0 tfp0 um0 -∗ udata_own data0 ==∗
          ∃ σ0' : mstate,
            ⌜(exists dvv : mword (8 * k),
                exec (vmem_read_addr (Virtaddr va0) k (LoadReserved Data) aq0 (andb aq0 rl0) true) σ0
                  = Some (Ok dvv, σ0'))
             \/ exec (vmem_read_addr (Virtaddr va0) k (LoadReserved Data) aq0 (andb aq0 rl0) true) σ0
                  = Some (Err (Trap (User, make_sync_exception (E_Load_Access_Fault tt) va0,
                                     register_lookup PC σ0.(sregs))), σ0')⌝ ∗
            ⌜σ0'.(mdev) = σ0.(mdev)⌝ ∗
            ⌜(σ0'.(sregs) = σ0.(sregs) \/
              exists tv, σ0'.(sregs) = register_set tlb tv σ0.(sregs))%type⌝ ∗
            reg_interp σ0'.(sregs) ∗ gen_heap_interp σ0'.(mem) ∗
            utlb_inv_pt uroot0 tfp0 um0 ∗ udata_own data0)
      (rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (LOADRES (aq, rl, Regidx rs1, k, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (LOADRES (aq, rl, Regidx rs1, k, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (LoadReserved Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (LoadReserved Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    assert (Hcfg : cfg_okR s). { unfold cfg_okR. repeat split; assumption. }
    assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|Hkv]; subst k; vm_compute; reflexivity).
    iMod (mem_read_lr_total k aq rl HkW Hlr_ok
            pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) Hwf Hcov va
            (register_lookup PC s.(sregs)) s Hcfg eq_refl with "Hreg Hgh Hutlb Hudata")
      as "[HOk | HErr]".
    - iDestruct "HOk" as (dvv sig') "(%Hvr & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (zeros' 64) k (LoadReserved Data) aq (andb aq rl) true) s = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (zeros' 64) k (LoadReserved Data) aq (andb aq rl) true Sv39 (Ok dvv) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvr. }
      destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
      + (* rd = 0: no write *)
        apply Z.eqb_eq in Hrd0.
        pose proof (exec_execute_LOADRES_u_ok_rd0 aq rl rs1 rd k dvv s sig' Hkle Hrd0 Hvread) as Hexec.
        iModIntro. iLeft. iExists g, sig'.
        iSplitR; [iPureIntro; exact Hexec |].
        iSplitR; [iPureIntro; exact Hmi |].
        iSplitR; [iPureIntro; exact Hnpc |].
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
      + (* rd <> 0: write sign-extended value *)
        apply Z.eqb_neq in Hrd0.
        pose proof (exec_execute_LOADRES_u_ok aq rl rs1 rd k dvv s sig' Hkle Hrd0 Hvread) as Hexec.
        iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
        iDestruct "Hrdf" as (v0) "Hrdf".
        set (nv := regval_into_reg (sign_extend' 64 dvv)).
        iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
        iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
        iModIntro. iLeft. set (s_x := set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
        iExists (<[Regidx rd := nv]> g), s_x.
        iSplitR; [ iPureIntro; unfold s_x, nv; exact Hexec |].
        assert (Tr : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                  register_lookup r s_x.(sregs) = register_lookup r sig'.(sregs)).
        { intros r Hne. unfold s_x, set_reg; cbn [sregs]. apply irrelevant_register_set; exact Hne. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
        { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (zeros' 64) k (LoadReserved Data) aq (andb aq rl) true) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_read_u rs1 (zeros' 64) k (LoadReserved Data) aq (andb aq rl) true Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_LOADRES_u_err aq rl rs1 rd k (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s sig' Hkle Hvread) as Hexec.
      iModIntro. iRight. iExists e, xv, pcx, sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hue |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End LRExecEngine.

(* ---- Part H: arm_LOADRES_u ---- *)
Lemma arm_LOADRES_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (aq rl : bool) (rs1 : regidx) (width : word_width) (rd : regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 4 \/ width = 8) ->
  exec (ext_decode w) sigma_f = Some (LOADRES (aq, rl, rs1, width, rd), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs1 as [rs1]. destruct rd as [rd].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hwidth as [Hw|Hw]; subst width.
  - (* width 4 *)
    iMod (mem_exec_lr_k pt 4 aq rl (or_introl eq_refl) user_pt_vmem_read_addr_lr_g4
            rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 8 *)
    iMod (mem_exec_lr_k pt 8 aq rl (or_intror eq_refl) user_pt_vmem_read_addr_lr_g8
            rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (LOADRES (aq, rl, Regidx rs1, 8, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (LOADRES (aq, rl, Regidx rs1, 8, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* =================== SC (STORECON) write stack =================== *)
(* ---- Part A': kinds-generic conditional write_ram leaves ---- *)
Lemma exec_write_ram_cond_kinds_4 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 32) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn match;
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

Lemma exec_write_ram_cond_kinds_8 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 64) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn [Mem_write_request_value]; cbn match; cbn [Interface.iMon_bind];
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

(* ---- SC mem_write_ea (generic flags) ---- *)
Lemma exec_mem_write_ea_sc_g (aq rl : bool) (width : Z) (addr : mword 64) s :
  is_aligned_paddr (Physaddr addr) width = true ->
  exec (mem_write_ea (Physaddr addr) width (andb aq rl) rl true) s = Some (Ok tt, s).
Proof.
  intros Halign. unfold mem_write_ea.
  destruct aq; destruct rl;
    (rewrite Halign; cbn [orb andb negb Riscv.rv64d.not];
     unfold write_kind_of_flags; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s));
     apply exec_returnM).
Qed.

(* ---- Part B': aq/rl-generic SC checked_mem_write / mem_write_value ---- *)
Lemma exec_checked_mem_write_sc_g4 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (StoreConditional Data) pbmt User tt (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  unfold checked_mem_write.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 4 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 4 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 4 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    rewrite (exec_bind_Some _ _ _ _ _ Hwke).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_kinds_4 wk addr data s Hwkv Hdev)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 4 true) s
                   = Some (Some (E_SAMO_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 4 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 4 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_sc_g8 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (StoreConditional Data) pbmt User tt (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  unfold checked_mem_write.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 8 true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 8 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 8 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    rewrite (exec_bind_Some _ _ _ _ _ Hwke).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_kinds_8 wk addr data s Hwkv Hdev)).
    apply exec_returnM.
  - assert (Hpac : exec (phys_access_check (StoreConditional Data) pbmt User (Physaddr addr) 8 true) s
                   = Some (Some (E_SAMO_Access_Fault tt), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc addr 8 s HA Hord Hrange HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 8 addr pbmt region s Hmatch Halign Hwrite)).
      rewrite Hr. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match. apply exec_returnM.
Qed.

Lemma exec_mem_write_value_sc_g4 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 4 data (StoreConditional Data) pbmt (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (StoreConditional Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_write_value_priv_meta.
  assert (Hcmw := exec_checked_mem_write_sc_g4 aq rl pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct aq; destruct rl;
    (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
     destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr;
     cbn match in Hcmw;
     rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM).
Qed.

Lemma exec_mem_write_value_sc_g8 (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 8 data (StoreConditional Data) pbmt (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (StoreConditional Data) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_write_value_priv_meta.
  assert (Hcmw := exec_checked_mem_write_sc_g8 aq rl pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct aq; destruct rl;
    (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
     destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone) eqn:Hr;
     cbn match in Hcmw;
     rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM).
Qed.

(* ---- Part C': aq/rl-generic SC aligned composers ---- *)
Section SCComposersG.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_write_addr_sc_g4 (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (dat : mword 32) (σ : mstate) :
    let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*4-1) (8*0*4))
              : mword 32 in
    um !! svpn_of va = Some w ->
    uleaf_ok (StoreConditional Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ'' : mstate,
      ⌜(exists b : bool,
          exec (vmem_write_addr (Virtaddr va) 4 dat (StoreConditional Data) (andb aq rl) rl true) σ
            = Some (Ok b, σ''))
       \/ exec (vmem_write_addr (Virtaddr va) 4 dat (StoreConditional Data) (andb aq rl) rl true) σ
            = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ'')⌝ ∗
      ⌜σ''.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ''.(sregs) = σ.(sregs) \/
        exists tv, σ''.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ''.(sregs) ∗ gen_heap_interp σ''.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros wv Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (StoreConditional Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (StoreConditional Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (StoreConditional Data) σ
               (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 4 ltac:(lia) ltac:(exists 1024; reflexivity)
                 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv0 & _ & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4)
      as (region & Hpmam & _ & _ & Hwrb).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 4 (Z.to_nat 4 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmiow : exec (within_mmio_writable (Physaddr pa) 4) σ' = Some (false, σ')).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 4 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 4 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false pa 4 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hwv := exec_mem_write_value_sc_g4 aq rl PBMT_PMA pa region wv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal)
             (proj1 Hwrb) Hmmiow (addr_is_ram_not_dev _ Hram0)
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Hpac : exec (phys_access_check (StoreConditional Data) PBMT_PMA User (Physaddr pa) 4 true) σ'
                   = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone
                            then None else Some (E_SAMO_Access_Fault tt)), σ')).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc pa 4 σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW)))).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 4 pa PBMT_PMA region σ' Hpmam
                 (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal) (proj1 Hwrb))).
      destruct (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone);
        cbn match; apply exec_returnM. }
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4))) (StoreConditional Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)).
      rewrite avi0. exact Htr. }
    assert (Hea := exec_mem_write_ea_sc_g aq rl 4 pa σ'
             (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal)).
    destruct (exec_vmem_write_addr_sc_disj 4 va pa (register_lookup PC σ'.(sregs)) dat
                (andb aq rl) rl (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr'
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl Hea Hwv Hpac)
      as [Hret | Hflt].
    - destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr; cbn match in Hret.
      + iMod (udata_own_store_g 4 data pa wv σ'.(mem)
                (fun j Hj => ltac:(
                   rewrite (u_walk_pa_window_div 4 w va j ltac:(lia) ltac:(exists 1024; reflexivity) Hal Hj);
                   exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl)))
                with "Hgh Hdata") as "[Hgh Hdata]".
        iModIntro.
        iExists (MState σ'.(sregs) (write_bytes σ'.(mem) pa (Z.to_N 4) wv) σ'.(mdev)).
        iSplit; [ iPureIntro; left; exists true; exact Hret | ].
        iSplit; [ iPureIntro; cbn; exact Hmdev | ].
        iSplit; [ iPureIntro; cbn; exact Hsregs | ].
        cbn. iFrame "Hri Hgh Hinv Hdata".
      + iModIntro. iExists σ'.
        iSplit; [ iPureIntro; left; exists false; exact Hret | ].
        iSplit; [ iPureIntro; exact Hmdev | ].
        iSplit; [ iPureIntro; exact Hsregs | ].
        iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 4)) with (add_vec_int va (0 * 4)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End SCComposersG.

(* ---- SC g8 composer ---- *)
Section SCComposersG8.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_write_addr_sc_g8 (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (dat : mword 64) (σ : mstate) :
    let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*8-1) (8*0*8))
              : mword 64 in
    um !! svpn_of va = Some w ->
    uleaf_ok (StoreConditional Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ σ'' : mstate,
      ⌜(exists b : bool,
          exec (vmem_write_addr (Virtaddr va) 8 dat (StoreConditional Data) (andb aq rl) rl true) σ
            = Some (Ok b, σ''))
       \/ exec (vmem_write_addr (Virtaddr va) 8 dat (StoreConditional Data) (andb aq rl) rl true) σ
            = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) va,
                               register_lookup PC σ.(sregs))), σ'')⌝ ∗
      ⌜σ''.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ''.(sregs) = σ.(sregs) \/
        exists tv, σ''.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ''.(sregs) ∗ gen_heap_interp σ''.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros wv Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (StoreConditional Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (StoreConditional Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (StoreConditional Data) σ
               (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g 8 ltac:(lia) ltac:(exists 512; reflexivity)
                 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv0 & _ & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8)
      as (region & Hpmam & _ & _ & Hwrb).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 8 (Z.to_nat 8 - 1) ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Hmmiow : exec (within_mmio_writable (Physaddr pa) 8) σ' = Some (false, σ')).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa 8 σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa 8 σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false pa 8 σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hwv := exec_mem_write_value_sc_g8 aq rl PBMT_PMA pa region wv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal)
             (proj1 Hwrb) Hmmiow (addr_is_ram_not_dev _ Hram0)
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    assert (Hpac : exec (phys_access_check (StoreConditional Data) PBMT_PMA User (Physaddr pa) 8 true) σ'
                   = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone
                            then None else Some (E_SAMO_Access_Fault tt)), σ')).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc pa 8 σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW)))).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_sc_g 8 pa PBMT_PMA region σ' Hpmam
                 (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal) (proj1 Hwrb))).
      destruct (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone);
        cbn match; apply exec_returnM. }
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8))) (StoreConditional Data)) σ
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)).
      rewrite avi0. exact Htr. }
    assert (Hea := exec_mem_write_ea_sc_g aq rl 8 pa σ'
             (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal)).
    destruct (exec_vmem_write_addr_sc_disj 8 va pa (register_lookup PC σ'.(sregs)) dat
                (andb aq rl) rl (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ' Hal Htr'
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl Hea Hwv Hpac)
      as [Hret | Hflt].
    - destruct (match_reservation (bits_of_physaddr (Physaddr pa))) eqn:Hmr; cbn match in Hret.
      + iMod (udata_own_store_g 8 data pa wv σ'.(mem)
                (fun j Hj => ltac:(
                   rewrite (u_walk_pa_window_div 8 w va j ltac:(lia) ltac:(exists 512; reflexivity) Hal Hj);
                   exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl)))
                with "Hgh Hdata") as "[Hgh Hdata]".
        iModIntro.
        iExists (MState σ'.(sregs) (write_bytes σ'.(mem) pa (Z.to_N 8) wv) σ'.(mdev)).
        iSplit; [ iPureIntro; left; exists true; exact Hret | ].
        iSplit; [ iPureIntro; cbn; exact Hmdev | ].
        iSplit; [ iPureIntro; cbn; exact Hsregs | ].
        cbn. iFrame "Hri Hgh Hinv Hdata".
      + iModIntro. iExists σ'.
        iSplit; [ iPureIntro; left; exists false; exact Hret | ].
        iSplit; [ iPureIntro; exact Hmdev | ].
        iSplit; [ iPureIntro; exact Hsregs | ].
        iFrame "Hri Hgh Hinv Hdata".
    - iModIntro. iExists σ'.
      iSplit; [ iPureIntro; right | ].
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt.
        change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * 8)) with (add_vec_int va (0 * 8)) in Hflt.
        rewrite avi0 in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End SCComposersG8.

(* ---- Part D': SC translate-fault composer ---- *)
Section SCFaultComposer.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_vmem_write_addr_sc_err (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pc : mword 64) (width : Z)
      (dat : mword (8 * width)) (σ : mstate) :
    u_fault_flavor (StoreConditional Data) tfp um va ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional Data) (andb aq rl) rl true) σ
      = Some (Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (StoreConditional Data) uroot tfp um va
                 (E_SAMO_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (StoreConditional Data)
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (StoreConditional Data) σ
                    (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    assert (Htr' : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (StoreConditional Data)) σ
                   = Some (Err (E_SAMO_Page_Fault tt, tt), σ)).
    { change (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))
        with (add_vec_int va (0 * width)).
      rewrite avi0. exact Htr. }
    assert (Hva : add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width) = va).
    { change (bits_of_virtaddr (Virtaddr va)) with va. apply avi0. }
    transitivity (Some ((Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt)
       (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width)), pc))
       : result bool ExecutionResult), σ)).
    { exact (exec_vmem_write_addr_translate_err width va pc (E_SAMO_Page_Fault tt)
               dat (StoreConditional Data) (andb aq rl) rl true User σ σ Halign Htr' Lcp Lpc). }
    rewrite Hva. reflexivity.
  Qed.

End SCFaultComposer.

(* ---- Part E': STORECON rd=0 execute ---- *)
Lemma exec_execute_STORECON_u_ok_rd0 (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (b : bool) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd = 0 ->
  exec (vmem_write (Regidx rs1) (zeros' 64) width
          (autocast (T := mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul width 8) 1) 0))
          (StoreConditional Data) (andb aq rl) rl true) s = Some (Ok b, s') ->
  exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hw Hrd Hvw.
  change (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_STORECON aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_STORECON. rewrite Hw.
  assert (Hass : exec (assert_exp' true "extensions/A/zalrsc_insts.sail:68.28-68.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hvw). cbn match.
  assert (Hw2 : exec (wX_bits (Regidx rd) (zero_extend' 64 (bool_bit_forwards (negb b)))) s'
               = Some (tt, s')).
  { rewrite (exec_wX_bits_gpr rd (zero_extend' 64 (bool_bit_forwards (negb b))) s').
    rewrite (proj2 (Z.eqb_eq (uint rd) 0) Hrd). reflexivity. }
  assert (Hwc : exec (Defs.bind0 (wX_bits (Regidx rd) (zero_extend' 64 (bool_bit_forwards (negb b))))
                        (cancel_reservation tt)) s'
               = Some (tt, s')).
  { rewrite (exec_bind0_Some _ _ _ _ _ Hw2). apply exec_cancel_reservation. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwc). apply exec_returnM.
Qed.

(* ---- Part F'/G': SC total classify + execute engine ---- *)
Section SCEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the aligned-Ok composer contract (matches user_pt_vmem_write_addr_sc_g4/_g8) *)
  Definition sc_ok_contract (k : Z) : Prop :=
    forall (aq0 rl0 : bool) (uroot0 tfp0 : mword 44)
      (um0 : gmap (mword 27) (mword 64)) (data0 : gset Arch.pa)
      (w0 va0 : mword 64) (dat0 : mword (8 * k)) (σ0 : mstate),
      um0 !! svpn_of va0 = Some w0 ->
      uleaf_ok (StoreConditional Data) w0 ->
      udata_cov um0 data0 ->
      is_aligned_vaddr (Virtaddr va0) k = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va0))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va0)) (Z.sub 39 1) 0)) = false ->
      register_lookup misa σ0.(sregs) = MISA_C ->
      register_lookup menvcfg σ0.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ0.(sregs) = None ->
      register_lookup cur_privilege σ0.(sregs) = User ->
      _get_Mstatus_SXL (register_lookup mstatus σ0.(sregs)) = 'b"10" ->
      eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ0.(sregs))) ('b"1") = false ->
      pma_allows_all (register_lookup pma_regions σ0.(sregs)) ->
      reg_interp σ0.(sregs) -∗ gen_heap_interp σ0.(mem) -∗
      utlb_inv_pt uroot0 tfp0 um0 -∗ udata_own data0 ==∗
      ∃ σ0'' : mstate,
        ⌜(exists b : bool,
            exec (vmem_write_addr (Virtaddr va0) k dat0 (StoreConditional Data) (andb aq0 rl0) rl0 true) σ0
              = Some (Ok b, σ0''))
         \/ exec (vmem_write_addr (Virtaddr va0) k dat0 (StoreConditional Data) (andb aq0 rl0) rl0 true) σ0
              = Some (Err (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt) va0,
                                 register_lookup PC σ0.(sregs))), σ0'')⌝ ∗
        ⌜σ0''.(mdev) = σ0.(mdev)⌝ ∗
        ⌜(σ0''.(sregs) = σ0.(sregs) \/
          exists tv, σ0''.(sregs) = register_set tlb tv σ0.(sregs))%type⌝ ∗
        reg_interp σ0''.(sregs) ∗ gen_heap_interp σ0''.(mem) ∗
        utlb_inv_pt uroot0 tfp0 um0 ∗ udata_own data0.

  Lemma mem_write_sc_total (k : Z) (aq rl : bool)
      (HkW : k = 4 \/ k = 8) (Hsc_ok : sc_ok_contract k)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (Hwf : upt_acc_wf um) (Hcov : udata_cov um data)
      (va pc : mword 64) (dat : mword (8 * k)) (s : mstate) :
    cfg_okR s -> register_lookup PC s.(sregs) = pc ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    (∃ (b : bool) (σ' : mstate),
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional Data) (andb aq rl) rl true) s = Some (Ok b, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional Data) (andb aq rl) rl true) s
           = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), σ')⌝ ∗
        ⌜user_exc e = true⌝ ∗ ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data).
  Proof.
    intros Hcfg Lpc.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & HMPRV & Hpma).
    iIntros "Hreg Hgh Hutlb Hudata".
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    - destruct (data_classify (StoreConditional Data) tfp um va
                  (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))) Hwf)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + iMod (Hsc_ok aq rl uroot tfp um data w va dat s
                Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL HMPRV Hpma
                with "Hreg Hgh Hutlb Hudata")
          as (σ') "(%Hdisj & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        destruct Hdisj as [ (b & Hok') | Herr ].
        * iModIntro. iLeft. iExists b, σ'. iFrame. iPureIntro.
          split; [exact Hok' |]. split; [exact Hmdev|].
          split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
        * iModIntro. iRight. iExists σ', (E_SAMO_Access_Fault tt), va, pc.
          iFrame. iPureIntro. rewrite Lpc in Herr. split; [exact Herr |].
          split; [vm_compute; reflexivity |]. split; [exact Hmdev|].
          split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
      + iDestruct (user_pt_vmem_write_addr_sc_err aq rl uroot tfp um va pc k dat s
                     Hfault Hal Lpc Hhtif Hcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Herr.
        iModIntro. iRight. iExists s, (E_SAMO_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - iModIntro. iRight. iExists s, (E_SAMO_Access_Fault tt), va, pc.
      iFrame. iPureIntro.
      split; [ exact (exec_vmem_write_addr_misaligned_sc va pc k dat (andb aq rl) rl User s Hal Hcp Lpc) |].
      split; [vm_compute; reflexivity |]. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  Qed.

  Lemma mem_exec_sc_k (pt : uptd) (k : Z) (aq rl : bool)
      (HkW : k = 4 \/ k = 8) (Hsc_ok : sc_ok_contract k)
      (rs2 rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (StoreConditional Data) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (StoreConditional Data)
                  (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    set (dat := autocast (T:=mword) (subrange_vec_dec
             (if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
             (Z.sub (Z.mul k 8) 1) 0) : mword (8 * k)).
    assert (Hcfg : cfg_okR s). { unfold cfg_okR. repeat split; assumption. }
    assert (Hkle : (k <=? xlen_bytes) = true) by (destruct HkW as [Hkv|Hkv]; subst k; vm_compute; reflexivity).
    iMod (mem_write_sc_total k aq rl HkW Hsc_ok
            pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) Hwf Hcov va
            (register_lookup PC s.(sregs)) dat s Hcfg eq_refl with "Hreg Hgh Hutlb Hudata")
      as "[HOk | HErr]".
    - iDestruct "HOk" as (b sig') "(%Hvw & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (zeros' 64) k dat (StoreConditional Data) (andb aq rl) rl true) s = Some (Ok b, sig')).
      { apply (exec_vmem_write_u rs1 (zeros' 64) k dat (StoreConditional Data) (andb aq rl) rl true Sv39 (Ok b) s sig' Lcp Heff Hpml Htm).
        fold va. exact Hvw. }
      destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
      + apply Z.eqb_eq in Hrd0.
        pose proof (exec_execute_STORECON_u_ok_rd0 aq rl rs2 rs1 rd k b s sig' Hkle Hrd0) as Hexec0.
        assert (Hexec : exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s = Some (RETIRE_SUCCESS, sig')).
        { apply Hexec0. fold dat. exact Hvwrite. }
        iModIntro. iLeft. iExists g, sig'.
        iSplitR; [iPureIntro; exact Hexec |].
        iSplitR; [iPureIntro; exact Hmi |].
        iSplitR; [iPureIntro; exact Hnpc |].
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
      + apply Z.eqb_neq in Hrd0.
        pose proof (exec_execute_STORECON_u_ok aq rl rs2 rs1 rd k b s sig' Hkle Hrd0) as Hexec0.
        assert (Hexec : exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                = Some (RETIRE_SUCCESS, set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd)))
                          (regval_into_reg (zero_extend' 64 (bool_bit_forwards (negb b)))))).
        { apply Hexec0. fold dat. exact Hvwrite. }
        iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
        iDestruct "Hrdf" as (v0) "Hrdf".
        set (nv := regval_into_reg (zero_extend' 64 (bool_bit_forwards (negb b)))).
        iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
        iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
        iModIntro. iLeft. set (s_x := set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
        iExists (<[Regidx rd := nv]> g), s_x.
        iSplitR; [ iPureIntro; unfold s_x, nv; exact Hexec |].
        assert (Tr : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                  register_lookup r s_x.(sregs) = register_lookup r sig'.(sregs)).
        { intros r Hne. unfold s_x, set_reg; cbn [sregs]. apply irrelevant_register_set; exact Hne. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
        { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (zeros' 64) k dat (StoreConditional Data) (andb aq rl) rl true) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_write_u rs1 (zeros' 64) k dat (StoreConditional Data) (andb aq rl) rl true Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
        fold va. exact Herr. }
      pose proof (exec_execute_STORECON_u_err aq rl rs2 rs1 rd k (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s sig' Hkle) as Hexec0.
      assert (Hexec : exec (execute (STORECON (aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), sig')).
      { apply Hexec0. fold dat. exact Hvwrite. }
      iModIntro. iRight. iExists e, xv, pcx, sig'.
      iSplitR; [iPureIntro; exact Hexec |].
      iSplitR; [iPureIntro; exact Hue |].
      iSplitR; [iPureIntro; exact Hmi |].
      iSplitR; [iPureIntro; exact Hnpc |].
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
      iFrame "Hgpr Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End SCEngine.

(* ---- Part H': arm_STORECON_u ---- *)
Lemma arm_STORECON_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (aq rl : bool) (rs2 rs1 : regidx) (width : word_width) (rd : regidx) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 4 \/ width = 8) ->
  exec (ext_decode w) sigma_f = Some (STORECON (aq, rl, rs2, rs1, width, rd), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs2 as [rs2]. destruct rs1 as [rs1]. destruct rd as [rd].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hwidth as [Hw|Hw]; subst width.
  - iMod (mem_exec_sc_k pt 4 aq rl (or_introl eq_refl) user_pt_vmem_write_addr_sc_g4
            rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - iMod (mem_exec_sc_k pt 8 aq rl (or_intror eq_refl) user_pt_vmem_write_addr_sc_g8
            rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (STORECON (aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (STORECON (aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* ===================================================================== *)
(* AMO memory family (relocated from AmoScratch): width-generic AMOSWAP    *)
(* retire / op-generic deny tower, the width-16 register-pair retire, and *)
(* the arm_AMO_u memory arm.                                              *)
(* ===================================================================== *)

(* ===================================================================== *)
(* Width-1/2 kinds-generic reserved read / conditional write RAM leaves.  *)
(* ===================================================================== *)
Lemma exec_read_ram_resv_kinds_1 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 8) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 1)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 1 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 1 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 1) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_read_ram_resv_kinds_2 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 16) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 2 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 2 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 2) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_write_ram_cond_kinds_1 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 8) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 1 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 1 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn match;
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

Lemma exec_write_ram_cond_kinds_2 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 16) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 2 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 2 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn match;
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

(* ram_fetch_pmp without the (w <= 8) premise (unused in its proof); the
   AMO tower reuses it up to width 16 (AMOSWAP retires at any width). *)
Lemma ram_fetch_pmp_g (a pmpaddr0 : mword 64) (w : Z) (k : nat) :
  0 < w ->
  (w <= 16)%Z ->
  uint (to_bits 64 w) = w ->
  (Z.of_nat k + 1 = w)%Z ->
  addr_is_ram a ->
  addr_is_ram (pa_add a k) ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint a) (uint (to_bits 64 w)) = PMP_Match.
Proof.
  intros Hw0 Hw16 Hwv Hkw Ha Hk Hcov.
  pose proof Ha as [Halo Hahi]. pose proof Hk as [_ Hkhi].
  rewrite (uint_pa_add a k ltac:(unfold ram_base, ram_size in Hahi; lia)) in Hkhi.
  apply (ram_pmp_match_w a pmpaddr0 w Hw0 Hwv Halo ltac:(unfold ram_base, ram_size in *; lia) Hcov).
Qed.

(* ===================================================================== *)
(* op/width/aq-rl-generic AMO memory leaves (Atomic acc, RAM).            *)
(* ===================================================================== *)
Section AmoGeneric.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk16 : k <= 16) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_resv : forall (rk : rv64d_types.read_kind) (addr : mword 64) (w : mword (8 * k)) s,
      (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rk (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_cond : forall (wk : rv64d_types.write_kind) (addr : mword 64) (data : mword (8 * k)) s,
      (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
      dev_addr addr = false ->
      exec (write_ram wk (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  (* op-generic pmpCheck user grant for Atomic (R&W). *)
  Lemma exec_pmpCheck_user_grant_amo_g (op : amoop) (a : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exec (pmpCheck (Physaddr a) k (Atomic (op, Data, Data)) User) s = Some (None, s).
  Proof.
    intros HA Hord Hrange HR HW.
    unfold pmpCheck. rewrite exec_catch_early_return.
    replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
    rewrite execR_bind0.
    match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
      assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
    { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
      rewrite execR_bind.
      rewrite execR_bind. rewrite execR_returnR. cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpMatchAddr_TOR_match a (to_bits 64 k)
                    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                    (zeros' 64) s HA Hord Hrange)). cbn beta.
      cbn match.
      unfold or_boolM.
      rewrite execR_bind.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                              (Atomic (op, Data, Data))) s = Some (true, s))).
      2:{ unfold pmpCheckRWX. cbn match. rewrite HR HW. apply exec_returnm. }
      cbn match. rewrite execR_returnR. cbn beta.
      cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
      unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
    rewrite Hfe. cbn match. reflexivity.
  Qed.

  (* op-generic pmaCheck for Atomic on RAM (support = AMOSwap):
     canAccess reduces to generic_eq op AMOSWAP. *)
  Lemma exec_pmaCheck_ram_amo_gk (op : amoop) (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) = AMOSwap ->
    exec (pmaCheck (Physaddr addr) k (Atomic (op, Data, Data)) pbmt true) s
      = Some ((if generic_eq op AMOSWAP then None else Some (E_SAMO_Access_Fault tt)), s).
  Proof.
    intros Hmatch Halign Hread Hwrite Hsupp.
    unfold pmaCheck.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
    rewrite Hmatch.
    destruct region as [rbase rsize rattr rdtree].
    cbn [PMA_Region_attributes] in Hread, Hwrite, Hsupp |- *.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
    destruct op; cbn match beta;
      (match goal with |- exec (?m >>= ?kk) s = _ =>
         assert (Hass : exec m s
                 = Some (andb (PMA_readable (override_PMA rattr pbmt))
                           (andb (PMA_writable (override_PMA rattr pbmt))
                              (pma_allows_atomic_op (PMA_atomic_support (override_PMA rattr pbmt))
                                 _ k)), s))
           by (rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl s)); apply exec_returnM);
         rewrite (exec_bind_Some _ _ _ _ _ Hass)
       end;
       cbn beta;
       rewrite Hread Hwrite Hsupp; cbn [andb pma_allows_atomic_op generic_eq];
       cbn match; apply exec_returnM).
  Qed.

  Lemma exec_checked_mem_read_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) = AMOSwap ->
    exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Atomic (op, Data, Data)) pbmt User (Physaddr addr) k aq (andb aq rl) true false) s
      = Some ((if generic_eq op AMOSWAP then Ok (w, default_meta) else Err (E_SAMO_Access_Fault tt)), s).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes.
    unfold checked_mem_read.
    assert (Hpac : exec (phys_access_check (Atomic (op, Data, Data)) pbmt User (Physaddr addr) k true) s
                   = Some ((if generic_eq op AMOSWAP then None else Some (E_SAMO_Access_Fault tt)), s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_amo_g op addr s HA Hord Hrange HR HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_amo_gk op addr pbmt region s Hmatch Halign Hread Hwrite Hsupp)).
      destruct (generic_eq op AMOSWAP); cbn match; apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    destruct (generic_eq op AMOSWAP) eqn:Hsw.
    - cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
      assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                      (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
      { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
          eexists; (split; [ apply exec_returnM | tauto ]). }
      destruct Hrk as (rk & Hrke & Hrkv).
      rewrite (exec_bind_Some _ _ _ _ _ Hrke).
      rewrite (exec_bind_Some _ _ _ _ _ (Hread_resv rk addr w s Hrkv Hdev Hbytes)).
      apply exec_returnM.
    - cbn match. apply exec_returnM.
  Qed.

  Lemma exec_mem_read_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) = AMOSwap ->
    exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_read (Atomic (op, Data, Data)) pbmt (Physaddr addr) k aq (andb aq rl) true) s
      = Some ((if generic_eq op AMOSWAP then Ok w else Err (E_SAMO_Access_Fault tt)), s).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes Hmprv Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm op _ _ s Hmprv)).
    unfold mem_read_priv.
    assert (Hcmr := exec_checked_mem_read_amo_gk op aq rl pbmt addr region w s HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes).
    assert (Hmrpm : exec (mem_read_priv_meta (Atomic (op, Data, Data)) pbmt User (Physaddr addr) k aq (andb aq rl) true false) s
                   = Some ((if generic_eq op AMOSWAP then Ok (w, default_meta) else Err (E_SAMO_Access_Fault tt)), s)).
    { unfold mem_read_priv_meta.
      destruct aq;
        (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
         rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
         destruct (generic_eq op AMOSWAP);
         cbn match; apply exec_returnM). }
    rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
    destruct (generic_eq op AMOSWAP);
      cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
  Qed.


  (* AMOSWAP write leaves (canAccess = true). *)
  Lemma exec_checked_mem_write_amo_gk (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) = AMOSwap ->
    exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) k data (Atomic (AMOSWAP, Data, Data)) pbmt User tt (andb aq rl) rl true) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev.
    unfold checked_mem_write.
    assert (Hpac : exec (phys_access_check (Atomic (AMOSWAP, Data, Data)) pbmt User (Physaddr addr) k true) s = Some (None, s)).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_amo_g AMOSWAP addr s HA Hord Hrange HR HW)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_amo_gk AMOSWAP addr pbmt region s Hmatch Halign Hread Hwrite Hsupp)).
      cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpac).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Hmmio).
    cbn match.
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    rewrite (exec_bind_Some _ _ _ _ _ Hwke).
    rewrite (exec_bind_Some _ _ _ _ _ (Hwrite_cond wk addr data s Hwkv Hdev)).
    apply exec_returnM.
  Qed.

  Lemma exec_mem_write_value_amo_gk (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) = AMOSwap ->
    exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_write_value (Physaddr addr) k data (Atomic (AMOSWAP, Data, Data)) pbmt (andb aq rl) rl true) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm AMOSWAP _ _ s Hmprv)).
    unfold mem_write_value_priv_meta.
    assert (Hcmw := exec_checked_mem_write_amo_gk aq rl pbmt addr region data s HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev).
    destruct aq; destruct rl;
      (rewrite Halign; cbn [Riscv.rv64d.not negb orb andb]; cbn match;
       rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; unfold mem_write_callback; apply exec_returnm).
  Qed.


  (* The Iris composer: at a mapped-ok page, the physical AMO facts. *)
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_amo_data_k (op : amoop) (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Atomic (op, Data, Data)) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (dv : mword (8 * k)) (σ' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Atomic (op, Data, Data))) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_write_ea (Physaddr (u_walk_pa w va)) k (andb aq rl) rl true) σ'
        = Some (Ok tt, σ')⌝ ∗
      ⌜exec (mem_read (Atomic (op, Data, Data)) PBMT_PMA
               (Physaddr (u_walk_pa w va)) k aq (andb aq rl) true) σ'
        = Some ((if generic_eq op AMOSWAP then Ok dv else Err (E_SAMO_Access_Fault tt)), σ')⌝ ∗
      ⌜forall v : mword (8 * k),
         exec (mem_write_value (Physaddr (u_walk_pa w va)) k v
                 (Atomic (AMOSWAP, Data, Data)) PBMT_PMA (andb aq rl) rl true) σ'
         = Some (Ok true,
                 MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) σ'.(mdev))⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (Atomic (op, Data, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_amo_nm op (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (Atomic (op, Data, Data)) σ
               (or_intror (or_intror (or_intror (or_intror (or_intror
                  (ex_intro _ op eq_refl))))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g k Hk Hkdvd um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k)
      as (region & Hpmam & _ & Hrd & Hwrat).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 k)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp_g pa _ k (Z.to_nat k - 1) Hk Hk16 Huintk ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Halp : is_aligned_paddr (Physaddr pa) k = true)
      by (exact (pa_aligned_div _ va k Hk Hkdvd Hal)).
    assert (Hmmior : exec (within_mmio_readable (Physaddr pa) k) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa k σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa k σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa k σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmmiow : exec (within_mmio_writable (Physaddr pa) k) σ' = Some (false, σ')).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa k σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa k σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false pa k σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    iModIntro.
    iExists dv, σ'.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { exact (exec_mem_write_ea_sc_g aq rl k pa σ' Halp). }
    iSplit; [ iPureIntro | ].
    { exact (exec_mem_read_amo_gk op aq rl PBMT_PMA pa region dv σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam Halp Hrd (proj1 Hwrat) (proj1 (proj2 Hwrat)) Hmmior (addr_is_ram_not_dev _ Hram0) Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; intros v | ].
    { exact (exec_mem_write_value_amo_gk aq rl PBMT_PMA pa region v σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam Halp Hrd (proj1 Hwrat) (proj1 (proj2 Hwrat)) Hmmiow (addr_is_ram_not_dev _ Hram0)
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

End AmoGeneric.

(* ===================================================================== *)
(* AMOSWAP retire with rd = 0 (no gpr write): final state is the write.   *)
(* ===================================================================== *)
Lemma exec_execute_AMO_u_ok_rd0
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5) (width : Z)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (loaded : mword (8 * width)) (md : SATPMode) (s s' s'' : mstate) :
  let rs2_val : bits (width * 8) :=
    trunc (Z.mul (__id width) 8)
      (if Z.eqb (uint rs2) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs)) in
  let lc : bits (width * 8) := autocast (T := mword) loaded in
  let result' : bits (width * 8) :=
    match op with
    | AMOSWAP => rs2_val | AMOADD => add_vec rs2_val lc | AMOXOR => xor_vec rs2_val lc
    | AMOAND => and_vec rs2_val lc | AMOOR => or_vec rs2_val lc
    | AMOMIN => if zopz0zI_s rs2_val lc then rs2_val else lc
    | AMOMAX => if zopz0zK_s rs2_val lc then rs2_val else lc
    | AMOMINU => if zopz0zI_u rs2_val lc then rs2_val else lc
    | AMOMAXU => if zopz0zK_u rs2_val lc then rs2_val else lc
    | AMOCAS => rs2_val end in
  (width <=? xlen_bytes) = true ->
  (width <=? Z.mul xlen_bytes 2) = true ->
  uint rd = 0 ->
  generic_eq op AMOCAS = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) width = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr width (andb aq rl) rl true) s' = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, Data, Data)) pbmt addr width aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (mem_write_value addr width (sign_extend' (Z.mul 8 (__id width)) result') (Atomic (op, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok true, s'') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd))) s
    = Some (RETIRE_SUCCESS, s'').
Proof.
  intros rs2_val lc result'.
  intros Hw Hw2 Hrd Hop Hcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, width, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) width (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return. rewrite Hw2.
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) width) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  rewrite Hw.
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_bits (Regidx rs2)))
                    (fun w6 : mword 64 => returnR ExecutionResult (trunc (__id width * 8) w6))) s'
               = Some (inr rs2_val, s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match.
  rewrite Hop.
  assert (Hab : forall (B : Defs.monadR ExecutionResult exception bool),
           execR (and_boolM (returnR ExecutionResult false) B) s' = Some (inr false, s')).
  { intro B. unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd false s')). cbn match.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ (Hab _)). cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
  assert (Hwx : exec (wX_bits (Regidx rd) (sign_extend' 64 lc)) s''
                = Some (tt, s'')).
  { rewrite (exec_wX_bits_gpr rd (sign_extend' 64 lc) s'').
    rewrite (proj2 (Z.eqb_eq (uint rd) 0) Hrd). reflexivity. }
  assert (Hwxr : execR (R := ExecutionResult) (Defs.liftR (wX_bits (Regidx rd) (sign_extend' 64 lc))) s''
               = Some (inr tt, s'')).
  { rewrite execR_liftR. rewrite Hwx. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.

(* ===================================================================== *)
(* Translate-fault composer at the Atomic acc (width-generic).            *)
(* ===================================================================== *)
Section AmoFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_amo_translate_fault (op : amoop) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (σ : mstate) :
    u_fault_flavor (Atomic (op, Data, Data)) tfp um va ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) (Atomic (op, Data, Data))) σ
      = Some (Err (E_SAMO_Page_Fault tt, tt), σ)⌝.
  Proof.
    intros Hflavor Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (Atomic (op, Data, Data)) uroot tfp um va
                 (E_SAMO_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_amo_nm op (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (Atomic (op, Data, Data)) σ
                    (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op eq_refl)))))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro. exact Htr.
  Qed.

End AmoFault.

(* ===================================================================== *)
(* The width-generic AMO execute engine (k in {1,2,4,8}).                 *)
(* ===================================================================== *)
Section AmoEngine.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_resv : forall (rk : rv64d_types.read_kind) (addr : mword 64) (w : mword (8 * k)) s,
      (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rk (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_cond : forall (wk : rv64d_types.write_kind) (addr : mword 64) (data : mword (8 * k)) s,
      (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
      dev_addr addr = false ->
      exec (write_ram wk (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_amo_k (pt : uptd) (op : amoop) (aq rl : bool)
      (rs2 rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (destruct op; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_amo_nm op (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    assert (Hxb : xlen_bytes = 8) by (vm_compute; reflexivity).
    assert (Hkle : (k <=? xlen_bytes) = true) by (apply Z.leb_le; rewrite Hxb; lia).
    assert (Hkle2 : (k <=? Z.mul xlen_bytes 2) = true) by (apply Z.leb_le; rewrite Hxb; lia).
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    2:{ (* misaligned -> E_SAMO_Access_Fault trap *)
      iModIntro. iRight.
      iExists (E_SAMO_Access_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_misaligned op aq rl rs2 rs1 rd k
                 (register_lookup PC s.(sregs)) Sv39 s Hkle2 Lcp Heff Hpml Htm eq_refl Hal). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
    (* aligned *)
    destruct (data_classify (Atomic (op, Data, Data)) pt.(ud_tfp) pt.(ud_um) va
                (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op eq_refl)))))) Hwf)
      as [ (w & Hum & Huleaf & Hcanon) | Hfault ].
    - (* mapped-ok *)
      iMod (user_pt_amo_data_k k Hk ltac:(lia) Hkdvd Huintk Hread_resv Hwrite_cond op aq rl
              pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) w va s
              Hum Huleaf Hcov Hal Hcanon Hmisa Hmenv Hhtif Lcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata")
        as (dv sig') "(%Htr & %Hea & %Hrdm & %Hwv & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      destruct (generic_eq op AMOSWAP) eqn:Hsw.
      + (* AMOSWAP: retire *)
        assert (Hopeq : op = AMOSWAP)
          by (destruct op; cbn in Hsw; try discriminate; reflexivity).
        subst op.
        assert (Hopcas : generic_eq AMOSWAP AMOCAS = false) by reflexivity.
        set (rs2v := trunc (Z.mul (__id k) 8)
                       (if Z.eqb (uint rs2) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) sig'.(sregs))
                     : bits (k * 8)).
        set (v := sign_extend' (Z.mul 8 (__id k)) rs2v : mword (8 * k)).
        assert (Hwv' := Hwv v).
        set (s2 := MState sig'.(sregs) (write_bytes sig'.(mem) (u_walk_pa w va) (Z.to_N k) v) sig'.(mdev)).
        (* Hrdm is already reduced to Some (Ok dv, sig') after subst op *)
        (* absorb the memory write into udata_own *)
        iMod (udata_own_store_g k
                pt.(ud_data) (u_walk_pa w va) v sig'.(mem)
                (fun j Hj => ltac:(
                   rewrite (u_walk_pa_window_div k _ _ _ Hk Hkdvd Hal Hj);
                   exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hum)))
                with "Hgh Hudata") as "[Hgh Hudata]".
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
        * (* rd = 0 *)
          apply Z.eqb_eq in Hrd0.
          assert (Hexec : exec (execute (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                          = Some (RETIRE_SUCCESS, s2)).
          { exact (exec_execute_AMO_u_ok_rd0 AMOSWAP aq rl rs2 rs1 rd k
                     (Physaddr (u_walk_pa w va)) PBMT_PMA dv Sv39 s sig' s2
                     Hkle Hkle2 Hrd0 Hopcas Lcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv'). }
          iModIntro. iLeft. iExists g, s2.
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR; [iPureIntro; unfold s2; cbn [sregs]; apply Tr; vm_compute; reflexivity |].
          iSplitR; [iPureIntro; unfold s2; cbn [sregs]; apply Tr; vm_compute; reflexivity |].
          iSplitL "Hreg Hgh Hdev". { unfold s2; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
        * (* rd <> 0 *)
          apply Z.eqb_neq in Hrd0.
          set (nv := regval_into_reg (sign_extend' 64 (autocast (T := mword) dv : mword (k * 8)))).
          assert (Hexec : exec (execute (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                          = Some (RETIRE_SUCCESS, set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd))) nv)).
          { exact (exec_execute_AMO_u_ok AMOSWAP aq rl rs2 rs1 rd k
                     (Physaddr (u_walk_pa w va)) PBMT_PMA dv Sv39 s sig' s2
                     Hkle Hkle2 Hrd0 Hopcas Lcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv'). }
          iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
          iDestruct "Hrdf" as (v0) "Hrdf".
          iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
          iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
          iModIntro. iLeft. set (s_x := set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
          iExists (<[Regidx rd := nv]> g), s_x.
          iSplitR; [iPureIntro; unfold s_x, nv; exact Hexec |].
          assert (Tr2 : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                    register_lookup r s_x.(sregs) = register_lookup r s2.(sregs)).
          { intros r Hne. unfold s_x, set_reg; cbn [sregs]. apply irrelevant_register_set; exact Hne. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitL "Hreg Hgh Hdev".
          { unfold s_x, s2, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
      + (* non-swap: mem_read Err (destruct already reduced Hrdm) -> trap *)
        assert (Hexec : exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                        = Some (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt)
                                  (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                           (zeros' 64)), register_lookup PC sig'.(sregs)), sig')).
        { exact (exec_execute_AMO_u_read_err op aq rl rs2 rs1 rd k
                   (Physaddr (u_walk_pa w va)) PBMT_PMA (E_SAMO_Access_Fault tt)
                   (register_lookup PC sig'.(sregs)) Sv39 s sig'
                   Hkle Hkle2 Lcp Heff Hpml Htm
                   (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp))
                   eq_refl Hal Htr Hea Hrdm). }
        iModIntro. iRight.
        iExists (E_SAMO_Access_Fault tt), _, (register_lookup PC sig'.(sregs)), sig'.
        iSplitR; [iPureIntro; exact Hexec |].
        iSplitR; [iPureIntro; vm_compute; reflexivity |].
        iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
        iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
        iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - (* fault -> translate-fault trap *)
      iDestruct (user_pt_amo_translate_fault op pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va s
                   Hfault Hhtif Lcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Htr.
      iModIntro. iRight.
      iExists (E_SAMO_Page_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_translate_err op aq rl rs2 rs1 rd k
                 (E_SAMO_Page_Fault tt) (register_lookup PC s.(sregs)) Sv39 s s
                 Hkle2 Lcp Heff Hpml Htm Lcp eq_refl Hal Htr). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End AmoEngine.

(* ===================================================================== *)
(* Width-16 (AMOCAS) read-deny trap: the width>xlen (rX_pair) branch.     *)
(* ===================================================================== *)
Lemma exec_rX_pair_bits_gpr (rs : mword 5) s :
  exists v : mword (64 * 2), exec (rX_pair_bits (Regidx rs)) s = Some (v, s).
Proof.
  unfold rX_pair_bits.
  destruct (generic_neq (Regidx rs) zreg) eqn:Hz.
  - eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (add_vec_int rs 1) s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs s)).
    apply exec_returnM.
  - eexists. apply exec_returnM.
Qed.

Lemma exec_execute_AMO_u_read_err_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type) (e : ExceptionType)
    (pc : mword 64) (md : SATPMode) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr 16 (andb aq rl) rl true) s' = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Err e, s') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (Trap (User, make_sync_exception e
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s').
Proof.
  intros Hcp Heff Hpml Htm Hcp' Hpc' Hal Htr Hea Hrdm.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  destruct (exec_rX_pair_bits_gpr rs2 s') as (rp & Hrp).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_memory_exception _ pc e User s' Hcp' Hpc')).
  reflexivity.
Qed.

(* ===================================================================== *)
(* Width-generic AMO read DENY (op != AMOSWAP): mem_read = Err, no bytes.  *)
(* ===================================================================== *)

(* ===================================================================== *)
(* addr_is_ram at any data address (from udata_own), + width-16 deny.      *)
(* ===================================================================== *)
Section AmoDeny16.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.



End AmoDeny16.

(* ===================================================================== *)
(* Width-16 (AMOCAS width) support: AMOSWAP RETIRES at width 16 (128-bit  *)
(* rX_pair/wX_pair), every other op DENIES (mem_read Err) -> trap.        *)
(* ===================================================================== *)

(* 128-bit RAM read/write leaves (clones of the width-8 versions). *)
Lemma exec_read_ram_resv_kinds_16 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 128) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 16)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 16 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 16 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 16) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_write_ram_cond_kinds_16 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 128) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 16 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 16 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn [Mem_write_request_value]; cbn match; cbn [Interface.iMon_bind];
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

(* rd = 0 bridge: relate the wX_pair zreg guard to the uint. *)
Lemma neq_rd_zreg_uint (rd : mword 5) :
  generic_neq (Regidx rd) zreg = true -> Z.eqb (uint rd) 0 = false.
Proof.
  intro Hz. apply generic_neq_true in Hz.
  apply Z.eqb_neq. intro E.
  apply Hz. unfold zreg. f_equal.
  apply bv_eq.
  replace (bv_unsigned (zero_extend' 5 ('b"00"))) with 0%Z by (vm_compute; reflexivity).
  rewrite <- (uint_unsigned_n 5 rd). exact E.
Qed.

(* wX_pair reduction: writes rd (low 64) and rd+1 (high 64) when rd<>0. *)
Definition wpair_state (rd : mword 5) (data : mword (64 * 2)) (s : mstate) : mstate :=
  if generic_neq (Regidx rd) zreg
  then
    let s1 := (if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (subrange_vec_dec data (Z.sub xlen 1) 0))) in
    (if Z.eqb (uint (add_vec_int rd 1)) 0 then s1
     else set_reg s1 (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1))))
            (regval_into_reg (subrange_vec_dec data (Z.sub (Z.mul xlen 2) 1) xlen)))
  else s.

Lemma exec_wX_pair_bits_gpr (rd : mword 5) (data : mword (64 * 2)) s :
  exec (wX_pair_bits (Regidx rd) data) s = Some (tt, wpair_state rd data s).
Proof.
  unfold wX_pair_bits, wpair_state.
  destruct (generic_neq (Regidx rd) zreg) eqn:Hz.
  - rewrite (exec_bind0_Some _ _ _ _ _
               (exec_wX_bits_gpr rd (subrange_vec_dec data (Z.sub xlen 1) 0) s)).
    change (regidx_offset_range (Regidx rd) 1) with (Regidx (add_vec_int rd 1)).
    apply exec_wX_bits_gpr.
  - apply exec_returnM.
Qed.

(* AMOSWAP retire at width 16: rs2 via rX_pair, rd written via wX_pair. *)
Lemma exec_execute_AMO_u_ok_16
    (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode) (s s' s'' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (AMOSWAP, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (AMOSWAP, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (AMOSWAP, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (mem_write_ea addr 16 (andb aq rl) rl true) s' = Some (Ok tt, s') ->
  exec (mem_read (Atomic (AMOSWAP, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (mem_write_value addr 16
          (sign_extend' (Z.mul 8 (__id 16)) (trunc (Z.mul (__id 16) 8) rp))
          (Atomic (AMOSWAP, Data, Data)) pbmt (andb aq rl) rl true) s' = Some (Ok true, s'') ->
  exec (execute (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'').
Proof.
  intros Hcp Heff Hpml Htm Hal Htr Hrp Hea Hrdm Hwv.
  change (execute (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO AMOSWAP aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (AMOSWAP, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match zeta.
  replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
  assert (Hab : forall (B : Defs.monadR ExecutionResult exception bool),
           execR (and_boolM (returnR ExecutionResult false) B) s' = Some (inr false, s')).
  { intro B. unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd false s')). cbn match.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ (Hab _)). cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))))) s''
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxpr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.

(* ===================================================================== *)
(* Width-16 AMO execute engine: AMOSWAP retires (128-bit, register pair), *)
(* every other op denies (mem_read Err) -> trap; misalign / walk-fault    *)
(* -> trap.  Mirrors mem_exec_amo_k but at the fixed wide width 16.        *)
(* ===================================================================== *)
Section AmoEngine16.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_amo_16 (pt : uptd) (op : amoop) (aq rl : bool)
      (rs2 rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Atomic (op, Data, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption; try (destruct op; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_amo_nm op (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    assert (Hkle2 : (16 <=? Z.mul xlen_bytes 2) = true) by (vm_compute; reflexivity).
    destruct (is_aligned_vaddr (Virtaddr va) 16) eqn:Hal.
    2:{ (* misaligned -> E_SAMO_Access_Fault trap *)
      iModIntro. iRight.
      iExists (E_SAMO_Access_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_misaligned op aq rl rs2 rs1 rd 16
                 (register_lookup PC s.(sregs)) Sv39 s Hkle2 Lcp Heff Hpml Htm eq_refl Hal). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
    (* aligned *)
    destruct (data_classify (Atomic (op, Data, Data)) pt.(ud_tfp) pt.(ud_um) va
                (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op eq_refl)))))) Hwf)
      as [ (w & Hum & Huleaf & Hcanon) | Hfault ].
    - (* mapped-ok *)
      iMod (user_pt_amo_data_k 16 ltac:(lia) ltac:(lia) ltac:(exists 256; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_resv_kinds_16 exec_write_ram_cond_kinds_16 op aq rl
              pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) w va s
              Hum Huleaf Hcov Hal Hcanon Hmisa Hmenv Hhtif Lcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata")
        as (dv sig') "(%Htr & %Hea & %Hrdm & %Hwv & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      destruct (generic_eq op AMOSWAP) eqn:Hsw.
      + (* AMOSWAP: retire (register pair) *)
        assert (Hopeq : op = AMOSWAP)
          by (destruct op; cbn in Hsw; try discriminate; reflexivity).
        subst op.
        destruct (exec_rX_pair_bits_gpr rs2 sig') as (rp & Hrp).
        set (v := sign_extend' (Z.mul 8 (__id 16)) (trunc (Z.mul (__id 16) 8) rp) : mword (8 * 16)).
        assert (Hwv' := Hwv v).
        set (s2 := MState sig'.(sregs) (write_bytes sig'.(mem) (u_walk_pa w va) (Z.to_N 16) v) sig'.(mdev)).
        iMod (udata_own_store_g 16
                pt.(ud_data) (u_walk_pa w va) v sig'.(mem)
                (fun j Hj => ltac:(
                   rewrite (u_walk_pa_window_div 16 _ _ _ ltac:(lia) ltac:(exists 256; reflexivity) Hal Hj);
                   exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hum)))
                with "Hgh Hudata") as "[Hgh Hudata]".
        set (D := sign_extend' (Z.mul 64 2) (autocast (T := mword) dv : mword (16 * 8))).
        assert (Hexec : exec (execute (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
                        = Some (RETIRE_SUCCESS, wpair_state rd D s2)).
        { exact (exec_execute_AMO_u_ok_16 aq rl rs2 rs1 rd
                   (Physaddr (u_walk_pa w va)) PBMT_PMA rp dv Sv39 s sig' s2
                   Lcp Heff Hpml Htm Hal Htr Hrp Hea Hrdm Hwv'). }
        (* minstret / nextPC are preserved through the wpair set_regs *)
        assert (Hpres : forall (r : register), register_beq r tlb = false ->
                  register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                  register_beq r (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = false ->
                  register_lookup r (wpair_state rd D s2).(sregs) = register_lookup r s.(sregs)).
        { intros r Hne1 Hne2 Hne3. unfold wpair_state.
          destruct (generic_neq (Regidx rd) zreg);
            [ destruct (Z.eqb (uint rd) 0); destruct (Z.eqb (uint (add_vec_int rd 1)) 0);
              unfold s2, set_reg; cbn [sregs];
              repeat (rewrite irrelevant_register_set; [| assumption]);
              apply Tr; exact Hne1
            | unfold s2; cbn [sregs]; apply Tr; exact Hne1 ]. }
        (* the register file after the pair write *)
        destruct (generic_neq (Regidx rd) zreg) eqn:Hz.
        * (* rd <> 0: rd (and maybe rd+1) written *)
          assert (Hrd0 : uint rd <> 0) by (apply Z.eqb_neq; apply neq_rd_zreg_uint; exact Hz).
          set (nvlo := regval_into_reg (subrange_vec_dec D (Z.sub xlen 1) 0)).
          iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
          iDestruct "Hrdf" as (v0) "Hrdf".
          iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nvlo with "Hreg Hrdf") as "[Hreg Hrdf]".
          iDestruct ("Hins" $! nvlo with "Hrdf") as "Hgpr".
          set (s1 := set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd))) nvlo).
          destruct (Z.eqb (uint (add_vec_int rd 1)) 0) eqn:Hrd1.
          -- (* rd+1 = 0: only rd written; final state = s1 *)
            iModIntro. iLeft. iExists (<[Regidx rd := nvlo]> g), (wpair_state rd D s2).
            assert (Hst : wpair_state rd D s2 = s1).
            { unfold wpair_state, s1. rewrite Hz. rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0).
              rewrite Hrd1. reflexivity. }
            iSplitR; [iPureIntro; exact Hexec |].
            iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne |
                       apply Z.eqb_eq in Hrd1; rewrite Hrd1 (* rd+1 = 0 -> R_bitvector_64 0 <> minstret *); reg_ne ]. }
            iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne |
                       apply Z.eqb_eq in Hrd1; rewrite Hrd1; reg_ne ]. }
            iSplitL "Hreg Hgh Hdev".
            { rewrite Hst. unfold s1, s2, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
            iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
          -- (* rd+1 <> 0: both rd and rd+1 written *)
            apply Z.eqb_neq in Hrd1.
            set (nvhi := regval_into_reg (subrange_vec_dec D (Z.sub (Z.mul xlen 2) 1) xlen)).
            iDestruct (gpr_file_acc (<[Regidx rd := nvlo]> g) (add_vec_int rd 1) Hrd1 with "Hgpr") as "[Hr1f Hins1]".
            iDestruct "Hr1f" as (v1) "Hr1f".
            iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) v1 nvhi with "Hreg Hr1f") as "[Hreg Hr1f]".
            iDestruct ("Hins1" $! nvhi with "Hr1f") as "Hgpr".
            iModIntro. iLeft.
            iExists (<[Regidx (add_vec_int rd 1) := nvhi]> (<[Regidx rd := nvlo]> g)), (wpair_state rd D s2).
            assert (Hst : wpair_state rd D s2
                      = set_reg s1 (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) nvhi).
            { unfold wpair_state, s1, nvlo, nvhi. rewrite Hz.
              rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0).
              rewrite (proj2 (Z.eqb_neq (uint (add_vec_int rd 1)) 0) Hrd1). reflexivity. }
            iSplitR; [iPureIntro; exact Hexec |].
            iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne | reg_ne ]. }
            iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne | reg_ne ]. }
            iSplitL "Hreg Hgh Hdev".
            { rewrite Hst. unfold s1, s2, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
            iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
        * (* rd = 0: no gpr write, final state = s2 *)
          iModIntro. iLeft. iExists g, (wpair_state rd D s2).
          assert (Hst : wpair_state rd D s2 = s2) by (unfold wpair_state; rewrite Hz; reflexivity).
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR. { iPureIntro. rewrite Hst. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitR. { iPureIntro. rewrite Hst. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitL "Hreg Hgh Hdev".
          { rewrite Hst. unfold s2; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
      + (* non-swap: mem_read Err -> trap (rX_pair path) *)
        destruct (exec_rX_pair_bits_gpr rs2 sig') as (rp & Hrp).
        assert (Hexec : exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
                        = Some (Trap (User, make_sync_exception (E_SAMO_Access_Fault tt)
                                  (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                           (zeros' 64)), register_lookup PC sig'.(sregs)), sig')).
        { exact (exec_execute_AMO_u_read_err_16 op aq rl rs2 rs1 rd
                   (Physaddr (u_walk_pa w va)) PBMT_PMA (E_SAMO_Access_Fault tt)
                   (register_lookup PC sig'.(sregs)) Sv39 s sig'
                   Lcp Heff Hpml Htm
                   (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp))
                   eq_refl Hal Htr Hea Hrdm). }
        iModIntro. iRight.
        iExists (E_SAMO_Access_Fault tt), _, (register_lookup PC sig'.(sregs)), sig'.
        iSplitR; [iPureIntro; exact Hexec |].
        iSplitR; [iPureIntro; vm_compute; reflexivity |].
        iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
        iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
        iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - (* fault -> translate-fault trap *)
      iDestruct (user_pt_amo_translate_fault op pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va s
                   Hfault Hhtif Lcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Htr.
      iModIntro. iRight.
      iExists (E_SAMO_Page_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_translate_err op aq rl rs2 rs1 rd 16
                 (E_SAMO_Page_Fault tt) (register_lookup PC s.(sregs)) Sv39 s s
                 Hkle2 Lcp Heff Hpml Htm Lcp eq_refl Hal Htr). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End AmoEngine16.

(* ===================================================================== *)
(* arm_AMO_u : the AMO memory arm.  Widths {1,2,4,8} via mem_exec_amo_k    *)
(* (AMOSWAP retires, all other ops trap); width 16 via mem_exec_amo_16     *)
(* (AMOSWAP retires with a register-pair write, all other ops trap).       *)
(* ===================================================================== *)
Lemma arm_AMO_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
  exec (ext_decode w) sigma_f = Some (AMO (op, aq, rl, rs2, rs1, width, rd), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs2 as [rs2]. destruct rs1 as [rs1]. destruct rd as [rd].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hwidth as [Hw|[Hw|[Hw|[Hw|Hw]]]]; subst width.
  - (* width 1 *)
    iMod (mem_exec_amo_k 1 ltac:(lia) ltac:(lia) ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_1 exec_write_ram_cond_kinds_1
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 1, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 1, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 2 *)
    iMod (mem_exec_amo_k 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_2 exec_write_ram_cond_kinds_2
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 2, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 2, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 4 *)
    iMod (mem_exec_amo_k 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_4 exec_write_ram_cond_kinds_4
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 8 *)
    iMod (mem_exec_amo_k 8 ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_8 exec_write_ram_cond_kinds_8
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 16 *)
    iMod (mem_exec_amo_16 pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* ===================================================================== *)
(*  arm_ZICBOP_u : the ZICBOP prefetch memory arm (19th memory arm).       *)
(*  execute_ZICBOP runs a CacheAccess(CB_prefetch) translateAddr and ALWAYS *)
(*  RETIRES (fault suppressed to nop-retire).  The CacheAccess leaf-check   *)
(*  equals the corresponding u_acc check (check_ca_eq), so upt_acc_wf       *)
(*  classifies it; the Ok branch's phys_access_check grants over the owned  *)
(*  RAM page; both outcomes reframe (finish-unchanged-shaped) to base_post. *)
(* ===================================================================== *)
Definition uacc_of (cbop : cbop_zicbop) : MemoryAccessType mem_payload :=
  match cbop with
  | PREFETCH_R => Load Data
  | PREFETCH_W => Store Data
  | PREFETCH_I => InstructionFetch tt
  end.

Lemma exec_is_shadow_stack_ca (cbop : cbop_zicbop) s :
  exec (is_shadow_stack_access (CacheAccess (CB_prefetch cbop))) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma check_ca_eq (cbop : cbop_zicbop) (mxr ds : bool) (flags : mword 8) (ext : mword 10) s :
  exec (check_PTE_permission (CacheAccess (CB_prefetch cbop)) User mxr ds flags ext tt) s
  = exec (check_PTE_permission (uacc_of cbop) User mxr ds flags ext tt) s.
Proof.
  unfold check_PTE_permission, uacc_of.
  rewrite !exec_catch_early_return.
  destruct cbop; cbn match; [ reflexivity | | ].
  all: set (W := bit_to_bool (_get_PTE_Flags_W flags)) in *;
       set (R := bit_to_bool (_get_PTE_Flags_R flags)) in *;
       set (X := bit_to_bool (_get_PTE_Flags_X flags)) in *;
       cbv zeta;
       rewrite !execR_bind;
       destruct (zopz0zJzJzK W R) eqn:Hassert;
       rewrite !execR_liftR;
       unfold assert_exp; cbn match;
       rewrite ?exec_returnm;
       cbn match;
       rewrite ?execR_returnR;
       cbn match.
  all: try reflexivity.
  all: destruct (bit_to_bool (_get_PTE_Flags_U flags)); cbn match.
  all: try reflexivity.
  all: change (not true) with false; cbn match.
  all: assert (Hmc : (negb R && (W && negb X))%bool = false)
         by (clear -Hassert; unfold zopz0zJzJzK in Hassert;
             destruct W, R; simpl in *; try discriminate; reflexivity).
  all: rewrite Hmc; cbn match.
  all: rewrite !execR_bind0.
  all: first
       [ rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_ca _ s))
       | rewrite (execR_liftR_seq _ _ _ _ _
                    (exec_is_shadow_stack_u_acc (Load Data) s ltac:(unfold u_acc; auto)))
       | rewrite (execR_liftR_seq _ _ _ _ _
                    (exec_is_shadow_stack_u_acc (Store Data) s ltac:(unfold u_acc; auto))) ].
  all: cbn match.
  all: rewrite !execR_returnR.
  all: cbn match.
  all: reflexivity.
Qed.

(* transfer the leaf classification from the u_acc access to the CacheAccess *)
Lemma uleaf_ok_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_ok (uacc_of cbop) w -> uleaf_ok (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s). apply H.
Qed.

Lemma uleaf_denied_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_denied (uacc_of cbop) w -> uleaf_denied (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s). apply H.
Qed.

(* ===== block alignment ===== *)
Lemma block_aligned (addr : mword 64) :
  is_aligned_vaddr (Virtaddr (and_vec addr (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp)))))) (pow2 (plat_cache_block_size_exp)) = true.
Proof.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  replace (pow2 plat_cache_block_size_exp) with 64 by (vm_compute; reflexivity).
  rewrite uint_unsigned. rewrite WpGprCsrwC.and_vec_unsigned.
  assert (HM : bv_unsigned (not_vec (zero_extend' 64 (ones plat_cache_block_size_exp)) : mword 64)
             = 18446744073709551552) by (vm_compute; reflexivity).
  rewrite HM.
  rewrite Z.rem_mod_nonneg; [ | apply Z.land_nonneg; left; apply (proj1 (bv_unsigned_in_range 64 addr)) | lia ].
  change 64 with (2 ^ 6).
  rewrite <- Z.land_ones by lia.
  replace (Z.ones 6) with 63 by (vm_compute; reflexivity).
  rewrite <- Z.land_assoc.
  replace (Z.land 18446744073709551552 63) with 0 by (vm_compute; reflexivity).
  apply Z.land_0_r.
Qed.

(* ===== pmpCheck CacheAccess grant (User) : entry-0 TOR RWX match -> None ===== *)
Lemma exec_pmpCheck_user_grant_ca (cbop : cbop_zicbop) (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (CacheAccess (CB_prefetch cbop)) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX HW HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (CacheAccess (CB_prefetch cbop))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. destruct cbop; cbn match;
        [ rewrite HX | rewrite HR | rewrite HW ]; apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ===== pmaCheck CacheAccess : aligned RAM page -> None ===== *)
Lemma exec_pmaCheck_ca (cbop : cbop_zicbop) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (width : Z) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) width (CacheAccess (CB_prefetch cbop)) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hx Hr Hw.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hx, Hr, Hw |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  destruct cbop; cbn match; [ rewrite Hx | rewrite Hr | rewrite Hw ];
    cbn [andb negb]; apply exec_returnM.
Qed.

(* ===== phys_access_check CacheAccess -> None ===== *)
Lemma exec_phys_access_check_ca (cbop : cbop_zicbop) (pbmt : page_based_mem_type)
    (a : mword 64) (region : PMA_Region) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) width = Some region ->
  is_aligned_paddr (Physaddr a) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (phys_access_check (CacheAccess (CB_prefetch cbop)) pbmt User (Physaddr a) width false) s
    = Some (None, s).
Proof.
  intros HA Hord Hrange HX HW HR Hmatch Halign Hx Hr Hw.
  unfold phys_access_check.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_ca cbop a width s HA Hord Hrange HX HW HR)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ca cbop a pbmt region width s Hmatch Halign Hx Hr Hw)).
  apply exec_returnM.
Qed.

(* ===== small pure helpers ===== *)
Lemma add_sub_cancel (a b : mword 64) : add_vec a (sub_vec b a) = b.
Proof.
  apply bv_eq.
  unfold add_vec, sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add, MachineWord.MachineWord.sub.
  rewrite bv_add_unsigned. rewrite bv_sub_unsigned.
  rewrite bv_wrap_add_idemp_r.
  replace (bv_unsigned a + (bv_unsigned b - bv_unsigned a)) with (bv_unsigned b) by lia.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma uacc_of_u_acc (cbop : cbop_zicbop) : u_acc (uacc_of cbop).
Proof. destruct cbop; unfold u_acc, uacc_of; auto. Qed.

Lemma u_fault_flavor_ca (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  u_fault_flavor (uacc_of cbop) tfp um va -> u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  unfold u_fault_flavor. intros [H|[H|H]].
  - left; exact H.
  - right; left; exact H.
  - right; right. destruct H as (Hc & w & Hleaf & Hden).
    split; [exact Hc|]. exists w. split; [exact Hleaf | apply uleaf_denied_ca; exact Hden].
Qed.

Lemma ca_classify (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  upt_acc_wf um ->
  u_data_ok (CacheAccess (CB_prefetch cbop)) um va \/ u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  intro Hwf.
  destruct (data_classify (uacc_of cbop) tfp um va (uacc_of_u_acc cbop) Hwf) as [Hok|Hf].
  - left. destruct Hok as (w & Hm & Hok & Hc). exists w.
    split; [exact Hm | split; [ apply uleaf_ok_ca; exact Hok | exact Hc ]].
  - right. apply u_fault_flavor_ca; exact Hf.
Qed.

(* the CacheAccess translationException maps every non-No_Access PTW error to
   the same page-fault exception (result discarded by ZICBOP) *)
Lemma exec_translationException_ca_pf (cbop : cbop_zicbop) (f : PTW_Error) s :
  (f = PTW_Invalid_Addr tt \/ f = PTW_Invalid_PTE tt \/ f = PTW_No_Permission tt) ->
  exec (translationException (CacheAccess (CB_prefetch cbop)) f) s
    = Some (match cbop with
            | PREFETCH_R => E_Load_Page_Fault tt
            | PREFETCH_W => E_SAMO_Page_Fault tt
            | PREFETCH_I => E_Fetch_Page_Fault tt end, s).
Proof.
  intro Hf. unfold translationException.
  destruct Hf as [-> | [-> | ->]]; destruct cbop; cbn match; apply exec_returnM.
Qed.

Section ZicbopExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma exec_execute_ZICBOP_u (cbop : cbop_zicbop) (rs1 : mword 5) (offset : mword 12)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (s0 : mstate) :
    register_lookup cur_privilege s0.(sregs) = User ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus s0.(sregs))) ('b"0") = true ->
    register_lookup misa s0.(sregs) = MISA_C ->
    register_lookup menvcfg s0.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s0.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s0.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus s0.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions s0.(sregs)) ->
    upt_acc_wf um -> udata_cov um data ->
    reg_interp s0.(sregs) -∗ gen_heap_interp s0.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ s_x : mstate,
      ⌜exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0 = Some (RETIRE_SUCCESS, s_x)⌝ ∗
      ⌜s_x.(mdev) = s0.(mdev)⌝ ∗
      ⌜(s_x.(sregs) = s0.(sregs) \/ exists tv, s_x.(sregs) = register_set tlb tv s0.(sregs))%type⌝ ∗
      reg_interp s_x.(sregs) ∗ gen_heap_interp s_x.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Lcp Hmprv Hmxr Hmisa Hmenv Hsenv Hhtif HSXL Hpma Hwf Hcov.
    iIntros "Hri Hgh Hinv Hdata".
    assert (Hpml : exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s0 = Some (0, s0)).
    { apply exec_get_pmlen_u;
        first [ assumption | destruct cbop; vm_compute; reflexivity ]. }
    assert (Heff : exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
                          (register_lookup mstatus s0.(sregs)) User) s0 = Some (User, s0))
      by (apply exec_effectivePrivilege_mprv0; exact Hmprv).
    iDestruct (utlb_inv_pt_translationMode_U uroot tfp um s0 HSXL with "Hri Hinv")
      as "(%Htm & Hri & Hinv)".
    set (rv := if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s0.(sregs)).
    set (cba := and_vec (add_vec rv (sign_extend' 64 offset))
                        (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp))))).
    (* get_transformed_data_addr -> OK (Virtaddr cba) *)
    assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (sub_vec cba rv)
                           (CacheAccess (CB_prefetch cbop)) (pow2 (plat_cache_block_size_exp))) s0
                    = Some (Ext_DataAddr_OK (Virtaddr cba), s0)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (sub_vec cba rv)
                 (CacheAccess (CB_prefetch cbop)) (pow2 (plat_cache_block_size_exp)) s0)).
      cbn match. fold rv.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_transform_effective_address_u (CacheAccess (CB_prefetch cbop)) Sv39
                    (add_vec rv (sub_vec cba rv)) s0 Lcp Heff Hpml Htm)).
      rewrite add_sub_cancel. apply exec_returnm. }
    destruct (ca_classify cbop tfp um cba Hwf) as [Hok | Hfault].
    - (* Ok : mapped, check passes -> translate Ok, phys grants, retire *)
      destruct Hok as (w & Hm & Hchk & Hcanon).
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um s0
                   with "Hri Hinv") as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (CacheAccess (CB_prefetch cbop)) uroot tfp um w cba
              (u_walk_pa w cba) s0 Hm Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Lcp HSXL Heff
              (exec_is_shadow_stack_ca cbop s0) Hpma with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r s0.(sregs)).
      { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      assert (Halb : is_aligned_vaddr (Virtaddr cba) 64 = true).
      { replace 64 with (pow2 (plat_cache_block_size_exp)) by (vm_compute; reflexivity).
        apply block_aligned. }
      iDestruct (udata_read_word_g 64 ltac:(lia) ltac:(exists 64; reflexivity) um data w cba σ'
                   Hm Hcov Halb with "Hgh Hdata") as %(dv & Hbytes & Hram0 & Hram63).
      set (pa := u_walk_pa w cba) in *.
      assert (HA' : pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA).
      assert (Hord' : zopz0zKzJ_u (zeros' 64)
        (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false)
        by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord).
      assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX).
      assert (HW' : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW).
      assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR).
      assert (Hcovp' : (ram_base + ram_size
        <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z)
        by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp).
      assert (Hpma' : pma_allows_all (register_lookup pma_regions σ'.(sregs)))
        by (rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hpma).
      destruct (Hpma' pa 64) as (region & Hpmam & Hxr & Hrr & Hwr & _).
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 64)) = PMP_Match).
      { pose proof Hram0 as [Halo Hahi]. pose proof Hram63 as [_ Hhilast].
        rewrite (uint_pa_add pa (Z.to_nat 64 - 1)
                   ltac:(unfold ram_base, ram_size in Hahi; rewrite uint_unsigned in Hahi |- *; lia))
          in Hhilast.
        apply (ram_pmp_match_w pa _ 64 ltac:(lia) ltac:(vm_compute; reflexivity)
                 Halo ltac:(unfold ram_base, ram_size in *; lia) Hcovp'). }
      assert (Hphys : exec (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA User
                (Physaddr pa) 64 false) σ' = Some (None, σ')).
      { apply (exec_phys_access_check_ca cbop PBMT_PMA pa region 64 σ'
                 HA' Hord' Hrange HX' HW' HR' Hpmam
                 (pa_aligned_div _ cba 64 ltac:(lia) ltac:(exists 64; reflexivity) Halb)
                 Hxr Hrr Hwr). }
      assert (Hexec : exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0
                      = Some (RETIRE_SUCCESS, σ')).
      { change (execute (ZICBOP (cbop, Regidx rs1, offset)))
          with (execute_ZICBOP cbop (Regidx rs1) offset).
        unfold execute_ZICBOP.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s0)). fold rv. cbn zeta.
        rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
        match goal with |- exec (Defs.bind0 ?A _) s0 = _ =>
          assert (HAbody : exec A s0 = Some (tt, σ')) end.
        { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus σ')).
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege σ')).
          rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). rewrite Lcp.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_effectivePrivilege_mprv0 (CacheAccess (CB_prefetch cbop))
                        (register_lookup mstatus σ'.(sregs)) User σ'
                        (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv)))).
          replace (pow2 (plat_cache_block_size_exp)) with 64 by (vm_compute; reflexivity).
          rewrite (exec_bind_Some _ _ _ _ _ Hphys). cbn match. apply exec_returnm. }
        unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody). apply exec_returnm. }
      iModIntro. iExists σ'.
      iSplit; [ iPureIntro; exact Hexec | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - (* Fault : translate Err -> retire, state unchanged *)
      set (e := match cbop with
                | PREFETCH_R => E_Load_Page_Fault tt
                | PREFETCH_W => E_SAMO_Page_Fault tt
                | PREFETCH_I => E_Fetch_Page_Fault tt end).
      iDestruct (utlb_inv_pt_translateAddr_u_fault (CacheAccess (CB_prefetch cbop)) uroot tfp um
                   cba e s0 Hfault Hhtif Lcp HSXL Heff (exec_is_shadow_stack_ca cbop s0) Hpma
                   (exec_translationException_ca_pf cbop (PTW_Invalid_Addr tt) s0 (or_introl eq_refl))
                   (exec_translationException_ca_pf cbop (PTW_Invalid_PTE tt) s0 (or_intror (or_introl eq_refl)))
                   (exec_translationException_ca_pf cbop (PTW_No_Permission tt) s0 (or_intror (or_intror eq_refl)))
                   with "Hri Hgh Hinv") as %Htr.
      assert (Hexec : exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0
                      = Some (RETIRE_SUCCESS, s0)).
      { change (execute (ZICBOP (cbop, Regidx rs1, offset)))
          with (execute_ZICBOP cbop (Regidx rs1) offset).
        unfold execute_ZICBOP.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s0)). fold rv. cbn zeta.
        rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
        match goal with |- exec (Defs.bind0 ?A _) s0 = _ =>
          assert (HAbody : exec A s0 = Some (tt, s0)) end.
        { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match. apply exec_returnm. }
        unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody). apply exec_returnm. }
      iModIntro. iExists s0.
      iSplit; [ iPureIntro; exact Hexec | ].
      iSplit; [ iPureIntro; reflexivity | ].
      iSplit; [ iPureIntro; left; reflexivity | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End ZicbopExec.

Lemma arm_ZICBOP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (p : cbop_zicbop * regidx * bits 12) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode w) sigma_f = Some (ZICBOP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[cbop rs1] offset]. destruct rs1 as [rs1].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hmsok0 as (HSXL0 & HMPRV0 & HMXR0 & _ & _).
  iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
  iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
  iMod (exec_execute_ZICBOP_u cbop rs1 offset pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) s0
          Lcp0 HMPRV0 HMXR0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 HSXL0 Hpma0 Hwf Hcov
          with "Hreg Hgh Hutlb Hudata")
    as (s_x) "(%Hexec & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
  assert (Hmi : register_lookup (R_bool minstret_increment) s_x.(sregs)
                = register_lookup (R_bool minstret_increment) s0.(sregs)).
  { destruct Hsregs as [-> | (tv & ->)]; [reflexivity | apply irrelevant_register_set; vm_compute; reflexivity]. }
  assert (Hnpc : register_lookup nextPC s_x.(sregs) = register_lookup nextPC s0.(sregs)).
  { destruct Hsregs as [-> | (tv & ->)]; [reflexivity | apply irrelevant_register_set; vm_compute; reflexivity]. }
  iApply (base_finish_mem C pt E sigma sigma_f va w g g
            (ZICBOP (cbop, Regidx rs1, offset)) RETIRE_SUCCESS s_x
            Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpc
            with "[Hreg Hgh Hdev] Hgpr Hnpc [Hutlb Hudata] Hcfg").
  - unfold mstate_interp. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev".
  - iFrame "Hutlb Hudata". iPureIntro; split; assumption.
Qed.
