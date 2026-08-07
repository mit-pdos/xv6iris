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
Require Import UserMemAccess UserMemPt UserMemMis.
Require Import TrampPt KptTree UserTranslate.
Require Import UserTotalU Pt4kWalk.
Require Import RiscvModelBytes CommonWalk WpLoad MemAmo4.
Local Open Scope Z_scope.
Import Defs.

(* A failing tactic at this altitude otherwise prints a goal that takes tens
   of minutes to format -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

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
    vmem_width width ->
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
    intros Hflavor Hvw Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ LSXL with "Hri Hinv") as %Htm.
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
    exact (exec_vmem_read_addr_translate_err width va pc (E_Load_Page_Fault tt)
             (Load Data) false false false User Sv39 User σ σ Hvw Halign
             ltac:(rewrite Lcp; apply exec_effectivePrivilege_mprv0; exact Lmprv)
             Htm Htr Lcp Lpc).
  Qed.

  Lemma user_pt_vmem_write_addr_store_err (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pc : mword 64) (width : Z)
      (data : mword (8 * width)) (σ : mstate) :
    u_fault_flavor (Store Data) tfp um va ->
    vmem_width width ->
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
    intros Hflavor Hvw Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ LSXL with "Hri Hinv") as %Htm.
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
    exact (exec_vmem_write_addr_translate_err width va pc (E_SAMO_Page_Fault tt)
             data (Store Data) false false false User Sv39 User σ σ Hvw Halign
             ltac:(rewrite Lcp; apply exec_effectivePrivilege_mprv0; exact Lmprv)
             Htm Htr Lcp Lpc).
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
  Context (Hkvw : vmem_width k).
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
    - iMod (user_pt_vmem_read_addr_load k Hk Hk8 Hkdvd Huintk Hkvw Hread_plain
              uroot tfp um data w va σ
              Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
              with "Hri Hgh Hinv Hdata")
        as (dvv σ') "(%Hvr & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
      iModIntro. iLeft. iExists dvv, σ'. iFrame "Hri Hgh Hinv Hdata".
      iPureIntro. split; [exact Hvr | split; [exact Hmdev | exact Hsregs]].
    - iDestruct (user_pt_vmem_read_addr_load_err uroot tfp um va pc k σ
                   Hfault Hkvw Hal Lpc Hhtif Hcp HSXL Hmprv Hall with "Hri Hgh Hinv") as %Herr.
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
    - iMod (user_pt_vmem_write_addr_store k Hk Hk8 Hkdvd Huintk Hkvw Hwrite_plain
              uroot tfp um data w va dat σ
              Hum Hok Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall
              with "Hri Hgh Hinv Hdata")
        as (σ') "(%Hvw & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
      iModIntro. iLeft. iExists w, σ'. iFrame "Hri Hgh Hinv Hdata".
      iPureIntro. split; [exact Hvw | split; [exact Hmdev | exact Hsregs]].
    - iDestruct (user_pt_vmem_write_addr_store_err uroot tfp um va pc k dat σ
                   Hfault Hkvw Hal Lpc Hhtif Hcp HSXL Hmprv Hall with "Hri Hgh Hinv") as %Herr.
      iModIntro. iRight. iFrame "Hri Hgh Hinv Hdata". iPureIntro. exact Herr.
  Qed.

End AlignedClassify.

(* the width instances (the names the memory arms consume) *)
Section AlignedClassifyInstances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition user_pt_vmem_read_addr_load_classify_1 :=
    user_pt_vmem_read_addr_load_classify 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) ltac:(unfold vmem_width; lia) exec_read_ram_plain_1.

  Definition user_pt_vmem_write_addr_store_classify_1 :=
    user_pt_vmem_write_addr_store_classify 1 ltac:(lia) ltac:(lia)
      ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity) ltac:(unfold vmem_width; lia) exec_write_ram_plain_1.

End AlignedClassifyInstances.

(* ===================================================================== *)
(* §6 THE MISALIGNED ACCESS, PER PAGE.                                     *)
(*                                                                         *)
(* The bump moved the misaligned split in two directions at once (see       *)
(* UserMemMis.v's header), and the consequence here is that this file no    *)
(* longer folds anything over CHUNKS.  A data access touches ONE page       *)
(* ([in_one_page]) or TWO ([exec_split_on_page_boundary_straddle]), and     *)
(* each page gets exactly one [data_classify] and one translation.  Whether *)
(* the access is aligned no longer enters into it: the platform raises no   *)
(* misalignment exception for plain load/store, so the aligned and the      *)
(* in-page misaligned cases are the SAME peel.                              *)
(* ===================================================================== *)

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

(* [in_one_page] is decidable, and that is the case split the whole misaligned
   pipeline turns on. *)
Lemma in_one_page_dec (va : mword 64) (W : Z) :
  {in_one_page va W} + {~ in_one_page va W}.
Proof. unfold in_one_page. apply Z_le_dec. Qed.

Section MisPageComposers.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the two facts a page's translation supplies, at any width the vmem level
     can hand a page: it lands, or it faults with a delegated User page fault *)
  Lemma u_translate_ok (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (data : gset Arch.pa) (w va : mword 64) (W : Z) (σ : mstate) :
    0 < W -> W <= 8 ->
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    in_one_page va W ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    cfg_okR σ ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (dv : mword (8 * W)) (σ' : mstate),
      ⌜exec (translate_and_read_value (Virtaddr va) W (Load Data) false false false) σ
        = Some (Ok (Physaddr (u_walk_pa w va), dv), σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros HW HW8 Hl Hchk Hcov Hp Hcanon Hcfg.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & Hmprv & Hall).
    iIntros "Hri Hgh Hinv Hdata".
    iMod (user_pt_load_data_mis uroot tfp um data w va W σ HW HW8 Hl Hchk Hcov Hp
            Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall with "Hri Hgh Hinv Hdata")
      as (dv σ') "(%Htr & %Hmr & %Hmdev & %Hsregs & Hri & Hgh & Hinv & Hdata)".
    iModIntro. iExists dv, σ'. iFrame "Hri Hgh Hinv Hdata". iPureIntro.
    split; [ exact (exec_translate_and_read_value_g W va (u_walk_pa w va) PBMT_PMA
                      dv σ σ' σ' Htr Hmr) | ].
    split; [ exact Hmdev | exact Hsregs ].
  Qed.

  Lemma u_translate_fault (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (acc : MemoryAccessType mem_payload) (e : ExceptionType)
      (va pc : mword 64) (W : Z) (σ : mstate) :
    (acc = Load Data /\ e = E_Load_Page_Fault tt) \/
    (acc = Store Data /\ e = E_SAMO_Page_Fault tt) ->
    u_fault_flavor acc tfp um va ->
    cfg_okR σ -> register_lookup PC σ.(sregs) = pc ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) acc) σ = Some (Err (e, tt), σ) /\
     exec (memory_exception (Virtaddr va) e) σ
       = Some (Trap (User, make_sync_exception e va, pc), σ)⌝.
  Proof.
    intros Hacc Hflavor Hcfg Lpc.
    pose proof Hcfg as (Hmisa & Hmenv & Hhtif & Hcp & HSXL & Hmprv & Hall).
    iIntros "Hri Hgh Hinv".
    destruct Hacc as [ [Ha He] | [Ha He] ]; subst acc; subst e.
    - iDestruct (utlb_inv_pt_translateAddr_u_fault (Load Data) uroot tfp um va
                   (E_Load_Page_Fault tt) σ Hflavor Hhtif Hcp HSXL
                   (exec_effectivePrivilege_mprv0 (Load Data)
                      (register_lookup mstatus σ.(sregs)) User σ Hmprv)
                   (exec_is_shadow_stack_u_acc (Load Data) σ
                      (or_intror (or_introl eq_refl))) Hall
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   with "Hri Hgh Hinv") as %Htr.
      iPureIntro. split; [ exact Htr | ].
      exact (exec_memory_exception va pc (E_Load_Page_Fault tt) User σ Hcp Lpc).
    - iDestruct (utlb_inv_pt_translateAddr_u_fault (Store Data) uroot tfp um va
                   (E_SAMO_Page_Fault tt) σ Hflavor Hhtif Hcp HSXL
                   (exec_effectivePrivilege_mprv0 (Store Data)
                      (register_lookup mstatus σ.(sregs)) User σ Hmprv)
                   (exec_is_shadow_stack_u_acc (Store Data) σ
                      (or_intror (or_intror (or_introl eq_refl)))) Hall
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   ltac:(unfold translationException; cbn match; apply exec_returnm)
                   with "Hri Hgh Hinv") as %Htr.
      iPureIntro. split; [ exact Htr | ].
      exact (exec_memory_exception va pc (E_SAMO_Page_Fault tt) User σ Hcp Lpc).
  Qed.

End MisPageComposers.


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
    - rewrite Hmi. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity].
    - rewrite Hnpc. rewrite ?sregs_set_reg. apply register_lookup_set.
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
    iDestruct (utlb_inv_pt_tmode uroot tfp um s HSXL with "Hreg Hutlb") as %Htm.
    assert (Heff : exec (effectivePrivilege (Load Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s))
      by (rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact HMPRV).
    assert (Hpm : plat_misaligned_exception (Load Data) false = None)
      by (apply plat_misaligned_loadstore_none; reflexivity).
    destruct (in_one_page_dec va k) as [Hin | Hout].
    - (* ONE PAGE: one classify, one translation, whatever the alignment *)
      destruct (data_classify (Load Data) tfp um va (or_intror (or_introl eq_refl)) Hwf)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + iMod (u_translate_ok uroot tfp um data w va k s Hk Hk8 Hum Hok Hcov Hin Hcanon Hcfg
                with "Hreg Hgh Hutlb Hudata")
          as (dv σ') "(%Htrv & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        iModIntro. iLeft. iExists dv, σ'. iFrame. iPureIntro.
        split.
        { exact (exec_vmem_read_addr_intra k va (u_walk_pa w va) dv (Load Data)
                   false false false User Sv39 s σ' Hk
                   (exec_split_on_page_boundary_intra va k s Hk Hin)
                   (or_intror Hpm) Heff Htm Htrv ltac:(discriminate)). }
        split; [ exact Hmdev |].
        split; [ apply Tr; vm_compute; reflexivity | apply Tr; vm_compute; reflexivity ].
      + iDestruct (u_translate_fault uroot tfp um (Load Data) (E_Load_Page_Fault tt) va pc k s
                     (or_introl (conj eq_refl eq_refl)) Hfault Hcfg Lpc
                     with "Hreg Hgh Hutlb") as %(Htr & Hme).
        iModIntro. iRight. iExists s, (E_Load_Page_Fault tt), va, pc.
        iFrame. iPureIntro.
        split.
        { exact (exec_vmem_read_addr_intra_err k va
                   (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc))
                   (Load Data) false false false User Sv39 s s Hk
                   (exec_split_on_page_boundary_intra va k s Hk Hin)
                   (or_intror Hpm) Heff Htm
                   (exec_translate_and_read_value_err k va (Load Data) false false false
                      (E_Load_Page_Fault tt) _ s s Htr Hme)). }
        split; [ vm_compute; reflexivity |].
        split; [ reflexivity |]. split; [ reflexivity | reflexivity ].
    - (* TWO PAGES: the access ends one page and starts the next *)
      destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp0 & Hq0 & Hp8 & Hq8).
      pose proof (exec_split_on_page_boundary_straddle va k s Hk Hk8 Hout) as Hsp.
      set (pp := 4096 - bv_unsigned va mod 4096) in *.
      set (qq := k - pp) in *.
      set (vb := add_vec_int va pp).
      destruct (data_classify (Load Data) tfp um va (or_intror (or_introl eq_refl)) Hwf)
        as [ (w1 & Hum1 & Hok1 & Hcanon1) | Hf1 ].
      + (* the first page lands; classify the second *)
        iMod (u_translate_ok uroot tfp um data w1 va pp s Hp0 Hp8 Hum1 Hok1 Hcov
                (straddle_part1_in_page va k) Hcanon1 Hcfg with "Hreg Hgh Hutlb Hudata")
          as (dv1 σ1) "(%Htrv1 & %Hmdev1 & %Hsregs1 & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr1 : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ1.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs1 as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        pose proof (cfg_okR_pres s σ1 Hsregs1 Hcfg) as Hcfg1.
        pose proof Hcfg1 as (Hmisa1 & Hmenv1 & Hhtif1 & Hcp1 & HSXL1 & HMPRV1 & Hpma1).
        destruct (data_classify (Load Data) tfp um vb (or_intror (or_introl eq_refl)) Hwf)
          as [ (w2 & Hum2 & Hok2 & Hcanon2) | Hf2 ].
        * iMod (u_translate_ok uroot tfp um data w2 vb qq σ1 Hq0 Hq8 Hum2 Hok2 Hcov
                  (straddle_part2_in_page va k Hk Hk8 Hout) Hcanon2 Hcfg1
                  with "Hreg Hgh Hutlb Hudata")
            as (dv2 σ2) "(%Htrv2 & %Hmdev2 & %Hsregs2 & Hreg & Hgh & Hutlb & Hudata)".
          assert (Tr2 : forall r : register, register_beq r tlb = false ->
                    register_lookup r σ2.(sregs) = register_lookup r σ1.(sregs)).
          { intros r Hne. destruct Hsregs2 as [He | (tv & He)]; rewrite He;
              [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
          destruct (exec_vmem_read_addr_split2 k pp qq va (u_walk_pa w1 va) (u_walk_pa w2 vb)
                      dv1 dv2 (Load Data) false false User Sv39 s σ1 σ2
                      Hp0 Hq0 Hsp Hpm Heff Htm ltac:(vm_compute; reflexivity) Htrv1 Htrv2)
            as (dvv & Hvr).
          iModIntro. iLeft. iExists dvv, σ2. iFrame. iPureIntro.
          split; [ exact Hvr |]. split; [ rewrite Hmdev2; exact Hmdev1 |].
          split; [ rewrite (Tr2 (R_bool minstret_increment) ltac:(vm_compute; reflexivity));
                   apply Tr1; vm_compute; reflexivity
                 | rewrite (Tr2 nextPC ltac:(vm_compute; reflexivity));
                   apply Tr1; vm_compute; reflexivity ].
        * (* the second page faults *)
          set (pc1 := register_lookup PC σ1.(sregs)).
          iDestruct (u_translate_fault uroot tfp um (Load Data) (E_Load_Page_Fault tt) vb pc1 qq σ1
                       (or_introl (conj eq_refl eq_refl)) Hf2 Hcfg1 eq_refl
                       with "Hreg Hgh Hutlb") as %(Htr2 & Hme2).
          iDestruct (utlb_inv_pt_tmode uroot tfp um σ1 HSXL1 with "Hreg Hutlb") as %Htm1.
          iModIntro. iRight.
          iExists σ1, (E_Load_Page_Fault tt), vb, pc1.
          iFrame. iPureIntro.
          split.
          { exact (exec_vmem_read_addr_split2_err2 k pp qq va (u_walk_pa w1 va) dv1
                     (Trap (User, make_sync_exception (E_Load_Page_Fault tt) vb, pc1))
                     (Load Data) false false User Sv39 s σ1 σ1
                     Hp0 Hq0 Hsp Hpm Heff Htm ltac:(vm_compute; reflexivity) Htrv1
                     (exec_translate_and_read_value_err qq vb (Load Data) false false false
                        (E_Load_Page_Fault tt) _ σ1 σ1 Htr2 Hme2)). }
          split; [ vm_compute; reflexivity |]. split; [ exact Hmdev1 |].
          split; [ apply Tr1; vm_compute; reflexivity | apply Tr1; vm_compute; reflexivity ].
      + (* the FIRST page faults *)
        iDestruct (u_translate_fault uroot tfp um (Load Data) (E_Load_Page_Fault tt) va pc pp s
                     (or_introl (conj eq_refl eq_refl)) Hf1 Hcfg Lpc
                     with "Hreg Hgh Hutlb") as %(Htr1 & Hme1).
        iModIntro. iRight. iExists s, (E_Load_Page_Fault tt), va, pc.
        iFrame. iPureIntro.
        split.
        { exact (exec_vmem_read_addr_split2_err1 k pp qq va
                   (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc))
                   (Load Data) false false User Sv39 s s
                   Hp0 Hq0 Hsp Hpm Heff Htm ltac:(vm_compute; reflexivity)
                   (exec_translate_and_read_value_err pp va (Load Data) false false false
                      (E_Load_Page_Fault tt) _ s s Htr1 Hme1)). }
        split; [ vm_compute; reflexivity |].
        split; [ reflexivity |]. split; [ reflexivity | reflexivity ].
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
      { intros r Hne. unfold s_x; rewrite ?sregs_set_reg. apply irrelevant_register_set; exact Hne. }
      iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
      iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
      unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
      { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
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
      { iPureIntro. unfold s_x; rewrite ?sregs_set_reg.
        rewrite (irrelevant_register_set (R_bool minstret_increment) (R_bitvector_64 (gpr_of_Z (uint rd)))).
        2:{ reg_ne. }
        apply Tr. vm_compute; reflexivity. }
      iSplitR.
      { iPureIntro. unfold s_x; rewrite ?sregs_set_reg.
        rewrite (irrelevant_register_set nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))).
        2:{ reg_ne. }
        apply Tr. vm_compute; reflexivity. }
      unfold mstate_interp.
      iSplitL "Hreg Hgh Hdev".
      { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh".
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
    iDestruct (utlb_inv_pt_tmode uroot tfp um s HSXL with "Hreg Hutlb") as %Htm.
    assert (Heff : exec (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s))
      by (rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact HMPRV).
    assert (Hpm : plat_misaligned_exception (Store Data) false = None)
      by (apply plat_misaligned_loadstore_none; reflexivity).
    destruct (in_one_page_dec va k) as [Hin | Hout].
    - (* ONE PAGE *)
      destruct (data_classify (Store Data) tfp um va
                  (or_intror (or_intror (or_introl eq_refl))) Hwf)
        as [ (w & Hum & Hok & Hcanon) | Hfault ].
      + iMod (user_pt_store_data_mis uroot tfp um data w va k dat s Hk Hk8 Hum Hok Hcov Hin
                Hcanon Hmisa Hmenv Hhtif Hcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb Hudata")
          as (σ' σ'') "(%Htr & %Hea & %Hwv & %Hs2 & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ'.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        iModIntro. iLeft. iExists σ''. iFrame. iPureIntro.
        split.
        { apply (exec_vmem_write_addr_intra k va (u_walk_pa w va) dat User Sv39 s σ' σ'' Hk
                   (exec_split_on_page_boundary_intra va k s Hk Hin)
                   (or_intror Hpm) Heff Htm Htr Hea).
          rewrite (subrange_full_gen_cast (8 * k) dat ltac:(lia)). exact Hwv. }
        split; [ exact Hmdev |].
        split; [ rewrite Hs2; apply Tr; vm_compute; reflexivity
               | rewrite Hs2; apply Tr; vm_compute; reflexivity ].
      + iDestruct (u_translate_fault uroot tfp um (Store Data) (E_SAMO_Page_Fault tt) va pc k s
                     (or_intror (conj eq_refl eq_refl)) Hfault Hcfg Lpc
                     with "Hreg Hgh Hutlb") as %(Htr & Hme).
        iModIntro. iRight. iExists s, (E_SAMO_Page_Fault tt), va, pc.
        iFrame. iPureIntro.
        split.
        { exact (exec_vmem_write_addr_intra_terr k va dat (Store Data) false false false
                   (E_SAMO_Page_Fault tt)
                   (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc))
                   User Sv39 s s Hk
                   (exec_split_on_page_boundary_intra va k s Hk Hin)
                   (or_intror Hpm) Heff Htm Htr Hme). }
        split; [ vm_compute; reflexivity |].
        split; [ reflexivity |]. split; [ reflexivity | reflexivity ].
    - (* TWO PAGES *)
      destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp0 & Hq0 & Hp8 & Hq8).
      pose proof (exec_split_on_page_boundary_straddle va k s Hk Hk8 Hout) as Hsp.
      set (pp := 4096 - bv_unsigned va mod 4096) in *.
      set (qq := k - pp) in *.
      set (vb := add_vec_int va pp).
      set (d1 := autocast (T := mword) (subrange_vec_dec dat (8 * pp - 1) 0) : mword (8 * pp)).
      set (d2 := autocast (T := mword) (subrange_vec_dec dat (8 * k - 1) (8 * pp)) : mword (8 * qq)).
      destruct (data_classify (Store Data) tfp um va
                  (or_intror (or_intror (or_introl eq_refl))) Hwf)
        as [ (w1 & Hum1 & Hok1 & Hcanon1) | Hf1 ].
      + iMod (user_pt_store_data_mis uroot tfp um data w1 va pp d1 s Hp0 Hp8 Hum1 Hok1 Hcov
                (straddle_part1_in_page va k) Hcanon1 Hmisa Hmenv Hhtif Hcp HSXL HMPRV Hpma
                with "Hreg Hgh Hutlb Hudata")
          as (σ1 σ1') "(%Htr1 & %Hea1 & %Hwv1 & %Hs1' & %Hmdev1 & %Hsregs1 & Hreg & Hgh & Hutlb & Hudata)".
        assert (Tr1 : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ1.(sregs) = register_lookup r s.(sregs)).
        { intros r Hne. destruct Hsregs1 as [He | (tv & He)]; rewrite He;
            [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
        assert (Hsregs1' : (σ1'.(sregs) = s.(sregs) \/
                  exists tv, σ1'.(sregs) = register_set tlb tv s.(sregs))%type)
          by (rewrite Hs1'; exact Hsregs1).
        pose proof (cfg_okR_pres s σ1' Hsregs1' Hcfg) as Hcfg1.
        pose proof Hcfg1 as (Hmisa1 & Hmenv1 & Hhtif1 & Hcp1 & HSXL1 & HMPRV1 & Hpma1).
        assert (Tr1' : forall r : register, register_beq r tlb = false ->
                  register_lookup r σ1'.(sregs) = register_lookup r s.(sregs))
          by (intros r Hne; rewrite Hs1'; apply Tr1; exact Hne).
        destruct (data_classify (Store Data) tfp um vb
                    (or_intror (or_intror (or_introl eq_refl))) Hwf)
          as [ (w2 & Hum2 & Hok2 & Hcanon2) | Hf2 ].
        * iMod (user_pt_store_data_mis uroot tfp um data w2 vb qq d2 σ1' Hq0 Hq8 Hum2 Hok2 Hcov
                  (straddle_part2_in_page va k Hk Hk8 Hout) Hcanon2
                  Hmisa1 Hmenv1 Hhtif1 Hcp1 HSXL1 HMPRV1 Hpma1
                  with "Hreg Hgh Hutlb Hudata")
            as (σ2 σ2') "(%Htr2 & %Hea2 & %Hwv2 & %Hs2' & %Hmdev2 & %Hsregs2 & Hreg & Hgh & Hutlb & Hudata)".
          assert (Tr2 : forall r : register, register_beq r tlb = false ->
                    register_lookup r σ2.(sregs) = register_lookup r σ1'.(sregs)).
          { intros r Hne. destruct Hsregs2 as [He | (tv & He)]; rewrite He;
              [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
          iModIntro. iLeft. iExists σ2'. iFrame. iPureIntro.
          split.
          { exact (exec_vmem_write_addr_split2 k pp qq va (u_walk_pa w1 va) dat
                     User Sv39 s σ1 σ1' σ2' (conj Hp0 Hq0) Hsp Hpm Heff Htm
                     ltac:(vm_compute; reflexivity) true Htr1 Hea1 Hwv1
                     (exec_translate_and_write_value_gen qq vb (u_walk_pa w2 vb) d2
                        (Store Data) false false false PBMT_PMA true σ1' σ2 σ2'
                        Htr2 Hea2 Hwv2)). }
          split; [ rewrite Hmdev2; exact Hmdev1 |].
          split; [ rewrite Hs2'; rewrite (Tr2 (R_bool minstret_increment) ltac:(vm_compute; reflexivity));
                   apply Tr1'; vm_compute; reflexivity
                 | rewrite Hs2'; rewrite (Tr2 nextPC ltac:(vm_compute; reflexivity));
                   apply Tr1'; vm_compute; reflexivity ].
        * set (pc1 := register_lookup PC σ1'.(sregs)).
          iDestruct (u_translate_fault uroot tfp um (Store Data) (E_SAMO_Page_Fault tt) vb pc1 qq σ1'
                       (or_intror (conj eq_refl eq_refl)) Hf2 Hcfg1 eq_refl
                       with "Hreg Hgh Hutlb") as %(Htr2 & Hme2).
          iModIntro. iRight.
          iExists σ1', (E_SAMO_Page_Fault tt), vb, pc1.
          iFrame. iPureIntro.
          split.
          { exact (exec_vmem_write_addr_split2_err2 k pp qq va (u_walk_pa w1 va) dat
                     User Sv39 s σ1 σ1' σ1' (conj Hp0 Hq0) Hsp Hpm Heff Htm
                     ltac:(vm_compute; reflexivity)
                     (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) vb, pc1))
                     Htr1 Hea1 Hwv1
                     (exec_translate_and_write_value_err qq vb d2 (Store Data) false false false
                        (E_SAMO_Page_Fault tt) _ σ1' σ1' Htr2 Hme2)). }
          split; [ vm_compute; reflexivity |].
          split; [ exact Hmdev1 |].
          split; [ apply Tr1'; vm_compute; reflexivity | apply Tr1'; vm_compute; reflexivity ].
      + iDestruct (u_translate_fault uroot tfp um (Store Data) (E_SAMO_Page_Fault tt) va pc pp s
                     (or_intror (conj eq_refl eq_refl)) Hf1 Hcfg Lpc
                     with "Hreg Hgh Hutlb") as %(Htr1 & Hme1).
        iModIntro. iRight. iExists s, (E_SAMO_Page_Fault tt), va, pc.
        iFrame. iPureIntro.
        split.
        { exact (exec_vmem_write_addr_split2_err1 k pp qq va dat
                   User Sv39 s s (conj Hp0 Hq0) Hsp Hpm Heff Htm
                   ltac:(vm_compute; reflexivity)
                   (E_SAMO_Page_Fault tt)
                   (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc))
                   Htr1 Hme1). }
        split; [ vm_compute; reflexivity |].
        split; [ reflexivity |]. split; [ reflexivity | reflexivity ].
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
    - rewrite Hmi. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Lmi | vm_compute; reflexivity].
    - rewrite Hnpc. rewrite ?sregs_set_reg. apply register_lookup_set.
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
  exec (checked_mem_read (LoadReserved (aq, rl, Data)) pbmt User (Physaddr addr) 4
          aq (andb aq rl) true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta)
             else Err (Physaddr addr, E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr.
  - (* the region is reservable: the LR retires *)
    assert (Hcp : exec (check_pma_with_pmp_priority (LoadReserved (aq, rl, Data)) pbmt User
                          (Physaddr addr) 4 true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_lr_ok 4 addr pbmt region aq rl s Hmatch Halign
                    ltac:(rewrite Hread; rewrite Hr; reflexivity))).
      cbn match. apply exec_returnM. }
    assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                    (rk = rv64d_types.Read_RISCV_reserved \/
                     rk = rv64d_types.Read_RISCV_reserved_acquire \/
                     rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
    { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hrk as (rk & Hrke & Hrkv).
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 4) = addr)
        by (change (0 * 4)%Z with 0%Z; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_lr aq rl addr 4 s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
        assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
        assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                      = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_read_ram_resv_kinds_4 rk addr w s Hrkv Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
      rewrite autocast_id. rewrite usvd_zeros_full_32.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite autocast_id. rewrite execR_returnR. reflexivity.
  - (* the region is not reservable: pmaCheck denies, pmpCheck grants, so the
       PMA exception is the one that survives the priority rule *)
    assert (Hcp : exec (check_pma_with_pmp_priority (LoadReserved (aq, rl, Data)) pbmt User
                          (Physaddr addr) 4 true) s
                  = Some (Err (E_Load_Access_Fault tt), s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_lr_deny 4 addr pbmt region aq rl s Hmatch
                    ltac:(rewrite Hread; rewrite Hr; reflexivity))).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_lr aq rl addr 4 s HA Hord Hrange HR)).
      cbn match. apply exec_returnM. }
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_early_ret. cbn match. reflexivity.
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
  exec (checked_mem_read (LoadReserved (aq, rl, Data)) pbmt User (Physaddr addr) 8
          aq (andb aq rl) true false) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok (w, default_meta)
             else Err (Physaddr addr, E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr.
  - (* the region is reservable: the LR retires *)
    assert (Hcp : exec (check_pma_with_pmp_priority (LoadReserved (aq, rl, Data)) pbmt User
                          (Physaddr addr) 8 true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_lr_ok 8 addr pbmt region aq rl s Hmatch Halign
                    ltac:(rewrite Hread; rewrite Hr; reflexivity))).
      cbn match. apply exec_returnM. }
    assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                    (rk = rv64d_types.Read_RISCV_reserved \/
                     rk = rv64d_types.Read_RISCV_reserved_acquire \/
                     rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
    { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hrk as (rk & Hrke & Hrkv).
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 8) = addr)
        by (change (0 * 8)%Z with 0%Z; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_lr aq rl addr 8 s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
        assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
        assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                      = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_read_ram_resv_kinds_8 rk addr w s Hrkv Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
      rewrite autocast_id. rewrite usvd_zeros_full_64.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite autocast_id. rewrite execR_returnR. reflexivity.
  - (* the region is not reservable: pmaCheck denies, pmpCheck grants, so the
       PMA exception is the one that survives the priority rule *)
    assert (Hcp : exec (check_pma_with_pmp_priority (LoadReserved (aq, rl, Data)) pbmt User
                          (Physaddr addr) 8 true) s
                  = Some (Err (E_Load_Access_Fault tt), s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_lr_deny 8 addr pbmt region aq rl s Hmatch
                    ltac:(rewrite Hread; rewrite Hr; reflexivity))).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_lr aq rl addr 8 s HA Hord Hrange HR)).
      cbn match. apply exec_returnM. }
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_early_ret. cbn match. reflexivity.
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
  exec (mem_read (LoadReserved (aq, rl, Data)) pbmt (Physaddr addr) 4 aq (andb aq rl) true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (Physaddr addr, E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data)) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_g4 aq rl pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved (aq, rl, Data)) pbmt User (Physaddr addr) 4 aq (andb aq rl) true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (Physaddr addr, E_Load_Access_Fault tt)), s)).
  (* [mem_read_priv_meta] no longer guards on alignment: it only dispatches on
     the (aq, rl, res) triple, and none of the three the LR flags can form is
     one of the two unimplemented ones. *)
  { unfold mem_read_priv_meta.
    destruct aq; [ destruct rl |]; cbn match;
      (rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
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
  exec (mem_read (LoadReserved (aq, rl, Data)) pbmt (Physaddr addr) 8 aq (andb aq rl) true) s
    = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
             then Ok w else Err (Physaddr addr, E_Load_Access_Fault tt)), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data)) _ _ s Hmprv)).
  rewrite Hpriv. unfold mem_read_priv.
  assert (Hcmr := exec_checked_mem_read_lr_g8 aq rl pbmt addr region w s HA Hord Hrange HR Hmatch Halign Hread Hmmio Hdev Hbytes).
  assert (Hmrpm : exec (mem_read_priv_meta (LoadReserved (aq, rl, Data)) pbmt User (Physaddr addr) 8 aq (andb aq rl) true false) s
                 = Some ((if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
                          then Ok (w, default_meta) else Err (Physaddr addr, E_Load_Access_Fault tt)), s)).
  (* [mem_read_priv_meta] no longer guards on alignment: it only dispatches on
     the (aq, rl, res) triple, and none of the three the LR flags can form is
     one of the two unimplemented ones. *)
  { unfold mem_read_priv_meta.
    destruct aq; [ destruct rl |]; cbn match;
      (rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
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
    uleaf_ok (LoadReserved (aq, rl, Data)) w ->
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
          exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 4 (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) σ
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
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved (aq, rl, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved (aq, rl, Data)) σ
               (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))) Hall
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
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4
                  (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
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
    destruct (exec_vmem_read_addr_lr_disj 4 va pa (register_lookup PC σ'.(sregs)) dv
                aq rl aq (andb aq rl) User Sv39 User
                (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ'
                ltac:(unfold vmem_width; lia)
                Hal
                (ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv))
                Htm Htr Hmr
                (offset_virtaddr_by_self va pa)
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
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt. exact Hflt. }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

  Lemma user_pt_vmem_read_addr_lr_g8 (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (LoadReserved (aq, rl, Data)) w ->
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
          exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) σ
            = Some (Ok dvv, σ'))
       \/ exec (vmem_read_addr (Virtaddr va) 8 (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) σ
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
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (utlb_inv_pt_translateAddr_u (LoadReserved (aq, rl, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (LoadReserved (aq, rl, Data)) σ
               (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))) Hall
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
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8
                  (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
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
    destruct (exec_vmem_read_addr_lr_disj 8 va pa (register_lookup PC σ'.(sregs)) dv
                aq rl aq (andb aq rl) User Sv39 User
                (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) RsrvNone)
                σ σ'
                ltac:(unfold vmem_width; lia)
                Hal
                (ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv))
                Htm Htr Hmr
                (offset_virtaddr_by_self va pa)
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
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt. exact Hflt. }
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
    u_fault_flavor (LoadReserved (aq, rl, Data)) tfp um va ->
    vmem_width width ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_read_addr (Virtaddr va) width (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) σ
      = Some (Err (Trap (User, make_sync_exception (E_Load_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Hvw Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ LSXL with "Hri Hinv") as %Htm.
    iDestruct (utlb_inv_pt_translateAddr_u_fault (LoadReserved (aq, rl, Data)) uroot tfp um va
                 (E_Load_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (LoadReserved (aq, rl, Data)) σ
                    (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    (* [Htr] is at the BARE vaddr now -- the vmem level's split offset is gone *)
    exact (exec_vmem_read_addr_translate_err width va pc (E_Load_Page_Fault tt)
             (LoadReserved (aq, rl, Data)) aq (andb aq rl) true User Sv39 User σ σ
             Hvw Halign
             (ltac:(rewrite Lcp; apply exec_effectivePrivilege_mprv0; exact Lmprv))
             Htm Htr Lcp Lpc).
  Qed.

End LRFaultComposer.

(* ---- Part E: LOADRES rd=0 execute ---- *)
Lemma exec_execute_LOADRES_u_ok_rd0 (aq rl : bool) (rs1 rd : mword 5) (width : Z)
    (data : mword (8 * width)) (s s' : mstate) :
  (width <=? xlen_bytes) = true ->
  uint rd = 0 ->
  exec (vmem_read (Regidx rs1) (zeros' 64) width (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) s
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
          uleaf_ok (LoadReserved (aq0, rl0, Data)) w0 ->
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
                exec (vmem_read_addr (Virtaddr va0) k (LoadReserved (aq0, rl0, Data)) aq0 (andb aq0 rl0) true) σ0
                  = Some (Ok dvv, σ0'))
             \/ exec (vmem_read_addr (Virtaddr va0) k (LoadReserved (aq0, rl0, Data)) aq0 (andb aq0 rl0) true) σ0
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
        ⌜exec (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) s = Some (Ok dvv, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_read_addr (Virtaddr va) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) s
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
    - destruct (data_classify (LoadReserved (aq, rl, Data)) tfp um va
                  (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))) Hwf)
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
                     Hfault ltac:(destruct HkW as [Hkv|Hkv]; rewrite Hkv; unfold vmem_width; tauto)
                     Hal Lpc Hhtif Hcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Herr.
        iModIntro. iRight. iExists s, (E_Load_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - iModIntro. iRight. iExists s, (E_Load_Access_Fault tt), va, pc.
      iFrame. iPureIntro.
      split; [ exact (exec_vmem_read_addr_misaligned_lr va pc k aq rl aq (andb aq rl) User s Hal Hcp Lpc) |].
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
          uleaf_ok (LoadReserved (aq0, rl0, Data)) w0 ->
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
                exec (vmem_read_addr (Virtaddr va0) k (LoadReserved (aq0, rl0, Data)) aq0 (andb aq0 rl0) true) σ0
                  = Some (Ok dvv, σ0'))
             \/ exec (vmem_read_addr (Virtaddr va0) k (LoadReserved (aq0, rl0, Data)) aq0 (andb aq0 rl0) true) σ0
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
    assert (Hpml : exec (get_pmlen (LoadReserved (aq, rl, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption;
        (destruct aq; destruct rl; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
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
      assert (Hvread : exec (vmem_read (Regidx rs1) (zeros' 64) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) s = Some (Ok dvv, sig')).
      { apply (exec_vmem_read_u rs1 (zeros' 64) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Ok dvv) s sig' Lcp Heff Hpml Htm).
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
        { intros r Hne. unfold s_x; rewrite ?sregs_set_reg. apply irrelevant_register_set; exact Hne. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
        { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvread : exec (vmem_read (Regidx rs1) (zeros' 64) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_read_u rs1 (zeros' 64) k (LoadReserved (aq, rl, Data)) aq (andb aq rl) true Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
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
Lemma exec_mem_write_ea_sc_g (aq rl : bool) (width : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
          RsrvNone) = true ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_ea (Physaddr addr) width (StoreConditional (aq, rl, Data)) pbmt
          (andb aq rl) rl true) s = Some (Ok tt, s).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hfield Hmprv Hpriv.
  assert (Heff : exec (effectivePrivilege (StoreConditional (aq, rl, Data))
                         (register_lookup mstatus s.(sregs))
                         (register_lookup cur_privilege s.(sregs))) s = Some (User, s))
    by (rewrite Hpriv; apply exec_effectivePrivilege_mprv0; exact Hmprv).
  assert (Hcp : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data)) pbmt User
                        (Physaddr addr) width true) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_sc_ok width addr pbmt region aq rl s Hmatch Halign Hfield)).
    cbn match. apply exec_returnM. }
  assert (Hwkf : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s)).
  { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
      eexists; apply exec_returnM. }
  destruct Hwkf as (wk & Hwke).
  unfold mem_write_ea. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwke). cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * width) = addr)
      by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_user_grant_sc aq rl addr width s HA Hord Hrange HW)).
    cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. reflexivity.
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
  exec (checked_mem_write (Physaddr addr) 4 data (StoreConditional (aq, rl, Data)) pbmt User tt
          (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (Physaddr addr, E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr.
  - assert (Hcp : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data)) pbmt User
                          (Physaddr addr) 4 true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_sc_ok 4 addr pbmt region aq rl s Hmatch Halign
                    ltac:(rewrite Hwrite; rewrite Hr; reflexivity))).
      cbn match. apply exec_returnM. }
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/
                     wk = rv64d_types.Write_RISCV_conditional_release \/
                     wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 4) = addr)
        by (change (0 * 4)%Z with 0%Z; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_sc aq rl addr 4 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * 4 - 1) (8 * 0 * 4))
              : mword (8 * 4))
        with (autocast (T := mword) (subrange_vec_dec data (8 * 4 - 1) 0)
              : mword (8 * 4)).
      rewrite (subrange_full_gen_cast (8 * 4) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_write_ram_cond_kinds_4 wk addr data s Hwkv Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  - assert (Hcp : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data)) pbmt User
                          (Physaddr addr) 4 true) s
                  = Some (Err (E_SAMO_Access_Fault tt), s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_sc_deny 4 addr pbmt region aq rl s Hmatch
                    ltac:(rewrite Hwrite; rewrite Hr; reflexivity))).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_sc aq rl addr 4 s HA Hord Hrange HW)).
      cbn match. apply exec_returnM. }
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_early_ret. cbn match. reflexivity.
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
  exec (checked_mem_write (Physaddr addr) 8 data (StoreConditional (aq, rl, Data)) pbmt User tt
          (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (Physaddr addr, E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev.
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr.
  - assert (Hcp : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data)) pbmt User
                          (Physaddr addr) 8 true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_sc_ok 8 addr pbmt region aq rl s Hmatch Halign
                    ltac:(rewrite Hwrite; rewrite Hr; reflexivity))).
      cbn match. apply exec_returnM. }
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/
                     wk = rv64d_types.Write_RISCV_conditional_release \/
                     wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * 8) = addr)
        by (change (0 * 8)%Z with 0%Z; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_sc aq rl addr 8 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * 8 - 1) (8 * 0 * 8))
              : mword (8 * 8))
        with (autocast (T := mword) (subrange_vec_dec data (8 * 8 - 1) 0)
              : mword (8 * 8)).
      rewrite (subrange_full_gen_cast (8 * 8) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_write_ram_cond_kinds_8 wk addr data s Hwkv Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  - assert (Hcp : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data)) pbmt User
                          (Physaddr addr) 8 true) s
                  = Some (Err (E_SAMO_Access_Fault tt), s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_sc_deny 8 addr pbmt region aq rl s Hmatch
                    ltac:(rewrite Hwrite; rewrite Hr; reflexivity))).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_sc aq rl addr 8 s HA Hord Hrange HW)).
      cbn match. apply exec_returnM. }
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_early_ret. cbn match. reflexivity.
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
  exec (mem_write_value (Physaddr addr) 4 data (StoreConditional (aq, rl, Data)) pbmt
          (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev))
            else (Err (Physaddr addr, E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data)) _ _ s Hmprv)).
  rewrite Hpriv.
  (* [mem_write_value_priv_meta] no longer guards on anything: it is the
     [checked_mem_write] and the callback. *)
  unfold mem_write_value_priv_meta.
  assert (Hcmw := exec_checked_mem_write_sc_g4 aq rl pbmt addr region data s
                    HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr;
    cbn match in Hcmw;
    (rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM).
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
  exec (mem_write_value (Physaddr addr) 8 data (StoreConditional (aq, rl, Data)) pbmt
          (andb aq rl) rl true) s
    = Some (if generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability) RsrvNone
            then (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev))
            else (Err (Physaddr addr, E_SAMO_Access_Fault tt), s)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _
             (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data)) _ _ s Hmprv)).
  rewrite Hpriv.
  (* [mem_write_value_priv_meta] no longer guards on anything: it is the
     [checked_mem_write] and the callback. *)
  unfold mem_write_value_priv_meta.
  assert (Hcmw := exec_checked_mem_write_sc_g8 aq rl pbmt addr region data s
                    HA Hord Hrange HW Hmatch Halign Hwrite Hmmio Hdev).
  destruct (generic_neq (override_PMA (PMA_Region_attributes region) pbmt).(PMA_reservability)
              RsrvNone) eqn:Hr;
    cbn match in Hcmw;
    (rewrite (exec_bind_Some _ _ _ _ _ Hcmw); cbn match; apply exec_returnM).
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
    uleaf_ok (StoreConditional (aq, rl, Data)) w ->
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
          exec (vmem_write_addr (Virtaddr va) 4 dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) σ
            = Some (Ok b, σ''))
       \/ exec (vmem_write_addr (Virtaddr va) 4 dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) σ
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
    (* the vmem level resolves the translation MODE before the access, so the
       fact has to come out of the invariant at the PRE-translate state *)
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (utlb_inv_pt_translateAddr_u (StoreConditional (aq, rl, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data))
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (StoreConditional (aq, rl, Data)) σ
               (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))))) Hall
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
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4
                  (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & _ & Hresv).
    (* DRAM is reservable, so the SC's PMA arm PASSES -- which is what makes
       [mem_write_ea] (which the reservation-HIT path runs BEFORE the store)
       answer [Ok] at all. *)
    assert (Hfield : andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable)
                       (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability)
                          RsrvNone) = true)
      by (rewrite Hwr; rewrite Hresv; reflexivity).
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
    assert (Halp : is_aligned_paddr (Physaddr pa) 4 = true)
      by exact (pa_aligned_div _ va 4 ltac:(lia) ltac:(exists 1024; reflexivity) Hal).
    assert (Hwv := exec_mem_write_value_sc_g4 aq rl PBMT_PMA pa region wv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam Halp
             Hwr Hmmiow (addr_is_ram_not_dev _ Hram0)
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    rewrite Hresv in Hwv. cbn match in Hwv.
    assert (Hpac : exec (phys_access_check (StoreConditional (aq, rl, Data)) PBMT_PMA User (Physaddr pa) 4 true) σ'
                   = Some (Ok pma_ok_aligned, σ')).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc aq rl pa 4 σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW)))).
      cbn match.
      exact (exec_pmaCheck_ram_sc_ok 4 pa PBMT_PMA region aq rl σ' Hpmam Halp Hfield). }
    assert (Hea := exec_mem_write_ea_sc_g aq rl 4 pa PBMT_PMA region σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam Halp Hfield
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    destruct (exec_vmem_write_addr_sc_disj 4 va pa (register_lookup PC σ'.(sregs)) dat
                aq rl (andb aq rl) rl User User Sv39 pma_ok_aligned true σ σ'
                ltac:(unfold vmem_width; lia)
                Hal
                (ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv))
                Htm Htr
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl Hea Hwv
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); rewrite Hcp;
                       apply exec_effectivePrivilege_mprv0;
                       rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                Hpac (offset_virtaddr_by_self va pa))
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
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt. exact Hflt. }
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
    uleaf_ok (StoreConditional (aq, rl, Data)) w ->
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
          exec (vmem_write_addr (Virtaddr va) 8 dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) σ
            = Some (Ok b, σ''))
       \/ exec (vmem_write_addr (Virtaddr va) 8 dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) σ
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
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ HSXL with "Hri Hinv") as %Htm.
    iMod (utlb_inv_pt_translateAddr_u (StoreConditional (aq, rl, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data))
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (StoreConditional (aq, rl, Data)) σ
               (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl)))))))) Hall
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
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8
                  (pma_access_ram _ _ _ Hram0 Hram7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & _ & Hresv).
    assert (Hfield : andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable)
                       (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability)
                          RsrvNone) = true)
      by (rewrite Hwr; rewrite Hresv; reflexivity).
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
    assert (Halp : is_aligned_paddr (Physaddr pa) 8 = true)
      by exact (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal).
    assert (Hwv := exec_mem_write_value_sc_g8 aq rl PBMT_PMA pa region wv σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam Halp
             Hwr Hmmiow (addr_is_ram_not_dev _ Hram0)
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    rewrite Hresv in Hwv. cbn match in Hwv.
    assert (Hpac : exec (phys_access_check (StoreConditional (aq, rl, Data)) PBMT_PMA User (Physaddr pa) 8 true) σ'
                   = Some (Ok pma_ok_aligned, σ')).
    { unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_sc aq rl pa 8 σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW)))).
      cbn match.
      exact (exec_pmaCheck_ram_sc_ok 8 pa PBMT_PMA region aq rl σ' Hpmam Halp Hfield). }
    assert (Hea := exec_mem_write_ea_sc_g aq rl 8 pa PBMT_PMA region σ'
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
             (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
             Hrange
             (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
             Hpmam Halp Hfield
             (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
             (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))).
    destruct (exec_vmem_write_addr_sc_disj 8 va pa (register_lookup PC σ'.(sregs)) dat
                aq rl (andb aq rl) rl User User Sv39 pma_ok_aligned true σ σ'
                ltac:(unfold vmem_width; lia)
                Hal
                (ltac:(rewrite Hcp; apply exec_effectivePrivilege_mprv0; exact Hmprv))
                Htm Htr
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                eq_refl Hea Hwv
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); rewrite Hcp;
                       apply exec_effectivePrivilege_mprv0;
                       rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                Hpac (offset_virtaddr_by_self va pa))
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
      { rewrite (Tr PC ltac:(vm_compute; reflexivity)) in Hflt. exact Hflt. }
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
    u_fault_flavor (StoreConditional (aq, rl, Data)) tfp um va ->
    vmem_width width ->
    is_aligned_vaddr (Virtaddr va) width = true ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (vmem_write_addr (Virtaddr va) width dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) σ
      = Some (Err (Trap (User, make_sync_exception (E_SAMO_Page_Fault tt) va, pc)), σ)⌝.
  Proof.
    intros Hflavor Hvw Halign Lpc Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_tmode uroot tfp um σ LSXL with "Hri Hinv") as %Htm.
    iDestruct (utlb_inv_pt_translateAddr_u_fault (StoreConditional (aq, rl, Data)) uroot tfp um va
                 (E_SAMO_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data))
                    (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (StoreConditional (aq, rl, Data)) σ
                    (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro.
    (* [Htr] is at the BARE vaddr now -- the vmem level's split offset is gone *)
    exact (exec_vmem_write_addr_translate_err width va pc (E_SAMO_Page_Fault tt)
             dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true User Sv39 User σ σ
             Hvw Halign
             (ltac:(rewrite Lcp; apply exec_effectivePrivilege_mprv0; exact Lmprv))
             Htm Htr Lcp Lpc).
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
          (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s = Some (Ok b, s') ->
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
      uleaf_ok (StoreConditional (aq0, rl0, Data)) w0 ->
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
            exec (vmem_write_addr (Virtaddr va0) k dat0 (StoreConditional (aq0, rl0, Data)) (andb aq0 rl0) rl0 true) σ0
              = Some (Ok b, σ0''))
         \/ exec (vmem_write_addr (Virtaddr va0) k dat0 (StoreConditional (aq0, rl0, Data)) (andb aq0 rl0) rl0 true) σ0
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
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s = Some (Ok b, σ')⌝ ∗
        ⌜σ'.(mdev) = s.(mdev)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) σ'.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC σ'.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um ∗ udata_own data)
    ∨ (∃ (σ' : mstate) (e : ExceptionType) (xv pcx : mword 64),
        ⌜exec (vmem_write_addr (Virtaddr va) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s
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
    - destruct (data_classify (StoreConditional (aq, rl, Data)) tfp um va
                  (or_intror (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq (ex_intro _ rl eq_refl))))))) Hwf)
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
                     Hfault ltac:(destruct HkW as [Hkv|Hkv]; rewrite Hkv; unfold vmem_width; tauto)
                     Hal Lpc Hhtif Hcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Herr.
        iModIntro. iRight. iExists s, (E_SAMO_Page_Fault tt), va, pc.
        iFrame. iPureIntro. split; [exact Herr |]. split; [vm_compute; reflexivity |].
        split; [reflexivity|]. split; [reflexivity|]. reflexivity.
    - iModIntro. iRight. iExists s, (E_SAMO_Access_Fault tt), va, pc.
      iFrame. iPureIntro.
      split; [ exact (exec_vmem_write_addr_misaligned_sc va pc k dat aq rl (andb aq rl) rl User s Hal Hcp Lpc) |].
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
    assert (Hpml : exec (get_pmlen (StoreConditional (aq, rl, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption;
        (destruct aq; destruct rl; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data))
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
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (zeros' 64) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s = Some (Ok b, sig')).
      { apply (exec_vmem_write_u rs1 (zeros' 64) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Ok b) s sig' Lcp Heff Hpml Htm).
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
        { intros r Hne. unfold s_x; rewrite ?sregs_set_reg. apply irrelevant_register_set; exact Hne. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hmi. }
        iSplitR. { iPureIntro. rewrite Tr; [| reg_ne]. exact Hnpc. }
        unfold mstate_interp. iSplitL "Hreg Hgh Hdev".
        { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
        iFrame "Hgpr". iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - iDestruct "HErr" as (sig' e xv pcx) "(%Herr & %Hue & %Hmdev & %Hmi & %Hnpc & Hreg & Hgh & Hutlb & Hudata)".
      assert (Hvwrite : exec (vmem_write (Regidx rs1) (zeros' 64) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true) s = Some (Err (rv64d_types.Trap (User, make_sync_exception e xv, pcx)), sig')).
      { apply (exec_vmem_write_u rs1 (zeros' 64) k dat (StoreConditional (aq, rl, Data)) (andb aq rl) rl true Sv39 (Err _) s sig' Lcp Heff Hpml Htm).
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

