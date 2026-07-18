(* UserPtTree.v -- U-MODE translation over the ptree user table
   (UptTree.v): the successor of UserPt.v's upt record for arbitrary
   user-mode execution.

   Layers:
     §1 privilege bricks: effectivePrivilege at MPRV=0 (access-generic)
        and is_shadow_stack for every access user execution can issue;
     §2 the per-leaf ACCESS classification: at User, a mapped leaf either
        passes the permission check on every A/D variant ([uleaf_ok]) or
        is denied on every variant ([uleaf_denied]) -- decided once per
        map entry from its concrete R/W/X/U flag byte ([upt_acc_wf]).
        The S-mode-only trampoline / trapframe leaves are DENIED for
        every user access (U = 0);
     §3 the user-execution page-table bundle [user_pt_inv]: the tree
        invariant [utlb_inv_pt] + ownership of the mapped pages' bytes
        with EXISTENTIAL contents ([udata_own], a flat pa-set -- two
        vpns may map one page, a gset dedups) + the coverage fact;
     §4 the U-mode Ok absorption instance: a user-mapped, check-passing
        va translates to its leaf page and the invariant absorbs
        whatever the walk did (hit / TLB fill / Svadu A/D write-back).

   The FAULT side (non-canonical / unmapped / denied / hit-denied) is §5.  *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import TrampPt.
Require Import SmodeCore.
Require Import KptTree.
Require Import UptTree.
Require Import UserTranslate.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Privilege bricks.                                                    *)
(* ===================================================================== *)

(* with MPRV clear the effective privilege is the current one, for EVERY
   access type (the fetch special case never consults MPRV) *)
Lemma exec_effectivePrivilege_mprv0 (acc : MemoryAccessType mem_payload)
    (m : mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  exec (effectivePrivilege acc m pr) s = Some (pr, s).
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  apply exec_returnM.
Qed.

(* the access types arbitrary user-mode execution can issue *)
Definition u_acc (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  acc = LoadReserved Data \/ acc = StoreConditional Data \/
  (exists op, acc = Atomic (op, Data, Data)).

Lemma exec_is_shadow_stack_u_acc (acc : MemoryAccessType mem_payload) s :
  u_acc acc ->
  exec (is_shadow_stack_access acc) s = Some (false, s).
Proof.
  intros [-> | [-> | [-> | [-> | [-> | (op & ->)]]]]];
    unfold is_shadow_stack_access; cbn match; apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §2 The per-leaf access classification at User.                          *)
(* ===================================================================== *)

(* the check passes on every A/D variant (check_PTE_permission never
   reads A/D, so this is a fact about the R/W/X/U byte of [w] alone) *)
Definition uleaf_ok (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_ok acc User mxr do_sum (pte_set_ad w a d).

(* ... or is denied on every variant.  NOTE the mxr quantifier: a leaf
   with X=1, R=0 would be load-DENIED only at mxr=0 -- such execute-only
   user pages fall in neither class and are excluded by [upt_acc_wf]
   (xv6 never builds them; user execution pins mstatus.MXR=0 anyway). *)
Definition uleaf_denied (acc : MemoryAccessType mem_payload) (w : mword 64) : Prop :=
  forall (a d : mword 1) (mxr do_sum : bool),
    pte_check_denied acc User mxr do_sum (PTE_No_Permission tt) (pte_set_ad w a d).

(* the classification each user-map entry carries: decided once when the
   map is built, from the entry's concrete flag byte (each side is a
   4-way a/d x 4-way mxr/do_sum vm_compute) *)
Definition upt_acc_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn w, um !! vpn = Some w ->
    forall acc, u_acc acc -> uleaf_ok acc w \/ uleaf_denied acc w.

(* the S-mode-only top pages deny every user access before the access
   type is even consulted (U = 0 fails the privilege step) *)
Lemma uleaf_denied_tramp (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc pte_tramp.
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags. rewrite tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

Lemma uleaf_denied_tf (tfp : mword 44) (acc : MemoryAccessType mem_payload) :
  uleaf_denied acc (pte_tf tfp).
Proof.
  intros a d mxr do_sum s.
  unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The user-execution page-table bundle.                                *)
(* ===================================================================== *)

(* the pas a mapped leaf can output: its page, at every offset *)
Definition udata_cov (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa) : Prop :=
  forall vpn w va, um !! vpn = Some w -> u_walk_pa w va ∈ data.

Section UserPtInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the owned bytes of the mapped pages, contents EXISTENTIAL: user-mode
     safety never depends on what the pages hold.  One aggregated byte
     map -- accesses look up plain addresses, no per-page decomposition;
     a flat pa-set dedups pages shared by several vpns. *)
  Definition udata_own (data : gset Arch.pa) : iProp Σ :=
    (∃ dm : gmap Arch.pa (bv 8),
       ⌜dom dm = data⌝ ∗ [∗ map] a ↦ b ∈ dm, a ↦ₘ b)%I.

  (* THE USER-EXECUTION PT BUNDLE: the tree invariant + the data pages +
     the pure coverage and access-classification facts. *)
  Definition user_pt_inv (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa) : iProp Σ :=
    (utlb_inv_pt uroot tfp um ∗
     udata_own data ∗
     ⌜udata_cov um data⌝ ∗
     ⌜upt_acc_wf um⌝)%I.

End UserPtInv.

(* ===================================================================== *)
(* §4 The U-mode Ok absorption instance: a user-mapped va whose leaf       *)
(*    passes the check translates to the leaf page; the invariant absorbs  *)
(*    whatever the walk did (hit / TLB fill / A-D write-back).             *)
(* ===================================================================== *)

Section UserPtTranslate.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Lemma utlb_inv_pt_translateAddr_u (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va pa : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok acc w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) User) σ
      = Some (User, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hl Hchk Hcanon Hout Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    apply (utlb_inv_pt_translateAddr acc User uroot tfp um w va pa σ
             Hchk (or_intror (or_intror Hl))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_U_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

End UserPtTranslate.
