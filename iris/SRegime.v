(* SRegime.v -- the S-mode TRANSLATION REGIME interface: ONE record
   abstracting how an S-mode instruction's fetch/data translation is
   absorbed, so the engine + leaf layer serves Sv39 (paging on, the
   kernel table installed) and BARE (boot, satp=0) without duplication.

   [sr_absorb] is the TrampStepPt-Habs shape, access-generic over the
   four classes the leaves use, keyed on [addr_is_ram va] (identity
   output pa), with the PMP grant facts at the output state exposed for
   the subsequent memory access.  Instances:
     - [kpt_regime root_ppn]: sr_inv := tlb_inv_pt root_ppn; the fields
       are the existing absorption wrappers + the ktramp-style PMP
       peel-and-reseal.
     - [bare_regime]: satp pinned to Mode=Bare + pmp_config; translation
       short-circuits to the identity before touching the TLB
       ([exec_translateAddr_bare]), so absorption is trivial.           *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte KptPt.
Require Import WpGpr WpMmodeLeafBase WpGprCsrwB.
Require Import SmodeCore KptTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Pure BARE-mode translateAddr reduction.                             *)
(* ===================================================================== *)

Lemma exec_translationMode_S_bare (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
  exec (translationMode Supervisor) s = Some (Bare, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  cbn match.
  change (xlen >=? 64) with true.
  match goal with |- exec (Defs.bind ?ARM _) s = _ =>
    assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ HARM).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"0000" : mword 4)) with (Some Bare)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

Section BareFront.
  Context (acc : MemoryAccessType mem_payload).

  Lemma exec_translateAddr_bare (va : mword 64) (s : mstate) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) Supervisor) s
      = Some (Supervisor, s) ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (translationMode Supervisor) s = Some (Bare, s) ->
    exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Heff Hss Hcp Htm.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR.
    cbn [bits_of_virtaddr].
    rewrite zero_extend'_id.
    reflexivity.
  Qed.

End BareFront.

(* ===================================================================== *)
(* §1b The pointer-masking effective-address transform is the IDENTITY    *)
(*     at pmlen 0, in EITHER translation mode -- the ONE fact the data    *)
(*     towers need from the mode.                                         *)
(* ===================================================================== *)

Lemma pm_transform_VA_0 (ea : mword 64) :
  pm_transform_VA (Virtaddr ea) 0 = Virtaddr ea.
Proof.
  unfold pm_transform_VA. f_equal.
  change (xlen - 0 - 1) with (xlen - 0 - 1).
  rewrite subrange_id. apply sign_extend'_id.
Qed.

Lemma pm_transform_PA_0 (ea : mword 64) :
  pm_transform_PA (Virtaddr ea) 0 = Virtaddr ea.
Proof.
  unfold pm_transform_PA. f_equal.
  rewrite subrange_id. apply zero_extend'_id.
Qed.

Section TransformFront.
  Context (acc : MemoryAccessType mem_payload).

  (* mode-GENERIC: with PMM off (pmlen 0) the transform is the identity
     whatever [translationMode] returns *)
  Lemma exec_transform_effective_address_mode (md : SATPMode) (ea : mword 64) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) Supervisor) s
      = Some (Supervisor, s) ->
    exec (get_pmlen acc Supervisor) s = Some (0, s) ->
    exec (translationMode Supervisor) s = Some (md, s) ->
    exec (transform_effective_address (Virtaddr ea) acc) s = Some (Virtaddr ea, s).
  Proof.
    intros Hcp Heff Hpml Htm.
    unfold transform_effective_address.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (exec_bind_Some _ _ _ _ _ Heff).
    rewrite (exec_bind_Some _ _ _ _ _ Hpml).
    rewrite (exec_bind_Some _ _ _ _ _ Htm).
    destruct (generic_eq md Bare);
      [ rewrite pm_transform_PA_0 | rewrite pm_transform_VA_0 ];
      apply exec_returnM.
  Qed.

End TransformFront.

(* ===================================================================== *)
(* §2 The regime record + the two instances.                              *)
(* ===================================================================== *)

(* the access classes the S-mode leaves use *)
Definition s_acc_ok (acc : MemoryAccessType mem_payload) : Prop :=
  acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
  acc = Atomic (AMOSWAP, Data, Data).

(* the per-access region predicate the absorption premise dispatches on: a
   fetch must land in the executable (text) region, a store/AMO in the
   writable (data) region, a load anywhere in RAM.  [sr_absorb]'s old
   uniform [addr_is_ram va] premise becomes [sr_addr_ok] over the regime's
   three predicate fields, so the permission split (kernel text R|X, data
   R|W) is reflected at the absorption interface. *)
Definition sr_addr_ok (fetch_ok load_ok store_ok : mword 64 -> Prop)
    (acc : MemoryAccessType mem_payload) (va : mword 64) : Prop :=
  match acc with
  | InstructionFetch _ => fetch_ok va
  | Store _ => store_ok va
  | Atomic _ => store_ok va
  | _ => load_ok va
  end.

(* the PMP grant facts at a state: the kernel TOR entry 0 covering RAM
   with R/W/X (what every post-translate memory access checks) *)
Definition pmp_grant_facts (σ : mstate) : Prop :=
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR /\
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false /\
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true /\
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z.

Section SRegimeDef.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Record s_regime := SRegime {
    sr_inv : iProp Σ;
    (* per-access region predicates: fetch → executable region, load →
       readable (all of RAM), store/AMO → writable region. *)
    sr_fetch_ok : mword 64 -> Prop;
    sr_load_ok : mword 64 -> Prop;
    sr_store_ok : mword 64 -> Prop;
    (* every RAM address is loadable (readable): the load leaves keep
       deriving [addr_is_ram] from ownership and lift it through this law,
       so no load call site changes. *)
    sr_load_ram : forall va : mword 64, addr_is_ram va -> sr_load_ok va;
    (* a kernel-text address is fetch-legal: the fetch engine extracts
       [addr_in_text pc] from the [instr] resource (all kernel code lives in
       [KERNBASE, etext)) and lifts it through this law, so no fetch call
       site changes. *)
    sr_fetch_text : forall va : mword 64, addr_in_text va -> sr_fetch_ok va;
    (* a kernel-data address is store-legal: store call sites discharge
       [addr_in_data] (vm_compute for globals/locks, [page_in_range] for
       kalloc pages, the bundled [stack_in_data] premise for stack slots)
       and lift it through this law. *)
    sr_store_data : forall va : mword 64, addr_in_data va -> sr_store_ok va;
    sr_absorb : forall (acc : MemoryAccessType mem_payload) (va : mword 64) (σ : mstate),
      s_acc_ok acc ->
      sr_addr_ok sr_fetch_ok sr_load_ok sr_store_ok acc va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv;
    sr_transform : forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ sr_inv -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝;
    sr_absorb_dev : forall (acc : MemoryAccessType mem_payload) (va : mword 64) (σ : mstate),
      (acc = Load Data \/ acc = Store Data) ->
      kpt_dev_vpn (svpn_of va) ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of va))
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv
  }.

  (* ---- the PMP facts, off any invariant that carries [pmp_config] ---- *)
  Lemma pmp_config_grant_facts (r : mword 44) (σ : mstate) :
    reg_interp σ.(sregs) -∗ pmp_config r -∗ ⌜pmp_grant_facts σ⌝.
  Proof.
    iIntros "Hri Hpmp".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %Hpmar & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    iPureIntro. rewrite /pmp_grant_facts Hpcv Hpav. tauto.
  Qed.

  Lemma tlb_inv_pt_grant_facts (root_ppn : mword 44) (σ : mstate) :
    reg_interp σ.(sregs) -∗ tlb_inv_pt root_ppn -∗ ⌜pmp_grant_facts σ⌝.
  Proof.
    iIntros "Hri Hinv".
    iDestruct (tlb_inv_pt_open with "Hinv") as (satp0 tlbvec t)
      "(Hsatp & _ & _ & _ & Htlb & _ & _ & _ & Ht & Hpmp)".
    iApply (pmp_config_grant_facts with "Hri Hpmp").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The Sv39-kernel instance.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma kpt_absorb (root_ppn : mword 44) :
    forall acc va σ, s_acc_ok acc ->
      sr_addr_ok addr_in_text addr_is_ram addr_in_data acc va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros acc va σ Hacc Hok Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iAssert (|==> ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn)%I
      with "[Hri Hgh Hinv]" as ">H".
    { destruct Hacc as [-> | [-> | [-> | ->]]]; cbn [sr_addr_ok] in Hok.
      - iApply (tlb_inv_pt_translateAddr_fetch root_ppn va σ Hok
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv").
      - iApply (tlb_inv_pt_translateAddr_load root_ppn va σ Hok
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv").
      - iApply (tlb_inv_pt_translateAddr_store root_ppn va σ Hok
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv").
      - iApply (tlb_inv_pt_translateAddr (Atomic (AMOSWAP, Data, Data)) root_ppn va σ
                  (fun a d mxr do_sum => kpt_variant_check_amo (svpn_of va) a d mxr do_sum
                                           (data_svpn_not_text va Hok))
                  (or_introl (ram_svpn_range va (addr_in_data_ram va Hok)))
                  (RiscvExtras.ram_canonical va (addr_in_data_ram va Hok))
                  (ram_ident_4k va (addr_in_data_ram va Hok))
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv"). }
    iDestruct "H" as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct (tlb_inv_pt_grant_facts root_ppn σ' with "Hri Hinv") as %Hpmp.
    iModIntro. iExists σ'. iFrame "Hri Hgh Hinv". iPureIntro. tauto.
  Qed.

  Lemma kpt_transform (root_ppn : mword 44) :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ tlb_inv_pt root_ppn -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri Hinv".
    iDestruct (tlb_inv_pt_open with "Hinv") as (satp0 tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & _)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Sv39 ea σ Hcp Heff Hpml
             (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Lemma kpt_absorb_dev (root_ppn : mword 44) :
    forall acc va σ, (acc = Load Data \/ acc = Store Data) ->
      kpt_dev_vpn (svpn_of va) ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of va))
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros acc va σ Hacc Hdev Hcanon Hident Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iAssert (|==> ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn)%I
      with "[Hri Hgh Hinv]" as ">H".
    { destruct Hacc as [-> | ->].
      - iApply (tlb_inv_pt_translateAddr_load_dev root_ppn va σ Hdev Hcanon Hident
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv").
      - iApply (tlb_inv_pt_translateAddr_store_dev root_ppn va σ Hdev Hcanon Hident
                  Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall with "Hri Hgh Hinv"). }
    iDestruct "H" as (σ') "(%Htr & %Hmdev & %Hsh & Hri & Hgh & Hinv)".
    iDestruct (tlb_inv_pt_grant_facts root_ppn σ' with "Hri Hinv") as %Hpmp.
    iModIntro. iExists σ'. iFrame "Hri Hgh Hinv". iPureIntro. tauto.
  Qed.

  Definition kpt_regime (root_ppn : mword 44) : s_regime :=
    SRegime (tlb_inv_pt root_ppn) addr_in_text addr_is_ram addr_in_data
            (fun _ H => H) (fun _ H => H) (fun _ H => H)
            (kpt_absorb root_ppn) (kpt_transform root_ppn)
            (kpt_absorb_dev root_ppn).

  (* ------------------------------------------------------------------- *)
  (* The BARE instance (boot: satp Mode = Bare, translation = identity).   *)
  (* ------------------------------------------------------------------- *)
  Definition bare_inv : iProp Σ :=
    (∃ satp0 : mword 64,
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ⌝ ∗
       pmp_config (mword_of_int 0))%I.

  Lemma bare_absorb :
    forall acc va σ, s_acc_ok acc ->
      sr_addr_ok addr_is_ram addr_is_ram addr_is_ram acc va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ bare_inv ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ bare_inv.
  Proof.
    intros acc va σ Hacc Hram Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (pmp_config_grant_facts (mword_of_int 0) σ with "Hri Hpmp") as %Hpmp.
    iModIntro. iExists σ.
    iSplit.
    { iPureIntro.
      exact (exec_translateAddr_bare acc va σ Heff Hss Hcp
               (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)). }
    iSplit; [iPureIntro; reflexivity |].
    iSplit; [iPureIntro; left; reflexivity |].
    iSplit; [iPureIntro; exact Hpmp |].
    iFrame "Hri Hgh".
    iExists satp0. iFrame "Hsatp Hpmp". iPureIntro. exact Hmode.
  Qed.

  Lemma bare_transform :
    forall (acc : MemoryAccessType mem_payload) (ea : mword 64) (σ : mstate),
      s_acc_ok acc ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (get_pmlen acc Supervisor) σ = Some (0, σ) ->
      ⊢ reg_interp σ.(sregs) -∗ bare_inv -∗
        ⌜ exec (transform_effective_address (Virtaddr ea) acc) σ = Some (Virtaddr ea, σ) ⌝.
  Proof.
    intros acc ea σ Hacc Hcp HSXL Heff Hpml.
    iIntros "Hri Hinv".
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iPureIntro.
    exact (exec_transform_effective_address_mode acc Bare ea σ Hcp Heff Hpml
             (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)).
  Qed.

  Lemma bare_absorb_dev :
    forall acc va σ, (acc = Load Data \/ acc = Store Data) ->
      kpt_dev_vpn (svpn_of va) ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of va))
          (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = Supervisor ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
        = Some (Supervisor, σ) ->
      exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      ⊢ reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ bare_inv ==∗
        ∃ σ' : mstate,
          ⌜ exec (translateAddr (Virtaddr va) acc) σ
            = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
          ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
          ⌜ (σ'.(sregs) = σ.(sregs) \/
             exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
          ⌜ pmp_grant_facts σ' ⌝ ∗
          reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ bare_inv.
  Proof.
    intros acc va σ Hacc Hdev Hcanon Hident Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0) "(Hsatp & %Hmode & Hpmp)".
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (pmp_config_grant_facts (mword_of_int 0) σ with "Hri Hpmp") as %Hpmp.
    iModIntro. iExists σ.
    iSplit.
    { iPureIntro.
      exact (exec_translateAddr_bare acc va σ Heff Hss Hcp
               (exec_translationMode_S_bare satp0 σ HSXL Hsatpv Hmode)). }
    iSplit; [iPureIntro; reflexivity |].
    iSplit; [iPureIntro; left; reflexivity |].
    iSplit; [iPureIntro; exact Hpmp |].
    iFrame "Hri Hgh".
    iExists satp0. iFrame "Hsatp Hpmp". iPureIntro. exact Hmode.
  Qed.

  Definition bare_regime : s_regime :=
    SRegime bare_inv addr_is_ram addr_is_ram addr_is_ram
            (fun _ H => H) addr_in_text_ram addr_in_data_ram
            bare_absorb bare_transform bare_absorb_dev.

End SRegimeDef.
