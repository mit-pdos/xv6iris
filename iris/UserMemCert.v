(* ====================================================================== *)
(* UserMemCert.v -- THE U-MODE DATA ACCESSES, PURE.                        *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge HartGoodb HartMemRun HartMemAsm PtBytes.
Require Import MemAccessGen WpLoad WpMmodeLeafBase SmodePte.
Require Import CommonWalk PtAdBits Pt4kWalk PtreeType KptPt PtTree PtTreeAdue KptTree.
Require Import ExecCommon UserTranslate UptTree UserPtTree UserBits UserMem UserFetch.
Require Import UserBytes PtWalkCert.
Require Import SmodeCore.
Require Import UserFrame UserExec UserClassify UserClassifyAsm.
Require Import UserMemPt UserMemAccess UserMemMis UserFetchCert.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. THE ACCESS-TYPE INGREDIENTS AT A U-MODE DATA ACCESS.                *)
(* ===================================================================== *)

Lemma goodb_effectivePrivilege_mprv0 (Db : register -> bool)
    (acc : MemoryAccessType mem_payload) (m : mword 64) (pr : Privilege)
    (s : mstate) :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  goodb Db (effectivePrivilege acc m pr) s = true.
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma goodb_is_shadow_stack_u_acc (Db : register -> bool)
    (acc : MemoryAccessType mem_payload) (s : mstate) :
  u_acc acc -> goodb Db (is_shadow_stack_access acc) s = true.
Proof.
  intros [-> | [-> | [-> | [(aq & rl & ->) | [(aq & rl & ->) | (op & aq & rl & ->)]]]]];
    unfold is_shadow_stack_access; cbn match; reflexivity.
Qed.

Lemma goodb_check_PTE_permission_u (acc : MemoryAccessType mem_payload)
    (w' : mword 64) (mxr do_sum : bool) (Db : register -> bool) (s : mstate) :
  u_acc acc ->
  pte_check_ok acc User mxr do_sum w' ->
  goodb Db (check_PTE_permission acc User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec w' 7 0))
              (ext_bits_of_PTE w') tt) s = true.
Proof.
  unfold pte_check_ok. intros Hacc Hchk.
  pose proof (Hchk dstateM) as Hc0.
  destruct Hacc as [-> | [-> | [-> | [(aq & rl & ->) | [(aq & rl & ->) | (op & aq & rl & ->)]]]]];
  destruct (mword1_cases (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HU|HU];
  destruct (mword1_cases (_get_PTE_Flags_R (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HR|HR];
  destruct (mword1_cases (_get_PTE_Flags_W (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HW|HW];
  destruct (mword1_cases (_get_PTE_Flags_X (Mk_PTE_Flags (subrange_vec_dec w' 7 0)))) as [HX|HX];
  unfold check_PTE_permission in Hc0 |- *;
  rewrite ?HU, ?HR, ?HW, ?HX in Hc0 |- *;
  first [ solve [ vm_compute; reflexivity ]
        | solve [ vm_compute in Hc0; discriminate Hc0 ] ].
Time Qed.

(* ===================================================================== *)
(* 2. THE DATA WINDOW, PURE.                                             *)
(*                                                                       *)
(* [UserMemPt.udata_read_word_g]'s content, with [gen_heap_interp] /      *)
(* [udata_own] replaced by [UserBytes.u_mem_wf]: the [k] bytes of an      *)
(* aligned access to a MAPPED page are in the hart's own map, and         *)
(* therefore assemble into a word.                                       *)
(* ===================================================================== *)

Lemma u_data_bytes (P : uptd) (t : ptree) (mm : pamap) (k : Z) (w va : mword 64) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  exists dv : mword (8 * k),
    forall j : nat, (N.of_nat j < Z.to_N k)%N ->
      mm !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j).
Proof.
  intros Hk Hdvd Hal Hwf Hl.
  pose proof (u_mem_wf_owned_data P t mm k w va Hk Hdvd Hal Hwf Hl) as Hown.
  assert (Hex : forall j : nat, (j < Z.to_nat k)%nat ->
            exists b, mm !! pa_add (u_walk_pa w va) j = Some b).
  { intros j Hj. exact (bytes_owned_spec mm _ _ Hown j ltac:(lia)). }
  destruct (bytes_list_of_lookups (fun j => mm !! pa_add (u_walk_pa w va) j)
              (Z.to_nat k) Hex) as (bs & Hlen & Hbs).
  exists (Z_to_bv _ (assemble_bytes bs) : mword (8 * k)).
  intros j HjN.
  assert (Hj : (j < Z.to_nat k)%nat) by lia.
  rewrite (nth_byte_assemble_len _ bs j).
  - exact (Hbs j Hj).
  - rewrite Hlen.
    assert (HZN : Z.of_N (MachineWord.MachineWord.Z_idx (8 * k)) = 8 * k).
    { unfold MachineWord.MachineWord.Z_idx. apply Z2N.id. lia. }
    rewrite HZN. lia.
  - rewrite Hlen. exact Hj.
Qed.

(* the RAM facts the physical access needs, at the two ends of the window *)
Lemma u_data_ram (P : uptd) (t : ptree) (mm : pamap) (k : Z) (w va : mword 64) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  addr_is_ram (u_walk_pa w va) /\
  addr_is_ram (pa_add (u_walk_pa w va) (Z.to_nat k - 1)).
Proof.
  intros Hk Hdvd Hal Hwf Hl.
  pose proof (u_mem_wf_owned_data P t mm k w va Hk Hdvd Hal Hwf Hl) as Hown.
  pose proof Hwf as (md & _ & _ & _ & _ & Hram & _).
  assert (Hj : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
            addr_is_ram (pa_add (u_walk_pa w va) j)).
  { intros j Hjb. apply Hram, elem_of_dom.
    exact (bytes_owned_spec mm _ _ Hown j Hjb). }
  split.
  - rewrite <- (pa_add_0 (u_walk_pa w va)). apply Hj. lia.
  - apply Hj. lia.
Qed.

(* ===================================================================== *)
(* 3. THE WALK, ONCE, FOR EVERY U-MODE DATA ACCESS TYPE.                  *)
(*                                                                       *)
(* [UserFetchCert] section 7's translation half, with the access type a   *)
(* PARAMETER: [PtWalkCert.goodmb_ptree_translateAddr] and                 *)
(* [KptTree.ptree_translateAddr_cases] are both generic in [acc] and in   *)
(* the privilege, and the three read-only probes                          *)
(* ([translationMode]/[effectivePrivilege]/[is_shadow_stack_access]) are  *)
(* generic over [UserPtTree.u_acc].  So the five data composers share ONE *)
(* walk and differ only in the physical access on top of it.              *)
(* ===================================================================== *)

(* the config cells a U-mode DATA access reads.  These are conjuncts 2-4 of *)
(* [UserExec.post_fetch_cfg] VERBATIM -- a caller holding that bundle at    *)
(* the fetched state has this by projection -- but the data address is NOT  *)
(* the PC, so [post_fetch_cfg]'s first conjunct must not be asked for here. *)
Definition u_data_cfg (rs : regstate) : Prop :=
  register_lookup cur_privilege rs = User /\
  user_mstatus_ok (register_lookup mstatus rs) /\
  register_lookup menvcfg rs = MENVCFG_S.

Lemma u_data_cfg_of_post_fetch (rs : regstate) (mm : pamap)
    (va : mword 64) (mi : bool) :
  post_fetch_cfg (u_state rs mm) va mi -> u_data_cfg rs.
Proof.
  intros (_ & Lcp & Lms & Lmenv & _ & _). exact (conj Lcp (conj Lms Lmenv)).
Qed.

(* the landing file differs from [rs] at [tlb] and nowhere else *)
Lemma u_tlb_irrel (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) ->
  forall r : register, register_beq r (tlb : register) = false ->
    register_lookup r rs' = register_lookup r rs.
Proof.
  intros [-> | (tv & ->)] r Hne;
    [ reflexivity | apply irrelevant_register_set; exact Hne ].
Qed.

Lemma u_data_cfg_tlb (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) ->
  u_data_cfg rs -> u_data_cfg rs'.
Proof.
  intros Hd (Lcp & Lms & Lmenv).
  pose proof (u_tlb_irrel rs rs' Hd) as Tr.
  split_and!;
    [ rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp
    | rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Lms
    | rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv ].
Qed.

Lemma u_exec_pins_tlb (P : uptd) (t t' : ptree) (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) ->
  tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
  u_exec_pins P t rs -> u_exec_pins P t' rs'.
Proof.
  intros Hd Htlbok' (Hhw & Hcfgp & Hpt & _).
  pose proof (u_tlb_irrel rs rs' Hd) as Tr.
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hcfgp as (Hmst0 & Hsst0).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HX & HW & HR & Hcovp).
  split_and!; [ | | | exact Htlbok' ].
  - split_and!;
      [ rewrite (Tr misa ltac:(vm_compute; reflexivity)); exact Hmisa
      | rewrite (Tr mseccfg ltac:(vm_compute; reflexivity)); exact Hmseccfg
      | rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)); exact Hsenv
      | rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif
      | rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall
      | rewrite (Tr elp ltac:(vm_compute; reflexivity)); exact Help ].
  - split_and!;
      [ rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)); exact Hmst0
      | rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)); exact Hsst0 ].
  - split_and!;
      [ exists usatp; split;
          [ exact Hsatpok
          | rewrite (Tr satp ltac:(vm_compute; reflexivity)); exact Hsatp ]
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp ].
Qed.

Lemma u_walk_pure (acc : MemoryAccessType mem_payload)
    (P : uptd) (t : ptree) (mm : pamap) (rs : regstate) (w va : mword 64) :
  u_acc acc ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok acc w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) acc) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) acc) (u_state rs mm) mm = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm'.
Proof.
  intros Hacc Hl Hleaf Hcanon Hcfg Hpins Hwf.
  pose proof Hcfg as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  pose proof Hpins as Hpins0.
  destruct Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  destruct Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
  pose proof Hwf as (md & Hdisj & Hdj & Hmm & Hdm & Hram & Hcov & Hacc0 & Hwfm & Hspec).
  pose proof Hspec as (Hbase & _).
  destruct (upt_spec_maps (ud_root P) (ud_tfp P) (ud_um P) t (svpn_of va) w
              Hspec (or_intror (or_intror Hl)))
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                       Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
  assert (Hvar : forall a d : mword 1,
            pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
            pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d))
    by exact (upt_variant (ud_tfp P) (ud_um P) (svpn_of va) w Hwfm
                (or_intror (or_intror Hl))).
  (* the three slots, as reads and as ownership *)
  assert (Hsm2 : pt_slot_mem (u_state rs mm) (pt_addr2 t (svpn_of va)) p2)
    by exact (u_slot_mem_at P t mm rs (pt_base t) (vpn_idx 2 (svpn_of va)) p2 Hwf
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm1 : pt_slot_mem (u_state rs mm) (pt_addr1 p2 (svpn_of va)) p1)
    by exact (u_slot_mem_at P t mm rs (u_next_base p2) (vpn_idx 1 (svpn_of va)) p1 Hwf
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm0 : pt_slot_mem (u_state rs mm) (pt_addr0 p1 (svpn_of va))
                   (pte_set_ad w a0 d0))
    by exact (u_slot_mem_at P t mm rs (u_next_base p1) (vpn_idx 0 (svpn_of va)) _ Hwf
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown2 : bytes_owned mm (pt_addr2 t (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p2 Hwf (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown1 : bytes_owned mm (pt_addr1 p2 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ p1 Hwf (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown0 : bytes_owned mm (pt_addr0 p1 (svpn_of va)) 8 = true)
    by exact (u_slot_owned P t mm _ _ Hwf (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  (* the three read-only probes of [translateAddr]'s front matter *)
  assert (Htm : exec (translationMode User) (u_state rs mm)
                = Some (Sv39, u_state rs mm))
    by exact (exec_translationMode_U_sv39 usatp (u_state rs mm) Lsxl Hsatp Hmode).
  assert (Htmg : goodb Du_r (translationMode User) (u_state rs mm) = true)
    by exact (goodb_translationMode_U Du_r usatp (u_state rs mm)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lsxl Hsatp Hmode).
  assert (Heff : exec (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs mm).(sregs)) User)
                   (u_state rs mm) = Some (User, u_state rs mm))
    by exact (exec_effectivePrivilege_mprv0 acc _ User (u_state rs mm) Lmprv).
  assert (Heffg : goodb Du_r (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs mm).(sregs)) User)
                    (u_state rs mm) = true)
    by exact (goodb_effectivePrivilege_mprv0 Du_r acc _ User (u_state rs mm) Lmprv).
  assert (Hssx : exec (is_shadow_stack_access acc) (u_state rs mm)
                 = Some (false, u_state rs mm))
    by exact (exec_is_shadow_stack_u_acc acc (u_state rs mm) Hacc).
  assert (Hssg : goodb Du_r (is_shadow_stack_access acc) (u_state rs mm) = true)
    by exact (goodb_is_shadow_stack_u_acc Du_r acc (u_state rs mm) Hacc).
  (* the PMA grants *)
  assert (Hpmar : pma_allows_pte_read
                    (register_lookup pma_regions (u_state rs mm).(sregs)))
    by exact (pma_allows_all_pte_read _ Hall).
  assert (Hpmaw : pma_allows_pte_write
                    (register_lookup pma_regions (u_state rs mm).(sregs)))
    by exact (Hpmaw_of _ Hall).
  (* the leaf's permission check and the three validity tests, certified *)
  assert (Hgchk : forall (a d : mword 1) (mxr do_sum : bool)
                    (Db : register -> bool) (s0 : mstate),
            goodb Db (check_PTE_permission acc User mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true).
  { intros a d mxr do_sum Db s0.
    exact (goodb_check_PTE_permission_u acc (pte_set_ad w a d) mxr do_sum Db s0
             Hacc (Hleaf a d mxr do_sum)). }
  assert (Hg2 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                        (ext_bits_of_PTE p2)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p2 Db s0 Hv2)).
  assert (Hg1 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                        (ext_bits_of_PTE p1)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p1 Db s0 Hv1)).
  assert (Hg0 : forall (a d : mword 1) (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true)
    by (intros a d Db s0;
        exact (goodb_pte_is_invalid_valid _ Db s0 (proj1 (Hvar a d)))).
  (* THE TRANSLATION, exec side and certificate side *)
  destruct (KptTree.ptree_translateAddr_cases acc User
              (ud_root P) va w (u_walk_pa w va) usatp t (register_lookup tlb rs)
              p2 p1 a0 d0 (u_state rs mm)
              Hleaf Hcanon eq_refl (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
              Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
              Hmisa Lmenv Hhtif Lcp Htm Heff Hssx Hsatp Hppn Hasid eq_refl
              HA Hord HRp HWp Hcovp Hpmar Hpmaw)
    as (sf & Htr & Harms).
  assert (Htrg : goodmb Du_r Du_w (translateAddr (Virtaddr va) acc)
                   (u_state rs mm) mm = true).
  { apply (goodmb_ptree_translateAddr Du_r Du_w acc User
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (ud_root P) t va w (u_walk_pa w va) usatp (register_lookup tlb rs)
             p2 p1 a0 d0 (u_state rs mm) mm
             Hleaf Hgchk Hcanon eq_refl
             (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
             Hbase Hmaps Htlbok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
             Hmisa Lmenv Hhtif Lcp Htm Htmg Heff Heffg Hssx Hssg
             Hsatp Hppn Hasid eq_refl HA Hord HRp HWp Hcovp Hpmar Hpmaw). }
  (* WHERE THE TRANSLATION LANDED: the three arms, each with its tree, its
     file and its [u_mem_step].  Nothing after this point looks at which. *)
  assert (Hland : exists (rs' : regstate) (mm' : pamap) (t' : ptree),
            sf = u_state rs' mm' /\
            (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
            tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
            u_mem_step P t t' mm mm').
  { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
    - exists rs, mm, t. split_and!;
        [ reflexivity | left; reflexivity | exact Htlbok
        | exact (u_mem_step_refl P t mm Hwf) ].
    - eexists _, mm, t. split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rs)
                 (svpn_of va) p2 p1 _ Hmaps Htlbok).
      + exact (u_mem_step_refl P t mm Hwf).
    - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w a0 d0 a1 d1).
      assert (Hv' : pte_valid (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hl' : pte_leaf (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hspec' : upt_tree_spec (ud_root P) (ud_tfp P) (ud_um P)
                (ptree_set_leaf t (svpn_of va)
                   (pte_set_ad (pte_set_ad w a0 d0) a1 d1))).
      { rewrite Habs.
        exact (upt_tree_spec_set_leaf (ud_root P) (ud_tfp P) (ud_um P) t
                 (svpn_of va) w p2 p1 a0 d0 a1 d1 Hwfm Hspec
                 (or_intror (or_intror Hl)) Hmaps). }
      eexists _, _,
        (ptree_set_leaf t (svpn_of va) (pte_set_ad (pte_set_ad w a0 d0) a1 d1)).
      split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0)
                 (ptree_set_leaf t (svpn_of va)
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                 (register_lookup tlb rs) (svpn_of va) p2 p1 _
                 (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                    (pte_set_ad w a0 d0) _ Hmaps Hv' Hl' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rs)
                    (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok)).
      + exact (u_mem_step_writeback P t mm (svpn_of va) p2 p1
                 (pte_set_ad w a0 d0) _ Hwf Hmaps Hspec'). }
  destruct Hland as (rs' & mm' & t' & Hsf & Hfile & Htlbok' & Hstep).
  rewrite Hsf in Htr.
  exists rs', mm', t'. split_and!.
  - exact Htr.
  - exact Htrg.
  - exact Hfile.
  - exact Htlbok'.
  - exact Hstep.
  - exact (u_data_cfg_tlb rs rs' Hfile Hcfg).
  - exact (u_exec_pins_tlb P t t' rs rs' Hfile Htlbok' Hpins0).
  - exact (u_mem_step_wf P t t' mm mm' Hwf Hstep).
Qed.

(* ===================================================================== *)
(* 5. WHAT A DATA STORE DOES TO THE OWNED MAP.                            *)
(*                                                                       *)
(* [UserFetchCert] section 4 is the PTE-side absorption (writing the leaf *)
(* slot IS setting the leaf).  This is the other half: writing a MAPPED   *)
(* page's bytes moves only the data half of [mm], at the same domain, so  *)
(* it is a [u_mem_step] at the SAME tree.  (FOLD BACK into [UserBytes.v]  *)
(* beside [u_mem_step].)                                                  *)
(* ===================================================================== *)

Lemma foldr_ins_union_r (A B : pamap) (a : Arch.pa) {wd : N} (v : bv wd)
    (js : list nat) :
  (forall j : nat, j ∈ js -> A !! pa_add a j = None) ->
  foldr (fun j acc => <[pa_add a j := nth_byte v j]> acc) (A ∪ B) js
  = A ∪ foldr (fun j acc => <[pa_add a j := nth_byte v j]> acc) B js.
Proof.
  induction js as [| j js IH]; cbn [foldr]; intros HA; [reflexivity |].
  rewrite (IH (fun j' Hj' => HA j' (elem_of_list_further j' j js Hj'))).
  apply insert_union_r. exact (HA j (elem_of_list_here j js)).
Qed.

Lemma write_bytes_union_r (A B : pamap) (a : Arch.pa) (n : N) {wd : N} (v : bv wd) :
  (forall j : nat, (N.of_nat j < n)%N -> A !! pa_add a j = None) ->
  write_bytes (A ∪ B) a n v = A ∪ write_bytes B a n v.
Proof.
  intros HA. unfold write_bytes. apply foldr_ins_union_r.
  intros j Hj. apply elem_of_seq in Hj. apply HA. lia.
Qed.

(* the domain of a write is the map's own, stated over [is_Some] and NOT
   over [dom]: naming [gset Arch.pa] here re-elaborates the key type's
   [Countable] instance (UserBytes section 3b's trap), and the two [dom]s
   then fail to rewrite into one another.  For the SAME reason the [<[_]>]
   equations are applied as CONCRETE instances rather than rewritten with:
   [write_bytes]'s inserts carry [RiscvModelBytes]' [bv_countable Arch.pa],
   which is not the one this file's typeclass search finds, so a bare
   [rewrite lookup_insert] reports "found no subterm" on a goal that prints
   as its own left-hand side. *)
Lemma foldr_ins_is_Some_rev (a : Arch.pa) {wd : N} (v : bv wd) (js : list nat)
    (m : pamap) (x : Arch.pa) :
  (forall j : nat, j ∈ js -> is_Some (m !! pa_add a j)) ->
  is_Some (foldr (fun j acc => <[pa_add a j := nth_byte v j]> acc) m js !! x) ->
  is_Some (m !! x).
Proof.
  induction js as [| j js IH]; cbn [foldr]; intros Hj Hx; [ exact Hx |].
  destruct (decide (x = pa_add a j)) as [Heq | Hne].
  - subst x. exact (Hj j (elem_of_list_here j js)).
  - apply (IH (fun j' Hj' => Hj j' (elem_of_list_further j' j js Hj'))).
    assert (Hne' : pa_add a j <> x) by (intros H; apply Hne; by rewrite H).
    assert (Heq : <[pa_add a j := nth_byte v j]>
                    (foldr (fun j0 acc => <[pa_add a j0 := nth_byte v j0]> acc) m js)
                    !! x
                  = foldr (fun j0 acc => <[pa_add a j0 := nth_byte v j0]> acc) m js !! x)
      by (apply lookup_insert_ne; exact Hne').
    rewrite Heq in Hx. exact Hx.
Qed.

Lemma write_bytes_is_Some_iff (m : pamap) (a : Arch.pa) (n : N) {wd : N}
    (v : bv wd) (x : Arch.pa) :
  (forall j : nat, (N.of_nat j < n)%N -> is_Some (m !! pa_add a j)) ->
  is_Some (write_bytes m a n v !! x) <-> is_Some (m !! x).
Proof.
  intros Hj. unfold write_bytes. split.
  - apply foldr_ins_is_Some_rev.
    intros j Hin. apply elem_of_seq in Hin. apply Hj. lia.
  - apply foldr_ins_is_Some.
Qed.

Lemma u_mem_step_store (P : uptd) (t t' : ptree) (mm mm' : pamap)
    (k : Z) (w va : mword 64) (v : mword (8 * k)) :
  0 < k -> in_one_page va k ->
  ud_um P !! svpn_of va = Some w ->
  u_mem_wf P t mm ->
  u_mem_step P t t' mm mm' ->
  u_mem_step P t t' mm (write_bytes mm' (u_walk_pa w va) (Z.to_N k) v).
Proof.
  intros Hk Hp Hl Hwf Hstep.
  pose proof Hwf as (mdd & _ & _ & _ & _ & _ & Hcov & _).
  destruct Hstep as (Hshape & Hspec' & md' & Hdj' & Hmm' & Hdm').
  (* the whole window is a DATA address, hence in [md'] and not in the tree *)
  assert (Hin : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
            is_Some (md' !! pa_add (u_walk_pa w va) j)).
  { intros j Hj.
    rewrite (u_walk_pa_window_page w va k j Hk Hp ltac:(lia)).
    apply (proj1 (Hdm' _)).
    exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
  assert (Hnt : forall j : nat, (N.of_nat j < Z.to_N k)%N ->
            ptree_bytes 2 t' !! pa_add (u_walk_pa w va) j = None).
  { intros j Hj.
    destruct (ptree_bytes 2 t' !! pa_add (u_walk_pa w va) j) as [c |] eqn:Hc;
      [ exfalso | reflexivity ].
    destruct (Hin j Hj) as (b & Hb).
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t') md') Hdj' _ c b Hc Hb). }
  pose proof (fun x => write_bytes_is_Some_iff md' (u_walk_pa w va) (Z.to_N k) v x Hin)
    as Hiff.
  split_and!; [ exact Hshape | exact Hspec' |].
  exists (write_bytes md' (u_walk_pa w va) (Z.to_N k) v).
  split_and!.
  - apply map_disjoint_spec. intros i x y Hx Hy.
    destruct (proj1 (Hiff i) (mk_is_Some _ _ Hy)) as (b & Hb).
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t') md') Hdj' i x b Hx Hb).
  - rewrite Hmm'. apply write_bytes_union_r. exact Hnt.
  - intros a. rewrite (Hdm' a). symmetry. exact (Hiff a).
Qed.

(* ===================================================================== *)
(* 6. [u_store_pure] -- THE PURE U-MODE DATA STORE.                       *)
(*                                                                       *)
(* [UserMemPt.user_pt_store_data_g]'s twin.  Three model calls, each with *)
(* its certificate: the walk, the effective-address ANNOUNCEMENT (the     *)
(* vmem layer runs it separately, and it repeats the PMA/PMP check), and  *)
(* the value write.  The write lands on [write_bytes mm' pa (Z.to_N k) v] *)
(* -- and section 5 says THAT map is a [u_mem_step] too, which is what    *)
(* re-seals [user_pt_inv] once the arm is done.                          *)
(* ===================================================================== *)

Lemma u_store_pure (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) (v : mword (8 * k)) :
  0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
  (forall (addr : mword 64) (dat : mword (8 * k)) (s : mstate),
     dev_addr addr = false ->
     exec (write_ram rv64d_types.Write_plain (Physaddr addr) k dat tt) s
       = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) dat)
                       s.(mdev))) ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (Store Data) w ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (Store Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Store Data))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data) PBMT_PMA
            false false false) (u_state rs' mm') = Some (Ok tt, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data)
            PBMT_PMA false false false) (u_state rs' mm') mm' = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data) PBMT_PMA
            false false false) (u_state rs' mm')
      = Some (Ok true, u_state rs' (write_bytes mm' (u_walk_pa w va) (Z.to_N k) v)) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data)
            PBMT_PMA false false false) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_mem_step P t t' mm (write_bytes mm' (u_walk_pa w va) (Z.to_N k) v).
Proof.
  intros Hk Hk8 Hkdvd Huintk Hwrite_plain Hl Hleaf Hal Hcanon Hcfg Hpins Hwf.
  destruct (u_walk_pure (Store Data) P t mm rs w va
              (or_intror (or_intror (or_introl eq_refl))) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  set (pa := u_walk_pa w va).
  set (s' := u_state rs' mm').
  destruct (u_data_ram P t' mm' k w va Hk Hkdvd Hal Hwf' Hl) as (Hram0 & Hramk).
  assert (Hdev : dev_addr pa = false)
    by exact (u_mem_wf_not_dev_data P t' mm' w va Hwf' Hl).
  assert (Hown : bytes_owned mm' pa (Z.to_N k) = true)
    by exact (u_mem_wf_owned_data P t' mm' k w va Hk Hkdvd Hal Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & HW & _ & Hcovp).
  destruct (pma_all_ram Hall pa k
              (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                 Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
    as (region & Hpmam & _ & _ & Hwrb).
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
            (uint pa) (uint (to_bits 64 k)) = PMP_Match)
    by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8 Huintk
                ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
  assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
    by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
  assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
  assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
  assert (Hwp : forall d : mword (8 * k),
            exec (write_ram rv64d_types.Write_plain (Physaddr pa) k d tt) s'
            = Some (true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N k) d)
                            s'.(mdev)))
    by (intro d; exact (Hwrite_plain pa d s' Hdev)).
  (* the effective-address announcement: the PMA and the PMP check, twice *)
  assert (Hcpe : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                         (Physaddr pa) k false) s' = Some (Ok pma_ok_aligned, s')).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_store_g k pa PBMT_PMA region s'
                  Hpmam Halign (proj1 Hwrb))).
    cbn match. apply exec_returnM. }
  assert (Hcpg : goodmb Du_r Du_w (check_pma_with_pmp_priority (Store Data) PBMT_PMA
                          User (Physaddr pa) k false) s' mm' = true)
    by exact (goodmb_check_pma_with_pmp_priority Du_r Du_w _ _ User _ _ false _ s' mm'
                (goodmb_pmaCheck_ram_store_g Du_r Du_w k pa PBMT_PMA region s' mm'
                   ltac:(vm_compute; reflexivity) Hpmam Halign (proj1 Hwrb))
                (exec_pmaCheck_ram_store_g k pa PBMT_PMA region s'
                   Hpmam Halign (proj1 Hwrb))).
  assert (Heffe : exec (effectivePrivilege (Store Data)
                          (register_lookup mstatus rs')
                          (register_lookup cur_privilege rs')) s'
                  = Some (User, s')).
  { rewrite Lcp.
    exact (exec_effectivePrivilege_mprv0 (Store Data)
             (register_lookup mstatus rs') User s' Lmprv). }
  assert (Hea : exec (mem_write_ea (Physaddr pa) k (Store Data) PBMT_PMA
                        false false false) s' = Some (Ok tt, s'))
    by exact (exec_mem_write_ea_g k pa (Store Data) PBMT_PMA User s'
                Heffe
                Hcpe
                (exec_pmpCheck_user_grant_store pa k s' HA Hord Hrange HW)).
  assert (Heag : goodmb Du_r Du_w (mem_write_ea (Physaddr pa) k (Store Data)
                          PBMT_PMA false false false) s' mm' = true)
    by exact (goodmb_mem_write_ea_g Du_r Du_w k pa (Store Data) PBMT_PMA User s' mm'
                Hk ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                   (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                   s' mm' Lmprv)
                Heffe Hcpg Hcpe
                (goodmb_pmpCheck_user_grant_store Du_r Du_w pa k s' mm'
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   HA Hord Hrange HW)
                (exec_pmpCheck_user_grant_store pa k s' HA Hord Hrange HW)).
  (* the value write, exec side and certificate side *)
  assert (Hwr : exec (mem_write_value (Physaddr pa) k v (Store Data) PBMT_PMA
                        false false false) s'
                = Some (Ok true, u_state rs' (write_bytes mm' pa (Z.to_N k) v)))
    by exact (exec_mem_write_value_U k Hk Hwrite_plain PBMT_PMA pa region v s'
                HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig
                (within_htif_writable_false pa k s' Hhtif) Hdev Lmprv Lcp).
  assert (Hchke : exec (checked_mem_write (Physaddr pa) k v (Store Data) PBMT_PMA
                          User tt false false false) s'
                  = Some (Ok true, MState s'.(sregs)
                            (write_bytes s'.(mem) pa (Z.to_N k) v) s'.(mdev)))
    by exact (exec_checked_mem_write_ram_U k Hk Hwrite_plain PBMT_PMA pa region v s'
                HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig
                (within_htif_writable_false pa k s' Hhtif) Hdev).
  assert (Hchkg : goodmb Du_r Du_w (checked_mem_write (Physaddr pa) k v (Store Data)
                           PBMT_PMA User tt false false false) s' mm' = true)
    by exact (goodmb_checked_mem_write_ram_U Du_r Du_w k Hk PBMT_PMA pa region v s' mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig Hhtif
                Hdev Hown Hwp).
  assert (Hwrg : goodmb Du_r Du_w (mem_write_value (Physaddr pa) k v (Store Data)
                          PBMT_PMA false false false) s' mm' = true)
    by exact (goodmb_mem_write_value_U Du_r Du_w k PBMT_PMA pa v s' mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lmprv Lcp Hchkg Hchke).
  exists rs', mm', t'. split_and!;
    [ exact Htr | exact Htrg | exact Hea | exact Heag | exact Hwr | exact Hwrg
    | exact Hfile | exact Htlbok' | exact Hstep
    | exact (u_mem_step_store P t t' mm mm' k w va v Hk
               (in_one_page_aligned va k Hk Hkdvd Hal) Hl Hwf Hstep) ].
Qed.

(* ===================================================================== *)
(* 7. THE PAGE WINDOW, PURE -- and the composers at an access of ANY       *)
(*    ALIGNMENT that stays inside ONE page.                                *)
(*                                                                       *)
(* A LOAD/STORE's effective address is [rs1 + imm], an arbitrary word, so  *)
(* the arms cannot assume alignment.  [UserMemMis.in_one_page] is what the *)
(* ownership side actually used alignment FOR, and P4a's                   *)
(* [exec_mem_read_mis_U] / [exec_mem_write_ea_mis_U] /                     *)
(* [exec_mem_write_value_mis_U] (and their [goodmb] twins) already run     *)
(* [checked_mem_*]'s split loop N times instead of once.  So the           *)
(* in-one-page composers are the PRIMARY ones and the aligned pair is a    *)
(* corollary through [UserMemMis.in_one_page_aligned].                     *)
(*                                                                       *)
(* [UserMemMis.udata_window_facts]' pure content.  Note the read composer  *)
(* needs NO width-typed [read_ram] brick: it sources the value from the    *)
(* per-chunk [exec_read_ram_plain_gen], so [u_load_pure_page] has neither  *)
(* an [Hread_plain] nor a [uint (to_bits 64 k) = k] premise.               *)
(* ===================================================================== *)

Lemma u_page_window (P : uptd) (t : ptree) (mm : pamap) (k : Z) (w va : mword 64) :
  0 < k -> in_one_page va k ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  forall j : nat, (j < Z.to_nat k)%nat ->
    is_Some (mm !! pa_add (u_walk_pa w va) j) /\
    addr_is_ram (pa_add (u_walk_pa w va) j) /\
    pa_add (u_walk_pa w va) j ∈ ud_data P.
Proof.
  intros Hk Hp Hwf Hl j Hj.
  pose proof Hwf as (md & _ & _ & Hmm & Hdm & Hram & Hcov & _).
  assert (Hd : pa_add (u_walk_pa w va) j ∈ ud_data P).
  { rewrite (u_walk_pa_window_page w va k j Hk Hp Hj).
    exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
  assert (Hs : is_Some (mm !! pa_add (u_walk_pa w va) j)).
  { rewrite Hmm. apply lookup_union_is_Some. right.
    exact (proj1 (Hdm _) Hd). }
  split_and!; [ exact Hs | apply Hram, elem_of_dom, Hs | exact Hd ].
Qed.

Lemma u_page_owned (P : uptd) (t : ptree) (mm : pamap) (k : Z) (w va : mword 64) :
  0 < k -> in_one_page va k ->
  u_mem_wf P t mm ->
  ud_um P !! svpn_of va = Some w ->
  bytes_owned mm (u_walk_pa w va) (Z.to_N k) = true.
Proof.
  intros Hk Hp Hwf Hl. apply bytes_owned_of_dom. intros j Hj.
  apply elem_of_dom.
  exact (proj1 (u_page_window P t mm k w va Hk Hp Hwf Hl j ltac:(lia))).
Qed.

Lemma u_load_pure_page (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) :
  0 < k -> k <= 8 -> in_one_page va k ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (Load Data) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (dv : mword (8 * k)) (rs' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (Load Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Load Data))
      (u_state rs mm) mm = true /\
    exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k
            false false false) (u_state rs' mm') = Some (Ok dv, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k
            false false false) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_walk_pure (Load Data) P t mm rs w va
              (or_intror (or_introl eq_refl)) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof (u_page_window P t' mm' k w va Hk Hp Hwf' Hl) as Hwin.
  assert (Hown : bytes_owned mm' (u_walk_pa w va) (Z.to_N k) = true)
    by exact (u_page_owned P t' mm' k w va Hk Hp Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & _ & HR & Hcovp).
  destruct (exec_mem_read_mis_U (u_walk_pa w va) k (u_state rs' mm') Hk Hk8
              HA Hord Hcovp Hhtif Hall
              (fun j Hj => proj1 (proj2 (Hwin j Hj)))
              Lmprv Lcp HR (fun j Hj => proj1 (Hwin j Hj)))
    as (dv & Hmr).
  exists dv, rs', mm', t'. split_and!;
    [ exact Htr | exact Htrg | exact Hmr | | exact Hfile | exact Htlbok' | exact Hstep ].
  exact (goodmb_mem_read_mis_U (u_walk_pa w va) k (u_state rs' mm') Hk Hk8
           HA Hord Hcovp Hhtif Hall (fun j Hj => proj1 (proj2 (Hwin j Hj)))
           Du_r Du_w mm'
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           Lmprv Lcp HR (fun j Hj => proj1 (Hwin j Hj)) Hown).
Qed.

(* [u_load_pure] -- the ALIGNED corollary.  Alignment enters only through
   [in_one_page]; the model's split loop is what makes the general case no
   harder, so this is one application and NOT a second development. *)
Lemma u_load_pure (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) :
  0 < k -> k <= 8 -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (Load Data) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (dv : mword (8 * k)) (rs' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (Load Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Load Data))
      (u_state rs mm) mm = true /\
    exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k
            false false false) (u_state rs' mm') = Some (Ok dv, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k
            false false false) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm'.
Proof.
  intros Hk Hk8 Hkdvd Hal Hl Hleaf Hcanon Hcfg Hpins Hwf.
  exact (u_load_pure_page P t mm rs k w va Hk Hk8
           (in_one_page_aligned va k Hk Hkdvd Hal) Hl Hleaf Hcanon Hcfg Hpins Hwf).
Qed.

(* --------------------------------------------------------------------- *)
(* 7b. THE SPLIT WRITE'S POST MAP IS STILL A [u_mem_step].                 *)
(*                                                                       *)
(* A misaligned in-page store writes N chunk windows, so the post state is *)
(* [UserMemMis.wchain] rather than one [write_bytes].  Section 5's         *)
(* absorption generalises to ANY window that lies in [ud_data P], and the  *)
(* chain is then N applications of it.                                     *)
(* --------------------------------------------------------------------- *)

Lemma u_mem_step_write_in (P : uptd) (t t' : ptree) (mm mm2 : pamap)
    (a : Arch.pa) (n : N) {wd : N} (v : bv wd) :
  (forall j : nat, (N.of_nat j < n)%N -> pa_add a j ∈ ud_data P) ->
  u_mem_step P t t' mm mm2 ->
  u_mem_step P t t' mm (write_bytes mm2 a n v).
Proof.
  intros Hd (Hshape & Hspec' & md' & Hdj' & Hmm' & Hdm').
  assert (Hin : forall j : nat, (N.of_nat j < n)%N -> is_Some (md' !! pa_add a j))
    by (intros j Hj; exact (proj1 (Hdm' _) (Hd j Hj))).
  assert (Hnt : forall j : nat, (N.of_nat j < n)%N ->
            ptree_bytes 2 t' !! pa_add a j = None).
  { intros j Hj.
    destruct (ptree_bytes 2 t' !! pa_add a j) as [c |] eqn:Hc;
      [ exfalso | reflexivity ].
    destruct (Hin j Hj) as (b & Hb).
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t') md') Hdj' _ c b Hc Hb). }
  pose proof (fun x => write_bytes_is_Some_iff md' a n v x Hin) as Hiff.
  split_and!; [ exact Hshape | exact Hspec' |].
  exists (write_bytes md' a n v). split_and!.
  - apply map_disjoint_spec. intros i x y Hx Hy.
    destruct (proj1 (Hiff i) (mk_is_Some _ _ Hy)) as (b & Hb).
    exact (proj1 (map_disjoint_spec (ptree_bytes 2 t') md') Hdj' i x b Hx Hb).
  - rewrite Hmm'. apply write_bytes_union_r. exact Hnt.
  - intros x. rewrite (Hdm' x). symmetry. exact (Hiff x).
Qed.

Lemma u_mem_step_wchain (P : uptd) (t t' : ptree) (mm : pamap)
    (pa : mword 64) (W bytes : Z) (N : nat) (sg : mstate) (dat : mword (8 * W)) :
  0 < bytes -> Z.of_nat N * bytes = W ->
  (forall j : nat, (j < Z.to_nat W)%nat -> pa_add pa j ∈ ud_data P) ->
  (forall j : nat, (j < Z.to_nat W)%nat -> addr_is_ram (pa_add pa j)) ->
  u_mem_step P t t' mm sg.(mem) ->
  forall k : nat, (k <= N)%nat ->
    u_mem_step P t t' mm (wchain pa W sg bytes dat k).(mem).
Proof.
  intros Hb Hw Hdata Hram Hstep.
  pose proof (chunk_dev_false pa W bytes N Hb Hw Hram) as Hdev.
  assert (HbN : Z.to_nat W = (N * Z.to_nat bytes)%nat).
  { rewrite <- Hw. rewrite Z2Nat.inj_mul; [| lia | lia]. rewrite Nat2Z.id. reflexivity. }
  induction k as [| k IH]; intro Hk; [ exact Hstep |].
  destruct (exec_write_ram_plain_gen bytes (add_vec_int pa (Z.of_nat k * bytes))
              (wvc W bytes dat k) (wchain pa W sg bytes dat k) (Hdev k ltac:(lia)))
    as (nn & v & Hwr).
  assert (Hstepk : wchain pa W sg bytes dat (S k)
            = MState (wchain pa W sg bytes dat k).(sregs)
                (write_bytes (wchain pa W sg bytes dat k).(mem)
                   (add_vec_int pa (Z.of_nat k * bytes)) (Z.to_N bytes) v)
                (wchain pa W sg bytes dat k).(mdev))
    by (cbn [wchain]; rewrite Hwr; reflexivity).
  rewrite Hstepk. cbn [mem].
  apply u_mem_step_write_in; [ | exact (IH ltac:(lia)) ].
  intros j Hj.
  rewrite (pa_add_chunk pa k bytes ltac:(lia)). rewrite pa_add_bump2.
  apply Hdata. rewrite HbN. nia.
Qed.

Lemma u_store_pure_page (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) (v : mword (8 * k)) :
  0 < k -> k <= 8 -> in_one_page va k ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (Store Data) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs' : regstate) (mm' mm2 : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (Store Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Store Data))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data) PBMT_PMA
            false false false) (u_state rs' mm') = Some (Ok tt, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w va)) k (Store Data)
            PBMT_PMA false false false) (u_state rs' mm') mm' = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data) PBMT_PMA
            false false false) (u_state rs' mm') = Some (Ok true, u_state rs' mm2) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data)
            PBMT_PMA false false false) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_mem_step P t t' mm mm2.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_walk_pure (Store Data) P t mm rs w va
              (or_intror (or_intror (or_introl eq_refl))) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  set (pa := u_walk_pa w va).
  set (s' := u_state rs' mm').
  pose proof (u_page_window P t' mm' k w va Hk Hp Hwf' Hl) as Hwin.
  assert (Hown : bytes_owned mm' pa (Z.to_N k) = true)
    by exact (u_page_owned P t' mm' k w va Hk Hp Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & HW & _ & Hcovp).
  assert (Hea : exec (mem_write_ea (Physaddr pa) k (Store Data) PBMT_PMA
                        false false false) s' = Some (Ok tt, s'))
    by exact (exec_mem_write_ea_mis_U pa k s' Hk Hk8 HA Hord Hcovp Hall
                (fun j Hj => proj1 (proj2 (Hwin j Hj))) Lmprv Lcp HW).
  assert (Heag : goodmb Du_r Du_w (mem_write_ea (Physaddr pa) k (Store Data)
                          PBMT_PMA false false false) s' mm' = true)
    by exact (goodmb_mem_write_ea_mis_U pa k s' Hk Hk8 HA Hord Hcovp Hall
                (fun j Hj => proj1 (proj2 (Hwin j Hj))) Du_r Du_w mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Lmprv Lcp HW).
  destruct (exec_mem_write_value_mis_U pa k s' Hk Hk8 HA Hord Hcovp Hhtif Hall
              (fun j Hj => proj1 (proj2 (Hwin j Hj))) v Lmprv Lcp HW)
    as (bytes & N & Hbpos & Hwidth & HN & Hwv).
  assert (Hwrg : goodmb Du_r Du_w (mem_write_value (Physaddr pa) k v (Store Data)
                          PBMT_PMA false false false) s' mm' = true)
    by exact (goodmb_mem_write_value_mis_U pa k s' Hk Hk8 HA Hord Hcovp Hhtif Hall
                (fun j Hj => proj1 (proj2 (Hwin j Hj))) Du_r Du_w v mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lmprv Lcp HW Hown).
  (* the split write's post state: same file, same devices, N chunk windows *)
  destruct (wchain_regs_gen pa k s' bytes N v
              (chunk_dev_false pa k bytes N Hbpos Hwidth
                 (fun j Hj => proj1 (proj2 (Hwin j Hj)))) N ltac:(lia)) as (Hcs & Hcd).
  assert (Heta : forall x : mstate, x = MState x.(sregs) x.(mem) x.(mdev))
    by (intros [a b c]; reflexivity).
  assert (Hpost : wchain pa k s' bytes v N
                  = u_state rs' (wchain pa k s' bytes v N).(mem)).
  { rewrite (Heta (wchain pa k s' bytes v N)) at 1.
    rewrite Hcs. rewrite Hcd. reflexivity. }
  exists rs', mm', (wchain pa k s' bytes v N).(mem), t'. split_and!;
    [ exact Htr | exact Htrg | exact Hea | exact Heag
    | rewrite <- Hpost; exact Hwv | exact Hwrg
    | exact Hfile | exact Htlbok' | exact Hstep |].
  exact (u_mem_step_wchain P t t' mm pa k bytes N s' v Hbpos Hwidth
           (fun j Hj => proj2 (proj2 (Hwin j Hj)))
           (fun j Hj => proj1 (proj2 (Hwin j Hj))) Hstep N ltac:(lia)).
Qed.

(* ===================================================================== *)
(* 8. TWO ACCESSES IN A ROW -- what a PAGE-STRADDLING load/store is.       *)
(*                                                                       *)
(* The model splits a straddling access into two translate-and-access     *)
(* steps ([UserMemMis] section g), so a composer must run the WALK TWICE,  *)
(* at [va] and at the next page's base, and thread the two [u_mem_step]s   *)
(* through each other.  Two things had to be added for that:               *)
(*                                                                       *)
(*  - [u_mem_step] TRANSITIVITY, which [UserBytes] does not have.  The     *)
(*    only missing ingredient is transitivity of [pt_same_shape 2]; the    *)
(*    other three conjuncts come from the second step alone.  (FOLD BACK   *)
(*    into [UserBytes.v] beside [u_mem_step_refl].)                        *)
(*                                                                       *)
(*  - A COMPOSABLE landing fact.  The one-walk composers say the landing   *)
(*    file is [rs] or ONE [register_set tlb], and that shape does NOT      *)
(*    compose: collapsing [register_set tlb v2 (register_set tlb v1 rs)]   *)
(*    to [register_set tlb v2 rs] is a pointwise equality of the record's  *)
(*    field FUNCTION, i.e. it needs functional extensionality, which is an *)
(*    axiom this development does not take.  [u_tlb_only] is what every    *)
(*    consumer actually uses the disjunction FOR (transporting the ambient *)
(*    pins by [irrelevant_register_set]), it is implied by it, and it is   *)
(*    transitive.  Two-walk composers conclude [u_tlb_only], not the       *)
(*    disjunction.                                                        *)
(* ===================================================================== *)

Definition u_tlb_only (rs rs' : regstate) : Prop :=
  forall r : register, register_beq r (tlb : register) = false ->
    register_lookup r rs' = register_lookup r rs.

Lemma u_tlb_only_land (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) -> u_tlb_only rs rs'.
Proof. exact (u_tlb_irrel rs rs'). Qed.

Lemma u_tlb_only_refl (rs : regstate) : u_tlb_only rs rs.
Proof. intros r _. reflexivity. Qed.

Lemma u_tlb_only_trans (rs rs1 rs2 : regstate) :
  u_tlb_only rs rs1 -> u_tlb_only rs1 rs2 -> u_tlb_only rs rs2.
Proof. intros H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma u_data_cfg_only (rs rs' : regstate) :
  u_tlb_only rs rs' -> u_data_cfg rs -> u_data_cfg rs'.
Proof.
  intros Tr (Lcp & Lms & Lmenv). split_and!;
    [ rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp
    | rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Lms
    | rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv ].
Qed.

Lemma u_exec_pins_only (P : uptd) (t t' : ptree) (rs rs' : regstate) :
  u_tlb_only rs rs' ->
  tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') ->
  u_exec_pins P t rs -> u_exec_pins P t' rs'.
Proof.
  intros Tr Htlbok' (Hhw & Hcfgp & Hpt & _).
  destruct Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  destruct Hcfgp as (Hmst0 & Hsst0).
  destruct Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HX & HW & HR & Hcovp).
  split_and!; [ | | | exact Htlbok' ].
  - split_and!;
      [ rewrite (Tr misa ltac:(vm_compute; reflexivity)); exact Hmisa
      | rewrite (Tr mseccfg ltac:(vm_compute; reflexivity)); exact Hmseccfg
      | rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)); exact Hsenv
      | rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif
      | rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall
      | rewrite (Tr elp ltac:(vm_compute; reflexivity)); exact Help ].
  - split_and!;
      [ rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)); exact Hmst0
      | rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)); exact Hsst0 ].
  - split_and!;
      [ exists usatp; split;
          [ exact Hsatpok
          | rewrite (Tr satp ltac:(vm_compute; reflexivity)); exact Hsatp ]
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW
      | rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR
      | rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp ].
Qed.

Lemma pt_same_shape_trans (lvl : nat) (t1 t2 t3 : ptree) :
  pt_same_shape lvl t1 t2 -> pt_same_shape lvl t2 t3 -> pt_same_shape lvl t1 t3.
Proof.
  revert t1 t2 t3. induction lvl as [| lvl IH]; intros t1 t2 t3 [Hb1 Hk1] [Hb2 Hk2].
  - split; [ by rewrite Hb1 | exact I ].
  - split; [ by rewrite Hb1 |]. intros i.
    specialize (Hk1 i). specialize (Hk2 i).
    destruct (pt_kids t1 i) as [c1|]; destruct (pt_kids t2 i) as [c2|];
      destruct (pt_kids t3 i) as [c3|]; try contradiction; try exact I.
    exact (IH c1 c2 c3 Hk1 Hk2).
Qed.

Lemma u_mem_step_trans (P : uptd) (t1 t2 t3 : ptree) (mm1 mm2 mm3 : pamap) :
  u_mem_step P t1 t2 mm1 mm2 -> u_mem_step P t2 t3 mm2 mm3 ->
  u_mem_step P t1 t3 mm1 mm3.
Proof.
  intros (Hs1 & _ & _) (Hs2 & Hspec & md & Hrest).
  split_and!; [ exact (pt_same_shape_trans 2 t1 t2 t3 Hs1 Hs2) | exact Hspec |].
  exists md. exact Hrest.
Qed.
