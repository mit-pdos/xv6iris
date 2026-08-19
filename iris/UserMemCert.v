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
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
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
    u_mem_step P t t' mm mm' /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm'.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_walk_pure (Load Data) P t mm rs w va
              (or_intror (or_introl eq_refl)) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
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
    [ exact Htr | exact Htrg | exact Hmr | | exact Hfile | exact Htlbok' | exact Hstep
    | exact Hcfg0 | exact Hpins0 | exact Hwf' ].
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
  destruct (u_load_pure_page P t mm rs k w va Hk Hk8
              (in_one_page_aligned va k Hk Hkdvd Hal) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (dv & rs' & mm' & t' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & _ & _).
  exists dv, rs', mm', t'. split_and!;
    [ exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 ].
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
    u_mem_step P t t' mm mm2 /\
    u_data_cfg rs' /\ u_exec_pins P t' rs'.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_walk_pure (Store Data) P t mm rs w va
              (or_intror (or_intror (or_introl eq_refl))) Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
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
    | exact Hfile | exact Htlbok' | exact Hstep | | exact Hcfg0 | exact Hpins0 ].
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

(* ===================================================================== *)
(* 9. THE PAGE-STRADDLING LOAD AND STORE.                                 *)
(*                                                                       *)
(* The model splits a straddling access in two and translates TWICE, so   *)
(* both pages must be MAPPED and the two walks' [u_mem_step]s compose.    *)
(* The general shape is "two in-one-page accesses in a row" -- stated as  *)
(* [u_load_pure_two] / [u_store_pure_two], which know nothing about page  *)
(* boundaries -- and the straddle itself is that at the geometry          *)
(* [UserMemMis.exec_split_on_page_boundary_straddle] computes.            *)
(*                                                                       *)
(* BOTH certificates are read back at the ORIGINAL map [mm], which is what *)
(* [UserMemMis.goodmb_vmem_read_addr_split2] / [_write_addr_split2] ask   *)
(* for: the first access's [u_mem_step] keeps the domain, so              *)
(* [HartMemRun.goodmb_dom] transports the second one.                     *)
(* ===================================================================== *)

(* the two read-only probes the vmem level runs before the split, pure *)
Lemma u_effectivePrivilege_pure (acc : MemoryAccessType mem_payload)
    (rs : regstate) (mm : pamap) :
  u_data_cfg rs ->
  exec (effectivePrivilege acc (register_lookup mstatus (u_state rs mm).(sregs))
          (register_lookup cur_privilege (u_state rs mm).(sregs))) (u_state rs mm)
    = Some (User, u_state rs mm).
Proof.
  intros (Lcp & (Lsxl & Lmprv & _) & _). cbn [u_state sregs].
  rewrite Lcp. exact (exec_effectivePrivilege_mprv0 acc _ User (u_state rs mm) Lmprv).
Qed.

Lemma u_goodmb_effectivePrivilege_pure (acc : MemoryAccessType mem_payload)
    (rs : regstate) (mm mb : pamap) :
  u_data_cfg rs ->
  goodmb Du_r Du_w (effectivePrivilege acc
          (register_lookup mstatus (u_state rs mm).(sregs))
          (register_lookup cur_privilege (u_state rs mm).(sregs))) (u_state rs mm) mb
    = true.
Proof.
  intros (Lcp & (Lsxl & Lmprv & _) & _).
  exact (goodmb_effectivePrivilege_mprv0 Du_r Du_w acc _ _ (u_state rs mm) mb Lmprv).
Qed.

Lemma u_translationMode_pure (P : uptd) (t : ptree) (rs : regstate) (mm : pamap) :
  u_data_cfg rs -> u_exec_pins P t rs ->
  exec (translationMode User) (u_state rs mm) = Some (Sv39, u_state rs mm).
Proof.
  intros (_ & (Lsxl & _) & _) (_ & _ & ((usatp & (Hmode & _) & Hsatp) & _) & _).
  exact (exec_translationMode_U_sv39 usatp (u_state rs mm) Lsxl Hsatp Hmode).
Qed.

Lemma u_goodmb_translationMode_pure (P : uptd) (t : ptree) (rs : regstate)
    (mm mb : pamap) :
  u_data_cfg rs -> u_exec_pins P t rs ->
  goodmb Du_r Du_w (translationMode User) (u_state rs mm) mb = true.
Proof.
  intros (_ & (Lsxl & _) & _) (_ & _ & ((usatp & (Hmode & _) & Hsatp) & _) & _).
  apply goodmb_of_goodb.
  exact (goodb_translationMode_U Du_r usatp (u_state rs mm)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           Lsxl Hsatp Hmode).
Qed.

(* --- the in-one-page [translate_and_read_value], pure --- *)
Lemma u_tarv_page (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
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
    exec (translate_and_read_value (Virtaddr va) k (Load Data) false false false)
      (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), dv), u_state rs' mm') /\
    goodmb Du_r Du_w
      (translate_and_read_value (Virtaddr va) k (Load Data) false false false)
      (u_state rs mm) mm = true /\
    u_tlb_only rs rs' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm'.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_load_pure_page P t mm rs k w va Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (dv & rs' & mm' & t' & Htr & Htrg & Hmr & Hmrg & Hfile & Htlbok' & Hstep
        & Hcfg' & Hpins' & Hwf').
  exists dv, rs', mm', t'. split_and!;
    [ exact (exec_translate_and_read_value_gen k va (u_walk_pa w va) (Load Data)
               false false false PBMT_PMA dv (u_state rs mm) (u_state rs' mm')
               (u_state rs' mm') Htr Hmr)
    | | exact (u_tlb_only_land rs rs' Hfile) | exact Htlbok' | exact Hstep
    | exact Hcfg' | exact Hpins' | exact Hwf' ].
  apply (goodmb_translate_and_read_value_gen Du_r Du_w k va (u_walk_pa w va)
           (Load Data) false false false PBMT_PMA dv (u_state rs mm) (u_state rs' mm')
           (u_state rs' mm') mm Htr Htrg Hmr).
  rewrite (goodmb_dom Du_r Du_w _ (u_state rs' mm') mm mm').
  - exact Hmrg.
  - symmetry. exact (u_mem_step_dom P t t' mm mm' Hwf Hstep).
Qed.

Lemma u_load_pure_two (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (p q : Z) (w1 w2 va : mword 64) :
  0 < p -> p <= 8 -> in_one_page va p ->
  0 < q -> q <= 8 -> in_one_page (add_vec_int va p) q ->
  ud_um P !! svpn_of va = Some w1 ->
  ud_um P !! svpn_of (add_vec_int va p) = Some w2 ->
  uleaf_ok (Load Data) w1 -> uleaf_ok (Load Data) w2 ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (v1 : mword (8 * p)) (v2 : mword (8 * q))
         (rs1 : regstate) (mm1 : pamap) (t1 : ptree)
         (rs2 : regstate) (mm2 : pamap) (t2 : ptree),
    exec (translate_and_read_value (Virtaddr va) p (Load Data) false false false)
      (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w1 va), v1), u_state rs1 mm1) /\
    goodmb Du_r Du_w
      (translate_and_read_value (Virtaddr va) p (Load Data) false false false)
      (u_state rs mm) mm = true /\
    exec (translate_and_read_value (Virtaddr (add_vec_int va p)) q (Load Data)
            false false false) (u_state rs1 mm1)
      = Some (Ok (Physaddr (u_walk_pa w2 (add_vec_int va p)), v2), u_state rs2 mm2) /\
    goodmb Du_r Du_w
      (translate_and_read_value (Virtaddr (add_vec_int va p)) q (Load Data)
         false false false) (u_state rs1 mm1) mm = true /\
    u_tlb_only rs rs2 /\
    tlb_ok_pt (mword_of_int 0) t2 (register_lookup tlb rs2) /\
    u_mem_step P t t2 mm mm2 /\
    u_data_cfg rs2 /\ u_exec_pins P t2 rs2 /\ u_mem_wf P t2 mm2.
Proof.
  intros Hp Hp8 Hpp Hq Hq8 Hqp Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf.
  destruct (u_tarv_page P t mm rs p w1 va Hp Hp8 Hpp Hl1 Hleaf1 Hc1 Hcfg Hpins Hwf)
    as (v1 & rs1 & mm1 & t1 & H1 & H1g & Ho1 & Htlb1 & Hst1 & Hcfg1 & Hpins1 & Hwf1).
  destruct (u_tarv_page P t1 mm1 rs1 q w2 (add_vec_int va p) Hq Hq8 Hqp Hl2 Hleaf2 Hc2
              Hcfg1 Hpins1 Hwf1)
    as (v2 & rs2 & mm2 & t2 & H2 & H2g & Ho2 & Htlb2 & Hst2 & Hcfg2 & Hpins2 & Hwf2).
  exists v1, v2, rs1, mm1, t1, rs2, mm2, t2. split_and!;
    [ exact H1 | exact H1g | exact H2 | | exact (u_tlb_only_trans rs rs1 rs2 Ho1 Ho2)
    | exact Htlb2 | exact (u_mem_step_trans P t t1 t2 mm mm1 mm2 Hst1 Hst2)
    | exact Hcfg2 | exact Hpins2 | exact Hwf2 ].
  rewrite (goodmb_dom Du_r Du_w _ (u_state rs1 mm1) mm mm1).
  - exact H2g.
  - symmetry. exact (u_mem_step_dom P t t1 mm mm1 Hwf Hst1).
Qed.

(* --- the in-one-page [translate_and_write_value], pure --- *)
Lemma u_tawv_page (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
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
  exists (rs' : regstate) (mm2 : pamap) (t' : ptree),
    exec (translate_and_write_value (Virtaddr va) k v (Store Data) false false false)
      (u_state rs mm) = Some (Ok true, u_state rs' mm2) /\
    goodmb Du_r Du_w
      (translate_and_write_value (Virtaddr va) k v (Store Data) false false false)
      (u_state rs mm) mm = true /\
    u_tlb_only rs rs' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm2 /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm2.
Proof.
  intros Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf.
  destruct (u_store_pure_page P t mm rs k w va v Hk Hk8 Hp Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & mm2 & t' & Htr & Htrg & Hea & Heag & Hwv & Hwvg & Hfile & Htlbok'
        & Hstep & Hstep2 & Hcfg' & Hpins').
  assert (Hdom : (dom mm : gset Arch.pa) = dom mm')
    by (symmetry; exact (u_mem_step_dom P t t' mm mm' Hwf Hstep)).
  exists rs', mm2, t'. split_and!;
    [ exact (exec_translate_and_write_value_gen k va (u_walk_pa w va) v (Store Data)
               false false false PBMT_PMA true (u_state rs mm) (u_state rs' mm')
               (u_state rs' mm2) Htr Hea Hwv)
    | | exact (u_tlb_only_land rs rs' Hfile) | exact Htlbok' | exact Hstep2
    | exact Hcfg' | exact Hpins'
    | exact (u_mem_step_wf P t t' mm mm2 Hwf Hstep2) ].
  apply (goodmb_translate_and_write_value_gen Du_r Du_w k va (u_walk_pa w va) v
           (Store Data) false false false PBMT_PMA true
           (u_state rs mm) (u_state rs' mm') (u_state rs' mm2) mm Htrg Htr);
    [ rewrite (goodmb_dom Du_r Du_w _ (u_state rs' mm') mm mm' Hdom); exact Heag
    | exact Hea
    | rewrite (goodmb_dom Du_r Du_w _ (u_state rs' mm') mm mm' Hdom); exact Hwvg
    | exact Hwv ].
Qed.

Lemma u_store_pure_two (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (p q : Z) (w1 w2 va : mword 64)
    (dat1 : mword (8 * p)) (dat2 : mword (8 * q)) :
  0 < p -> p <= 8 -> in_one_page va p ->
  0 < q -> q <= 8 -> in_one_page (add_vec_int va p) q ->
  ud_um P !! svpn_of va = Some w1 ->
  ud_um P !! svpn_of (add_vec_int va p) = Some w2 ->
  uleaf_ok (Store Data) w1 -> uleaf_ok (Store Data) w2 ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs1 : regstate) (mm1 mm1w : pamap) (t1 : ptree)
         (rs2 : regstate) (mm2 : pamap) (t2 : ptree),
    exec (translateAddr (Virtaddr va) (Store Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w1 va), PBMT_PMA, init_ext_ptw),
              u_state rs1 mm1) /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Store Data))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w1 va)) p (Store Data) PBMT_PMA
            false false false) (u_state rs1 mm1) = Some (Ok tt, u_state rs1 mm1) /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w1 va)) p (Store Data)
            PBMT_PMA false false false) (u_state rs1 mm1) mm = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w1 va)) p dat1 (Store Data) PBMT_PMA
            false false false) (u_state rs1 mm1) = Some (Ok true, u_state rs1 mm1w) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w1 va)) p dat1 (Store Data)
            PBMT_PMA false false false) (u_state rs1 mm1) mm = true /\
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) q dat2 (Store Data)
            false false false) (u_state rs1 mm1w) = Some (Ok true, u_state rs2 mm2) /\
    goodmb Du_r Du_w (translate_and_write_value (Virtaddr (add_vec_int va p)) q dat2
            (Store Data) false false false) (u_state rs1 mm1w) mm = true /\
    u_tlb_only rs rs2 /\
    tlb_ok_pt (mword_of_int 0) t2 (register_lookup tlb rs2) /\
    u_mem_step P t t2 mm mm2 /\
    u_data_cfg rs2 /\ u_exec_pins P t2 rs2 /\ u_mem_wf P t2 mm2.
Proof.
  intros Hp Hp8 Hpp Hq Hq8 Hqp Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf.
  destruct (u_store_pure_page P t mm rs p w1 va dat1 Hp Hp8 Hpp Hl1 Hleaf1 Hc1
              Hcfg Hpins Hwf)
    as (rs1 & mm1 & mm1w & t1 & Htr & Htrg & Hea & Heag & Hwv & Hwvg & Hfile
        & Htlb1 & Hst1 & Hst1w & Hcfg1 & Hpins1).
  assert (Hdom1 : (dom mm : gset Arch.pa) = dom mm1)
    by (symmetry; exact (u_mem_step_dom P t t1 mm mm1 Hwf Hst1)).
  assert (Hdom1w : (dom mm : gset Arch.pa) = dom mm1w)
    by (symmetry; exact (u_mem_step_dom P t t1 mm mm1w Hwf Hst1w)).
  assert (Hwf1w : u_mem_wf P t1 mm1w)
    by exact (u_mem_step_wf P t t1 mm mm1w Hwf Hst1w).
  destruct (u_tawv_page P t1 mm1w rs1 q w2 (add_vec_int va p) dat2 Hq Hq8 Hqp Hl2
              Hleaf2 Hc2 Hcfg1 Hpins1 Hwf1w)
    as (rs2 & mm2 & t2 & H2 & H2g & Ho2 & Htlb2 & Hst2 & Hcfg2 & Hpins2 & Hwf2).
  exists rs1, mm1, mm1w, t1, rs2, mm2, t2. split_and!;
    [ exact Htr | exact Htrg
    | exact Hea | rewrite (goodmb_dom Du_r Du_w _ (u_state rs1 mm1) mm mm1 Hdom1); exact Heag
    | exact Hwv | rewrite (goodmb_dom Du_r Du_w _ (u_state rs1 mm1) mm mm1 Hdom1); exact Hwvg
    | exact H2 | rewrite (goodmb_dom Du_r Du_w _ (u_state rs1 mm1w) mm mm1w Hdom1w); exact H2g
    | exact (u_tlb_only_trans rs rs1 rs2 (u_tlb_only_land rs rs1 Hfile) Ho2)
    | exact Htlb2 | exact (u_mem_step_trans P t t1 t2 mm mm1w mm2 Hst1w Hst2)
    | exact Hcfg2 | exact Hpins2 | exact Hwf2 ].
Qed.

(* --- the straddle itself: the two-part composers at the geometry the      *)
(*     model computes.  [p] is the distance to the page boundary and [q]    *)
(*     the remainder; both parts are [in_one_page] by construction          *)
(*     ([UserMemMis.straddle_part1_in_page] / [_part2_in_page]) and both    *)
(*     are non-empty and at most 8 bytes ([straddle_bounds]).               *)
Lemma u_load_pure_straddle (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w1 w2 va : mword 64) :
  0 < k -> k <= 8 -> ~ in_one_page va k ->
  let p := 4096 - bv_unsigned va mod 4096 in
  ud_um P !! svpn_of va = Some w1 ->
  ud_um P !! svpn_of (add_vec_int va p) = Some w2 ->
  uleaf_ok (Load Data) w1 -> uleaf_ok (Load Data) w2 ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (v1 : mword (8 * p)) (v2 : mword (8 * (k - p)))
         (rs1 : regstate) (mm1 : pamap) (t1 : ptree)
         (rs2 : regstate) (mm2 : pamap) (t2 : ptree),
    exec (split_on_page_boundary va k) (u_state rs mm)
      = Some ((p, k - p), u_state rs mm) /\
    goodmb Du_r Du_w (split_on_page_boundary va k) (u_state rs mm) mm = true /\
    0 < p /\ 0 < k - p /\
    exec (translate_and_read_value (Virtaddr va) p (Load Data) false false false)
      (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w1 va), v1), u_state rs1 mm1) /\
    goodmb Du_r Du_w
      (translate_and_read_value (Virtaddr va) p (Load Data) false false false)
      (u_state rs mm) mm = true /\
    exec (translate_and_read_value (Virtaddr (add_vec_int va p)) (k - p) (Load Data)
            false false false) (u_state rs1 mm1)
      = Some (Ok (Physaddr (u_walk_pa w2 (add_vec_int va p)), v2), u_state rs2 mm2) /\
    goodmb Du_r Du_w
      (translate_and_read_value (Virtaddr (add_vec_int va p)) (k - p) (Load Data)
         false false false) (u_state rs1 mm1) mm = true /\
    u_tlb_only rs rs2 /\
    tlb_ok_pt (mword_of_int 0) t2 (register_lookup tlb rs2) /\
    u_mem_step P t t2 mm mm2 /\
    u_data_cfg rs2 /\ u_exec_pins P t2 rs2 /\ u_mem_wf P t2 mm2.
Proof.
  intros Hk Hk8 Hout p Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf.
  destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp & Hq & Hp8 & Hq8).
  destruct (u_load_pure_two P t mm rs p (k - p) w1 w2 va
              Hp Hp8 (straddle_part1_in_page va k)
              Hq Hq8 (straddle_part2_in_page va k Hk Hk8 Hout)
              Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf)
    as (v1 & v2 & rs1 & mm1 & t1 & rs2 & mm2 & t2 & H1 & H1g & H2 & H2g & Ho
        & Htlb2 & Hst & Hcfg2 & Hpins2 & Hwf2).
  exists v1, v2, rs1, mm1, t1, rs2, mm2, t2. split_and!;
    [ exact (exec_split_on_page_boundary_straddle va k (u_state rs mm) Hk Hk8 Hout)
    | exact (goodmb_split_on_page_boundary_straddle Du_r Du_w va k (u_state rs mm) mm
               Hk Hk8 Hout)
    | exact Hp | exact Hq | exact H1 | exact H1g | exact H2 | exact H2g
    | exact Ho | exact Htlb2 | exact Hst | exact Hcfg2 | exact Hpins2 | exact Hwf2 ].
Qed.

Lemma u_store_pure_straddle (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w1 w2 va : mword 64) :
  0 < k -> k <= 8 -> ~ in_one_page va k ->
  let p := 4096 - bv_unsigned va mod 4096 in
  forall (dat1 : mword (8 * p)) (dat2 : mword (8 * (k - p))),
  ud_um P !! svpn_of va = Some w1 ->
  ud_um P !! svpn_of (add_vec_int va p) = Some w2 ->
  uleaf_ok (Store Data) w1 -> uleaf_ok (Store Data) w2 ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va p)))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs1 : regstate) (mm1 mm1w : pamap) (t1 : ptree)
         (rs2 : regstate) (mm2 : pamap) (t2 : ptree),
    exec (split_on_page_boundary va k) (u_state rs mm)
      = Some ((p, k - p), u_state rs mm) /\
    goodmb Du_r Du_w (split_on_page_boundary va k) (u_state rs mm) mm = true /\
    0 < p /\ 0 < k - p /\
    exec (translateAddr (Virtaddr va) (Store Data)) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w1 va), PBMT_PMA, init_ext_ptw),
              u_state rs1 mm1) /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Store Data))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w1 va)) p (Store Data) PBMT_PMA
            false false false) (u_state rs1 mm1) = Some (Ok tt, u_state rs1 mm1) /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w1 va)) p (Store Data)
            PBMT_PMA false false false) (u_state rs1 mm1) mm = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w1 va)) p dat1 (Store Data) PBMT_PMA
            false false false) (u_state rs1 mm1) = Some (Ok true, u_state rs1 mm1w) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w1 va)) p dat1 (Store Data)
            PBMT_PMA false false false) (u_state rs1 mm1) mm = true /\
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) (k - p) dat2
            (Store Data) false false false) (u_state rs1 mm1w)
      = Some (Ok true, u_state rs2 mm2) /\
    goodmb Du_r Du_w (translate_and_write_value (Virtaddr (add_vec_int va p)) (k - p)
            dat2 (Store Data) false false false) (u_state rs1 mm1w) mm = true /\
    u_tlb_only rs rs2 /\
    tlb_ok_pt (mword_of_int 0) t2 (register_lookup tlb rs2) /\
    u_mem_step P t t2 mm mm2 /\
    u_data_cfg rs2 /\ u_exec_pins P t2 rs2 /\ u_mem_wf P t2 mm2.
Proof.
  intros Hk Hk8 Hout p dat1 dat2 Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf.
  destruct (straddle_bounds va k Hk Hk8 Hout) as (Hp & Hq & Hp8 & Hq8).
  destruct (u_store_pure_two P t mm rs p (k - p) w1 w2 va dat1 dat2
              Hp Hp8 (straddle_part1_in_page va k)
              Hq Hq8 (straddle_part2_in_page va k Hk Hk8 Hout)
              Hl1 Hl2 Hleaf1 Hleaf2 Hc1 Hc2 Hcfg Hpins Hwf)
    as (rs1 & mm1 & mm1w & t1 & rs2 & mm2 & t2 & Htr & Htrg & Hea & Heag & Hwv & Hwvg
        & H2 & H2g & Ho & Htlb2 & Hst & Hcfg2 & Hpins2 & Hwf2).
  exists rs1, mm1, mm1w, t1, rs2, mm2, t2. split_and!;
    [ exact (exec_split_on_page_boundary_straddle va k (u_state rs mm) Hk Hk8 Hout)
    | exact (goodmb_split_on_page_boundary_straddle Du_r Du_w va k (u_state rs mm) mm
               Hk Hk8 Hout)
    | exact Hp | exact Hq | exact Htr | exact Htrg | exact Hea | exact Heag
    | exact Hwv | exact Hwvg | exact H2 | exact H2g
    | exact Ho | exact Htlb2 | exact Hst | exact Hcfg2 | exact Hpins2 | exact Hwf2 ].
Qed.

(* ===================================================================== *)
(* 10. THE ACCESS-TYPE-GENERIC ALIGNED PHYSICAL ACCESS.                   *)
(*                                                                       *)
(* [UserMemPt] section 5/5b's [checked_mem_read] / [checked_mem_write]     *)
(* composers bake in [Load Data] / [Store Data] and [Read_plain] /         *)
(* [Write_plain]; LR / SC / AMO need the same stretch at their own access  *)
(* type and at a RESERVED read kind / CONDITIONAL write kind.  Everything  *)
(* the stretch consults is taken as a premise here, so the lemma is        *)
(* generic in the access type, the privilege, the [res] flag and the       *)
(* memory kind, and the LR/SC bricks discharge the premises.               *)
(* (This is [PtWalkCert]'s [pr_exec_chk] / [pr_good_chk] with the width,   *)
(* the access type and the privilege lifted out.)                         *)
(* ===================================================================== *)

Section GenCheckedReadU.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (Hk : 0 < k).
  Context (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
          (priv : Privilege) (addr : mword 64) (aq rl res : bool) (rk : read_kind).
  Context (w : mword (8 * k)) (s : mstate) (mm : PtBytes.pamap).

  Hypothesis Hcpe : exec (check_pma_with_pmp_priority acc pbmt priv
                            (Physaddr addr) k res) s = Some (Ok pma_ok_aligned, s).
  Hypothesis Hcpg : goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt priv
                            (Physaddr addr) k res) s mm = true.
  Hypothesis Hrkf : exec (read_kind_of_flags aq rl res) s = Some (rk, s).
  Hypothesis Hrkg : goodmb Dr Dw (read_kind_of_flags aq rl res) s mm = true.
  Hypothesis Hpmpe : exec (pmpCheck (Physaddr addr) k acc priv) s = Some (None, s).
  Hypothesis Hpmpg : goodmb Dr Dw (pmpCheck (Physaddr addr) k acc priv) s mm = true.
  Hypothesis Hmmioe : exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hmmiog : goodmb Dr Dw (within_mmio_readable (Physaddr addr) k) s mm = true.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr (Z.to_N k) = true.
  Hypothesis Hrkram : rk_ram_ok rk = true.
  Hypothesis Hrame : exec (read_ram rk (Physaddr addr) k false) s
                     = Some ((w, default_meta), s).

  Local Lemma gcr_avi : add_vec_int addr (0 * k) = addr.
  Proof. assert (H0 : (0 * k)%Z = 0) by lia. rewrite H0. apply avi0. Qed.

  Lemma exec_checked_mem_read_u :
    exec (checked_mem_read acc pbmt priv (Physaddr addr) k aq rl res false) s
      = Some (Ok (w, default_meta), s).
  Proof.
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcpe). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)).
    cbn beta. rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite gcr_avi.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmioe. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hrame). cbn beta match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrdr). cbn beta zeta.
      change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
        with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                (autocast (T := mword) w)).
      rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. kill_autocast. reflexivity.
  Qed.

  Lemma goodmb_checked_mem_read_u :
    goodmb Dr Dw (checked_mem_read acc pbmt priv (Physaddr addr) k aq rl res false)
      s mm = true.
  Proof.
    unfold checked_mem_read. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | exact Hcpg | exact Hcpe ].
    cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr k 0 s mm)
             (exec_split_misaligned_unsplit addr k 0 s). cbn beta.
    cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
    gmm_lift Hrkg Hrkf. cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s));
      [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ] end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite gcr_avi.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmioe. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hrame). cbn beta match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrdr). cbn beta zeta.
      change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
        with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                (autocast (T := mword) w)).
      rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
      apply execR_returnR_fwd. }
    { eapply gm_untilMT_1; [ reflexivity | | | | ].
      - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite gcr_avi.
        gmm_lift Hpmpg Hpmpe. cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseqg : goodmb Dr Dw (Defs.bind0 aa bb) s mm = true);
          [ | assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) ] end.
        { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
          apply goodmb_liftR. exact Hmmiog. }
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite Hmmioe. reflexivity. }
        erewrite (gm_bindR Dr Dw _ _ s s mm false Hseqg Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?ad ?wd ?mt)) ?k1) _] =>
          assert (Hrdg : goodmb Dr Dw
                    (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s mm = true);
          [ | assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s
                            = Some (inr w, s)) ] end.
        { erewrite gm_liftR_seq;
            [ | exact (goodmb_read_ram_of_exec Dr Dw rk k addr false
                         (w, default_meta) s s mm Hrkram Hdev Hown Hrame)
              | exact Hrame ].
          cbn beta match. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ Hrame). cbn beta match.
          apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s s mm w Hrdg Hrd). cbn beta zeta.
        change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                  (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
          with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                  (autocast (T := mword) w)).
        rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
        apply goodmb_returnm.
      - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite gcr_avi.
        rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
          assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite Hmmioe. reflexivity. }
        rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?ad ?wd ?mt)) ?k1) _] =>
          assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s
                        = Some (inr w, s)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hrame). cbn beta match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
        change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                  (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
          with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                  (autocast (T := mword) w)).
        rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
        apply execR_returnR_fwd.
      - reflexivity.
      - apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm (w, true, 0) Hug Hu).
    cbn beta zeta. kill_autocast. apply goodmb_returnm.
  Qed.

End GenCheckedReadU.

(* --------------------------------------------------------------------- *)
(* 10b. THE RESERVED / CONDITIONAL RAM LEAVES, WIDTH-GENERIC.              *)
(*                                                                       *)
(* [MemAccessGen.exec_read_ram_plain_gen] / [exec_write_ram_plain_gen] at  *)
(* the LR/SC memory kinds.  The interpreter routes by ADDRESS and ignores  *)
(* the access kind, so the memory effect is identical; the only reason     *)
(* these are separate lemmas is that [read_ram]/[write_ram] MATCH on the   *)
(* kind to build the access-kind record, and three of the kinds are        *)
(* [internal_error]s.  (Same shape as                                      *)
(* [UserMemClassifyAmo.exec_read_ram_resv_kinds_16], one width up.)        *)
(* --------------------------------------------------------------------- *)

Lemma rk_resv_ram_ok (rk : read_kind) :
  rk = rv64d_types.Read_RISCV_reserved \/
  rk = rv64d_types.Read_RISCV_reserved_acquire \/
  rk = rv64d_types.Read_RISCV_reserved_strong_acquire ->
  rk_ram_ok rk = true.
Proof. intros [-> | [-> | ->]]; reflexivity. Qed.

Definition rk_resv (rk : read_kind) : Prop :=
  rk = rv64d_types.Read_RISCV_reserved \/
  rk = rv64d_types.Read_RISCV_reserved_acquire \/
  rk = rv64d_types.Read_RISCV_reserved_strong_acquire.

Definition wk_cond (wk : write_kind) : Prop :=
  wk = rv64d_types.Write_RISCV_conditional \/
  wk = rv64d_types.Write_RISCV_conditional_release \/
  wk = rv64d_types.Write_RISCV_conditional_strong_release.

Lemma exec_read_ram_resv_gen (rk : read_kind) (width : Z) (addr : mword 64) s :
  rk_resv rk ->
  dev_addr addr = false ->
  read_bytes s.(mem) addr (Z.to_N width) <> None ->
  exists w : mword (8 * width),
    exec (read_ram rk (Physaddr addr) width false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hrb.
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa Mem_read_request_pa];
     destruct (read_bytes s.(mem) addr (Z.to_N width)) as [w0|] eqn:Erb; [| congruence];
     eexists; cbn [Interface.iMon_bind]; cbn match beta iota; reflexivity).
Qed.

Lemma exec_write_ram_cond_gen (wk : write_kind) (width : Z) (addr : mword 64)
    (data : mword (8 * width)) s :
  wk_cond wk ->
  dev_addr addr = false ->
  exists (nn : N) (v : bv nn),
    exec (write_ram wk (Physaddr addr) width data tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N width) v) s.(mdev)).
Proof.
  intros Hwk Hdev.
  destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn [Mem_write_request_value]; cbn match; cbn [Interface.iMon_bind];
     rewrite exec_MemWrite; [| exact Hdev];
     eexists _, _; reflexivity).
Qed.

(* --------------------------------------------------------------------- *)
(* 10c. THE FLAG-GENERIC [mem_read] SHELL, and the LR read kind.           *)
(*                                                                       *)
(* [MemAccessGen.exec_mem_read_of_checked_plain] is at flags               *)
(* [false false false].  [mem_read_priv_meta] THROWS on [(false,true,_)]   *)
(* -- an unreserved/reserved load with release semantics -- and that is    *)
(* the only pair a shell has to rule out; [LOADRES] calls [vmem_read] with *)
(* [aq, aq && rl], so it never builds it.                                 *)
(* --------------------------------------------------------------------- *)

Definition mem_flags_ok (aq rl : bool) : Prop := aq = true \/ rl = false.

Lemma exec_read_kind_of_flags_resv (aq rl : bool) (s : mstate) :
  mem_flags_ok aq rl ->
  exists rk : read_kind,
    rk_resv rk /\ exec (read_kind_of_flags aq rl true) s = Some (rk, s).
Proof.
  intros Hfl. destruct aq; destruct rl;
    try (destruct Hfl as [Hf | Hf]; discriminate Hf);
    [ exists rv64d_types.Read_RISCV_reserved_strong_acquire
    | exists rv64d_types.Read_RISCV_reserved_acquire
    | exists rv64d_types.Read_RISCV_reserved ];
    (split; [ unfold rk_resv; tauto
            | unfold read_kind_of_flags; cbn match; apply exec_returnM ]).
Qed.

Lemma goodmb_read_kind_of_flags_resv (Dr Dw : register -> bool)
    (aq rl : bool) (s : mstate) (mm : pamap) :
  mem_flags_ok aq rl ->
  goodmb Dr Dw (read_kind_of_flags aq rl true) s mm = true.
Proof.
  intros Hfl. destruct aq; destruct rl;
    try (destruct Hfl as [Hf | Hf]; discriminate Hf);
    (unfold read_kind_of_flags; cbn match; apply goodmb_returnm).
Qed.

Lemma exec_mem_read_of_checked_u (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (pa : mword 64) (width : Z)
    (v : mword (8 * width)) (ep : Privilege) (aq rl res : bool) (s : mstate) :
  mem_flags_ok aq rl ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (checked_mem_read acc pbmt ep (Physaddr pa) width aq rl res false) s
    = Some (Ok (v, default_meta), s) ->
  exec (mem_read acc pbmt (Physaddr pa) width aq rl res) s = Some (Ok v, s).
Proof.
  intros Hfl Heff Hchk.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ Heff).
  assert (Hpm : exec (mem_read_priv_meta acc pbmt ep (Physaddr pa) width aq rl res false) s
                = Some (Ok (v, default_meta), s)).
  { unfold mem_read_priv_meta.
    destruct aq; destruct rl; destruct res;
      try (destruct Hfl as [Hf | Hf]; discriminate Hf);
      (cbn match; rewrite (exec_bind_Some _ _ _ _ _ Hchk); cbn match;
       unfold mem_read_callback; apply exec_returnM). }
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _ Hpm).
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma goodmb_mem_read_of_checked_u (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (pa : mword 64) (width : Z) (v : mword (8 * width)) (ep : Privilege)
    (aq rl res : bool) (s : mstate) (mm : pamap) :
  mem_flags_ok aq rl ->
  Dr mstatus = true -> Dr cur_privilege = true ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (checked_mem_read acc pbmt ep (Physaddr pa) width aq rl res false)
    s mm = true ->
  exec (checked_mem_read acc pbmt ep (Physaddr pa) width aq rl res false) s
    = Some (Ok (v, default_meta), s) ->
  goodmb Dr Dw (mem_read acc pbmt (Physaddr pa) width aq rl res) s mm = true.
Proof.
  intros Hfl HDm HDc Heffg Heff Hchkg Hchk.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold mem_read.
  gmm_peel Hmst (exec_read_reg mstatus s).
  gmm_peel Hcpr (exec_read_reg cur_privilege s).
  gmm_peel Heffg Heff.
  unfold mem_read_priv, mem_read_priv_meta.
  destruct aq; destruct rl; destruct res;
    try (destruct Hfl as [Hf | Hf]; discriminate Hf);
    (cbn match; gmm_peel Hchkg Hchk; cbn match;
     unfold mem_read_callback; cbn [MemoryOpResult_drop_meta];
     apply goodmb_returnm).
Qed.

(* ===================================================================== *)
(* 11. [u_lr_pure] -- THE PURE U-MODE LOAD-RESERVED.                      *)
(*                                                                       *)
(* Same shape as [u_load_pure], at [LoadReserved (aq, rl, Data)] and with  *)
(* the reserved read kind.  It is ALIGNED-only on purpose: the platform    *)
(* faults a misaligned LR before any access                               *)
(* ([UserMemAccess.plat_misaligned_lrsc]), so the in-one-page geometry has *)
(* no LR/SC instance to serve.                                            *)
(*                                                                       *)
(* THE RESERVABILITY GATE IS NOT AN EXTRA PREMISE.  [pmaCheck]'s LR arm    *)
(* branches on [PMA_reservability], and [RiscvFetchExec.pma_allows_all]    *)
(* pins [generic_neq ... RsrvNone = true] on the RAM class -- so the       *)
(* grant is a projection of the pin the tier already carries and the       *)
(* composer has one total outcome, not a retire-or-fault disjunction.      *)
(*                                                                       *)
(* THE ACCESS TYPE'S aq/rl AND THE MEM LEVEL'S ARE NOT THE SAME PAIR       *)
(* (UserMemAccess section 5d): [LOADRES] builds [LoadReserved (aq,rl,Data)] *)
(* and calls [vmem_read] with [aq, aq && rl], so both are taken, with the  *)
(* one pair [mem_read_priv_meta] throws on excluded by [mem_flags_ok].     *)
(* ===================================================================== *)

Lemma u_lr_pure (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) (aq rl maq mrl : bool) :
  0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  mem_flags_ok maq mrl ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (LoadReserved (aq, rl, Data)) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (dv : mword (8 * k)) (rs' : regstate) (mm' : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (LoadReserved (aq, rl, Data))) (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (LoadReserved (aq, rl, Data)))
      (u_state rs mm) mm = true /\
    exec (mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA
            (Physaddr (u_walk_pa w va)) k maq mrl true) (u_state rs' mm')
      = Some (Ok dv, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA
            (Physaddr (u_walk_pa w va)) k maq mrl true) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_data_cfg rs' /\ u_exec_pins P t' rs' /\ u_mem_wf P t' mm'.
Proof.
  intros Hk Hk8 Hkdvd Huintk Hal Hfl Hl Hleaf Hcanon Hcfg Hpins Hwf.
  assert (Hp : in_one_page va k) by exact (in_one_page_aligned va k Hk Hkdvd Hal).
  destruct (u_walk_pure (LoadReserved (aq, rl, Data)) P t mm rs w va
              (or_intror (or_intror (or_intror (or_introl (ex_intro _ aq
                 (ex_intro _ rl eq_refl))))))
              Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
  set (pa := u_walk_pa w va).
  set (s' := u_state rs' mm').
  pose proof (u_page_window P t' mm' k w va Hk Hp Hwf' Hl) as Hwin.
  assert (Hown : bytes_owned mm' pa (Z.to_N k) = true)
    by exact (u_page_owned P t' mm' k w va Hk Hp Hwf' Hl).
  assert (Hdev : dev_addr pa = false)
    by exact (u_mem_wf_not_dev_data P t' mm' w va Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & _ & HR & Hcovp).
  assert (Hram0 : addr_is_ram pa)
    by (rewrite <- (pa_add_0 pa); exact (proj1 (proj2 (Hwin 0%nat ltac:(lia))))).
  assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1)))
    by exact (proj1 (proj2 (Hwin (Z.to_nat k - 1)%nat ltac:(lia)))).
  destruct (pma_all_ram Hall pa k
              (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                 Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
    as (region & Hpmam & _ & Hrd & _ & _ & _ & _ & _ & Hresv).
  assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
    by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
  assert (Hgate : andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable)
                    (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA)
                       .(PMA_reservability) RsrvNone) = true)
    by (rewrite Hrd; exact Hresv).
  (* the PMA plan and the PMP grant, at the LR access type *)
  assert (Hpmae : exec (pmaCheck (Physaddr pa) k (LoadReserved (aq, rl, Data))
                          PBMT_PMA true) s' = Some (Ok pma_ok_aligned, s'))
    by exact (exec_pmaCheck_ram_lr_ok k pa PBMT_PMA region aq rl s'
                Hpmam Halign Hgate).
  assert (Hpmag : goodmb Du_r Du_w (pmaCheck (Physaddr pa) k
                    (LoadReserved (aq, rl, Data)) PBMT_PMA true) s' mm' = true)
    by exact (goodmb_pmaCheck_ram_lr_ok Du_r Du_w k pa PBMT_PMA region aq rl s' mm'
                ltac:(vm_compute; reflexivity) Hpmam Halign Hgate).
  assert (Hcpe : exec (check_pma_with_pmp_priority (LoadReserved (aq, rl, Data))
                         PBMT_PMA User (Physaddr pa) k true) s'
                 = Some (Ok pma_ok_aligned, s')).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ Hpmae). cbn match. apply exec_returnM. }
  assert (Hcpg : goodmb Du_r Du_w (check_pma_with_pmp_priority
                    (LoadReserved (aq, rl, Data)) PBMT_PMA User (Physaddr pa) k true)
                   s' mm' = true)
    by exact (goodmb_check_pma_with_pmp_priority Du_r Du_w _ _ User _ _ true _ s' mm'
                Hpmag Hpmae).
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
            (uint pa) (uint (to_bits 64 k)) = PMP_Match)
    by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8 Huintk
                ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
  assert (Hpmpe : exec (pmpCheck (Physaddr pa) k (LoadReserved (aq, rl, Data)) User) s'
                  = Some (None, s'))
    by exact (exec_pmpCheck_user_grant_lr aq rl pa k s' HA Hord Hrange HR).
  assert (Hpmpg : goodmb Du_r Du_w (pmpCheck (Physaddr pa) k
                    (LoadReserved (aq, rl, Data)) User) s' mm' = true)
    by exact (goodmb_pmpCheck_user_grant_lr Du_r Du_w aq rl pa k s' mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA Hord Hrange HR).
  (* the MMIO windows *)
  assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
  assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
  assert (Hmmioe : exec (within_mmio_readable (Physaddr pa) k) s' = Some (false, s')).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hclint). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa k s' Hhtif)).
    cbn match. reflexivity. }
  assert (Hmmiog : goodmb Du_r Du_w (within_mmio_readable (Physaddr pa) k) s' mm' = true)
    by exact (goodmb_within_mmio_readable Du_r Du_w pa k s' mm'
                ltac:(vm_compute; reflexivity) Hhtif Hclint Hsig).
  (* the reserved read kind and the RAM leaf *)
  destruct (exec_read_kind_of_flags_resv maq mrl s' Hfl) as (rk & Hrk & Hrkf).
  assert (Hrbne : read_bytes mm' pa (Z.to_N k) <> None)
    by (apply read_bytes_is_Some; intros j Hj;
        exact (proj1 (Hwin j ltac:(lia)))).
  destruct (exec_read_ram_resv_gen rk k pa s' Hrk Hdev Hrbne) as (dv & Hrame).
  (* ...and the two shells on top *)
  assert (Hchke : exec (checked_mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA User
                          (Physaddr pa) k maq mrl true false) s'
                  = Some (Ok (dv, default_meta), s'))
    by exact (exec_checked_mem_read_u k Hk (LoadReserved (aq, rl, Data)) PBMT_PMA User
                pa maq mrl true rk dv s' Hcpe Hrkf Hpmpe Hmmioe Hrame).
  assert (Hchkg : goodmb Du_r Du_w
                    (checked_mem_read (LoadReserved (aq, rl, Data)) PBMT_PMA User
                       (Physaddr pa) k maq mrl true false) s' mm' = true)
    by exact (goodmb_checked_mem_read_u Du_r Du_w k Hk (LoadReserved (aq, rl, Data))
                PBMT_PMA User pa maq mrl true rk dv s' mm'
                Hcpe Hcpg Hrkf (goodmb_read_kind_of_flags_resv Du_r Du_w maq mrl s' mm' Hfl)
                Hpmpe Hpmpg Hmmioe Hmmiog Hdev Hown (rk_resv_ram_ok rk Hrk) Hrame).
  assert (Heffe : exec (effectivePrivilege (LoadReserved (aq, rl, Data))
                          (register_lookup mstatus rs')
                          (register_lookup cur_privilege rs')) s'
                  = Some (User, s')).
  { rewrite Lcp.
    exact (exec_effectivePrivilege_mprv0 (LoadReserved (aq, rl, Data))
             (register_lookup mstatus rs') User s' Lmprv). }
  exists dv, rs', mm', t'. split_and!;
    [ exact Htr | exact Htrg
    | exact (exec_mem_read_of_checked_u (LoadReserved (aq, rl, Data)) PBMT_PMA pa k
               dv User maq mrl true s' Hfl Heffe Hchke)
    | exact (goodmb_mem_read_of_checked_u Du_r Du_w (LoadReserved (aq, rl, Data))
               PBMT_PMA pa k dv User maq mrl true s' mm' Hfl
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w (LoadReserved (aq, rl, Data))
                  (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                  s' mm' Lmprv)
               Heffe Hchkg Hchke)
    | exact Hfile | exact Htlbok' | exact Hstep
    | exact Hcfg0 | exact Hpins0 | exact Hwf' ].
Qed.

(* ===================================================================== *)
(* 12. THE ACCESS-TYPE-GENERIC PHYSICAL WRITE (the SC side of section 10). *)
(* ===================================================================== *)

Definition wr_flags_ok (aq rl : bool) : Prop := aq = false \/ rl = true.

Lemma exec_write_kind_of_flags_cond (aq rl : bool) (s : mstate) :
  wr_flags_ok aq rl ->
  exists wk : write_kind,
    wk_cond wk /\ exec (write_kind_of_flags aq rl true) s = Some (wk, s).
Proof.
  intros Hfl. destruct aq; destruct rl;
    try (destruct Hfl as [Hf | Hf]; discriminate Hf);
    [ exists rv64d_types.Write_RISCV_conditional_strong_release
    | exists rv64d_types.Write_RISCV_conditional_release
    | exists rv64d_types.Write_RISCV_conditional ];
    (split; [ unfold wk_cond; tauto
            | unfold write_kind_of_flags; cbn match; apply exec_returnM ]).
Qed.

Lemma goodmb_write_kind_of_flags_cond (Dr Dw : register -> bool)
    (aq rl : bool) (s : mstate) (mm : pamap) :
  wr_flags_ok aq rl ->
  goodmb Dr Dw (write_kind_of_flags aq rl true) s mm = true.
Proof.
  intros Hfl. destruct aq; destruct rl;
    try (destruct Hfl as [Hf | Hf]; discriminate Hf);
    (unfold write_kind_of_flags; cbn match; apply goodmb_returnm).
Qed.

Lemma wk_cond_ram_ok (wk : write_kind) : wk_cond wk -> wk_ram_ok wk = true.
Proof. intros [-> | [-> | ->]]; reflexivity. Qed.

Section GenCheckedWriteU.
  Context (Dr Dw : register -> bool).
  Context (k : Z) (Hk : 0 < k).
  Context (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
          (priv : Privilege) (addr : mword 64) (aq rl con : bool) (wk : write_kind).
  Context (data : mword (8 * k)) (s sw : mstate) (mm : PtBytes.pamap).

  Hypothesis Hcpe : exec (check_pma_with_pmp_priority acc pbmt priv
                            (Physaddr addr) k con) s = Some (Ok pma_ok_aligned, s).
  Hypothesis Hcpg : goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt priv
                            (Physaddr addr) k con) s mm = true.
  Hypothesis Hwkf : exec (write_kind_of_flags aq rl con) s = Some (wk, s).
  Hypothesis Hwkg : goodmb Dr Dw (write_kind_of_flags aq rl con) s mm = true.
  Hypothesis Hpmpe : exec (pmpCheck (Physaddr addr) k acc priv) s = Some (None, s).
  Hypothesis Hpmpg : goodmb Dr Dw (pmpCheck (Physaddr addr) k acc priv) s mm = true.
  Hypothesis Hmmioe : exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s).
  Hypothesis Hmmiog : goodmb Dr Dw (within_mmio_writable (Physaddr addr) k) s mm = true.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr (Z.to_N k) = true.
  Hypothesis Hwkram : wk_ram_ok wk = true.
  Hypothesis Hwre : exec (write_ram wk (Physaddr addr) k data tt) s = Some (true, sw).

  Local Lemma gcw_avi : add_vec_int addr (0 * k) = addr.
  Proof. assert (H0 : (0 * k)%Z = 0) by lia. rewrite H0. apply avi0. Qed.

  Lemma exec_checked_mem_write_u :
    exec (checked_mem_write (Physaddr addr) k data acc pbmt priv tt aq rl con) s
      = Some (Ok true, sw).
  Proof.
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcpe). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)).
    cbn beta. rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite gcw_avi.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmioe). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
              : mword (8 * k))
        with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
              : mword (8 * k)).
      rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hwre).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

  Lemma goodmb_checked_mem_write_u :
    goodmb Dr Dw (checked_mem_write (Physaddr addr) k data acc pbmt priv tt aq rl con)
      s mm = true.
  Proof.
    unfold checked_mem_write. apply goodmb_cer.
    erewrite gm_liftR_seq; [ | exact Hcpg | exact Hcpe ].
    cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr k 0 s mm)
             (exec_split_misaligned_unsplit addr k 0 s). cbn beta.
    cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
    gmm_lift Hwkg Hwkf. cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw));
      [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ] end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite gcw_avi.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmioe). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
              : mword (8 * k))
        with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
              : mword (8 * k)).
      rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Hwre).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    { eapply gm_untilMT_1; [ reflexivity | | | | ].
      - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite gcw_avi.
        gmm_lift Hpmpg Hpmpe. cbn beta. cbn match.
        erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
        cbn match zeta.
        gmm_lift Hmmiog Hmmioe. cbn beta. cbn match.
        change (autocast (T := mword)
                  (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
                : mword (8 * k))
          with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
                : mword (8 * k)).
        rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwrg : goodmb Dr Dw
                    (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s mm = true);
          [ | assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                             = Some (inr true, sw)) ] end.
        { erewrite gm_liftR_seq;
            [ | exact (goodmb_write_ram Dr Dw wk k addr data s mm Hwkram Hdev Hown)
              | exact Hwre ].
          cbn beta. cbn [andb]. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ Hwre).
          cbn beta. cbn [andb]. apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s sw mm true Hwrg Hwrr). cbn beta zeta.
        apply goodmb_returnm.
      - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite gcw_avi.
        rewrite (execR_liftR_seq _ _ _ _ _ Hpmpe). cbn beta. cbn match.
        rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
        rewrite (execR_liftR_seq _ _ _ _ _ Hmmioe). cbn beta. cbn match.
        change (autocast (T := mword)
                  (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
                : mword (8 * k))
          with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
                : mword (8 * k)).
        rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                         = Some (inr true, sw)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hwre).
          cbn beta. cbn [andb]. apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
        apply execR_returnR_fwd.
      - reflexivity.
      - apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s sw mm (true, 0, true) Hug Hu).
    cbn beta zeta. apply goodmb_returnm.
  Qed.

End GenCheckedWriteU.

(* --- the two flag-generic write shells --- *)
Lemma exec_mem_write_ea_u (width : Z) (Hw : 0 < width) (addr : mword 64)
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (ep : Privilege) (aq rl con : bool) (wk : write_kind) (s : mstate) :
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width con) s
    = Some (Ok pma_ok_aligned, s) ->
  exec (write_kind_of_flags aq rl con) s = Some (wk, s) ->
  exec (pmpCheck (Physaddr addr) width acc ep) s = Some (None, s) ->
  exec (mem_write_ea (Physaddr addr) width acc pbmt aq rl con) s = Some (Ok tt, s).
Proof.
  intros Heff Hcp Hwkf Hpmpchk.
  assert (Havi : add_vec_int addr (0 * width) = addr)
    by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
  unfold mem_write_ea. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr width 0 s)).
  cbn beta. rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _ Hpmpchk). cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_mem_write_ea_u (Dr Dw : register -> bool) (width : Z) (Hw : 0 < width)
    (addr : mword 64) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (ep : Privilege) (aq rl con : bool)
    (wk : write_kind) (s : mstate) (mm : pamap) :
  Dr mstatus = true -> Dr cur_privilege = true ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
                  (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width con)
    s mm = true ->
  exec (check_pma_with_pmp_priority acc pbmt ep (Physaddr addr) width con) s
    = Some (Ok pma_ok_aligned, s) ->
  goodmb Dr Dw (write_kind_of_flags aq rl con) s mm = true ->
  exec (write_kind_of_flags aq rl con) s = Some (wk, s) ->
  goodmb Dr Dw (pmpCheck (Physaddr addr) width acc ep) s mm = true ->
  exec (pmpCheck (Physaddr addr) width acc ep) s = Some (None, s) ->
  goodmb Dr Dw (mem_write_ea (Physaddr addr) width acc pbmt aq rl con) s mm = true.
Proof.
  intros HDm HDp Heffg Heff Hcpg Hcp Hwkg Hwkf Hpmpg Hpmpchk.
  assert (Hms : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hpv : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDp).
  assert (Havi : add_vec_int addr (0 * width) = addr)
    by (assert (H0 : (0 * width)%Z = 0) by lia; rewrite H0; apply avi0).
  unfold mem_write_ea. apply goodmb_cer.
  gmm_lift Hms (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hpv (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  gmm_lift Hcpg Hcp. cbn beta. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
  gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr width 0 s mm)
           (exec_split_misaligned_unsplit addr width 0 s). cbn beta.
  cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
  gmm_lift Hwkg Hwkf. cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?bb) _] =>
    assert (Hu : execR (Defs.untilMT vs m c bb) s = Some (inr (true, 0), s));
    [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m c bb) s mm = true) ] end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _ Hpmpchk). cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    apply execR_returnR_fwd. }
  { eapply gm_untilMT_1; [ reflexivity | | | | ].
    - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                ltac:(apply exec_assert_exp'_true). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite Havi.
      gmm_lift Hpmpg Hpmpchk. cbn beta. cbn match.
      erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      cbn match zeta. apply goodmb_returnm.
    - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _ Hpmpchk). cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      apply execR_returnR_fwd.
    - reflexivity.
    - apply execR_returnR_fwd. }
  erewrite (gm_bindR Dr Dw _ _ s s mm (true, 0) Hug Hu).
  cbn beta zeta. apply goodmb_returnm.
Qed.

Lemma exec_mem_write_value_of_checked_u (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (pa : mword 64) (width : Z)
    (dat : mword (8 * width)) (b : bool) (ep : Privilege) (aq rl con : bool)
    (s s' : mstate) :
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (checked_mem_write (Physaddr pa) width dat acc pbmt ep tt aq rl con) s
    = Some (Ok b, s') ->
  exec (mem_write_value (Physaddr pa) width dat acc pbmt aq rl con) s
    = Some (Ok b, s').
Proof.
  intros Heff Hchk.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ Heff).
  unfold mem_write_value_priv_meta.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk).
  cbn match. unfold mem_write_callback. apply exec_returnM.
Qed.

Lemma goodmb_mem_write_value_of_checked_u (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (pa : mword 64) (width : Z) (dat : mword (8 * width)) (b : bool)
    (ep : Privilege) (aq rl con : bool) (s s' : mstate) (mm : pamap) :
  Dr mstatus = true -> Dr cur_privilege = true ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (checked_mem_write (Physaddr pa) width dat acc pbmt ep tt aq rl con)
    s mm = true ->
  exec (checked_mem_write (Physaddr pa) width dat acc pbmt ep tt aq rl con) s
    = Some (Ok b, s') ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width dat acc pbmt aq rl con) s mm = true.
Proof.
  intros HDm HDc Heffg Heff Hchkg Hchk.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold mem_write_value, mem_write_value_meta.
  gmm_peel Hmst (exec_read_reg mstatus s).
  gmm_peel Hcpr (exec_read_reg cur_privilege s).
  gmm_peel Heffg Heff.
  unfold mem_write_value_priv_meta.
  gmm_peel Hchkg Hchk. cbn match.
  unfold mem_write_callback. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* 13. [u_sc_pure] -- THE PURE U-MODE STORE-CONDITIONAL.                  *)
(*                                                                       *)
(* The mirror of [u_lr_pure], at [StoreConditional (aq, rl, Data)] and    *)
(* with [con = true] -- which is what routes [pmaCheck] into its          *)
(* reservability arm and [write_kind_of_flags] into a CONDITIONAL kind.   *)
(*                                                                       *)
(* IT COVERS BOTH RESERVATION OUTCOMES, AND THAT IS WHY IT ISSUES FOUR    *)
(* CALLS, NOT THREE.  The conditional test is not inside the physical     *)
(* write: [vmem_write_addr] itself branches on [match_reservation paddr]  *)
(* AFTER the walk, and the two arms call DIFFERENT things --              *)
(*   held -> [mem_write_ea] then [mem_write_value] (the write lands);     *)
(*   lost -> [phys_access_check] alone (nothing is written).              *)
(* The reservation is machine state no user-tier arm owns, so an arm      *)
(* cannot force the branch and needs the certificate for BOTH.  Hence the *)
(* fourth pair below.  It costs nothing: [phys_access_check] is the same  *)
(* [pmpCheck] and [pmaCheck] the write path already needed, composed in   *)
(* the other order.                                                       *)
(*                                                                       *)
(* The written value is existential because a width-generic [write_ram]   *)
(* cannot name the bytes it wrote                                         *)
(* ([MemAccessGen.exec_write_ram_plain_gen]'s shape); that is why         *)
(* [UserMemAccess.exec_vmem_write_addr_sc] takes its post-write state as  *)
(* a PARAMETER rather than as a [write_bytes] literal.                    *)
(* ===================================================================== *)

Lemma u_sc_pure (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) (v : mword (8 * k)) (aq rl maq mrl : bool) :
  0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  wr_flags_ok maq mrl ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (StoreConditional (aq, rl, Data)) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (rs' : regstate) (mm' mm2 : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (StoreConditional (aq, rl, Data)))
      (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (StoreConditional (aq, rl, Data)))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w va)) k
            (StoreConditional (aq, rl, Data)) PBMT_PMA maq mrl true)
      (u_state rs' mm') = Some (Ok tt, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w va)) k
            (StoreConditional (aq, rl, Data)) PBMT_PMA maq mrl true)
      (u_state rs' mm') mm' = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w va)) k v
            (StoreConditional (aq, rl, Data)) PBMT_PMA maq mrl true)
      (u_state rs' mm') = Some (Ok true, u_state rs' mm2) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w va)) k v
            (StoreConditional (aq, rl, Data)) PBMT_PMA maq mrl true)
      (u_state rs' mm') mm' = true /\
    (* the LOST-reservation arm's own call: no write, only the re-check *)
    exec (phys_access_check (StoreConditional (aq, rl, Data)) PBMT_PMA User
            (Physaddr (u_walk_pa w va)) k true) (u_state rs' mm')
      = Some (Ok pma_ok_aligned, u_state rs' mm') /\
    goodmb Du_r Du_w (phys_access_check (StoreConditional (aq, rl, Data)) PBMT_PMA
            User (Physaddr (u_walk_pa w va)) k true) (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_mem_step P t t' mm mm2 /\
    u_data_cfg rs' /\ u_exec_pins P t' rs'.
Proof.
  intros Hk Hk8 Hkdvd Huintk Hal Hfl Hl Hleaf Hcanon Hcfg Hpins Hwf.
  assert (Hp : in_one_page va k) by exact (in_one_page_aligned va k Hk Hkdvd Hal).
  destruct (u_walk_pure (StoreConditional (aq, rl, Data)) P t mm rs w va
              (or_intror (or_intror (or_intror (or_intror (or_introl
                 (ex_intro _ aq (ex_intro _ rl eq_refl)))))))
              Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
  set (pa := u_walk_pa w va).
  set (s' := u_state rs' mm').
  pose proof (u_page_window P t' mm' k w va Hk Hp Hwf' Hl) as Hwin.
  assert (Hown : bytes_owned mm' pa (Z.to_N k) = true)
    by exact (u_page_owned P t' mm' k w va Hk Hp Hwf' Hl).
  assert (Hdev : dev_addr pa = false)
    by exact (u_mem_wf_not_dev_data P t' mm' w va Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & HW & _ & Hcovp).
  assert (Hram0 : addr_is_ram pa)
    by (rewrite <- (pa_add_0 pa); exact (proj1 (proj2 (Hwin 0%nat ltac:(lia))))).
  assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1)))
    by exact (proj1 (proj2 (Hwin (Z.to_nat k - 1)%nat ltac:(lia)))).
  destruct (pma_all_ram Hall pa k
              (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                 Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
    as (region & Hpmam & _ & _ & Hwrb & _ & _ & _ & _ & Hresv).
  assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
    by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
  assert (Hgate : andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable)
                    (generic_neq (override_PMA (PMA_Region_attributes region) PBMT_PMA)
                       .(PMA_reservability) RsrvNone) = true)
    by (rewrite Hwrb; exact Hresv).
  assert (Hpmae : exec (pmaCheck (Physaddr pa) k (StoreConditional (aq, rl, Data))
                          PBMT_PMA true) s' = Some (Ok pma_ok_aligned, s'))
    by exact (exec_pmaCheck_ram_sc_ok k pa PBMT_PMA region aq rl s'
                Hpmam Halign Hgate).
  assert (Hpmag : goodmb Du_r Du_w (pmaCheck (Physaddr pa) k
                    (StoreConditional (aq, rl, Data)) PBMT_PMA true) s' mm' = true)
    by exact (goodmb_pmaCheck_ram_sc_ok Du_r Du_w k pa PBMT_PMA region aq rl s' mm'
                ltac:(vm_compute; reflexivity) Hpmam Halign Hgate).
  assert (Hcpe : exec (check_pma_with_pmp_priority (StoreConditional (aq, rl, Data))
                         PBMT_PMA User (Physaddr pa) k true) s'
                 = Some (Ok pma_ok_aligned, s')).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ Hpmae). cbn match. apply exec_returnM. }
  assert (Hcpg : goodmb Du_r Du_w (check_pma_with_pmp_priority
                    (StoreConditional (aq, rl, Data)) PBMT_PMA User (Physaddr pa) k true)
                   s' mm' = true)
    by exact (goodmb_check_pma_with_pmp_priority Du_r Du_w _ _ User _ _ true _ s' mm'
                Hpmag Hpmae).
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
            (uint pa) (uint (to_bits 64 k)) = PMP_Match)
    by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8 Huintk
                ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
  assert (Hpmpe : exec (pmpCheck (Physaddr pa) k (StoreConditional (aq, rl, Data)) User) s'
                  = Some (None, s'))
    by exact (exec_pmpCheck_user_grant_sc aq rl pa k s' HA Hord Hrange HW).
  assert (Hpmpg : goodmb Du_r Du_w (pmpCheck (Physaddr pa) k
                    (StoreConditional (aq, rl, Data)) User) s' mm' = true)
    by exact (goodmb_pmpCheck_user_grant_sc Du_r Du_w aq rl pa k s' mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA Hord Hrange HW).
  (* [phys_access_check] is the SAME two checks in the OTHER order -- pmp
     first, and only on its [None] the pma plan -- so the lost-reservation
     arm's certificate costs one composition of facts the write path already
     needed. *)
  assert (Hpace : exec (phys_access_check (StoreConditional (aq, rl, Data))
                          PBMT_PMA User (Physaddr pa) k true) s'
                  = Some (Ok pma_ok_aligned, s')).
  { unfold phys_access_check.
    rewrite (exec_bind_Some _ _ _ _ _ Hpmpe). cbn match. exact Hpmae. }
  assert (Hpacg : goodmb Du_r Du_w (phys_access_check (StoreConditional (aq, rl, Data))
                    PBMT_PMA User (Physaddr pa) k true) s' mm' = true).
  { unfold phys_access_check. gmm_peel Hpmpg Hpmpe. cbn match. exact Hpmag. }
  assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
  assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
  assert (Hmmioe : exec (within_mmio_writable (Physaddr pa) k) s' = Some (false, s')).
  { unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hclint). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _
               (within_htif_writable_false pa k s' Hhtif)). cbn match. reflexivity. }
  assert (Hmmiog : goodmb Du_r Du_w (within_mmio_writable (Physaddr pa) k) s' mm' = true)
    by exact (goodmb_within_mmio_writable Du_r Du_w pa k s' mm'
                ltac:(vm_compute; reflexivity) Hhtif Hclint Hsig).
  destruct (exec_write_kind_of_flags_cond maq mrl s' Hfl) as (wk & Hwk & Hwkf).
  destruct (exec_write_ram_cond_gen wk k pa v s' Hwk Hdev) as (nn & vv & Hwre).
  assert (Heffe : exec (effectivePrivilege (StoreConditional (aq, rl, Data))
                          (register_lookup mstatus rs')
                          (register_lookup cur_privilege rs')) s'
                  = Some (User, s')).
  { rewrite Lcp.
    exact (exec_effectivePrivilege_mprv0 (StoreConditional (aq, rl, Data))
             (register_lookup mstatus rs') User s' Lmprv). }
  assert (Hchke : exec (checked_mem_write (Physaddr pa) k v
                          (StoreConditional (aq, rl, Data)) PBMT_PMA User tt
                          maq mrl true) s'
                  = Some (Ok true,
                          MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N k) vv)
                            s'.(mdev)))
    by exact (exec_checked_mem_write_u k Hk (StoreConditional (aq, rl, Data)) PBMT_PMA
                User pa maq mrl true wk v s' _ Hcpe Hwkf Hpmpe Hmmioe Hwre).
  assert (Hchkg : goodmb Du_r Du_w (checked_mem_write (Physaddr pa) k v
                    (StoreConditional (aq, rl, Data)) PBMT_PMA User tt maq mrl true)
                    s' mm' = true)
    by exact (goodmb_checked_mem_write_u Du_r Du_w k Hk
                (StoreConditional (aq, rl, Data)) PBMT_PMA User pa maq mrl true wk
                v s' _ mm' Hcpe Hcpg Hwkf
                (goodmb_write_kind_of_flags_cond Du_r Du_w maq mrl s' mm' Hfl)
                Hpmpe Hpmpg Hmmioe Hmmiog Hdev Hown (wk_cond_ram_ok wk Hwk) Hwre).
  exists rs', mm', (write_bytes mm' pa (Z.to_N k) vv), t'. split_and!;
    [ exact Htr | exact Htrg
    | exact (exec_mem_write_ea_u k Hk pa (StoreConditional (aq, rl, Data)) PBMT_PMA
               User maq mrl true wk s' Heffe Hcpe Hwkf Hpmpe)
    | exact (goodmb_mem_write_ea_u Du_r Du_w k Hk pa (StoreConditional (aq, rl, Data))
               PBMT_PMA User maq mrl true wk s' mm'
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                  (StoreConditional (aq, rl, Data)) (register_lookup mstatus rs')
                  (register_lookup cur_privilege rs') s' mm' Lmprv)
               Heffe Hcpg Hcpe
               (goodmb_write_kind_of_flags_cond Du_r Du_w maq mrl s' mm' Hfl) Hwkf
               Hpmpg Hpmpe)
    | exact (exec_mem_write_value_of_checked_u (StoreConditional (aq, rl, Data))
               PBMT_PMA pa k v true User maq mrl true s' _ Heffe Hchke)
    | exact (goodmb_mem_write_value_of_checked_u Du_r Du_w
               (StoreConditional (aq, rl, Data)) PBMT_PMA pa k v true User
               maq mrl true s' _ mm'
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w
                  (StoreConditional (aq, rl, Data)) (register_lookup mstatus rs')
                  (register_lookup cur_privilege rs') s' mm' Lmprv)
               Heffe Hchkg Hchke)
    | exact Hpace | exact Hpacg
    | exact Hfile | exact Htlbok' | exact Hstep
    | exact (u_mem_step_write_in P t t' mm mm' pa (Z.to_N k) vv
               (fun j Hj => proj2 (proj2 (Hwin j ltac:(lia)))) Hstep)
    | exact Hcfg0 | exact Hpins0 ].
Qed.

(* ===================================================================== *)
(* 14. THE AMO BRICKS THAT DID NOT EXIST, and [u_amo_pure].               *)
(*                                                                       *)
(* [UserMemAccess] ends with a "THE AMO PMA BRICK -- PORT PENDING" note:   *)
(* the LR/SC [pmaCheck] pair was ported but the atomic one was not, on the *)
(* diagnosis that [RiscvExtras.pma_ok_peel]'s assert-arm fires and its     *)
(* [execR_liftR_seq] then fails to match.  IT DOES MATCH.  The atomic arm  *)
(* of [pmaCheck] is structurally the LR/SC arm -- [assert_exp' res_or_con] *)
(* then a [returnR] of an [andb] of attribute fields -- so [pma_ok_peel]   *)
(* closes it unchanged once the FIELD hypothesis is spelled as the whole   *)
(* three-way [andb] the arm returns (readable, writable, and              *)
(* [pma_allows_atomic_op] at THIS op and width).  All three are conjuncts  *)
(* of [pma_allows_all]'s RAM class, so nothing new is assumed.            *)
(* ===================================================================== *)

Lemma exec_pmaCheck_ram_amo_ok (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (op : amoop) (aq rl : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
    (andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (pma_allows_atomic_op
          (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k))
    = true ->
  exec (pmaCheck (Physaddr addr) k (Atomic (op, aq, rl, Data, Data)) pbmt true) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hfield.
  destruct region as [rbase rsize rattr rdtree].
  (* THE AMO ARM SCRUTINISES [op].  Every branch is identical, but the
     generated [match op with AMOSWAP | _ => ...] blocks [cbn match] at a
     symbolic op -- which is what made [pma_ok_peel]'s assert arm report
     "does not match any subterm" and left this brick unported in P4a.
     One [destruct op] in front of the tactic is the whole fix. *)
  destruct op;
    match goal with
    | |- context[Atomic (?o, _, _, _, _)] =>
        pma_ok_peel Hmatch Hfield (exec_is_mag_applicable_amo o aq rl k s) Halign
    end.
Qed.

Lemma goodmb_pmaCheck_ram_amo_ok (Dr Dw : register -> bool) (k : Z) (addr : mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) (op : amoop) (aq rl : bool)
    s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  is_aligned_paddr (Physaddr addr) k = true ->
  andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
    (andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
       (pma_allows_atomic_op
          (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k))
    = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (Atomic (op, aq, rl, Data, Data)) pbmt true)
    s mm = true.
Proof.
  intros HD Hmatch Halign Hfield.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s). cbn beta.
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hfield |- *.
  (* same [destruct op] as the exec twin, and for the same reason *)
  destruct op;
    (cbn match;
     erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ];
     cbn match beta;
     cbn [Riscv.rv64d.not negb];
     match goal with |- context[Defs.assert_exp' true ?msg] =>
       gmxlR (goodmb_assert_exp'_true Dr Dw msg s mm) (exec_assert_exp'_true msg s) end;
     cbn beta;
     erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ];
     cbn match beta;
     rewrite Hfield; cbn [Riscv.rv64d.not negb]; cbn match;
     match goal with |- context[Atomic (?o, _, _, _, _)] =>
       gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr pbmt)
                   (Atomic (o, aq, rl, Data, Data)) (Physaddr addr) k true s mm
                   (goodmb_returnm Dr Dw true s mm)
                   (exec_is_mag_applicable_amo o aq rl k s) Halign)
                (exec_mag_pma_check_aligned (override_PMA rattr pbmt)
                   (Atomic (o, aq, rl, Data, Data)) (Physaddr addr) k true s
                   (exec_is_mag_applicable_amo o aq rl k s) Halign) end;
     cbn beta; cbn match; apply goodmb_returnm).
Qed.

Lemma exec_pmpCheck_user_grant_amo (op : amoop) (aq rl : bool) (a : mword 64)
    (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0))
    ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0))
    ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Atomic (op, aq, rl, Data, Data)) User) s
    = Some (None, s).
Proof.
  intros HA Hord Hrange HR HW.
  (* TWO shape notes, neither of which the InstructionFetch / Load / Store
     versions of this lemma need.  [sys_pmp_count] is OPAQUE in this import
     set (PtWalkCert makes it so), so [cbn] cannot decide the loop guard and
     the [if] has to be closed by hand; and the entry-0 body is then the LEFT
     operand of the loop's own bind, so the peel starts one level in and the
     early return is carried out by [UserMemMis.execR_bind_inl]. *)
  destruct op;
    (unfold pmpCheck; rewrite exec_catch_early_return;
     replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity);
     cbn zeta;
     rewrite execR_bind0;
     match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
       assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s));
       [ unfold foreach_ZM_up; cbn [foreach_ZM_up'];
         replace (0 <=? sys_pmp_count - 1) with true by (vm_compute; reflexivity);
         change (0 >? 0) with false; cbn match;
         rewrite bindR_ret; cbn beta;
         lazymatch goal with |- execR (Defs.bind ?inner ?kk) s = _ =>
           assert (Hin : execR inner s = Some (inl None, s));
           [ rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)); cbn beta;
             rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)); cbn beta;
             rewrite (execR_liftR_seq _ _ _ _ _
                        (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                           (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                           (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                           (zeros' 64) s HA Hord Hrange)); cbn beta;
             cbn match;
             unfold or_boolM;
             rewrite execR_bind;
             match goal with
             | |- context[pmpCheckRWX ?e ?acc] =>
                 assert (Hrwx : exec (pmpCheckRWX e acc) s = Some (true, s))
                   by (unfold pmpCheckRWX; cbn match; rewrite HR; rewrite HW;
                       apply exec_returnm);
                 rewrite (execR_liftR_seq _ _ _ _ _ Hrwx)
             end;
             cbn match; rewrite (execR_returnm_fwd true s); cbn match beta;
             rewrite execR_bind; rewrite execR_returnR; cbn match;
             unfold early_return, throw; cbn [execR]; cbn match; reflexivity
           | exact (execR_bind_inl _ kk s s None Hin) ]
         end
       | rewrite Hfe; cbn match; reflexivity ] end).
Qed.

Lemma goodmb_pmpCheck_user_grant_amo (Dr Dw : register -> bool) (op : amoop)
    (aq rl : bool) (a : mword 64) (width : Z) s mm :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0))
    ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0))
    ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (Atomic (op, aq, rl, Data, Data)) User)
    s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HR HW.
  apply (goodmb_pmpCheck_grant Dr Dw a width (Atomic (op, aq, rl, Data, Data)) User
           s mm HDc HDa HA Hord Hrange);
    [ unfold pmpCheckRWX; cbn match; rewrite HR; rewrite HW; apply exec_returnm
    | unfold pmpCheckRWX; cbn match; apply goodmb_returnm ].
Qed.

(* --- the two flag side conditions an AMO always satisfies --- *)
Lemma mem_flags_ok_amo (aq rl : bool) : mem_flags_ok aq (andb aq rl).
Proof. unfold mem_flags_ok. destruct aq; [ by left | by right ]. Qed.

Lemma wr_flags_ok_amo (aq rl : bool) : wr_flags_ok (andb aq rl) rl.
Proof.
  unfold wr_flags_ok. destruct rl; [ by right |].
  left. by rewrite andb_false_r.
Qed.

(* ===================================================================== *)
(* [u_amo_pure] -- THE PURE U-MODE ATOMIC.                                *)
(*                                                                       *)
(* Four model calls, in the order the AMO leaf issues them: the walk, the  *)
(* effective-address announcement, the READ and the WRITE, all at          *)
(* [Atomic (op, aq, rl, Data, Data)].  THE ACCESS TYPE'S aq/rl AND THE MEM *)
(* LEVEL'S ARE AGAIN NOT THE SAME PAIR: the leaf reads at [(aq, aq && rl)] *)
(* and writes at [(aq && rl, rl)] (UserMemClassifyAmo), and both of those  *)
(* satisfy the shells' side conditions unconditionally.                    *)
(*                                                                       *)
(* Width up to 8.  The 128-bit AMOCAS.Q path has its own layer            *)
(* ([UserMemClassifyAmo]'s width-16 section) and is not covered here.      *)
(* ===================================================================== *)

Lemma u_amo_pure (P : uptd) (t : ptree) (mm : pamap) (rs : regstate)
    (k : Z) (w va : mword 64) (v : mword (8 * k)) (op : amoop) (aq rl : bool) :
  0 < k -> k <= 8 -> (k | 4096) -> uint (to_bits 64 k) = k ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  ud_um P !! svpn_of va = Some w ->
  uleaf_ok (Atomic (op, aq, rl, Data, Data)) w ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                        (Z.sub 39 1) 0)) = false ->
  u_data_cfg rs ->
  u_exec_pins P t rs ->
  u_mem_wf P t mm ->
  exists (dv : mword (8 * k)) (rs' : regstate) (mm' mm2 : pamap) (t' : ptree),
    exec (translateAddr (Virtaddr va) (Atomic (op, aq, rl, Data, Data)))
      (u_state rs mm)
      = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' mm') /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (Atomic (op, aq, rl, Data, Data)))
      (u_state rs mm) mm = true /\
    exec (mem_write_ea (Physaddr (u_walk_pa w va)) k
            (Atomic (op, aq, rl, Data, Data)) PBMT_PMA (andb aq rl) rl true)
      (u_state rs' mm') = Some (Ok tt, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_write_ea (Physaddr (u_walk_pa w va)) k
            (Atomic (op, aq, rl, Data, Data)) PBMT_PMA (andb aq rl) rl true)
      (u_state rs' mm') mm' = true /\
    exec (mem_read (Atomic (op, aq, rl, Data, Data)) PBMT_PMA
            (Physaddr (u_walk_pa w va)) k aq (andb aq rl) true) (u_state rs' mm')
      = Some (Ok dv, u_state rs' mm') /\
    goodmb Du_r Du_w (mem_read (Atomic (op, aq, rl, Data, Data)) PBMT_PMA
            (Physaddr (u_walk_pa w va)) k aq (andb aq rl) true)
      (u_state rs' mm') mm' = true /\
    exec (mem_write_value (Physaddr (u_walk_pa w va)) k v
            (Atomic (op, aq, rl, Data, Data)) PBMT_PMA (andb aq rl) rl true)
      (u_state rs' mm') = Some (Ok true, u_state rs' mm2) /\
    goodmb Du_r Du_w (mem_write_value (Physaddr (u_walk_pa w va)) k v
            (Atomic (op, aq, rl, Data, Data)) PBMT_PMA (andb aq rl) rl true)
      (u_state rs' mm') mm' = true /\
    (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    u_mem_step P t t' mm mm' /\
    u_mem_step P t t' mm mm2 /\
    u_data_cfg rs' /\ u_exec_pins P t' rs'.
Proof.
  intros Hk Hk8 Hkdvd Huintk Hal Hl Hleaf Hcanon Hcfg Hpins Hwf.
  assert (Hp : in_one_page va k) by exact (in_one_page_aligned va k Hk Hkdvd Hal).
  destruct (u_walk_pure (Atomic (op, aq, rl, Data, Data)) P t mm rs w va
              (or_intror (or_intror (or_intror (or_intror (or_intror
                 (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl))))))))
              Hl Hleaf Hcanon Hcfg Hpins Hwf)
    as (rs' & mm' & t' & Htr & Htrg & Hfile & Htlbok' & Hstep & Hcfg' & Hpins' & Hwf').
  pose proof Hcfg' as Hcfg0. pose proof Hpins' as Hpins0.
  set (pa := u_walk_pa w va).
  set (s' := u_state rs' mm').
  set (ac := Atomic (op, aq, rl, Data, Data)).
  pose proof (u_page_window P t' mm' k w va Hk Hp Hwf' Hl) as Hwin.
  assert (Hown : bytes_owned mm' pa (Z.to_N k) = true)
    by exact (u_page_owned P t' mm' k w va Hk Hp Hwf' Hl).
  assert (Hdev : dev_addr pa = false)
    by exact (u_mem_wf_not_dev_data P t' mm' w va Hwf' Hl).
  destruct Hcfg' as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  destruct Hpins' as (Hhw & _ & Hpt & _).
  destruct Hhw as (Hmisa & _ & _ & Hhtif & Hall & _).
  destruct Hpt as (_ & HA & Hord & _ & HW & HR & Hcovp).
  assert (Hram0 : addr_is_ram pa)
    by (rewrite <- (pa_add_0 pa); exact (proj1 (proj2 (Hwin 0%nat ltac:(lia))))).
  assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1)))
    by exact (proj1 (proj2 (Hwin (Z.to_nat k - 1)%nat ltac:(lia)))).
  destruct (pma_all_ram Hall pa k
              (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                 Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
    as (region & Hpmam & _ & Hrd & Hwrb & Hatom & _ & _ & _ & _).
  assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
    by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
  assert (Hgate : andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable)
                    (andb (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable)
                       (pma_allows_atomic_op
                          (override_PMA (PMA_Region_attributes region) PBMT_PMA)
                            .(PMA_atomic_support) op k)) = true).
  { rewrite Hrd. rewrite Hwrb. cbn [andb].
    exact (Hatom op k ltac:(apply Z.leb_le; lia)). }
  assert (Hpmae : exec (pmaCheck (Physaddr pa) k ac PBMT_PMA true) s'
                  = Some (Ok pma_ok_aligned, s'))
    by exact (exec_pmaCheck_ram_amo_ok k pa PBMT_PMA region op aq rl s'
                Hpmam Halign Hgate).
  assert (Hpmag : goodmb Du_r Du_w (pmaCheck (Physaddr pa) k ac PBMT_PMA true)
                    s' mm' = true)
    by exact (goodmb_pmaCheck_ram_amo_ok Du_r Du_w k pa PBMT_PMA region op aq rl s' mm'
                ltac:(vm_compute; reflexivity) Hpmam Halign Hgate).
  assert (Hcpe : exec (check_pma_with_pmp_priority ac PBMT_PMA User
                         (Physaddr pa) k true) s' = Some (Ok pma_ok_aligned, s')).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ Hpmae). cbn match. apply exec_returnM. }
  assert (Hcpg : goodmb Du_r Du_w (check_pma_with_pmp_priority ac PBMT_PMA User
                    (Physaddr pa) k true) s' mm' = true)
    by exact (goodmb_check_pma_with_pmp_priority Du_r Du_w _ _ User _ _ true _ s' mm'
                Hpmag Hpmae).
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
            (uint pa) (uint (to_bits 64 k)) = PMP_Match)
    by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8 Huintk
                ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
  assert (Hpmpe : exec (pmpCheck (Physaddr pa) k ac User) s' = Some (None, s'))
    by exact (exec_pmpCheck_user_grant_amo op aq rl pa k s' HA Hord Hrange HR HW).
  assert (Hpmpg : goodmb Du_r Du_w (pmpCheck (Physaddr pa) k ac User) s' mm' = true)
    by exact (goodmb_pmpCheck_user_grant_amo Du_r Du_w op aq rl pa k s' mm'
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                HA Hord Hrange HR HW).
  assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
  assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
    by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
  assert (Hmmiore : exec (within_mmio_readable (Physaddr pa) k) s' = Some (false, s')).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hclint). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa k s' Hhtif)).
    cbn match. reflexivity. }
  assert (Hmmiorg : goodmb Du_r Du_w (within_mmio_readable (Physaddr pa) k) s' mm' = true)
    by exact (goodmb_within_mmio_readable Du_r Du_w pa k s' mm'
                ltac:(vm_compute; reflexivity) Hhtif Hclint Hsig).
  assert (Hmmiowe : exec (within_mmio_writable (Physaddr pa) k) s' = Some (false, s')).
  { unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hclint). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _
               (within_htif_writable_false pa k s' Hhtif)). cbn match. reflexivity. }
  assert (Hmmiowg : goodmb Du_r Du_w (within_mmio_writable (Physaddr pa) k) s' mm' = true)
    by exact (goodmb_within_mmio_writable Du_r Du_w pa k s' mm'
                ltac:(vm_compute; reflexivity) Hhtif Hclint Hsig).
  assert (Heffe : exec (effectivePrivilege ac (register_lookup mstatus rs')
                          (register_lookup cur_privilege rs')) s' = Some (User, s')).
  { rewrite Lcp.
    exact (exec_effectivePrivilege_mprv0 ac (register_lookup mstatus rs') User s' Lmprv). }
  (* the READ half *)
  destruct (exec_read_kind_of_flags_resv aq (andb aq rl) s' (mem_flags_ok_amo aq rl))
    as (rk & Hrk & Hrkf).
  assert (Hrbne : read_bytes mm' pa (Z.to_N k) <> None)
    by (apply read_bytes_is_Some; intros j Hj; exact (proj1 (Hwin j ltac:(lia)))).
  destruct (exec_read_ram_resv_gen rk k pa s' Hrk Hdev Hrbne) as (dv & Hrame).
  assert (Hchkre : exec (checked_mem_read ac PBMT_PMA User (Physaddr pa) k
                           aq (andb aq rl) true false) s'
                   = Some (Ok (dv, default_meta), s'))
    by exact (exec_checked_mem_read_u k Hk ac PBMT_PMA User pa aq (andb aq rl) true
                rk dv s' Hcpe Hrkf Hpmpe Hmmiore Hrame).
  assert (Hchkrg : goodmb Du_r Du_w (checked_mem_read ac PBMT_PMA User (Physaddr pa) k
                     aq (andb aq rl) true false) s' mm' = true)
    by exact (goodmb_checked_mem_read_u Du_r Du_w k Hk ac PBMT_PMA User pa
                aq (andb aq rl) true rk dv s' mm' Hcpe Hcpg Hrkf
                (goodmb_read_kind_of_flags_resv Du_r Du_w aq (andb aq rl) s' mm'
                   (mem_flags_ok_amo aq rl))
                Hpmpe Hpmpg Hmmiore Hmmiorg Hdev Hown (rk_resv_ram_ok rk Hrk) Hrame).
  (* the WRITE half *)
  destruct (exec_write_kind_of_flags_cond (andb aq rl) rl s' (wr_flags_ok_amo aq rl))
    as (wk & Hwk & Hwkf).
  destruct (exec_write_ram_cond_gen wk k pa v s' Hwk Hdev) as (nn & vv & Hwre).
  assert (Hchkwe : exec (checked_mem_write (Physaddr pa) k v ac PBMT_PMA User tt
                           (andb aq rl) rl true) s'
                   = Some (Ok true,
                           MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N k) vv)
                             s'.(mdev)))
    by exact (exec_checked_mem_write_u k Hk ac PBMT_PMA User pa (andb aq rl) rl true
                wk v s' _ Hcpe Hwkf Hpmpe Hmmiowe Hwre).
  assert (Hchkwg : goodmb Du_r Du_w (checked_mem_write (Physaddr pa) k v ac PBMT_PMA
                     User tt (andb aq rl) rl true) s' mm' = true)
    by exact (goodmb_checked_mem_write_u Du_r Du_w k Hk ac PBMT_PMA User pa
                (andb aq rl) rl true wk v s' _ mm' Hcpe Hcpg Hwkf
                (goodmb_write_kind_of_flags_cond Du_r Du_w (andb aq rl) rl s' mm'
                   (wr_flags_ok_amo aq rl))
                Hpmpe Hpmpg Hmmiowe Hmmiowg Hdev Hown (wk_cond_ram_ok wk Hwk) Hwre).
  exists dv, rs', mm', (write_bytes mm' pa (Z.to_N k) vv), t'. split_and!;
    [ exact Htr | exact Htrg
    | exact (exec_mem_write_ea_u k Hk pa ac PBMT_PMA User (andb aq rl) rl true wk s'
               Heffe Hcpe Hwkf Hpmpe)
    | exact (goodmb_mem_write_ea_u Du_r Du_w k Hk pa ac PBMT_PMA User
               (andb aq rl) rl true wk s' mm'
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w ac
                  (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                  s' mm' Lmprv)
               Heffe Hcpg Hcpe
               (goodmb_write_kind_of_flags_cond Du_r Du_w (andb aq rl) rl s' mm'
                  (wr_flags_ok_amo aq rl)) Hwkf Hpmpg Hpmpe)
    | exact (exec_mem_read_of_checked_u ac PBMT_PMA pa k dv User aq (andb aq rl) true
               s' (mem_flags_ok_amo aq rl) Heffe Hchkre)
    | exact (goodmb_mem_read_of_checked_u Du_r Du_w ac PBMT_PMA pa k dv User
               aq (andb aq rl) true s' mm' (mem_flags_ok_amo aq rl)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w ac
                  (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                  s' mm' Lmprv)
               Heffe Hchkrg Hchkre)
    | exact (exec_mem_write_value_of_checked_u ac PBMT_PMA pa k v true User
               (andb aq rl) rl true s' _ Heffe Hchkwe)
    | exact (goodmb_mem_write_value_of_checked_u Du_r Du_w ac PBMT_PMA pa k v true
               User (andb aq rl) rl true s' _ mm'
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (goodmb_effectivePrivilege_mprv0 Du_r Du_w ac
                  (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                  s' mm' Lmprv)
               Heffe Hchkwg Hchkwe)
    | exact Hfile | exact Htlbok' | exact Hstep
    | exact (u_mem_step_write_in P t t' mm mm' pa (Z.to_N k) vv
               (fun j Hj => proj2 (proj2 (Hwin j ltac:(lia)))) Hstep)
    | exact Hcfg0 | exact Hpins0 ].
Qed.
