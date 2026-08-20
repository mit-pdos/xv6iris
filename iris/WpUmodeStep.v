(* WpUmodeStep.v -- THE STEP ENGINE of the VERIFIED user-execution tier
   (claude-notes/projects/user-verified.md), REBASED ON PER-NODE SEMANTICS.

   The safety tier's wrapper (UserStepFull.v + UserActiveClass.v) proves that
   an ARBITRARY user machine steps safely; this file is its VALUE-PRECISE
   twin.  Everything here threads the concrete bundle [uv_cap_gpr]
   (UmodeCap.v): a known image [M], a known register file [m], a known pc --
   and hands the kernel the CONCRETE trapped frame [uv_trap_frame] rather
   than the existential [user_trap_frame].

   WHAT THE PORT CHANGED.  There is no [wp_exec_step_minstret], no
   [mstate_interp], no [minstret_inv_body] and NO WIRE/MIP BORROW: the hart
   OWNS mcycle/mtime/mip (they ride inside [pc_is] via
   [MinstretInv.clock_res]), so [dispatchInterrupt]'s wire reads are answered
   from the hart's own read-only frame.  The cycle is
   [HartStepFull.swp_exec_step_full] driven exactly as
   [UserStepFull.wp_user_step_active] drives it, with
   [HartRunFull.swp_run_hart_active_res] in its body slot so that the tier's
   linear residue crosses the dispatch's branch.

   THE ONE THING THE VERIFIED TIER CANNOT TAKE FROM THE SAFETY TIER is the
   fetch.  [UserFetchCert.u_fetch_pure] answers with an EXISTENTIAL word and
   an EXISTENTIAL post byte-map, which is exactly what a value-precise tier
   may not accept; and its post-map existential also loses the fact that the
   walk's A/D write-back leaves the process IMAGE alone.  So section 2 below
   re-derives the walk with both named: the map is always
   [ptree_bytes 2 t ∪ md] with the image half [md] LITERALLY unchanged, and
   the fetched word is the one [uinstr] names. *)
From Stdlib Require Import ZArith Bool Lia FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv WireInv WpGpr RegFile InstrBytes.
Require Import SmodeCore WpIntrCore ExecCommon.
Require Import WpDecodeBridge DecodeTotalU.
Require Import CommonWalk.
Require Import PtreeType PtAdBits PtTree SmodePte KptPt KptTree.
Require Import SRegime UptTree UptWalkPt.
Require Import UserBits UserMem UserFetch UserPtTree UserTranslate.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFetchCert UserFaultCert.
Require Import UserExec UserStep UserTrap UserExecFacts.
(* NOT [Import]ed: [UserTotalU.u_pins_tick] shadows [UserFrame.u_pins_tick],
   which is the one the frames bridge is stated over. *)
Require UserTotalU.
Require Import UserStepFull UserActiveClass.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpDecode.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE TIER'S BYTE MAP.                                                *)
(*                                                                        *)
(* [uv_mm t md] is what the hart owns: the page table's bytes, plus the    *)
(* process image [md] (which is [UmodeMem.upa_map pt M], the image re-keyed *)
(* by physical address).  The two halves are DISJOINT -- derived from the  *)
(* ownership, never assumed -- and the image half is what every step of    *)
(* this file carries through unchanged.                                   *)
(* ===================================================================== *)

Definition uv_mm (t : ptree) (md : PtBytes.pamap) : PtBytes.pamap :=
  ptree_bytes 2 t ∪ md.

(* the tree half's well-formedness, at a fixed image half *)
Definition uv_tree_ok (pt : uptd) (md : PtBytes.pamap) (t : ptree) : Prop :=
  maps_disj (pt_maps 2 t) /\
  ptree_bytes 2 t ##ₘ md /\
  (forall a : Arch.pa, a ∈ (dom (uv_mm t md) : gset Arch.pa) -> addr_is_ram a) /\
  upt_map_wf (ud_um pt) /\
  upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt) t.

Lemma uv_tree_mem_ok (pt : uptd) (md : PtBytes.pamap) (t : ptree) :
  uv_tree_ok pt md t -> u_mem_ok pt t (uv_mm t md).
Proof.
  intros (Hdisj & Hdj & Hram & Hwfm & Hspec).
  exists md. split_and!;
    [ exact Hdisj | exact Hdj | reflexivity | exact Hram | exact Hwfm
    | exact Hspec ].
Qed.

(* a same-shaped tree change keeps the domain, hence the RAM clause *)
Lemma uv_tree_ok_shape (pt : uptd) (md : PtBytes.pamap) (t t' : ptree) :
  uv_tree_ok pt md t ->
  pt_same_shape 2 t t' ->
  upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt) t' ->
  ptree_bytes 2 t' ##ₘ md ->
  uv_tree_ok pt md t'.
Proof.
  intros (Hdisj & Hdj & Hram & Hwfm & Hspec) Hshape Hspec' Hdj'.
  split_and!;
    [ exact (pt_maps_disj_shape 2 t t' Hshape Hdisj) | exact Hdj' | | exact Hwfm
    | exact Hspec' ].
  intros a Ha. apply Hram.
  assert (Hd : (dom (uv_mm t' md) : gset Arch.pa) = dom (uv_mm t md))
    by exact (dom_union_shape (ptree_bytes 2 t') (ptree_bytes 2 t) md
                (eq_sym (ptree_bytes_dom_shape 2 t t' Hshape))).
  rewrite <- Hd. exact Ha.
Qed.

(* ===================================================================== *)
(* §2 THE WALK, WITH THE LANDING MAP NAMED.                               *)
(*                                                                        *)
(* [UserFetchCert.u_walk_fetch_pure] answers with [exists mm', ... /\      *)
(* u_mem_step_ok P t t' mm mm'], which pins [mm']'s DOMAIN and nothing     *)
(* else: for the safety tier that is enough (its data bytes are            *)
(* existential), for a tier that owns a NAMED image it is not.  The three  *)
(* arms of [KptTree.ptree_translateAddr_cases] do say it -- the TLB hit    *)
(* and the fill leave memory alone, and the A/D write-back writes the LEAF *)
(* SLOT, which is inside the tree half -- so the walk is re-derived here   *)
(* with the map spelled [uv_mm t' md] at the same [md].                    *)
(*                                                                        *)
(* Only the [goodmb] certificate is taken from the safety tier's producer: *)
(* it is stated at the PRE map alone and so is untouched by all this.      *)
(* ===================================================================== *)

Lemma uv_walk_fetch (pt : uptd) (t : ptree) (md : PtBytes.pamap)
    (rsf : regstate) (w va : mword 64) :
  ud_um pt !! svpn_of va = Some w ->
  uleaf_ok (InstructionFetch tt) w ->
  uva_canon va ->
  register_lookup cur_privilege rsf = User ->
  _get_Mstatus_SXL (register_lookup mstatus rsf) = 'b"10" ->
  register_lookup menvcfg rsf = MENVCFG_S ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt md t ->
  exists (rsf' : regstate) (t' : ptree),
    exec (translateAddr (Virtaddr va) (InstructionFetch tt))
      (u_state rsf (uv_mm t md))
      = Some (Values.Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rsf' (uv_mm t' md)) /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) (InstructionFetch tt))
      (u_state rsf (uv_mm t md)) (uv_mm t md) = true /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    uv_tree_ok pt md t' /\
    pt_same_shape 2 t t'.
Proof.
  intros Hl Hleaf Hcanon Lcp Lsxl Lmenv Hpins Htok.
  pose proof (uv_tree_mem_ok pt md t Htok) as Hwf.
  pose proof Htok as (Hdisj & Hdj & Hram & Hwfm & Hspec).
  pose proof Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  pose proof Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
  pose proof Hspec as (Hbase & _).
  (* the certificate, from the safety tier's producer *)
  destruct (u_walk_fetch_pure pt t (uv_mm t md) rsf w va Hl Hleaf Hcanon Lcp
              Lsxl Lmenv Hpins Hwf)
    as (rsfX & mmX & tX & HtrX & Htrg & HfileX & HtlbokX & HstepX).
  clear HtrX HfileX HtlbokX HstepX.
  (* the walk's own data *)
  destruct (upt_spec_maps (ud_root pt) (ud_tfp pt) (ud_um pt) t (svpn_of va) w
              Hspec (or_intror (or_intror Hl)))
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof (upt_variant (ud_tfp pt) (ud_um pt) (svpn_of va) w Hwfm
                (or_intror (or_intror Hl))) as Hvar.
  assert (Hsm2 : pt_slot_mem (u_state rsf (uv_mm t md)) (pt_addr2 t (svpn_of va)) p2)
    by exact (u_slot_mem_at pt t (uv_mm t md) rsf (pt_base t)
                (vpn_idx 2 (svpn_of va)) p2 Hwf
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm1 : pt_slot_mem (u_state rsf (uv_mm t md)) (pt_addr1 p2 (svpn_of va)) p1)
    by exact (u_slot_mem_at pt t (uv_mm t md) rsf (u_next_base p2)
                (vpn_idx 1 (svpn_of va)) p1 Hwf
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm0 : pt_slot_mem (u_state rsf (uv_mm t md)) (pt_addr0 p1 (svpn_of va))
                   (pte_set_ad w a0 d0))
    by exact (u_slot_mem_at pt t (uv_mm t md) rsf (u_next_base p1)
                (vpn_idx 0 (svpn_of va)) _ Hwf
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Htm : exec (translationMode User) (u_state rsf (uv_mm t md))
                = Some (Sv39, u_state rsf (uv_mm t md)))
    by exact (exec_translationMode_U_sv39 usatp (u_state rsf (uv_mm t md))
                Lsxl Hsatp Hmode).
  assert (Heff : exec (effectivePrivilege (InstructionFetch tt)
                        (register_lookup mstatus (u_state rsf (uv_mm t md)).(sregs))
                        User) (u_state rsf (uv_mm t md))
                 = Some (User, u_state rsf (uv_mm t md)))
    by exact (exec_effectivePrivilege_fetch _ User (u_state rsf (uv_mm t md))).
  assert (Hss : exec (is_shadow_stack_access (InstructionFetch tt))
                  (u_state rsf (uv_mm t md))
                = Some (false, u_state rsf (uv_mm t md)))
    by exact (exec_is_shadow_stack_fetch (u_state rsf (uv_mm t md))).
  destruct (ptree_translateAddr_cases (InstructionFetch tt) User
              (ud_root pt) va w (u_walk_pa w va) usatp t
              (register_lookup tlb rsf) p2 p1 a0 d0 (u_state rsf (uv_mm t md))
              Hleaf Hcanon eq_refl (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
              Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
              Hmisa Lmenv Hhtif Lcp Htm Heff Hss
              Hsatp Hppn Hasid eq_refl HA Hord HRp HWp Hcovp
              (pma_allows_all_pte_read _ Hall) (Hpmaw_of _ Hall))
    as (sf & Htr & Harms).
  (* WHERE THE WALK LANDED, with the image half NAMED *)
  assert (Hland : exists (rsf' : regstate) (t' : ptree),
            sf = u_state rsf' (uv_mm t' md) /\
            (rsf' = rsf \/ exists tv, rsf' = register_set tlb tv rsf) /\
            tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
            pt_same_shape 2 t t' /\
            upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt) t' /\
            ptree_bytes 2 t' ##ₘ md).
  { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
    - exists rsf, t. split_and!;
        [ reflexivity | left; reflexivity | exact Htlbok
        | apply pt_same_shape_refl | exact Hspec | exact Hdj ].
    - eexists _, t. split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rsf)
                 (svpn_of va) p2 p1 _ Hmaps Htlbok).
      + apply pt_same_shape_refl.
      + exact Hspec.
      + exact Hdj.
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
      assert (Hspec' : upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt)
                (ptree_set_leaf t (svpn_of va)
                   (pte_set_ad (pte_set_ad w a0 d0) a1 d1))).
      { rewrite Habs.
        exact (upt_tree_spec_set_leaf (ud_root pt) (ud_tfp pt) (ud_um pt) t
                 (svpn_of va) w p2 p1 a0 d0 a1 d1 Hwfm Hspec
                 (or_intror (or_intror Hl)) Hmaps). }
      (* the tree half absorbs the write; the image half is untouched *)
      assert (Heqt : ptree_bytes 2 (ptree_set_leaf t (svpn_of va)
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                     = write_bytes (ptree_bytes 2 t) (pt_addr0 p1 (svpn_of va)) 8
                         (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by exact (ptree_bytes_set_leaf t (svpn_of va) p2 p1 _ _ Hdisj Hmaps).
      assert (Hwdj : word_bytes (pt_addr0 p1 (svpn_of va))
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1) ##ₘ md).
      { apply map_disjoint_spec. intros x b1 b2 H1 H2.
        destruct (word_bytes_is_Some (pt_addr0 p1 (svpn_of va))
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1) (pte_set_ad w a0 d0)
                    x (mk_is_Some _ _ H1)) as [b0 Hb0].
        pose proof (maps_disj_subseteq (pt_maps 2 t)
                      (word_bytes (pt_addr0 p1 (svpn_of va)) (pte_set_ad w a0 d0))
                      Hdisj (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps))
          as Hsubt.
        pose proof (lookup_weaken _ _ x b0 Hb0 Hsubt) as Hbt.
        exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj x b0 b2 Hbt H2). }
      assert (Hdj' : ptree_bytes 2 (ptree_set_leaf t (svpn_of va)
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1)) ##ₘ md).
      { rewrite Heqt write_bytes_word. apply map_disjoint_union_l.
        split; [ exact Hwdj | exact Hdj ]. }
      eexists _,
        (ptree_set_leaf t (svpn_of va) (pte_set_ad (pte_set_ad w a0 d0) a1 d1)).
      split_and!.
      + rewrite /set_reg. cbn [sregs mem mdev]. rewrite /uv_mm.
        rewrite Heqt. rewrite <- write_bytes_union_l. reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0)
                 (ptree_set_leaf t (svpn_of va)
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                 (register_lookup tlb rsf) (svpn_of va) p2 p1 _
                 (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                    (pte_set_ad w a0 d0) _ Hmaps Hv' Hl' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rsf)
                    (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok)).
      + exact (pt_same_shape_set_leaf t (svpn_of va) p2 p1 _ _ Hmaps).
      + exact Hspec'.
      + exact Hdj'. }
  destruct Hland as (rsf' & t' & -> & Hfile & Htlbok' & Hshape & Hspec' & Hdj').
  exists rsf', t'. split_and!.
  - exact Htr.
  - exact Htrg.
  - exact (u_tlb_only_land rsf rsf' Hfile).
  - exact Htlbok'.
  - exact (uv_tree_ok_shape pt md t t' Htok Hshape Hspec' Hdj').
  - exact Hshape.
Qed.

(* ===================================================================== *)
(* §3 THE VALUE-PRECISE FETCH.                                            *)
(*                                                                        *)
(* Four geometries, exactly as the pre-port file had them (all four occur  *)
(* in the binaries this tier verifies): compressed / base x 4-aligned /    *)
(* 2-mod-4.  Each takes the [uinstr] data and produces the CONCRETE        *)
(* [FetchResult] together with its [goodmb] certificate, the landing file  *)
(* and the landing tree -- the image half of the map never moves.          *)
(* ===================================================================== *)

(* the image half of the map is read through the union's right slot *)
Lemma uv_mm_lookup (t : ptree) (md : PtBytes.pamap) (x : Arch.pa) (b : bv 8) :
  ptree_bytes 2 t ##ₘ md -> md !! x = Some b -> uv_mm t md !! x = Some b.
Proof.
  intros Hdj Hx. rewrite /uv_mm.
  destruct (ptree_bytes 2 t !! x) as [c|] eqn:Ht.
  - exfalso. exact (proj1 (map_disjoint_spec _ _) Hdj x c b Ht Hx).
  - rewrite (lookup_union_r _ md x Ht). exact Hx.
Qed.

(* [uinstr]'s "these bytes are in [M]" AT THE PHYSICAL WINDOW *)
Lemma uv_win_bytes (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
    (w_leaf pc : mword 64) (k : nat) (n : N) (iw : bv n) :
  uva_inj pt M ->
  ptree_bytes 2 t ##ₘ upa_map pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  (forall j : nat, (j < k)%nat -> bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
  uM_bytes M (uint pc) k iw ->
  forall j : nat, (j < k)%nat ->
    uv_mm t (upa_map pt M) !! pa_add (u_walk_pa w_leaf pc) j
    = Some (nth_byte iw j).
Proof.
  intros Hinj Hdj Hl Hnc Hb j Hj.
  rewrite <- (uva_pa_window pt w_leaf pc j Hl (Hnc j Hj)).
  apply (uv_mm_lookup t (upa_map pt M) _ (nth_byte iw j) Hdj).
  exact (upa_map_lookup pt M (uint pc + Z.of_nat j) (nth_byte iw j) Hinj
           (Hb j Hj)).
Qed.

Lemma uv_win_some (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
    (w_leaf pc : mword 64) (k : nat) (n : N) (iw : bv n) :
  uva_inj pt M ->
  ptree_bytes 2 t ##ₘ upa_map pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  (forall j : nat, (j < k)%nat -> bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
  uM_bytes M (uint pc) k iw ->
  forall j : nat, (j < k)%nat ->
    is_Some (uv_mm t (upa_map pt M) !! pa_add (u_walk_pa w_leaf pc) j).
Proof.
  intros Hinj Hdj Hl Hnc Hb j Hj. exists (nth_byte iw j).
  exact (uv_win_bytes pt M t w_leaf pc k n iw Hinj Hdj Hl Hnc Hb j Hj).
Qed.

(* ---- the two instruction READS, at the state the walk landed on ------- *)

Lemma uv_read_4 (pt : uptd) (M : gmap Z (bv 8)) (t t' : ptree)
    (rsf rsf' : regstate) (w_leaf pc : mword 64) (iw : mword 32) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  (forall j : nat, (j < 4)%nat ->
     bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  uM_bytes M (uint pc) 4 iw ->
  register_lookup cur_privilege rsf = User ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt (upa_map pt M) t ->
  uv_tree_ok pt (upa_map pt M) t' ->
  u_tlb_only rsf rsf' ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA
          (Physaddr (u_walk_pa w_leaf pc)) 4 false false false)
    (u_state rsf' (uv_mm t' (upa_map pt M)))
    = Some (Ok iw, u_state rsf' (uv_mm t' (upa_map pt M))) /\
  goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
           (Physaddr (u_walk_pa w_leaf pc)) 4 false false false)
    (u_state rsf' (uv_mm t' (upa_map pt M))) (uv_mm t (upa_map pt M)) = true.
Proof.
  intros Hinj Hl Hnc Hal Hb Lcp Hpins Htok Htok' Tr.
  pose proof (uv_win_bytes pt M t' w_leaf pc 4 32 iw Hinj
                (proj1 (proj2 Htok')) Hl Hnc Hb) as Hbytes'.
  destruct (u_fetch_read_ok pt t t' (uv_mm t (upa_map pt M))
              (uv_mm t' (upa_map pt M)) rsf rsf' 4 w_leaf pc
              ltac:(lia) (Z.divide_factor_l 4 1024) ltac:(lia)
              ltac:(vm_compute; reflexivity) Hal Hl Lcp Hpins
              (uv_tree_mem_ok pt (upa_map pt M) t Htok)
              (uv_tree_mem_ok pt (upa_map pt M) t' Htok')
              ltac:(intros j Hj;
                    exact (uv_win_some pt M t w_leaf pc 4 32 iw Hinj
                             (proj1 (proj2 Htok)) Hl Hnc Hb j ltac:(lia)))
              ltac:(intros j Hj;
                    exact (uv_win_some pt M t' w_leaf pc 4 32 iw Hinj
                             (proj1 (proj2 Htok')) Hl Hnc Hb j ltac:(lia)))
              Tr)
    as (region & HA & Hord & Hrange & HX & Hpmam & Halp & Hexecp &
        Hclint & Hsig & Hhtif & Hdev & Hown & Lcp').
  split.
  - exact (exec_mem_read_fetch_4_U PBMT_PMA (u_walk_pa w_leaf pc) region iw
             (u_state rsf' (uv_mm t' (upa_map pt M)))
             HA Hord Hrange HX Hpmam Halp Hexecp Hclint Hsig
             (within_htif_false (u_walk_pa w_leaf pc) 4
                (u_state rsf' (uv_mm t' (upa_map pt M))) Hhtif)
             Hdev ltac:(intros j Hj; apply Hbytes'; lia) Lcp').
  - exact (goodmb_mem_read_fetch_4_U Du_r Du_w PBMT_PMA (u_walk_pa w_leaf pc)
             region iw (u_state rsf' (uv_mm t' (upa_map pt M)))
             (uv_mm t (upa_map pt M))
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             HA Hord Hrange HX Hpmam Halp Hexecp Hclint Hsig Hhtif Hdev Hown
             ltac:(intros j Hj; apply Hbytes'; lia) Lcp').
Qed.

Lemma uv_read_2 (pt : uptd) (M : gmap Z (bv 8)) (t t' : ptree)
    (rsf rsf' : regstate) (w_leaf pc : mword 64) (ih : mword 16) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  (forall j : nat, (j < 2)%nat ->
     bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  uM_bytes M (uint pc) 2 ih ->
  register_lookup cur_privilege rsf = User ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt (upa_map pt M) t ->
  uv_tree_ok pt (upa_map pt M) t' ->
  u_tlb_only rsf rsf' ->
  exec (mem_read (InstructionFetch tt) PBMT_PMA
          (Physaddr (u_walk_pa w_leaf pc)) 2 false false false)
    (u_state rsf' (uv_mm t' (upa_map pt M)))
    = Some (Ok ih, u_state rsf' (uv_mm t' (upa_map pt M))) /\
  goodmb Du_r Du_w (mem_read (InstructionFetch tt) PBMT_PMA
           (Physaddr (u_walk_pa w_leaf pc)) 2 false false false)
    (u_state rsf' (uv_mm t' (upa_map pt M))) (uv_mm t (upa_map pt M)) = true.
Proof.
  intros Hinj Hl Hnc Hal Hb Lcp Hpins Htok Htok' Tr.
  pose proof (uv_win_bytes pt M t' w_leaf pc 2 16 ih Hinj
                (proj1 (proj2 Htok')) Hl Hnc Hb) as Hbytes'.
  destruct (u_fetch_read_ok pt t t' (uv_mm t (upa_map pt M))
              (uv_mm t' (upa_map pt M)) rsf rsf' 2 w_leaf pc
              ltac:(lia) (Z.divide_factor_l 2 2048) ltac:(lia)
              ltac:(vm_compute; reflexivity) Hal Hl Lcp Hpins
              (uv_tree_mem_ok pt (upa_map pt M) t Htok)
              (uv_tree_mem_ok pt (upa_map pt M) t' Htok')
              ltac:(intros j Hj;
                    exact (uv_win_some pt M t w_leaf pc 2 16 ih Hinj
                             (proj1 (proj2 Htok)) Hl Hnc Hb j ltac:(lia)))
              ltac:(intros j Hj;
                    exact (uv_win_some pt M t' w_leaf pc 2 16 ih Hinj
                             (proj1 (proj2 Htok')) Hl Hnc Hb j ltac:(lia)))
              Tr)
    as (region & HA & Hord & Hrange & HX & Hpmam & Halp & Hexecp &
        Hclint & Hsig & Hhtif & Hdev & Hown & Lcp').
  split.
  - exact (exec_mem_read_fetch_2_U PBMT_PMA (u_walk_pa w_leaf pc) region ih
             (u_state rsf' (uv_mm t' (upa_map pt M)))
             HA Hord Hrange HX Hpmam Halp Hexecp Hclint Hsig
             (within_htif_false (u_walk_pa w_leaf pc) 2
                (u_state rsf' (uv_mm t' (upa_map pt M))) Hhtif)
             Hdev ltac:(intros j Hj; apply Hbytes'; lia) Lcp').
  - exact (goodmb_mem_read_fetch_2_U Du_r Du_w PBMT_PMA (u_walk_pa w_leaf pc)
             region ih (u_state rsf' (uv_mm t' (upa_map pt M)))
             (uv_mm t (upa_map pt M))
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             HA Hord Hrange HX Hpmam Halp Hexecp Hclint Hsig Hhtif Hdev Hown
             ltac:(intros j Hj; apply Hbytes'; lia) Lcp').
Qed.

(* the domain does not move along a same-shaped tree change -- which is what
   transports the SECOND walk's certificate back to the entry map *)
Lemma uv_mm_dom (t t' : ptree) (md : PtBytes.pamap) :
  pt_same_shape 2 t t' ->
  (dom (uv_mm t md) : gset Arch.pa) = dom (uv_mm t' md).
Proof.
  intros Hs.
  exact (dom_union_shape (ptree_bytes 2 t) (ptree_bytes 2 t') md
           (ptree_bytes_dom_shape 2 t t' Hs)).
Qed.

(* ---- (a) a 4-ALIGNED pc: ONE 4-byte read ----------------------------- *)
Lemma uv_fetch_4 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) (rsf : regstate)
    (w_leaf pc : mword 64) (iw : mword 32) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  uleaf_ok (InstructionFetch tt) w_leaf ->
  uva_canon pc ->
  Z.rem (uint pc) 4096 <= 4092 ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  uM_bytes M (uint pc) 4 iw ->
  register_lookup PC rsf = pc ->
  register_lookup cur_privilege rsf = User ->
  _get_Mstatus_SXL (register_lookup mstatus rsf) = 'b"10" ->
  register_lookup menvcfg rsf = MENVCFG_S ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt (upa_map pt M) t ->
  exists (rsf' : regstate) (t' : ptree),
    exec (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      = Some ((if isRVC (subrange_vec_dec iw 15 0)
               then F_RVC (subrange_vec_dec iw 15 0) else F_Base iw),
              u_state rsf' (uv_mm t' (upa_map pt M))) /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    uv_tree_ok pt (upa_map pt M) t' /\
    pt_same_shape 2 t t'.
Proof.
  intros Hinj Hl Hleaf Hcanon Hpg Hal Hb Lpc Lcp Lsxl Lmenv Hpins Htok.
  assert (Hnc : forall j : nat, (j < 4)%nat ->
            bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
    by (intros j Hj; exact (uinpage_nc pc (Z.of_nat j) Hpg ltac:(lia))).
  destruct (uv_walk_fetch pt t (upa_map pt M) rsf w_leaf pc
              Hl Hleaf Hcanon Lcp Lsxl Lmenv Hpins Htok)
    as (rsf1 & t1 & Htr & Htrg & Tr1 & Htlbok1 & Htok1 & Hshape1).
  destruct (uv_read_4 pt M t t1 rsf rsf1 w_leaf pc iw
              Hinj Hl Hnc Hal Hb Lcp Hpins Htok Htok1 Tr1) as [Hmr Hmrg].
  exists rsf1, t1. split_and!.
  - pose proof (exec_fetch_ok_4 (u_state rsf (uv_mm t (upa_map pt M)))
                  (u_state rsf1 (uv_mm t1 (upa_map pt M))) pc
                  (u_walk_pa w_leaf pc) iw Lpc Hal Htr Hmr) as Hf.
    rewrite autocast_mword_id in Hf. exact Hf.
  - exact (goodmb_fetch_ok_4 Du_r Du_w (u_state rsf (uv_mm t (upa_map pt M)))
             (u_state rsf1 (uv_mm t1 (upa_map pt M))) (uv_mm t (upa_map pt M))
             pc (u_walk_pa w_leaf pc) iw ltac:(vm_compute; reflexivity)
             Lpc Hal Htr Htrg Hmr Hmrg).
  - exact Tr1.
  - exact Htlbok1.
  - exact Htok1.
  - exact Hshape1.
Qed.

(* ---- (b) a 2-mod-4 pc holding a COMPRESSED instruction: ONE 2-byte read *)
Lemma uv_fetch_rvc_2 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
    (rsf : regstate) (w_leaf pc : mword 64) (h : mword 16) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  uleaf_ok (InstructionFetch tt) w_leaf ->
  uva_canon pc ->
  Z.rem (uint pc) 4096 <= 4092 ->
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  uM_bytes M (uint pc) 2 h ->
  isRVC h = true ->
  register_lookup PC rsf = pc ->
  register_lookup cur_privilege rsf = User ->
  _get_Mstatus_SXL (register_lookup mstatus rsf) = 'b"10" ->
  register_lookup menvcfg rsf = MENVCFG_S ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt (upa_map pt M) t ->
  exists (rsf' : regstate) (t' : ptree),
    exec (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      = Some (F_RVC h, u_state rsf' (uv_mm t' (upa_map pt M))) /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    uv_tree_ok pt (upa_map pt M) t' /\
    pt_same_shape 2 t t'.
Proof.
  intros Hinj Hl Hleaf Hcanon Hpg Hal2 Hnal4 Hb Hrvc Lpc Lcp Lsxl Lmenv
    Hpins Htok.
  pose proof Hpins as ((Hmisa & _ & _ & _ & _ & _) & _).
  assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsf)) ('b"1") = true)
    by (rewrite Hmisa; vm_compute; reflexivity).
  destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
  assert (Hnc : forall j : nat, (j < 2)%nat ->
            bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
    by (intros j Hj; exact (uinpage_nc pc (Z.of_nat j) Hpg ltac:(lia))).
  destruct (uv_walk_fetch pt t (upa_map pt M) rsf w_leaf pc
              Hl Hleaf Hcanon Lcp Lsxl Lmenv Hpins Htok)
    as (rsf1 & t1 & Htr & Htrg & Tr1 & Htlbok1 & Htok1 & Hshape1).
  destruct (uv_read_2 pt M t t1 rsf rsf1 w_leaf pc h
              Hinj Hl Hnc Hal2 Hb Lcp Hpins Htok Htok1 Tr1) as [Hmr Hmrg].
  exists rsf1, t1. split_and!.
  - exact (exec_fetch_rvc_2 (u_state rsf (uv_mm t (upa_map pt M)))
             (u_state rsf1 (uv_mm t1 (upa_map pt M))) pc (u_walk_pa w_leaf pc)
             Lpc HmisaC Hbit0 Hbit1 Hnal4 h Htr Hmr Hrvc).
  - exact (goodmb_fetch_rvc_2 Du_r Du_w (u_state rsf (uv_mm t (upa_map pt M)))
             (u_state rsf1 (uv_mm t1 (upa_map pt M))) (uv_mm t (upa_map pt M))
             pc (u_walk_pa w_leaf pc)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lpc HmisaC Hbit0 Hbit1 Hnal4 h Htr Htrg Hmr Hmrg Hrvc).
  - exact Tr1.
  - exact Htlbok1.
  - exact Htok1.
  - exact Hshape1.
Qed.

(* ---- (c) a 2-mod-4 pc holding a BASE instruction: TWO 2-byte reads ---- *)
Lemma uv_fetch_base_2 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
    (rsf : regstate) (w_leaf pc : mword 64) (iw : mword 32) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  uleaf_ok (InstructionFetch tt) w_leaf ->
  uva_canon pc ->
  Z.rem (uint pc) 4096 <= 4092 ->
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false ->
  uM_bytes M (uint pc) 4 iw ->
  isRVC (subrange_vec_dec iw 15 0) = false ->
  register_lookup PC rsf = pc ->
  register_lookup cur_privilege rsf = User ->
  _get_Mstatus_SXL (register_lookup mstatus rsf) = 'b"10" ->
  register_lookup menvcfg rsf = MENVCFG_S ->
  u_exec_pins pt t rsf ->
  uv_tree_ok pt (upa_map pt M) t ->
  exists (rsf' : regstate) (t' : ptree),
    exec (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      = Some (F_Base iw, u_state rsf' (uv_mm t' (upa_map pt M))) /\
    goodmb Du_r Du_w (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true /\
    u_tlb_only rsf rsf' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf') /\
    uv_tree_ok pt (upa_map pt M) t' /\
    pt_same_shape 2 t t'.
Proof.
  intros Hinj Hl Hleaf Hcanon Hpg Hal2 Hnal4 Hb HnRVC Lpc Lcp Lsxl Lmenv
    Hpins Htok.
  pose proof Hpins as ((Hmisa & _ & _ & _ & _ & _) & _).
  assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsf)) ('b"1") = true)
    by (rewrite Hmisa; vm_compute; reflexivity).
  destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
  pose proof (uinpage_nc pc 2 Hpg ltac:(lia)) as Hnc2.
  pose proof (uinpage_nc pc 3 Hpg ltac:(lia)) as Hnc3.
  (* the SECOND halfword's va is on the SAME page, hence the same leaf *)
  assert (Hl2 : ud_um pt !! svpn_of (add_vec_int pc 2) = Some w_leaf).
  { rewrite (usvpn_window pc 2 ltac:(lia) Hnc2). exact Hl. }
  pose proof (uva_canon_add pc 2 Hcanon ltac:(lia) Hnc2) as Hcanon2.
  destruct (uwin_shift pc 2 Hpg ltac:(lia)) as [Hu2 Hmod2].
  assert (Hnch : forall j : nat, (j < 2)%nat ->
            bv_unsigned (add_vec_int pc 2) mod 4096 + Z.of_nat j < 4096).
  { intros j Hj. rewrite Hmod2. lia. }
  assert (Hncl : forall j : nat, (j < 2)%nat ->
            bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
    by (intros j Hj; lia).
  assert (Hb2 : uM_bytes M (uint (add_vec_int pc 2)) 2
                  (subrange_vec_dec iw 31 16 : mword 16)).
  { intros j Hj.
    rewrite (nth_byte_subrange_hi iw j ltac:(lia)).
    pose proof (Hb (2 + j)%nat ltac:(lia)) as Hbj.
    rewrite Nat2Z.inj_add in Hbj. change (Z.of_nat 2) with 2 in Hbj.
    rewrite Hu2. rewrite <- Z.add_assoc. exact Hbj. }
  assert (Hb1 : uM_bytes M (uint pc) 2 (subrange_vec_dec iw 15 0 : mword 16)).
  { intros j Hj. rewrite (nth_byte_subrange_lo iw j ltac:(lia)).
    exact (Hb j ltac:(lia)). }
  assert (Hal2h : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true)
    by exact (ualign2_plus2 pc Hal2).
  (* ---- the low halfword ---- *)
  destruct (uv_walk_fetch pt t (upa_map pt M) rsf w_leaf pc
              Hl Hleaf Hcanon Lcp Lsxl Lmenv Hpins Htok)
    as (rsf1 & t1 & Htr1 & Htr1g & Tr1 & Htlbok1 & Htok1 & Hshape1).
  destruct (uv_read_2 pt M t t1 rsf rsf1 w_leaf pc
              (subrange_vec_dec iw 15 0 : mword 16)
              Hinj Hl Hncl Hal2 Hb1 Lcp Hpins Htok Htok1 Tr1) as [Hmr1 Hmr1g].
  (* ---- the high halfword, at the state the first walk landed on ---- *)
  assert (Hpins1 : u_exec_pins pt t1 rsf1)
    by exact (u_exec_pins_only pt t t1 rsf rsf1 Tr1 Htlbok1 Hpins).
  assert (Lcp1 : register_lookup cur_privilege rsf1 = User)
    by (rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp).
  assert (Lsxl1 : _get_Mstatus_SXL (register_lookup mstatus rsf1) = 'b"10")
    by (rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact Lsxl).
  assert (Lmenv1 : register_lookup menvcfg rsf1 = MENVCFG_S)
    by (rewrite (Tr1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
  assert (Lpc1 : register_lookup PC rsf1 = pc)
    by (rewrite (Tr1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
  destruct (uv_walk_fetch pt t1 (upa_map pt M) rsf1 w_leaf (add_vec_int pc 2)
              Hl2 Hleaf Hcanon2 Lcp1 Lsxl1 Lmenv1 Hpins1 Htok1)
    as (rsf2 & t2 & Htr2 & Htr2g & Tr2 & Htlbok2 & Htok2 & Hshape2).
  destruct (uv_read_2 pt M t1 t2 rsf1 rsf2 w_leaf (add_vec_int pc 2)
              (subrange_vec_dec iw 31 16 : mword 16)
              Hinj Hl2 Hnch Hal2h Hb2 Lcp1 Hpins1 Htok1 Htok2 Tr2)
    as [Hmr2 Hmr2g].
  (* the second walk's and read's certificates are at [uv_mm t1 md]; the
     shell wants every certificate at the ENTRY map, and the domain has not
     moved *)
  pose proof (uv_mm_dom t t1 (upa_map pt M) Hshape1) as Hdom1.
  exists rsf2, t2. split_and!.
  - rewrite <- (concat_subranges_id iw).
    exact (exec_fetch_base_2 (u_state rsf (uv_mm t (upa_map pt M)))
             (u_state rsf1 (uv_mm t1 (upa_map pt M))) pc (u_walk_pa w_leaf pc)
             Lpc HmisaC Hbit0 Hbit1 Hnal4 (subrange_vec_dec iw 15 0)
             Htr1 Hmr1 (u_state rsf2 (uv_mm t2 (upa_map pt M)))
             (u_walk_pa w_leaf (add_vec_int pc 2)) Lpc1 HnRVC
             (subrange_vec_dec iw 31 16) Htr2 Hmr2).
  - exact (goodmb_fetch_base_2 Du_r Du_w
             (u_state rsf (uv_mm t (upa_map pt M)))
             (u_state rsf1 (uv_mm t1 (upa_map pt M))) (uv_mm t (upa_map pt M))
             pc (u_walk_pa w_leaf pc)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lpc HmisaC Hbit0 Hbit1 Hnal4 (subrange_vec_dec iw 15 0)
             Htr1 Htr1g Hmr1 Hmr1g (u_state rsf2 (uv_mm t2 (upa_map pt M)))
             (u_walk_pa w_leaf (add_vec_int pc 2)) Lpc1 HnRVC
             (subrange_vec_dec iw 31 16) Htr2
             ltac:(rewrite (goodmb_dom Du_r Du_w
                     (translateAddr (Virtaddr (add_vec_int pc 2))
                        (InstructionFetch tt))
                     (u_state rsf1 (uv_mm t1 (upa_map pt M)))
                     (uv_mm t (upa_map pt M)) (uv_mm t1 (upa_map pt M)) Hdom1);
                   exact Htr2g)
             Hmr2 ltac:(rewrite (goodmb_dom Du_r Du_w
                     (mem_read (InstructionFetch tt) PBMT_PMA
                        (Physaddr (u_walk_pa w_leaf (add_vec_int pc 2))) 2
                        false false false)
                     (u_state rsf2 (uv_mm t2 (upa_map pt M)))
                     (uv_mm t (upa_map pt M)) (uv_mm t1 (upa_map pt M)) Hdom1);
                   exact Hmr2g)).
  - exact (u_tlb_only_trans rsf rsf1 rsf2 Tr1 Tr2).
  - exact Htlbok2.
  - exact Htok2.
  - exact (pt_same_shape_trans 2 t t1 t2 Hshape1 Hshape2).
Qed.

(* ===================================================================== *)
(* §4 THE RESOURCE BRIDGES.                                               *)
(*                                                                        *)
(* [utlb_inv_pt] + [umem] in, ONE byte map out -- plus the four register   *)
(* cells the walk reads and writes and a closer that takes a same-shaped   *)
(* tree back.  This is [UserBytes.user_pt_inv_bytes] for a tier that owns  *)
(* its NAMED image instead of the whole data half, so the memory predicate *)
(* is [uv_tree_ok] (i.e. [u_mem_ok], not [u_mem_wf]) and the image half of *)
(* the map is literally [UmodeMem.upa_map pt M].                           *)
(* ===================================================================== *)

Section UvOpen.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma uv_pt_open (pt : uptd) (M : gmap Z (bv 8)) :
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M -∗
    ∃ (t : ptree) (usatp : mword 64) (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜uva_inj pt M⌝ ∗ ⌜uv_tree_ok pt (upa_map pt M) t⌝ ∗
      ⌜upt_satp_ok_pt (ud_root pt) usatp⌝ ∗ ⌜pmp_ent0_ok pcfg paddr⌝ ∗
      ⌜tlb_ok_pt (mword_of_int 0) t tlbvec⌝ ∗
      satp ↦ᵣ usatp ∗ tlb ↦ᵣ tlbvec ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      pt_claims 2 t ∗ bytes_own (uv_mm t (upa_map pt M)) ∗
      (∀ (t' : ptree) (tlbvec' : type_of_register tlb),
         ⌜pt_same_shape 2 t t'⌝ -∗
         ⌜uv_tree_ok pt (upa_map pt M) t'⌝ -∗
         ⌜tlb_ok_pt (mword_of_int 0) t' tlbvec'⌝ -∗
         satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec' -∗
         pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
         bytes_own (uv_mm t' (upa_map pt M)) -∗
         utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M).
  Proof.
    iIntros "Hinv HM".
    iDestruct (umem_uva_inj pt M with "HM") as %Hinj.
    iDestruct (umem_to_bytes pt M with "HM") as "HMb".
    iDestruct (upt_swp_open (ud_root pt) (ud_tfp pt) (ud_um pt) with "Hinv")
      as (usatp tlbvec pcfg paddr) "(%Hsatpok & %Hpmpok & Hsatp & Htlb &
                                     Hpcfg & Hpaddr & Hres)".
    iDestruct "Hres" as (t) "(%Htlbok & %Hspec & %Hwfm & Htree)".
    iDestruct (ptree_own_bytes 2 t with "Htree") as "(#Hclaims & %Hdisj & Hmt)".
    iDestruct (bytes_own_disj with "Hmt HMb") as %Hdj.
    iAssert (bytes_own (uv_mm t (upa_map pt M))) with "[Hmt HMb]" as "Hmm".
    { rewrite /uv_mm (bytes_own_union _ _ Hdj). iFrame. }
    iDestruct (bytes_own_ram with "Hmm") as %Hram.
    iExists t, usatp, tlbvec, pcfg, paddr.
    iSplitR; [ by iPureIntro |].
    iSplitR.
    { iPureIntro. split_and!;
        [ exact Hdisj | exact Hdj | exact Hram | exact Hwfm | exact Hspec ]. }
    iSplitR; [ by iPureIntro |]. iSplitR; [ by iPureIntro |].
    iSplitR; [ by iPureIntro |].
    iFrame "Hsatp Htlb Hpcfg Hpaddr Hclaims Hmm".
    iIntros (t' tlbvec') "%Hshape %Htok' %Htlbok' Hsatp Htlb Hpcfg Hpaddr Hmm".
    pose proof Htok' as (Hdisj' & Hdj' & _ & _ & Hspec').
    rewrite /uv_mm (bytes_own_union _ _ Hdj').
    iDestruct "Hmm" as "[Hmt' HMb']".
    iSplitR "HMb'".
    - iApply (upt_swp_close (ud_root pt) (ud_tfp pt) (ud_um pt) usatp tlbvec'
                pcfg paddr Hsatpok Hpmpok with "Hsatp Htlb Hpcfg Hpaddr").
      iExists t'. iSplitR; [ by iPureIntro |]. iSplitR; [ by iPureIntro |].
      iSplitR; [ by iPureIntro |].
      iApply (ptree_own_of_bytes 2 t' Hdisj' with "[] Hmt'").
      by iApply (pt_claims_shape 2 t t' Hshape).
    - iApply (bytes_to_umem pt M Hinj with "HMb'").
  Qed.

  (* ---- the [swp] bridge over a PURE fetch fact -------------------------
     [UserActiveClass.swp_fetch_of_pure] at the tier's map: the landing map
     is pinned by [UserClassifyAsm.u_map_eq] (a submap with the full domain
     IS the map) rather than by [u_landing_map], because the tier's step
     relation is [uv_tree_ok] plus the shape, not [u_mem_step_ok]. *)
  Lemma uv_swp_fetch (pt : uptd) (M : gmap Z (bv 8)) (t t' : ptree)
      (dq : dfrac) (rsf rsf' : regstate) (fr : FetchResult)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ)
      (Pf : mword 64 -> ExceptionType -> iProp Σ)
      (Px : ext_fetch_addr_error -> iProp Σ) :
    exec (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      = Some (fr, u_state rsf' (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsf (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    pt_same_shape 2 t t' ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsf u_Drw -∗ hreg_frame_ro (u_Df dq) rsf u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf'⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       bytes_own (uv_mm t' (upa_map pt M)) -∗ resv_any cpu_id -∗
       run_fetch_post u_Drw u_Dro (u_Df dq) Pe Pf Px fr) -∗
    swp (fetch tt) (run_fetch_post u_Drw u_Dro (u_Df dq) Pe Pf Px).
  Proof.
    intros He Hg Hshape.
    iIntros "#Hcert Hany Hrw Hro Hown Hk".
    iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
    2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq) (fetch tt)
                  (u_state rsf (uv_mm t (upa_map pt M)))
                  (u_state rsf' (uv_mm t' (upa_map pt M))) fr rsf
                  (uv_mm t (upa_map pt M))
                  u_disj Du_r_sub Du_w_sub
                  ltac:(intros r _; reflexivity) ltac:(reflexivity) Hg He
                  with "Hcert Hany Hrw Hro Hown"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost"
      as (rs2 mm2) "(%Hag & %Hsub & %Hdom & Hrw & Hro & Hown & Hany)".
    assert (Hmm2 : mm2 = uv_mm t' (upa_map pt M)).
    { apply (u_map_eq mm2 (uv_mm t' (upa_map pt M)) Hsub).
      rewrite Hdom. exact (uv_mm_dom t t' (upa_map pt M) Hshape). }
    subst mm2.
    iApply ("Hk" $! rs2 with "[%] Hrw Hro Hown Hany"). exact Hag.
  Qed.

  (* ---- and over a PURE execute fact, for the register-only instructions
     this file's funnel serves.  The map does not move at all, so the
     landing map is pinned by the SAME argument at [t' := t]. *)
  Lemma uv_swp_execute (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rsx : regstate) (instr : instruction)
      (r : ExecutionResult) (rs_x : regstate) (ib : mword 32)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) :
    exec (execute instr) (u_state rsx (uv_mm t (upa_map pt M)))
      = Some (r, u_state rs_x (uv_mm t (upa_map pt M))) ->
    goodmb Du_r Du_w (execute instr) (u_state rsx (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    (match r with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsx u_Drw -∗ hreg_frame_ro (u_Df dq) rsx u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rs_x⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       bytes_own (uv_mm t (upa_map pt M)) -∗ resv_any cpu_id -∗
       Pe r ib) -∗
    swp (execute instr) (run_exec_post Pe ib).
  Proof.
    intros He Hg Hnr.
    iIntros "#Hcert Hany Hrw Hro Hown Hk".
    iApply (swp_mono with "[Hk] [Hany Hrw Hro Hown]").
    2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                  (execute instr) (u_state rsx (uv_mm t (upa_map pt M)))
                  (u_state rs_x (uv_mm t (upa_map pt M))) r rsx
                  (uv_mm t (upa_map pt M))
                  u_disj Du_r_sub Du_w_sub
                  ltac:(intros q _; reflexivity) ltac:(reflexivity) Hg He
                  with "Hcert Hany Hrw Hro Hown"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost"
      as (rs2 mm2) "(%Hag & %Hsub & %Hdom & Hrw & Hro & Hown & Hany)".
    assert (Hmm2 : mm2 = uv_mm t (upa_map pt M))
      by (apply (u_map_eq mm2 (uv_mm t (upa_map pt M)) Hsub); exact Hdom).
    subst mm2.
    iApply (run_exec_post_direct Pe ib r Hnr).
    iApply ("Hk" $! rs2 with "[%] Hrw Hro Hown Hany"). exact Hag.
  Qed.

End UvOpen.

(* ===================================================================== *)
(* §5 THE CYCLE.                                                          *)
(*                                                                        *)
(* [UserStepFull.wp_user_step_active]'s shape, at the verified tier's      *)
(* concrete frames: [Q] is [UserStepFull.u_land] verbatim (it mentions     *)
(* neither the config nor the page table), [Psi] is a CLOSER, and          *)
(* [HartRunFull.swp_run_hart_active_res] threads the tier's linear residue *)
(* -- the byte map, the page-table re-former, the reservation fragment and *)
(* the caller's OBLIGATION -- from the dispatch's [None] branch into the   *)
(* fetch, while the INTERRUPT arm is owned here.                           *)
(* ===================================================================== *)

Local Ltac uv_notin_clock := apply (bool_decide_unpack _); vm_compute; reflexivity.

(* ---- THE LANDING PREDICATE.  [UserStepFull.u_land] admits the ENTER-WAIT
   shape, which a verified program never reaches and whose landing file the
   verified frames cannot describe (the wait step skips the tick, so PC and
   nextPC come apart and [pc_is] is unprovable).  Ruling it out in [Q] is
   free -- the body slot answers [False] on that arm anyway -- and it is
   what makes the cycle's tail a SINGLE shape. *)
Definition uv_land (rs1 : regstate) (st : Step) (rs2 : regstate) : Prop :=
  register_lookup hart_state rs2 = HART_ACTIVE tt /\
  register_lookup (R_bool minstret_increment) rs2
    = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
        (register_lookup (R_bitvector_64 minstretcfg) rs1)
        (register_lookup cur_privilege rs1) /\
  match st with
  | Step_Execute (Enter_Wait _, _) => False
  | _ => True
  end.

(* ...so the cycle's tail is exactly [wrap_post]: the PC tick and the
   minstret bump, up to agreement off the three clock cells. *)
Definition uv_tail (rs2 rs3 : regstate) : Prop :=
  exists mi : mword 64,
    forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
      register_lookup r rs3 = register_lookup r (wrap_post rs2 mi).

Lemma uv_tail_of (rs1 rs2 rs3 : regstate) :
  (exists rsP : regstate, tsf_post (uv_land rs1) rs2 rsP /\
     reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 rsP) ->
  uv_tail rs2 rs3.
Proof.
  intros (rsP & (st & Hq & Hsh) & Hag).
  assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
            register_lookup r rs3 = register_lookup r rsP).
  { intros r H1 H2. apply Hag, elem_of_difference. split; assumption. }
  destruct st as [ [ii pr] | x | [xv e] | [r ib] | wq ];
    try (destruct Hsh as (mi & ->); exists mi; exact T).
  destruct r as [u | i0 | wr0 | u | u | trp | u | ec | ed | u];
    try (destruct Hsh as (mi & ->); exists mi; exact T).
  destruct Hq as (_ & _ & []).
Qed.

Lemma uv_tail_reg (rs2 rs3 : regstate) (r : register) :
  uv_tail rs2 rs3 ->
  r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
  register_beq r (R_bitvector_64 minstret) = false ->
  register_beq r (R_bitvector_64 PC) = false ->
  register_lookup r rs3 = register_lookup r rs2.
Proof.
  intros (mi & T) Hin Hnc Hms Hpc.
  rewrite (T r Hin Hnc). exact (wrap_post_other r rs2 mi Hms Hpc).
Qed.

Lemma uv_tail_pc (rs2 rs3 : regstate) :
  uv_tail rs2 rs3 ->
  register_lookup (R_bitvector_64 PC) rs3
  = register_lookup (R_bitvector_64 nextPC) rs2.
Proof.
  intros (mi & T). rewrite (T _ u_in_PC ltac:(uv_notin_clock)).
  apply wrap_post_PC.
Qed.

(* a GPR is none of the three clock cells -- the symbolic-index side
   condition, discharged once (WpGpr's [regbeq_gpr_*] recipe) *)
Lemma uv_gpr_notin_clock3 (n : Z) :
  (R_bitvector_64 (gpr_of_Z n) : register) ∉ tk_clock3.
Proof.
  unfold gpr_of_Z; repeat case_match; uv_notin_clock.
Qed.

(* the register file a landing file determines IS the caller's, once x0 is
   known to read [zero_reg] there.  [UserFrame.u_gpr_file_eq] proves the
   same equality from the RESOURCE; a closer that has already handed the
   file back needs it from the PURE side. *)
Lemma uv_regfile_eq (g : regfile) (rs : regstate) :
  u_gpr_agree g rs ->
  g (Regidx (mword_of_int 0)) = zero_reg ->
  g = u_regfile rs.
Proof.
  intros Hag H0. apply functional_extensionality. intros [i].
  destruct (decide (uint i = 0)) as [Hz | Hnz].
  - rewrite /u_regfile (proj2 (Z.eqb_eq (uint i) 0) Hz).
    rewrite (u_mword5_eq i 0 ltac:(lia) Hz). exact H0.
  - by rewrite (Hag i Hnz) /u_regfile (proj2 (Z.eqb_neq (uint i) 0) Hnz).
Qed.

Section UvResume.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* the kernel's resume wand, in EXACTLY the shape [UmodeCap.uv_intr_wp]
     takes it: hart-free, because the scheduler may migrate the process
     while it is parked. *)
  Definition uv_resume (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ CID : CpuId, uv_run C pt M m pc -∗ WP (Loop : expr riscv_lang))%I.

End UvResume.

Section UvEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ---- the page-table re-former, keyed on the tree it was opened at ---- *)
  Definition uv_close (M : gmap Z (bv 8)) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      : iProp Σ :=
    (∀ (t' : ptree) (tlbv' : type_of_register tlb),
       ⌜pt_same_shape 2 t t'⌝ -∗ ⌜uv_tree_ok pt (upa_map pt M) t'⌝ -∗
       ⌜tlb_ok_pt (mword_of_int 0) t' tlbv'⌝ -∗
       satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbv' -∗
       pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
       bytes_own (uv_mm t' (upa_map pt M)) -∗
       utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M)%I.

  Definition uv_res (M : gmap Z (bv 8)) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      : iProp Σ :=
    (pt_claims 2 t ∗ uv_close M t usatp pcfg paddr)%I.

  (* the residue travels with the tree the walk landed on *)
  Lemma uv_res_move (M : gmap Z (bv 8)) (t t' : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    pt_same_shape 2 t t' ->
    uv_res M t usatp pcfg paddr -∗ uv_res M t' usatp pcfg paddr.
  Proof.
    intros Hshape. iIntros "[#Hc Hcl]". iSplitR.
    { by iApply (pt_claims_shape 2 t t' Hshape). }
    iIntros (t'' tlbv'') "%Hs'' %Htok'' %Hok'' Hsatp Htlb Hpcfg Hpaddr Hmm".
    iApply ("Hcl" $! t'' tlbv'' with "[%] [%] [%] Hsatp Htlb Hpcfg Hpaddr Hmm");
      [ exact (pt_same_shape_trans 2 t t' t'' Hshape Hs'')
      | exact Htok'' | exact Hok'' ].
  Qed.

  (* ---- the payload: a CLOSER over the file the CYCLE (not the arm)
     landed on.  It takes the interrupt-resume wand from the wrapper -- the
     one thing an arm cannot build for itself, since it is the Loeb
     hypothesis and only the wrapper's continuation is under the later. *)
  (* [R] is what the WRAPPER supplies to the closer and an arm cannot build
     for itself: the Loeb hypothesis, which is [|>]-guarded and only becomes
     usable inside the cycle rule's continuation.  Keeping it ABSTRACT here
     is what breaks the definitional cycle (the hypothesis mentions the
     obligation, the obligation mentions the payload). *)
  Definition uv_psi (R : iProp Σ) (rs2 : regstate) : iProp Σ :=
    (resv_any cpu_id ∗
     (∀ rs3 : regstate,
        ⌜uv_tail rs2 rs3⌝ -∗
        hreg_frame rs3 u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rs3 u_Dro -∗
        resv_any cpu_id -∗ R -∗
        WP (Loop : expr riscv_lang)))%I.

  Definition uv_arm_res (R : iProp Σ) (rs2 : regstate) : iProp Σ :=
    (hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df (uc_dqc C)) rs2 u_Dro ∗
     uv_psi R rs2)%I.

  (* the three arms this tier can reach.  A verified program never executes
     an illegal word, never enters a wait and never fetches from an unmapped
     page (its [uinstr] says so), so those three shapes are [False]. *)
  Definition uv_step_post (R : iProp Σ) (rs1 : regstate) (st : Step) : iProp Σ :=
    (∃ rs2 : regstate, ⌜uv_land rs1 st rs2⌝ ∗
       match st with
       | Step_Execute (Retire_Success tt, _) => uv_arm_res R rs2
       | Step_Pending_Interrupt (i, p) =>
           swp (handle_interrupt i p) (fun _ => uv_arm_res R rs2)
       | Step_Execute (rv64d_types.Trap (p, exc, pcx), _) =>
           swp (Defs.bind (exception_handler p exc pcx) set_next_pc)
             (fun _ => uv_arm_res R rs2)
       | _ => False
       end)%I.

  (* ---- the pure pin bundle the obligation and the arms share ---------- *)
  Definition uv_pre (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64)
      (t : ptree) (rs1 rsA : regstate) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) : Prop :=
    uva_inj pt M /\
    uv_tree_ok pt (upa_map pt M) t /\
    u_exec_pins pt t rsA /\
    register_lookup hart_state rsA = HART_ACTIVE tt /\
    register_lookup cur_privilege rsA = User /\
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsA) /\
    register_lookup (R_bitvector_64 PC) rsA = pc /\
    u_gpr_agree m rsA /\
    register_lookup (R_bitvector_64 stvec) rsA = uc_stvec C /\
    register_lookup (R_bitvector_64 mie) rsA = uc_mie C /\
    register_lookup (R_bitvector_64 mideleg) rsA = uc_mideleg C /\
    register_lookup (R_bitvector_64 medeleg) rsA = uc_medeleg C /\
    register_lookup (R_bitvector_64 menvcfg) rsA = MENVCFG_S /\
    register_lookup (R_bitvector_64 satp) rsA = usatp /\
    register_lookup pmpcfg_n rsA = pcfg /\
    register_lookup pmpaddr_n rsA = paddr /\
    register_lookup (R_bool minstret_increment) rsA
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) /\
    m (Regidx (mword_of_int 0)) = zero_reg.

End UvEngine.

(* THE OBLIGATION lives in a CpuId-FREE section, with the hart as an
   ordinary leading binder: the engine consumes it at whatever hart the
   process is running on after any number of absorbed interrupts, and a
   SECTION CpuId variable is auto-applied and cannot be named at
   application (claude-notes/projects/user-verified.md section 5). *)
Section UvObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* ---- THE OBLIGATION: fetch-onward.  The engine has already taken the
     dispatch's [None] branch, so what is left to say is what the machine
     does from the FETCH on -- which is exactly where the caller's [uinstr]
     and execute facts live. *)
  (* [Kc] is the CALLER's continuation.  It arrives [|>]-guarded (that is
     what [wp_uv_retire_later] is FOR: an [iLoeb] back edge can only close
     under a later), and the only later-stripping point in the whole chain
     is the cycle rule's own continuation -- which runs AFTER the body slot
     where this obligation lives.  So the obligation does not hold [Kc]: it
     holds a WAND [R -∗ Kc] out of the abstract payload argument, and the
     wrapper -- which does stand past the later -- puts [Kc] into [R]. *)
  Definition uv_step_obl (Kc : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (R : iProp Σ) (CIDo : CpuId) (t : ptree) (rs1 rsA : regstate)
       (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
       (paddr : type_of_register pmpaddr_n),
       ⌜uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr⌝ -∗
       uv_amb (CID := CIDo) -∗
       uv_cap C pt Ψ -∗
       (R -∗ Kc) -∗
       resv_any cpu_id -∗
       hreg_frame rsA u_Drw -∗
       hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
       bytes_own (uv_mm t (upa_map pt M)) -∗
       uv_res (CID := CIDo) pt M t usatp pcfg paddr -∗
       swp (fetch tt)
         (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
            (fun (r : ExecutionResult) (ib : mword 32) =>
               uv_step_post (CID := CIDo) C R rs1 (Step_Execute (r, ib)))
            (fun (xv : mword 64) (e : ExceptionType) =>
               uv_step_post (CID := CIDo) C R rs1
                 (Step_Fetch_Failure (Virtaddr xv, e)))
            (fun _ : ext_fetch_addr_error => False)))%I.

  (* the Loeb hypothesis, named: what the wrapper hands the payload closer *)
  Definition uv_ih (Kc : iProp Σ) (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ CID : CpuId, uv_cap_gpr C pt Ψ M m -∗ pc_is pc -∗
       uv_step_obl Kc Ψ M m pc -∗ ▷ Kc -∗ WP (Loop : expr riscv_lang))%I.

End UvObl.

(* ===================================================================== *)
(* §5b THE CYCLE'S TAIL, ONCE FOR BOTH LANDING SHAPES.                    *)
(*                                                                        *)
(* A retiring cycle and a trapping one land on files that differ only in   *)
(* the privilege and in what the trap tower wrote; in BOTH the tail is     *)
(* [wrap_post], so PC = nextPC = [rs2]'s nextPC and every other cell of    *)
(* the footprint reads through.  One lemma therefore takes the frames      *)
(* apart and rebuilds the tier's bundles for both.                        *)
(* ===================================================================== *)

Section UvLandClose.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Lemma uv_land_close (M : gmap Z (bv 8)) (g : regfile) (npc : mword 64)
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (p : Privilege)
      (rs2 rs3 : regstate) :
    uv_tail rs2 rs3 ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = p ->
    register_lookup (R_bitvector_64 nextPC) rs2 = npc ->
    u_gpr_agree g rs2 ->
    g (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    uv_tree_ok pt (upa_map pt M) t ->
    tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rs2) ->
    hreg_frame rs3 u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rs3 u_Dro -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    (hart_state ↦ᵣ HART_ACTIVE tt ∗ cur_privilege ↦ᵣ p ∗
     mstatus ↦ᵣ (register_lookup (R_bitvector_64 mstatus) rs2) ∗
     scause ↦ᵣ (register_lookup (R_bitvector_64 scause) rs2) ∗
     stval ↦ᵣ (register_lookup (R_bitvector_64 stval) rs2) ∗
     sepc ↦ᵣ (register_lookup (R_bitvector_64 sepc) rs2) ∗
     pc_is npc ∗ gpr_file g ∗ user_cfg C ∗
     utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem pt M).
  Proof.
    intros Htail Lhs Lpriv Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv Lmste
      Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok.
    (* every cell of the footprint but PC and minstret reads through *)
    assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
              register_beq r (R_bitvector_64 minstret) = false ->
              register_beq r (R_bitvector_64 PC) = false ->
              register_lookup r rs3 = register_lookup r rs2)
      by (intros r H1 H2 H3 H4; exact (uv_tail_reg rs2 rs3 r Htail H1 H2 H3 H4)).
    assert (Lhs3 : register_lookup hart_state rs3 = HART_ACTIVE tt)
      by (rewrite (T _ u_in_hart ltac:(uv_notin_clock) eq_refl eq_refl); exact Lhs).
    assert (Lpriv3 : register_lookup cur_privilege rs3 = p)
      by (rewrite (T _ u_in_priv ltac:(uv_notin_clock) eq_refl eq_refl); exact Lpriv).
    assert (Lpc3 : register_lookup (R_bitvector_64 PC) rs3 = npc)
      by (rewrite (uv_tail_pc rs2 rs3 Htail); exact Lnpc).
    assert (Lnpc3 : register_lookup (R_bitvector_64 nextPC) rs3 = npc)
      by (rewrite (T _ u_in_nPC ltac:(uv_notin_clock) eq_refl eq_refl); exact Lnpc).
    assert (Lstvec3 : register_lookup (R_bitvector_64 stvec) rs3 = uc_stvec C)
      by (rewrite (T _ u_in_stvec ltac:(uv_notin_clock) eq_refl eq_refl); exact Lstvec).
    assert (Lmie3 : register_lookup (R_bitvector_64 mie) rs3 = uc_mie C)
      by (rewrite (T _ u_in_mie ltac:(uv_notin_clock) eq_refl eq_refl); exact Lmie).
    assert (Lmdl3 : register_lookup (R_bitvector_64 mideleg) rs3 = uc_mideleg C)
      by (rewrite (T _ u_in_mdl ltac:(uv_notin_clock) eq_refl eq_refl); exact Lmdl).
    assert (Lmedl3 : register_lookup (R_bitvector_64 medeleg) rs3 = uc_medeleg C)
      by (rewrite (T _ u_in_medl ltac:(uv_notin_clock) eq_refl eq_refl); exact Lmedl).
    assert (Lmenv3 : register_lookup (R_bitvector_64 menvcfg) rs3 = MENVCFG_S)
      by (rewrite (T _ u_in_menv ltac:(uv_notin_clock) eq_refl eq_refl); exact Lmenv).
    assert (Lmste3 : register_lookup (R_bitvector_64 mstateen0) rs3
                     = (mword_of_int 0 : mword 64))
      by (rewrite (T _ u_in_mste ltac:(uv_notin_clock) eq_refl eq_refl); exact Lmste).
    assert (Lsste3 : register_lookup (R_bitvector_32 sstateen0) rs3
                     = (mword_of_int 0 : mword 32))
      by (rewrite (T _ u_in_sste ltac:(uv_notin_clock) eq_refl eq_refl); exact Lsste).
    assert (Lsenv3 : register_lookup (R_bitvector_64 senvcfg) rs3
                     = (mword_of_int 0 : mword 64))
      by (rewrite (T _ u_in_senv ltac:(uv_notin_clock) eq_refl eq_refl); exact Lsenv).
    assert (Lsatp3 : register_lookup (R_bitvector_64 satp) rs3 = usatp)
      by (rewrite (T _ u_in_satp ltac:(uv_notin_clock) eq_refl eq_refl); exact Lsatp).
    assert (Lpcfg3 : register_lookup pmpcfg_n rs3 = pcfg)
      by (rewrite (T _ u_in_pcfg ltac:(uv_notin_clock) eq_refl eq_refl); exact Lpcfg).
    assert (Lpaddr3 : register_lookup pmpaddr_n rs3 = paddr)
      by (rewrite (T _ u_in_paddr ltac:(uv_notin_clock) eq_refl eq_refl); exact Lpaddr).
    assert (Ltlb3 : register_lookup tlb rs3 = register_lookup tlb rs2)
      by (exact (T _ u_in_tlb ltac:(uv_notin_clock) eq_refl eq_refl)).
    (* ...including every GPR, at a SYMBOLIC index *)
    assert (Hgag3 : u_gpr_agree g rs3).
    { intros i Hnz.
      rewrite (T _ (u_gpr_in_D i Hnz) (uv_gpr_notin_clock3 (uint i))
                 (regbeq_gpr_minstret (uint i)) (regbeq_gpr_PC (uint i))).
      exact (Hgag i Hnz). }
    assert (Hgeq : g = u_regfile rs3) by exact (uv_regfile_eq g rs3 Hgag3 Hx0).
    (* ---- the five pin bundles at [rs3] ---- *)
    assert (Hregs : u_pins_regs_at p rs3 (HART_ACTIVE tt)
              (register_lookup (R_bitvector_64 mstatus) rs2)
              (register_lookup (R_bitvector_64 scause) rs2)
              (register_lookup (R_bitvector_64 stval) rs2)
              (register_lookup (R_bitvector_64 sepc) rs2)
              npc npc (u_regfile rs3)).
    { rewrite /u_pins_regs_at. split_and!;
        [ exact Lhs3 | exact Lpriv3
        | exact (T _ u_in_mst ltac:(uv_notin_clock) eq_refl eq_refl)
        | exact (T _ u_in_scause ltac:(uv_notin_clock) eq_refl eq_refl)
        | exact (T _ u_in_stval ltac:(uv_notin_clock) eq_refl eq_refl)
        | exact (T _ u_in_sepc ltac:(uv_notin_clock) eq_refl eq_refl)
        | exact Lpc3 | exact Lnpc3 | exact (u_regfile_agree rs3) ]. }
    assert (Htick : u_pins_tick rs3
              (register_lookup (R_bitvector_64 minstret) rs3)
              (register_lookup (R_bool minstret_increment) rs3)
              (register_lookup (R_bitvector_32 mcountinhibit) rs3)
              (register_lookup (R_bitvector_64 minstretcfg) rs3)
              (register_lookup (R_bitvector_64 mcycle) rs3)
              (register_lookup (R_bitvector_64 mtime) rs3)
              (register_lookup (R_bitvector_64 mip) rs3))
      by (rewrite /u_pins_tick; split_and!; reflexivity).
    assert (Hcfg : u_pins_cfg rs3 (uc_stvec C) (uc_mie C) (uc_mideleg C)
              (uc_medeleg C) MENVCFG_S (mword_of_int 0 : mword 64)
              (mword_of_int 0 : mword 32)
              (register_lookup (R_bitvector_32 mcounteren) rs3)
              (register_lookup (R_bitvector_32 scounteren) rs3)
              (register_lookup mhpmcounter rs3)).
    { rewrite /u_pins_cfg. split_and!;
        [ exact Lstvec3 | exact Lmie3 | exact Lmdl3 | exact Lmedl3
        | exact Lmenv3 | exact Lmste3 | exact Lsste3
        | reflexivity | reflexivity | reflexivity ]. }
    assert (Hhw : u_pins_hw rs3
              (register_lookup (R_bitvector_64 misa) rs3)
              (register_lookup (R_bitvector_64 mseccfg) rs3)
              (mword_of_int 0 : mword 64)
              (register_lookup pma_regions rs3)
              (register_lookup htif_tohost_base rs3)
              (register_lookup (R_bitvector_1 elp) rs3)).
    { rewrite /u_pins_hw. split_and!;
        [ reflexivity | reflexivity | exact Lsenv3
        | reflexivity | reflexivity | reflexivity ]. }
    assert (Hpt : u_pins_pt rs3 usatp pcfg paddr (register_lookup tlb rs3))
      by (rewrite /u_pins_pt; split_and!;
          [ exact Lsatp3 | exact Lpcfg3 | exact Lpaddr3 | reflexivity ]).
    iIntros "Hrw Hro Hresv Hmm [#Hclaims Hcl]".
    iDestruct (u_frames_elim_at p rs3 (uc_dqc C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 Hregs Htick Hcfg Hhw Hpt with "Hrw Hro")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & HPC & HnPC & Hgpr &
           Hminstret & Hmincr & #Hmcnt & #Hmicfg & Hmcycle & Hmtime & Hmip &
           Hstvec & Hmie & Hmdl & #Hmedl & Hmenv & #Hmste & #Hsste & #Hmcen &
           #Hscen & #Hhpm & #Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help &
           #Hsenv & Hsatp & Htlb & Hpcfg & Hpaddr)".
    iDestruct ("Hcl" $! t (register_lookup tlb rs3)
                 with "[%] [%] [%] Hsatp Htlb Hpcfg Hpaddr Hmm")
      as "[Hutlb Humem]".
    { apply pt_same_shape_refl. }
    { exact Htok. }
    { rewrite Ltlb3. exact Htlbok. }
    rewrite <- Hgeq.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hutlb Humem".
    iSplitL "HPC HnPC Hminstret Hmincr Hmcycle Hmtime Hmip Hresv".
    { rewrite /pc_is /minstret_res /clock_res. iFrame "HPC HnPC Hresv".
      iSplitL "Hminstret Hmincr".
      - iExists _, _, _, _. iFrame "Hminstret Hmincr Hmcnt Hmicfg".
      - iExists _, _, _. iFrame "Hmcycle Hmtime Hmip". }
    rewrite /user_cfg. iFrame "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmste Hsste".
    iSplitR; [ iExists _, _; iFrame "Hmcen Hscen" | iExists _; iFrame "Hhpm" ].
  Qed.

End UvLandClose.

(* peel the trap tower's landing file down to the file it started from --
   [UserActiveClass]'s [u_trap_peel], plus the SYMBOLIC-GPR variant its
   concrete [vm_compute] side condition cannot serve *)
Local Ltac uv_trap_peel :=
  unfold u_trap_rs; cbv zeta;
  repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).

Local Ltac uv_gpr_ne := unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity.

Lemma uv_gpr_agree_trap (g : regfile) (rsf : regstate) (c : TrapCause)
    (info : option (mword 64)) (pcx sv : mword 64) :
  u_gpr_agree g rsf -> u_gpr_agree g (u_trap_rs rsf c info pcx sv).
Proof.
  intros Hag i Hnz. rewrite (Hag i Hnz).
  unfold u_trap_rs; cbv zeta.
  repeat (rewrite irrelevant_register_set; [ | uv_gpr_ne ]).
  reflexivity.
Qed.

(* ===================================================================== *)
(* §5c THE TWO PAYLOAD BUILDERS AND THE INTERRUPT ARM.                    *)
(* ===================================================================== *)

Section UvArms.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* the RETIRING payload: the process runs on, at the new file and pc *)
  Lemma uv_psi_active (R : iProp Σ) (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m' : regfile) (npc : mword 64) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs2 : regstate) :
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    register_lookup (R_bitvector_64 nextPC) rs2 = npc ->
    u_gpr_agree m' rs2 ->
    m' (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    uv_tree_ok pt (upa_map pt M) t ->
    tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rs2) ->
    uv_amb -∗ uv_cap C pt Ψ -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    (R -∗ ∀ CID0 : CpuId, uv_cap_gpr (CID := CID0) C pt Ψ M m' -∗
       pc_is (CID := CID0) npc -∗ WP (Loop : expr riscv_lang)) -∗
    uv_psi C R rs2.
  Proof.
    intros Lhs Lpriv Hmsok Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv Lmste
      Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok.
    iIntros "#Hamb #Hcap Hresv Hmm Hres Hk".
    rewrite /uv_psi. iFrame "Hresv".
    iIntros (rs3) "%Htail Hrw Hro Hresv HR".
    iDestruct ("Hk" with "HR") as "Hcont".
    iDestruct (uv_land_close C pt M m' npc t usatp pcfg paddr User rs2 rs3
                 Htail Lhs Lpriv Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv
                 Lmste Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok
                 with "Hrw Hro Hresv Hmm Hres")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hgpr & Hcfg &
           Hutlb & Humem)".
    iApply ("Hcont" $! CID with "[-Hpc] Hpc").
    rewrite /uv_cap_gpr /uv_lin /uv_regs.
    iFrame "Hcap Hamb Hutlb Humem Hcfg Hgpr".
    iExists _, _, _, _. iSplitR; [ iPureIntro; exact Hmsok |].
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc".
  Qed.

  (* the TRAPPING payload: the kernel takes over at [stvec_base] *)
  Lemma uv_psi_trap (R : iProp Σ) (M : gmap Z (bv 8))
      (g : regfile) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs2 : regstate) (sc_v stv_v sep_v : mword 64) :
    register_lookup (R_bitvector_64 scause) rs2 = sc_v ->
    register_lookup (R_bitvector_64 stval) rs2 = stv_v ->
    register_lookup (R_bitvector_64 sepc) rs2 = sep_v ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = Supervisor ->
    trap_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    register_lookup (R_bitvector_64 nextPC) rs2 = stvec_base (uc_stvec C) ->
    u_gpr_agree g rs2 ->
    g (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    uv_tree_ok pt (upa_map pt M) t ->
    tlb_ok_pt (mword_of_int 0) t (register_lookup tlb rs2) ->
    resv_any cpu_id -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    (uv_trap_frame C pt sc_v stv_v sep_v g M -∗ R -∗
     WP (Loop : expr riscv_lang)) -∗
    uv_psi C R rs2.
  Proof.
    intros Lsc Lstv Lsep.
    subst sc_v stv_v sep_v.
    intros Lhs Lpriv Hmsok Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv Lmste
      Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok.
    iIntros "Hresv Hmm Hres Hcont".
    rewrite /uv_psi. iFrame "Hresv".
    iIntros (rs3) "%Htail Hrw Hro Hresv Hresume".
    iDestruct (uv_land_close C pt M g (stvec_base (uc_stvec C)) t usatp pcfg
                 (* the trapped landing shape *)
                 paddr Supervisor rs2 rs3
                 Htail Lhs Lpriv Lnpc Hgag Hx0 Lstvec Lmie Lmdl Lmedl Lmenv
                 Lmste Lsste Lsenv Lsatp Lpcfg Lpaddr Htok Htlbok
                 with "Hrw Hro Hresv Hmm Hres")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hgpr & Hcfg &
           Hutlb & Humem)".
    iApply ("Hcont" with "[-Hresume] Hresume"). rewrite /uv_trap_frame.
    iExists _. iSplitR; [ iPureIntro; exact Hmsok |].
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hgpr Hutlb Humem Hcfg".
  Qed.

  (* ---- ARM 1: a pending delegated interrupt.  The frame goes to the
     capability's [uv_intr_wp] and comes back -- same (M, m, pc), ARBITRARY
     hart -- at the wrapper's resume wand. *)
  Lemma uv_arm_intr (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (t : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA : regstate) (i : InterruptType) (Kc : iProp Σ) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    gen_cert -∗ uv_cap C pt Ψ -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    uv_step_obl C pt Kc Ψ M m pc -∗
    uv_step_post C (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I rs1
      (Step_Pending_Interrupt (i, Supervisor)).
  Proof.
    intros (Hinj & Htok & Hpins & Lhs & Lpriv & Hmsok & Lpc & Hgag & Lstvec &
            Lmie & Lmdl & Lmedl & Lmenv & Lsatp & Lpcfg & Lpaddr & Lmi & Hx0).
    pose proof Hpins as ((Hmisa & Hsec & Hsenv & Hhtif & Hall & Helpne) &
                         (Hmste & Hsste) & _ & Htlbok).
    pose proof (elp_no_lp _ Helpne) as Lelp.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsA))
                       ('b"1") = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    iIntros "#Hcert #Hcap Hany Hrw Hro Hmm Hres Hobl".
    iDestruct "Hcap" as "[#Hintr #Hsys]".
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    rewrite Lelp.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hmm Hres Hobl".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs | uv_trap_peel; exact Lmi | exact I ]. }
    iApply (swp_mono with "[Hmm Hres Hobl] [Hany Hrw Hro]").
    2:{ iApply (swp_handle_interrupt_u
                  (u_state rsA (uv_mm t (upa_map pt M)))
                  (Interrupt i) None pc
                  (register_lookup (R_bitvector_64 mstatus) rsA)
                  (register_lookup (R_bitvector_64 scause) rsA)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lpriv eq_refl eq_refl Lstvec Lelp HmisaS (uc_tvd C) Lpc
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rsA i eq_refl eq_refl
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(intros r _; reflexivity) eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs'
                 (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)) u_Drw
                 ltac:(intros r Hr; apply Hag, elem_of_union_l, Hr)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C)) u_Dro
                 ltac:(intros r Hr; apply Hag, elem_of_union_r, Hr)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I M m t usatp pcfg paddr
              (u_trap_rs rsA (Interrupt i) None pc (uc_stvec C))
              (utrap_scause (Interrupt i) (register_lookup (R_bitvector_64 scause) rsA))
              (tval None) pc
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; exact Lhs)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsok))
              ltac:(uv_trap_peel; apply register_lookup_set)
              (uv_gpr_agree_trap m rsA _ _ _ _ Hgag) Hx0
              ltac:(uv_trap_peel; exact Lstvec)
              ltac:(uv_trap_peel; exact Lmie)
              ltac:(uv_trap_peel; exact Lmdl)
              ltac:(uv_trap_peel; exact Lmedl)
              ltac:(uv_trap_peel; exact Lmenv)
              ltac:(uv_trap_peel; exact Hmste)
              ltac:(uv_trap_peel; exact Hsste)
              ltac:(uv_trap_peel; exact Hsenv)
              ltac:(uv_trap_peel; exact Lsatp)
              ltac:(uv_trap_peel; exact Lpcfg)
              ltac:(uv_trap_peel; exact Lpaddr)
              Htok ltac:(uv_trap_peel; exact Htlbok)
              with "Hany Hmm Hres [Hintr Hobl]").
    iIntros "Hframe [Hih Hkc]".
    iApply ("Hintr" $! CID m M pc i
              (register_lookup (R_bitvector_64 scause) rsA) (tval None)
              with "Hframe").
    iIntros (CID') "Hrun".
    iDestruct (uv_run_cap_gpr (CID := CID') C pt Ψ M m pc
                 with "[$Hintr $Hsys] Hrun") as "[Hcg Hpc']".
    iApply ("Hih" $! CID' with "Hcg Hpc' Hobl [Hkc]"). iNext. iExact "Hkc".
  Qed.

End UvArms.

(* ---- the two transports across the cycle's minstret PRELUDE ---------- *)
Lemma uv_pins_wpre (P : uptd) (t : ptree) (rs : regstate) :
  u_exec_pins P t rs -> u_exec_pins P t (wrap_pre rs).
Proof.
  intros H. unfold u_exec_pins, u_hw_pins, u_cfg_pins, u_pt_pins in H |- *.
  repeat (rewrite wrap_pre_other; [ | vm_compute; reflexivity ]).
  exact H.
Qed.

Lemma uv_gpr_agree_wpre (g : regfile) (rs : regstate) :
  u_gpr_agree g rs -> u_gpr_agree g (wrap_pre rs).
Proof.
  intros Hag i Hnz. rewrite (Hag i Hnz). symmetry.
  exact (wrap_pre_other (R_bitvector_64 (gpr_of_Z (uint i))) rs
           (regbeq_gpr_minc (uint i))).
Qed.

(* ===================================================================== *)
(* §5d THE ENGINE.                                                        *)
(* ===================================================================== *)

Section UvStepEngine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* THE ENGINE, in the hart-quantified form the Loeb induction needs: only
     [CID] is bound inside the entailment, everything else is a lemma
     binder, so the induction hypothesis can be re-applied at the RESUMING
     hart after a migration. *)
  Lemma wp_uv_step_gen (Kc : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) :
    ⊢ uv_ih C pt Kc Ψ M m pc.
  Proof.
    rewrite /uv_ih.
    iLöb as "IH".
    iIntros (CID) "(#Hcap & Hlin & Hgpr) Hpc Hobl Hkc".
    iDestruct "Hlin" as "(#Hamb & Hregs & Hutlb & Humem & Hcfg)".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iDestruct "Hregs" as (ms_v sc_v stval_v sepc_v)
      "(%Hmsok & Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc)".
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (mst mi mc micfg) "(Hminstret & Hmincr & #Hmcnt & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hmcycle & Hmtime & Hmip)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & #Hmedl & Hmenv & #Hsenv &
                          #Hmste & #Hsste & Hctr & Hhpmb)".
    iDestruct "Hctr" as (mcenv scenv) "[#Hmcen #Hscen]".
    iDestruct "Hhpmb" as (hpm) "#Hhpm".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenvhw &
        _ & _ & _ & _ & %Hpmaall & _ & _ & %Helpne & _ &
        %Hmisaeq & %Hseceq & _ & #Hcert & _)".
    iDestruct (gpr_file_x0 m (mword_of_int 0)
                 ltac:(apply (u_uint_mword5 0); lia) with "Hgpr")
      as "[%Hx0 Hgpr]".
    iDestruct (uv_pt_open pt M with "Hutlb Humem")
      as (t usatp tlbvec pcfg paddr)
         "(%Hinj & %Htok & %Hsatpok & %Hpmpok & %Htlbok &
           Hsatp & Htlb & Hpcfg & Hpaddr & #Hclaims & Hmm & Hcl)".
    pose proof Hpmpok as (HpA & Hpord & HpX & HpW & HpR & Hpcov).
    (* ---- the entry file ---- *)
    set (RS := u_rs m (HART_ACTIVE tt) mi mc (mword_of_int 0 : mword 32)
                 mcenv scenv hpm elp0 pmar0 None pcfg paddr tlbvec
                 pc pc ms_v sc_v stval_v sepc_v mst cy ti ip micfg
                 misa0 mseccfg0 (mword_of_int 0 : mword 64)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C) (uc_medeleg C)
                 MENVCFG_S (mword_of_int 0 : mword 64) usatp).
    iDestruct (u_frames_intro RS (uc_dqc C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (u_rs_pins_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_tick _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_cfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr
                       Hminstret Hmincr Hmcnt Hmicfg Hmcycle Hmtime Hmip
                       Hstvec Hmie Hmdl Hmedl Hmenv Hmste Hsste
                       Hmcen Hscen Hhpm
                       Hmisa Hmseccfg Hpma Hhtif Help Hsenv
                       Hsatp Htlb Hpcfg Hpaddr")
      as "[Hrw Hro]".
    (* ---- the ambient pins, at the entry file and after the prelude ---- *)
    assert (HpinsR : u_exec_pins pt t RS).
    { rewrite /u_exec_pins /u_hw_pins /u_cfg_pins /u_pt_pins.
      split_and!;
        [ exact Hmisaeq | exact Hseceq | reflexivity | reflexivity
        | exact Hpmaall | exact Helpne
        | reflexivity | reflexivity
        | exists usatp; split; [ exact Hsatpok | reflexivity ]
        | exact HpA | exact Hpord | exact HpX | exact HpW | exact HpR
        | exact Hpcov
        | exact Htlbok ]. }
    assert (Hpre : uv_pre C pt M m pc t RS (wrap_pre RS) usatp pcfg paddr).
    { rewrite /uv_pre. split_and!.
      - exact Hinj.
      - exact Htok.
      - exact (uv_pins_wpre pt t RS HpinsR).
      - rewrite (wrap_pre_other hart_state RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other cur_privilege RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mstatus) RS
                   ltac:(vm_compute; reflexivity)). exact Hmsok.
      - rewrite (wrap_pre_other (R_bitvector_64 PC) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - apply uv_gpr_agree_wpre.
        exact (u_rs_gpr_agree m (HART_ACTIVE tt) mi mc _ mcenv scenv hpm elp0
                 pmar0 None pcfg paddr tlbvec pc pc ms_v sc_v stval_v sepc_v
                 mst cy ti ip micfg misa0 mseccfg0 _ (uc_stvec C) (uc_mie C)
                 (uc_mideleg C) (uc_medeleg C) MENVCFG_S _ usatp).
      - rewrite (wrap_pre_other (R_bitvector_64 stvec) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mie) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 mideleg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 medeleg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 menvcfg) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other (R_bitvector_64 satp) RS
                   ltac:(vm_compute; reflexivity)). reflexivity.
      - rewrite (wrap_pre_other pmpcfg_n RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - rewrite (wrap_pre_other pmpaddr_n RS ltac:(vm_compute; reflexivity)).
        reflexivity.
      - exact (wrap_pre_mi RS).
      - exact Hx0. }
    pose proof Hpre as (_ & _ & HpinsA & LhsA & LcpA & HmsokA & LpcA & _ &
                        LstvecA & LmieA & LmdlA & LmedlA & LmenvA & LsatpA &
                        LpcfgA & LpaddrA & LmiA & _).
    pose proof HpinsA as (HhwA & HcfgpA & _ & _).
    assert (HagdA : agree_on D_u
              (u_state (wrap_pre RS) (uv_mm t (upa_map pt M))) dstateU)
      by exact (UserTotalU.u_agree_decode (wrap_pre RS) (uv_mm t (upa_map pt M))
                  LcpA LmenvA HhwA HcfgpA).
    (* ---- the one cycle ---- *)
    iApply (swp_exec_step_full u_Drw u_Dro (u_Df (uc_dqc C)) RS (wrap_pre RS)
              (uv_land RS) (uv_psi C (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I)
              u_disj u_w_cy u_w_ti u_w_ip u_in_priv u_w_hart u_in_hart
              u_in_mc u_in_micfg u_w_mi u_in_mi u_w_ms u_in_ms
              u_w_PC u_in_PC u_in_nPC
              (eq_refl : register_lookup hart_state RS = HART_ACTIVE tt)
              ltac:(intros st rs2 H; exact (proj1 H))
              ltac:(intros st rs2 H; exact (proj1 (proj2 H)))
              ltac:(intros r _; reflexivity)
              with "Hcert Hresv Hrw Hro [Hmm Hcl Hobl] [Hkc]").
    - (* ================= THE BODY SLOT ================= *)
      iIntros "Hfrag Hrw Hro".
      iApply (swp_mono with "[] [-]").
      2: iApply (swp_run_hart_active_res u_Drw u_Dro (u_Df (uc_dqc C))
                   (wrap_pre RS) User
                   (resv_frag cpu_id None ∗
                    bytes_own (uv_mm t (upa_map pt M)) ∗
                    uv_res pt M t usatp pcfg paddr ∗
                    uv_step_obl C pt Kc Ψ M m pc)%I
                   (fun (ii : InterruptType) (pr : Privilege) =>
                      uv_step_post C (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I RS
                        (Step_Pending_Interrupt (ii, pr)))
                   (fun (r : ExecutionResult) (ib : mword 32) =>
                      uv_step_post C (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I RS
                        (Step_Execute (r, ib)))
                   (fun (xv : mword 64) (e : ExceptionType) =>
                      uv_step_post C (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I RS
                        (Step_Fetch_Failure (Virtaddr xv, e)))
                   (fun _ : ext_fetch_addr_error => False%I)
                   u_disj u_in_priv u_in_PC u_w_nPC LcpA
                   with "Hcert Hrw Hro [Hfrag Hmm Hcl Hobl] [] []").
      + (* the outcome map: the three shapes this tier rules out are
           [False] on our side and anything at all on the rule's *)
        iIntros (st) "H". rewrite /uv_step_post.
        destruct st as [ [ii pr] | x | [[xv] e] | [r ib] | wq ].
        * iDestruct "H" as (rs2) "[%Hq H]".
          iExists rs2. iSplitR; [ by iPureIntro |]. iApply "H".
        * iExFalso. iExact "H".
        * iDestruct "H" as (rs2) "[%Hq H]". iExFalso. iExact "H".
        * destruct r as [u | i0 | wr0 | u1 | u2 | trp | u3 | ec | ed | u4];
            [ destruct u | | | | | destruct trp as [[p exc] pcx] | | | | ];
            iDestruct "H" as (rs2) "[%Hq H]";
            try (iExFalso; iExact "H");
            iExists rs2; (iSplitR; [ by iPureIntro |]); iApply "H".
        * iExFalso. iExact "H".
      + (* the threaded residue *)
        rewrite /uv_res. iFrame "Hfrag Hmm Hclaims Hcl Hobl".
      + (* ---- THE DISPATCH ---- *)
        iIntros "HWd Hrw Hro".
        iApply (swp_mono with "[HWd] [Hrw Hro]").
        2:{ iApply (swp_dispatchInterrupt_U u_Drw u_Dro (u_Df (uc_dqc C))
                      (wrap_pre RS) dstateU D_u
                      (register_lookup mip (wrap_pre RS)) (uc_mie C)
                      (uc_mideleg C) u_disj u_in_ip u_in_mie u_in_mdl
                      eq_refl LmieA LmdlA (uc_mm C) UserTotalU.u_D_u_sub HagdA
                      (UserTotalU.s0_ext_S dstateU ltac:(vm_compute; reflexivity))
                      ltac:(reflexivity)
                      with "Hcert Hrw Hro"). }
        iIntros (o). iDestruct 1 as (meip seip) "(%Hd & Hrw & Hro)".
        destruct o as [[ii pr] |].
        * assert (Hsup : pr = Supervisor).
          { rewrite <- u_dispatch_of_pending in Hd. unfold u_dispatch in Hd.
            destruct (neq_vec (s_pending (register_lookup mip (wrap_pre RS))
                                 meip seip (uc_mie C) (uc_mideleg C))
                        (zeros' 64)); [| discriminate Hd].
            destruct (findPendingInterrupt
                        (s_pending (register_lookup mip (wrap_pre RS)) meip seip
                           (uc_mie C) (uc_mideleg C))); [| discriminate Hd].
            congruence. }
          subst pr.
          iDestruct "HWd" as "(Hfrag & Hmm & Hres & Hobl)".
          iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
          iApply (uv_arm_intr C pt Ψ M m pc t usatp pcfg paddr RS
                    (wrap_pre RS) ii Kc Hpre
                    with "Hcert Hcap Hany Hrw Hro Hmm Hres Hobl").
        * iFrame.
      + (* ---- THE FETCH: the caller's obligation ---- *)
        iIntros "HWd Hrw Hro".
        iDestruct "HWd" as "(Hfrag & Hmm & Hres & Hobl)".
        iDestruct (resv_any_intro cpu_id None with "Hfrag") as "Hany".
        iApply ("Hobl" $! (uv_ih C pt Kc Ψ M m pc ∗ Kc)%I CID t RS (wrap_pre RS)
                  usatp pcfg paddr
                  with "[%] Hamb Hcap [] Hany Hrw Hro Hmm Hres").
        { exact Hpre. }
        iIntros "[_ $]".
    - (* ================= THE CYCLE'S TAIL ================= *)
      iNext. iIntros (rs3 rs2) "%Hag Hrw Hro [Hresv Hcl]".
      iApply ("Hcl" $! rs3 with "[%] Hrw Hro Hresv [$IH $Hkc]").
      exact (uv_tail_of RS rs2 rs3 Hag).
  Qed.

End UvStepEngine.

(* ===================================================================== *)
(* §6 THE RETIRE FUNNEL AND THE ECALL DRIVER.                             *)
(*                                                                        *)
(* The state a retiring, non-CSR, memory-preserving instruction leaves is  *)
(* always the same two-layer tower over the post-fetch state: an OPTIONAL  *)
(* nextPC redirect (a jump) and an OPTIONAL single gpr write, in THAT      *)
(* order -- which is the order the model writes them (see                 *)
(* [exec_execute_JAL_gpr]: set_next_pc first, then wX).  Both layers are   *)
(* [None] for a plain arithmetic instruction, and the leaf states its      *)
(* execute fact against exactly this tower.                               *)
(* ===================================================================== *)

Definition uv_jmp (s : mstate) (jt : option (mword 64)) : mstate :=
  match jt with Some t => set_reg s nextPC t | None => s end.

Definition uv_wr (s : mstate) (wr : option (mword 5 * mword 64)) : mstate :=
  match wr with
  | Some (rd, v) => set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)
  | None => s
  end.

(* the post-execute machine state of a retiring instruction *)
Definition uv_post (s : mstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) : mstate := uv_wr (uv_jmp s jt) wr.

(* ... and the register file / next pc it leaves *)
Definition uv_upd (m : regfile) (wr : option (mword 5 * mword 64)) : regfile :=
  match wr with
  | Some (rd, v) => <[Regidx rd := regval_into_reg v]> m
  | None => m
  end.

Definition uv_next (jt : option (mword 64)) (d : mword 64) : mword 64 :=
  match jt with Some t => t | None => d end.

(* a gpr write must not target x0 (writing x0 is a no-op the tower does not
   describe; every leaf that "writes x0" states [wr := None] instead) *)
Definition uv_wrok (wr : option (mword 5 * mword 64)) : Prop :=
  match wr with Some (rd, _) => uint rd <> 0 | None => True end.

(* the instruction actually executed: the decoded one, or -- for the
   compressed / SINVAL_VMA style [ExecuteAs] redirects -- its expansion *)
Definition uv_exp (i : instruction) (o : option instruction) : instruction :=
  match o with Some j => j | None => i end.

(* the redirect premise, in the shape the leaves' [exec_execute_C_*] facts
   already have *)
Definition uv_redirect (i : instruction) (o : option instruction) : Prop :=
  forall s : mstate,
    match o with
    | Some j => exec (execute i) s = Some (ExecuteAs j, s)
    | None => True
    end.

Lemma uv_post_nextPC (s : mstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) (d : mword 64) :
  register_lookup nextPC s.(sregs) = d ->
  register_lookup nextPC (uv_post s jt wr).(sregs) = uv_next jt d.
Proof.
  intro Hd.
  assert (Hj : register_lookup nextPC (uv_jmp s jt).(sregs) = uv_next jt d).
  { destruct jt as [t | ]; [ | exact Hd ].
    unfold uv_jmp, uv_next; rewrite ?sregs_set_reg. apply register_lookup_set. }
  unfold uv_post. destruct wr as [[rd v] | ]; [ | exact Hj ].
  unfold uv_wr; rewrite ?sregs_set_reg.
  rewrite (irrelevant_register_set _ _ _ _ (regbeq_nextPC_gpr (uint rd))).
  exact Hj.
Qed.

(* the REGISTER-level twin of the tower, which is what the frames speak *)
Definition uv_jmp_rs (rs : regstate) (jt : option (mword 64)) : regstate :=
  match jt with Some t => register_set nextPC t rs | None => rs end.

Definition uv_wr_rs (rs : regstate) (wr : option (mword 5 * mword 64))
    : regstate :=
  match wr with
  | Some (rd, v) =>
      register_set (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v) rs
  | None => rs
  end.

Definition uv_post_rs (rs : regstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) : regstate :=
  uv_wr_rs (uv_jmp_rs rs jt) wr.

Lemma uv_post_sregs (s : mstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) :
  (uv_post s jt wr).(sregs) = uv_post_rs s.(sregs) jt wr.
Proof.
  unfold uv_post, uv_post_rs, uv_jmp, uv_jmp_rs, uv_wr, uv_wr_rs.
  destruct jt as [tv | ]; destruct wr as [[rd v] | ];
    rewrite ?sregs_set_reg; reflexivity.
Qed.

(* every cell the tower does NOT write reads through *)
Lemma uv_post_rs_other (rs : regstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) (r : register) :
  register_beq r (R_bitvector_64 nextPC) = false ->
  (forall n : Z, register_beq r (R_bitvector_64 (gpr_of_Z n)) = false) ->
  register_lookup r (uv_post_rs rs jt wr) = register_lookup r rs.
Proof.
  intros Hnpc Hgpr. unfold uv_post_rs, uv_jmp_rs, uv_wr_rs.
  destruct jt as [tv | ]; destruct wr as [[rd v] | ];
    repeat (rewrite irrelevant_register_set; [ | first [ exact Hnpc | apply Hgpr ] ]);
    reflexivity.
Qed.

(* [gpr_of_Z] is INJECTIVE on x1..x31 -- the one pure fact a gpr write at a
   SYMBOLIC index needs, and the only 31x31 split in this file.  Each leaf is
   a [register_beq] of two distinct constructors, i.e. milliseconds. *)
Lemma uv_idx_cases (x : Z) : 0 < x < 32 -> x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31.
Proof. lia. Qed.

Lemma uv_gpr_of_Z_ne (a b : Z) :
  0 < a < 32 -> 0 < b < 32 -> a <> b ->
  register_beq (R_bitvector_64 (gpr_of_Z a)) (R_bitvector_64 (gpr_of_Z b))
  = false.
Proof.
  intros Ha Hb Hne.
  pose proof (uv_idx_cases a Ha) as Hca.
  pose proof (uv_idx_cases b Hb) as Hcb.
  repeat (destruct Hca as [Hca | Hca]);
    repeat (destruct Hcb as [Hcb | Hcb]);
    subst; try (exfalso; exact (Hne eq_refl)); vm_compute; reflexivity.
Qed.

Lemma uv_gpr_agree_post (g : regfile) (rs : regstate) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) :
  uv_wrok wr -> u_gpr_agree g rs ->
  u_gpr_agree (uv_upd g wr) (uv_post_rs rs jt wr).
Proof.
  intros Hok Hag i Hnz.
  unfold uv_post_rs, uv_jmp_rs, uv_wr_rs, uv_upd.
  destruct wr as [[rd v] | ].
  - cbn [uv_wrok] in Hok.
    destruct (decide (i = rd)) as [-> | Hne].
    + rewrite <- (rf_lookup (<[Regidx rd := regval_into_reg v]> g) (Regidx rd)).
      rewrite upd_eq. rewrite register_lookup_set. reflexivity.
    + assert (Hnr : Regidx i <> Regidx rd)
        by (intros Hc; injection Hc as Hc; exact (Hne Hc)).
      assert (Hni : uint i <> uint rd).
      { intros Heq. apply Hne. apply bv_eq.
        rewrite <- (u_uint5_bv i), <- (u_uint5_bv rd). exact Heq. }
      rewrite <- (rf_lookup (<[Regidx rd := regval_into_reg v]> g) (Regidx i)).
      rewrite (upd_ne g (Regidx rd) (Regidx i) (regval_into_reg v) Hnr).
      rewrite rf_lookup.
      rewrite (irrelevant_register_set _ _ _ _
                 (uv_gpr_of_Z_ne (uint i) (uint rd)
                    ltac:(pose proof (uint5_lt i); lia)
                    ltac:(pose proof (uint5_lt rd); lia) Hni)).
      destruct jt as [tv | ];
        [ rewrite (irrelevant_register_set _ _ _ _ (regbeq_gpr_nextPC (uint i))) | ];
        exact (Hag i Hnz).
  - destruct jt as [tv | ];
      [ rewrite (irrelevant_register_set _ _ _ _ (regbeq_gpr_nextPC (uint i))) | ];
      exact (Hag i Hnz).
Qed.

Lemma uv_upd_x0 (g : regfile) (wr : option (mword 5 * mword 64)) :
  uv_wrok wr -> g (Regidx (mword_of_int 0)) = zero_reg ->
  uv_upd g wr (Regidx (mword_of_int 0)) = zero_reg.
Proof.
  intros Hok Hx0. unfold uv_upd. destruct wr as [[rd v] | ]; [ | exact Hx0 ].
  cbn [uv_wrok] in Hok.
  assert (Hne : Regidx (mword_of_int 0) <> Regidx rd).
  { intros Heq. injection Heq as Heq. apply Hok. rewrite <- Heq.
    exact (u_uint_mword5 0 ltac:(lia)). }
  rewrite <- (rf_lookup (<[Regidx rd := regval_into_reg v]> g)
                (Regidx (mword_of_int 0))).
  rewrite (upd_ne g (Regidx rd) (Regidx (mword_of_int 0)) (regval_into_reg v) Hne).
  rewrite rf_lookup. exact Hx0.
Qed.

(* the gpr READS an execute obligation is stated over *)
Lemma uv_gpr_vals (g : regfile) (rs : regstate) :
  u_gpr_agree g rs -> g (Regidx (mword_of_int 0)) = zero_reg ->
  forall r : mword 5,
    (if Z.eqb (uint r) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) rs)
    = g !!! Regidx r.
Proof.
  intros Hag Hx0 r.
  destruct (decide (uint r = 0)) as [Hz | Hnz].
  - rewrite (proj2 (Z.eqb_eq (uint r) 0) Hz).
    change (g !!! Regidx r) with (g (Regidx r)).
    rewrite (u_mword5_eq r 0 ltac:(lia) Hz). exact (eq_sym Hx0).
  - rewrite (proj2 (Z.eqb_neq (uint r) 0) Hnz).
    change (g !!! Regidx r) with (g (Regidx r)).
    exact (eq_sym (Hag r Hnz)).
Qed.


(* a NAMED register is never a GPR -- the symbolic-index side condition of
   every peel through the retire tower, proved once per name (WpGpr's
   [regbeq_gpr_*] recipe: 31 [vm_compute]s each, in an empty context). *)
Definition uv_nogpr (r : register) : Prop :=
  forall n : Z, register_beq r (R_bitvector_64 (gpr_of_Z n)) = false.

Local Ltac uv_nogpr_tac :=
  intro n; unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity.

Lemma uv_nogpr_minc : uv_nogpr (R_bool minstret_increment).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_hart : uv_nogpr hart_state.
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_priv : uv_nogpr cur_privilege.
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_mst : uv_nogpr (R_bitvector_64 mstatus).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_sc : uv_nogpr (R_bitvector_64 scause).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_stv : uv_nogpr (R_bitvector_64 stval).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_sep : uv_nogpr (R_bitvector_64 sepc).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_stvec : uv_nogpr (R_bitvector_64 stvec).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_mie : uv_nogpr (R_bitvector_64 mie).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_mdl : uv_nogpr (R_bitvector_64 mideleg).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_medl : uv_nogpr (R_bitvector_64 medeleg).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_menv : uv_nogpr (R_bitvector_64 menvcfg).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_mste : uv_nogpr (R_bitvector_64 mstateen0).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_sste : uv_nogpr (R_bitvector_32 sstateen0).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_senv : uv_nogpr (R_bitvector_64 senvcfg).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_satp : uv_nogpr (R_bitvector_64 satp).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_pcfg : uv_nogpr pmpcfg_n.
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_paddr : uv_nogpr pmpaddr_n.
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_tlb : uv_nogpr tlb.
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_misa : uv_nogpr (R_bitvector_64 misa).
Proof. uv_nogpr_tac. Qed.

Lemma uv_nogpr_elp : uv_nogpr (R_bitvector_1 elp).
Proof. uv_nogpr_tac. Qed.

(* peel a named cell through the retire tower and the [nextPC := pc+k] write *)
Lemma uv_land_reg (rs : regstate) (v : mword 64) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) (r : register) (val : type_of_register r) :
  register_beq r (R_bitvector_64 nextPC) = false ->
  uv_nogpr r ->
  register_lookup r rs = val ->
  register_lookup r (uv_post_rs (register_set nextPC v rs) jt wr) = val.
Proof.
  intros H1 H2 Hv.
  rewrite (uv_post_rs_other _ jt wr r H1 H2).
  rewrite (irrelevant_register_set r (R_bitvector_64 nextPC) rs v H1). exact Hv.
Qed.

Lemma uv_land_nextPC (rs : regstate) (v : mword 64) (jt : option (mword 64))
    (wr : option (mword 5 * mword 64)) :
  register_lookup (R_bitvector_64 nextPC)
    (uv_post_rs (register_set nextPC v rs) jt wr) = uv_next jt v.
Proof.
  unfold uv_post_rs, uv_jmp_rs, uv_wr_rs, uv_next.
  destruct jt as [tv | ]; destruct wr as [[rd vv] | ];
    repeat (rewrite irrelevant_register_set; [ | apply regbeq_nextPC_gpr ]);
    apply register_lookup_set.
Qed.

(* ---- the U-mode CONFIG agreement, transported to the leaf's state -----
   A retiring instruction that JUMPS needs more of the machine than its pc
   and its registers: [jump_to] consults Zca (the C extension gates the
   2-aligned-target relaxation) and [update_elp_state] consults Zicfilp.
   Both are functions of the very read-set the funnel already establishes
   at the fetched state -- [agree_on D_u sf dstateU] -- so the funnel hands
   the leaf THAT one fact (it survives the [nextPC := pc + k] write), and
   the leaf projects out whatever config value its execute obligation
   needs.  Nothing else about the machine leaks into a leaf. *)

Lemma D_u_ne_nextPC (r : register) : D_u r = true -> register_beq r nextPC = false.
Proof.
  unfold D_u. intro Hr.
  repeat (apply orb_true_elim in Hr as [Hr | Hr]);
    apply register_beq_eq in Hr; subst r; vm_compute; reflexivity.
Qed.

Lemma agree_u_set_nextPC (s : mstate) (v : mword 64) :
  agree_on D_u s dstateU -> agree_on D_u (set_reg s nextPC v) dstateU.
Proof.
  intros Hag r Hr. rewrite <- (Hag r Hr).
  rewrite ?sregs_set_reg.
  apply irrelevant_register_set. exact (D_u_ne_nextPC r Hr).
Qed.

Lemma agree_u_priv (s : mstate) :
  agree_on D_u s dstateU -> register_lookup cur_privilege s.(sregs) = User.
Proof.
  intro H.
  rewrite (H (R_Privilege cur_privilege) ltac:(vm_compute; reflexivity)).
  vm_compute; reflexivity.
Qed.

Lemma agree_u_misa (s : mstate) :
  agree_on D_u s dstateU -> register_lookup misa s.(sregs) = MISA_C.
Proof.
  intro H.
  rewrite (H (R_bitvector_64 misa) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

Lemma agree_u_menvcfg (s : mstate) :
  agree_on D_u s dstateU -> register_lookup menvcfg s.(sregs) = MENVCFG_S.
Proof.
  intro H.
  rewrite (H (R_bitvector_64 menvcfg) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

Lemma agree_u_senvcfg (s : mstate) :
  agree_on D_u s dstateU ->
  register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64).
Proof.
  intro H.
  rewrite (H (R_bitvector_64 senvcfg) ltac:(vm_compute; reflexivity)).
  first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* the two extension gates a jumping leaf needs, straight off the
   agreement (Zca from misa.C; Zicfilp off because get_xLPE at User reads
   senvcfg.LPE and [user_cfg] pins senvcfg = 0) *)
Lemma agree_u_zca (s : mstate) :
  agree_on D_u s dstateU -> exec (currentlyEnabled Ext_Zca) s = Some (true, s).
Proof.
  intro H. apply exec_currentlyEnabled_Zca.
  rewrite (agree_u_misa s H). vm_compute; reflexivity.
Qed.

(* verbatim [UserTotalU.s0_zicfilp], restated off the agreement so the
   verified tier does not have to Require the classification/totality
   tower.  RELOCATION DEBT: the two should become one lemma once
   UserTotalU's copy can be re-derived from this one. *)
Lemma agree_u_zicfilp (s : mstate) :
  agree_on D_u s dstateU -> exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
Proof.
  intro Hag.
  pose proof (agree_u_priv s Hag) as Hpriv.
  pose proof (agree_u_misa s Hag) as Hmisa.
  pose proof (agree_u_menvcfg s Hag) as Hmenv.
  pose proof (agree_u_senvcfg s Hag) as Hsenv.
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

(* ===================================================================== *)
(* §6b THE FUNNEL'S POST-FETCH HALF, geometry-agnostic.                   *)
(* ===================================================================== *)

Section UvFunnel.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* the engine at the ambient hart *)
  Lemma wp_uv_step (Kc : iProp Σ) (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) :
    uv_cap_gpr C pt Ψ M m -∗ pc_is pc -∗ uv_step_obl C pt Kc Ψ M m pc -∗
    ▷ Kc -∗ WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hcg Hpc Hobl Hkc".
    iPoseProof (wp_uv_step_gen C pt Kc Ψ M m pc) as "H". rewrite /uv_ih.
    iApply ("H" $! CID with "Hcg Hpc Hobl Hkc").
  Qed.

  (* the execute, at the EMPTY byte map: a register-only instruction never
     reaches a memory node, so [goodmb] at the empty map is exactly what the
     catalogue proves and the tier's own bytes stay framed. *)
  Lemma uv_swp_exec (dq : dfrac) (rsx : regstate) (i : instruction)
      (o : option instruction) (s_x : mstate) (ib : mword 32)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) :
    uv_redirect i o ->
    goodmb Du_r Du_w (execute i) (u_state rsx ∅) ∅ = true ->
    goodmb Du_r Du_w (execute (uv_exp i o)) (u_state rsx ∅) ∅ = true ->
    exec (execute (uv_exp i o)) (u_state rsx ∅) = Some (RETIRE_SUCCESS, s_x) ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsx u_Drw -∗ hreg_frame_ro (u_Df dq) rsx u_Dro -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 s_x.(sregs)⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       resv_any cpu_id -∗ Pe RETIRE_SUCCESS ib) -∗
    swp (execute i) (run_exec_post Pe ib).
  Proof.
    intros Hred Hg1 Hg2 He.
    iIntros "#Hcert Hany Hrw Hro Hk".
    iAssert (bytes_own (∅ : gmap Arch.pa (bv 8))) as "#Hemp";
      [ by rewrite /bytes_own big_sepM_empty |].
    destruct o as [j | ].
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx ∅) (u_state rsx ∅) (ExecuteAs j)
                    rsx ∅ u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) (map_empty_subseteq _)
                    Hg1 (Hred (u_state rsx ∅))
                    with "Hcert Hany Hrw Hro Hemp"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs1 mm1) "(%Hag1 & _ & _ & Hrw & Hro & _ & Hany)".
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[Hk] [Hany Hrw Hro]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute j) (u_state rsx ∅) s_x RETIRE_SUCCESS rs1 ∅
                    u_disj Du_r_sub Du_w_sub Hag1 (map_empty_subseteq _)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hemp"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm2) "(%Hag & _ & _ & Hrw & Hro & _ & Hany)".
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hany"). exact Hag.
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx ∅) s_x RETIRE_SUCCESS rsx ∅
                    u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) (map_empty_subseteq _)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hemp"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm2) "(%Hag & _ & _ & Hrw & Hro & _ & Hany)".
      iApply (run_exec_post_direct Pe ib RETIRE_SUCCESS I).
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hany"). exact Hag.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* Everything from the FETCHED file on: the leaf's value-precise         *)
  (* execute, and the payload that rebuilds [uv_cap_gpr] at the new file.  *)
  (* ------------------------------------------------------------------- *)
  Lemma uv_retire_post_fetch (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (k : Z)
      (i : instruction) (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rs2 : regstate) :
    uv_wrok wr ->
    uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc k ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs2) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt M) t' ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId, uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0) (uv_next jt (add_vec_int pc k)) -∗
       WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt M)) -∗
    uv_res pt M t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc k) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc k) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rs1 (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hwrok Hred Hg1 Hg2 Hexec Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2
      Lmie2 Lmdl2 Lmedl2 Lmenv2 Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2
      Lmi2 Htlbok2 Hagd2 Htok'.
    set (rsx := register_set nextPC (add_vec_int pc k) rs2).
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc).
    { unfold rsx.
      rewrite (irrelevant_register_set (R_bitvector_64 PC)
                 (R_bitvector_64 nextPC) rs2 _ ltac:(vm_compute; reflexivity)).
      exact Lpc2. }
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc k)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User).
    { unfold rsx.
      rewrite (irrelevant_register_set cur_privilege
                 (R_bitvector_64 nextPC) rs2 _ ltac:(vm_compute; reflexivity)).
      exact Lcp2. }
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc k) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    pose proof (Hexec (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                  (uv_gpr_vals m rsx Hgagx Hx0)) as Hex.
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hmm Hres Hrw Hro".
    iApply (uv_swp_exec (uc_dqc C) rsx i o
              (uv_post (u_state rsx ∅) jt wr) ib _
              Hred
              (Hg1 (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                 (uv_gpr_vals m rsx Hgagx Hx0))
              (Hg2 (u_state rsx ∅) Lpcx Lnpcx Lcpx Hagdx
                 (uv_gpr_vals m rsx Hgagx Hx0))
              Hex with "Hcert Hany Hrw Hro [Hk Hmm Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hany".
    rewrite uv_post_sregs in Hag3.
    rewrite /uv_step_post.
    iExists (uv_post_rs rsx jt wr).
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (uv_land_reg rs2 _ jt wr hart_state _
                   ltac:(vm_compute; reflexivity) uv_nogpr_hart Lhs2)
        | exact (uv_land_reg rs2 _ jt wr (R_bool minstret_increment) _
                   ltac:(vm_compute; reflexivity) uv_nogpr_minc Lmi2)
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 (uv_post_rs rsx jt wr) u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3
                 (uv_post_rs rsx jt wr) u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_active C pt R Ψ M (uv_upd m wr)
              (uv_next jt (add_vec_int pc k)) t' usatp pcfg paddr
              (uv_post_rs rsx jt wr)
              (uv_land_reg rs2 _ jt wr hart_state _
                 ltac:(vm_compute; reflexivity) uv_nogpr_hart Lhs2)
              (uv_land_reg rs2 _ jt wr cur_privilege _
                 ltac:(vm_compute; reflexivity) uv_nogpr_priv Lcp2)
              ltac:(rewrite (uv_land_reg rs2 _ jt wr (R_bitvector_64 mstatus) _
                               ltac:(vm_compute; reflexivity) uv_nogpr_mst eq_refl);
                    exact Hms2)
              (uv_land_nextPC rs2 (add_vec_int pc k) jt wr)
              (uv_gpr_agree_post m rsx jt wr Hwrok Hgagx)
              (uv_upd_x0 m wr Hwrok Hx0)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 stvec) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_stvec Lstvec2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mie) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mie Lmie2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mideleg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mdl Lmdl2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 medeleg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_medl Lmedl2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 menvcfg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_menv Lmenv2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 mstateen0) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_mste Lmste2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_32 sstateen0) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_sste Lsste2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 senvcfg) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_senv Lsenv2)
              (uv_land_reg rs2 _ jt wr (R_bitvector_64 satp) _
                 ltac:(vm_compute; reflexivity) uv_nogpr_satp Lsatp2)
              (uv_land_reg rs2 _ jt wr pmpcfg_n _
                 ltac:(vm_compute; reflexivity) uv_nogpr_pcfg Lpcfg2)
              (uv_land_reg rs2 _ jt wr pmpaddr_n _
                 ltac:(vm_compute; reflexivity) uv_nogpr_paddr Lpaddr2)
              Htok'
              ltac:(rewrite (uv_land_reg rs2 _ jt wr tlb _
                               ltac:(vm_compute; reflexivity) uv_nogpr_tlb eq_refl);
                    exact Htlbok2)
              with "Hamb Hcap Hany Hmm Hres Hk").
  Qed.

End UvFunnel.

Lemma uv_gpr_ne_tlb (n : Z) :
  register_beq (R_bitvector_64 (gpr_of_Z n)) tlb = false.
Proof. unfold gpr_of_Z; repeat case_match; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* §6c THE OBLIGATION, once per FETCH SHAPE.                              *)
(* ===================================================================== *)

Section UvObligation.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Lemma uv_obl_base (R : iProp Σ) (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (w : mword 32) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (t t' : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    uv_wrok wr -> uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId, uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0) (uv_next jt (add_vec_int pc 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hwrok Hred Hg1 Hg2 Hexec.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, i, pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_retire_post_fetch C pt R Ψ M m pc 4 i o jt wr
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2
              Hwrok Hred Hg1 Hg2 Hexec
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

  Lemma uv_obl_rvc (R : iProp Σ) (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (h : mword 16) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) (t t' : ptree) (usatp : mword 64)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    uv_wrok wr -> uv_redirect i o ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId, uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0) (uv_next jt (add_vec_int pc 2)) -∗
       WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hwrok Hred Hg1 Hg2 Hexec.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_retire_post_fetch C pt R Ψ M m pc 2 i o jt wr
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2
              Hwrok Hred Hg1 Hg2 Hexec
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UvObligation.

(* ===================================================================== *)
(* §7 THE RETIRE FUNNEL.                                                  *)
(*                                                                        *)
(* One [uinstr] fact + one value-precise execute obligation = one          *)
(* verified instruction.  The funnel picks the fetch geometry off the      *)
(* [uinstr] (compressed x 4-aligned), transports the decode fact to the    *)
(* fetched state, and re-establishes [uv_cap_gpr] at the updated register  *)
(* file.  The image [M] is UNCHANGED -- this is the memory-preserving      *)
(* funnel.                                                                *)
(*                                                                        *)
(* [wp_uv_retire_later] IS THE GENERAL FORM and hands the step's own       *)
(* [|>] OUT: it is the only way an [iLoeb] back edge can strip its IH, and *)
(* what every UNBOUNDED loop in this tier needs.  [wp_uv_retire] is the    *)
(* later-free restatement every existing leaf uses.                        *)
(*                                                                        *)
(* THE PORT'S ONE ADDITION is the [goodmb] certificate: the per-node       *)
(* cycle rule wants it beside the pure [exec] fact, at the EMPTY byte map  *)
(* (a register-only execute never reaches a memory node) -- which is       *)
(* exactly the shape the catalogue [UserTotalU.goodmb_execute_C_*] /       *)
(* [UserExecFacts.*_total] already proves.                                 *)
(*                                                                        *)
(* IT CARRIES THE SAME STATE GUARD AS [Hexec], AND MUST.  Stated at an     *)
(* unconstrained [forall s], the certificate is FALSE for every            *)
(* instruction that reaches [jump_to]: [jump_to] ASSERTS bit 0 of the      *)
(* target is clear, a failed [assert_exp] is a [GenericFail] node, and     *)
(* [goodmb]'s catch-all arm answers [false] there -- so at an [s] whose PC *)
(* is odd there is nothing to prove.  JAL / JALR / BTYPE's catalogue       *)
(* certificates say exactly that: they take the target's alignment and the *)
(* Zca / Zicfilp gate values as hypotheses, which are readings of the      *)
(* state.  The five premises below are the ones the leaf needs to discharge*)
(* them ([register_lookup PC s = pc] turns a leaf's own target-alignment   *)
(* premise into [goodmb_execute_JAL_total]'s; [agree_on D_u s dstateU]     *)
(* gives the gates through [UserTotalU.u_gm_zca] / [agree_u_zca]; the      *)
(* register-value reading decides which arm a BTYPE walk takes), and they  *)
(* cost the caller nothing: the funnel consumes both certificates at the   *)
(* ONE state [u_state rsx ∅] in [uv_retire_post_fetch], where all five are *)
(* already proved for [Hexec].  A register-only leaf ignores all five.     *)
(* ===================================================================== *)

Section UvRetire.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Lemma wp_uv_retire_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) (is_rvc : bool) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_wrok wr ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
         pc_is (CID := CID0)
           (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec.
    destruct Hui as [Hal2 Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_step C pt _ Ψ M m pc with "Hcg Hpc [] Hcont").
    rewrite /uv_step_obl.
    iIntros (R CIDo t rs1 rsA usatp pcfg paddr)
      "%Hpre #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* 4-aligned: one 4-byte read, low half is the instruction *)
        destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes M (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt M t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanon Hinpage Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uv_obl_rvc C pt R Ψ M m pc h i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdecrvc
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + (* 2 mod 4: one 2-byte read *)
        destruct (uv_fetch_rvc_2 pt M t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_obl_rvc C pt R Ψ M m pc h i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdecrvc
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uv_obl_base C pt R Ψ M m pc w i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdecbase
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_base_2 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_obl_base C pt R Ψ M m pc w i o jt wr t t' usatp pcfg paddr
                  rs1 rsA rsf Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdecbase
                  Hwrok Hred Hg1 Hg2 Hexec
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every leaf takes *)
  Lemma wp_uv_retire (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (o : option instruction) (jt : option (mword 64))
      (wr : option (mword 5 * mword 64)) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uv_wrok wr ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute i) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       goodmb Du_r Du_w (execute (uv_exp i o)) s_pc ∅ = true) ->
    (forall s_pc : mstate,
       register_lookup PC s_pc.(sregs) = pc ->
       register_lookup nextPC s_pc.(sregs)
         = add_vec_int pc (if is_rvc then 2 else 4) ->
       register_lookup cur_privilege s_pc.(sregs) = User ->
       agree_on D_u s_pc dstateU ->
       (forall r : mword 5,
          (if Z.eqb (uint r) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s_pc.(sregs))
          = m !!! Regidx r) ->
       exec (execute (uv_exp i o)) s_pc
         = Some (RETIRE_SUCCESS, uv_post s_pc jt wr)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0)
         (uv_next jt (add_vec_int pc (if is_rvc then 2 else 4))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire_later Ψ M m pc is_rvc i o jt wr
              Hui Hred Hlpad Hwrok Hg1 Hg2 Hexec with "Hcg Hpc [Hcont]").
    iNext. iExact "Hcont".
  Qed.

End UvRetire.

(* ===================================================================== *)
(* §8 THE ECALL DRIVER.                                                   *)
(*                                                                        *)
(* [ecall] at User raises E_U_EnvCall with the state UNCHANGED             *)
(* ([UserExecFacts.exec_execute_ECALL_U]); [uc_del] delegates it to        *)
(* Supervisor, the shared trap tower ([UserTrap.swp_exec_trap_u])          *)
(* delivers it, and the CONCRETE frame goes to the capability's            *)
(* [uv_sys_wp] together with the caller's protocol payload at the number   *)
(* in a7.  Nothing comes back: what the syscall does is entirely the       *)
(* protocol's business.                                                    *)
(* ===================================================================== *)

(* the trap half lives in a section of its OWN: [wp_uv_ecall] applies it at
   the hart the OBLIGATION runs on, which is a [forall]-bound one, and a
   section CpuId variable is auto-applied and cannot be named at
   application (claude-notes/projects/user-verified.md section 5). *)
Section UvEcallPost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Lemma uv_ecall_post_fetch (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rs2 : regstate) :
    (forall s : mstate, goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bitvector_64 misa) rs2 = MISA_C ->
    eq_vec (register_lookup (R_bitvector_1 elp) rs2)
      (landing_pad_bits_backwards LP_EXPECTED) = false ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
          (register_lookup (R_bitvector_64 minstretcfg) rs1)
          (register_lookup cur_privilege rs1) ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs2) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    gen_cert -∗ uv_cap C pt Ψ -∗
    (R -∗ Ψ (uint (m !!! Regidx a7_idx)) m pc M) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt M)) -∗
    uv_res pt M t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc 4) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc 4) rs2) u_Dro -∗
    swp (execute (ECALL tt))
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rs1 (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hg Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmisa2 Helpne2 Lmi2
      Htlbok2 Htok'.
    set (rsx := register_set nextPC (add_vec_int pc 4) rs2).
    (* every named pin survives the [nextPC := pc+4] write *)
    assert (Tx : forall (r : register) (val : type_of_register r),
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rs2 = val -> register_lookup r rsx = val).
    { intros r val Hne Hv. unfold rsx.
      rewrite (irrelevant_register_set r (R_bitvector_64 nextPC) rs2 _ Hne).
      exact Hv. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by exact (Tx (R_bitvector_64 PC) _ ltac:(vm_compute; reflexivity) Lpc2).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by exact (Tx cur_privilege _ ltac:(vm_compute; reflexivity) Lcp2).
    assert (Lhsx : register_lookup hart_state rsx = HART_ACTIVE tt)
      by exact (Tx hart_state _ ltac:(vm_compute; reflexivity) Lhs2).
    assert (Hmsx : user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsx))
      by (rewrite (Tx (R_bitvector_64 mstatus) _
                     ltac:(vm_compute; reflexivity) eq_refl); exact Hms2).
    assert (Lstvecx : register_lookup (R_bitvector_64 stvec) rsx = uc_stvec C)
      by exact (Tx (R_bitvector_64 stvec) _ ltac:(vm_compute; reflexivity) Lstvec2).
    assert (Lmiex : register_lookup (R_bitvector_64 mie) rsx = uc_mie C)
      by exact (Tx (R_bitvector_64 mie) _ ltac:(vm_compute; reflexivity) Lmie2).
    assert (Lmdlx : register_lookup (R_bitvector_64 mideleg) rsx = uc_mideleg C)
      by exact (Tx (R_bitvector_64 mideleg) _ ltac:(vm_compute; reflexivity) Lmdl2).
    assert (Lmedlx : register_lookup (R_bitvector_64 medeleg) rsx = uc_medeleg C)
      by exact (Tx (R_bitvector_64 medeleg) _ ltac:(vm_compute; reflexivity) Lmedl2).
    assert (Lmenvx : register_lookup (R_bitvector_64 menvcfg) rsx = MENVCFG_S)
      by exact (Tx (R_bitvector_64 menvcfg) _ ltac:(vm_compute; reflexivity) Lmenv2).
    assert (Lmstex : register_lookup (R_bitvector_64 mstateen0) rsx
                     = (mword_of_int 0 : mword 64))
      by exact (Tx (R_bitvector_64 mstateen0) _ ltac:(vm_compute; reflexivity) Lmste2).
    assert (Lsstex : register_lookup (R_bitvector_32 sstateen0) rsx
                     = (mword_of_int 0 : mword 32))
      by exact (Tx (R_bitvector_32 sstateen0) _ ltac:(vm_compute; reflexivity) Lsste2).
    assert (Lsenvx : register_lookup (R_bitvector_64 senvcfg) rsx
                     = (mword_of_int 0 : mword 64))
      by exact (Tx (R_bitvector_64 senvcfg) _ ltac:(vm_compute; reflexivity) Lsenv2).
    assert (Lsatpx : register_lookup (R_bitvector_64 satp) rsx = usatp)
      by exact (Tx (R_bitvector_64 satp) _ ltac:(vm_compute; reflexivity) Lsatp2).
    assert (Lpcfgx : register_lookup pmpcfg_n rsx = pcfg)
      by exact (Tx pmpcfg_n _ ltac:(vm_compute; reflexivity) Lpcfg2).
    assert (Lpaddrx : register_lookup pmpaddr_n rsx = paddr)
      by exact (Tx pmpaddr_n _ ltac:(vm_compute; reflexivity) Lpaddr2).
    assert (Lmisax : register_lookup (R_bitvector_64 misa) rsx = MISA_C)
      by exact (Tx (R_bitvector_64 misa) _ ltac:(vm_compute; reflexivity) Lmisa2).
    assert (Helpnex : eq_vec (register_lookup (R_bitvector_1 elp) rsx)
                        (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite (Tx (R_bitvector_1 elp) _
                     ltac:(vm_compute; reflexivity) eq_refl); exact Helpne2).
    assert (Lmix : register_lookup (R_bool minstret_increment) rsx
              = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs1)
                  (register_lookup (R_bitvector_64 minstretcfg) rs1)
                  (register_lookup cur_privilege rs1))
      by exact (Tx (R_bool minstret_increment) _ ltac:(vm_compute; reflexivity) Lmi2).
    assert (Ltlbx : register_lookup tlb rsx = register_lookup tlb rs2)
      by exact (Tx tlb _ ltac:(vm_compute; reflexivity) eq_refl).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. rewrite (Hgag2 q Hnz). symmetry.
      exact (Tx (R_bitvector_64 (gpr_of_Z (uint q))) _ (regbeq_gpr_nextPC (uint q)) eq_refl). }
    pose proof (elp_no_lp _ Helpnex) as Lelpx.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsx))
                       ('b"1") = true)
      by (rewrite Lmisax; vm_compute; reflexivity).
    assert (Hdel : bit_to_bool (access_vec_dec
              (register_lookup (R_bitvector_64 medeleg) rsx)
              (uint (exceptionType_bits_forwards (E_U_EnvCall tt)))) = true)
      by (rewrite Lmedlx; exact (uc_del C (E_U_EnvCall tt) eq_refl)).
    pose proof (exec_execute_ECALL_U (u_state rsx ∅) pc Lcpx Lpcx) as Hex.
    iIntros "#Hcert #Hcap Hk Hany Hmm Hres Hrw Hro".
    iDestruct "Hcap" as "[#Hintr #Hsys]".
    iAssert (bytes_own (∅ : gmap Arch.pa (bv 8))) as "#Hemp";
      [ by rewrite /bytes_own big_sepM_empty |].
    (* ---- the execute: one node, no memory ---- *)
    iApply (swp_mono with "[Hk Hmm Hres] [Hany Hrw Hro]").
    2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C))
                  (execute (ECALL tt)) (u_state rsx ∅) (u_state rsx ∅)
                  (rv64d_types.Trap
                     (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc))
                  rsx ∅ u_disj Du_r_sub Du_w_sub
                  ltac:(intros q _; reflexivity) (map_empty_subseteq _)
                  (Hg (u_state rsx ∅)) Hex
                  with "Hcert Hany Hrw Hro Hemp"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost" as (rs3 mm3) "(%Hag3 & _ & _ & Hrw & Hro & _ & Hany)".
    iApply (run_exec_post_direct
              (fun (r : ExecutionResult) (ib' : mword 32) =>
                 uv_step_post C R rs1 (Step_Execute (r, ib'))) ib
              (rv64d_types.Trap
                 (User, make_sync_exception (E_U_EnvCall tt) (zeros' 64), pc)) I).
    (* ---- the trap tower ---- *)
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    assert (Lelp3 : register_lookup (R_bitvector_1 elp) rs3
                    = landing_pad_bits_backwards NO_LP_EXPECTED)
      by (rewrite (Hag3 _ u_in_elp); exact Lelpx).
    rewrite Lelp3.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
               (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
               (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hmm Hres Hk".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs2 | uv_trap_peel; exact Lmi2 | exact I ]. }
    iApply (swp_mono with "[Hk Hmm Hres] [Hany Hrw Hro]").
    2:{ iApply (swp_exec_trap_u (u_state rsx ∅)
                  (rv64d_types.Exception (E_U_EnvCall tt))
                  (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                  (register_lookup (R_bitvector_64 mstatus) rsx)
                  (register_lookup (R_bitvector_64 scause) rsx)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lcpx eq_refl eq_refl Lstvecx Lelpx HmisaS (uc_tvd C)
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rs3
                  (E_U_EnvCall tt) (zeros' 64) eq_refl eq_refl Hdel
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Hag3 eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                    (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                    (uc_stvec C)) u_Drw
                 ltac:(intros q Hq; apply Hag, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                    (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                    (uc_stvec C)) u_Dro
                 ltac:(intros q Hq; apply Hag, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap C pt R M m t' usatp pcfg paddr
              (u_trap_rs rsx (rv64d_types.Exception (E_U_EnvCall tt))
                 (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)) pc
                 (uc_stvec C))
              (utrap_scause (rv64d_types.Exception (E_U_EnvCall tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_U_EnvCall tt) (zeros' 64))) pc
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; exact Lhs2)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsx))
              ltac:(uv_trap_peel; apply register_lookup_set)
              (uv_gpr_agree_trap m rsx _ _ _ _ Hgagx) Hx0
              ltac:(uv_trap_peel; exact Lstvec2)
              ltac:(uv_trap_peel; exact Lmie2)
              ltac:(uv_trap_peel; exact Lmdl2)
              ltac:(uv_trap_peel; exact Lmedl2)
              ltac:(uv_trap_peel; exact Lmenv2)
              ltac:(uv_trap_peel; exact Lmste2)
              ltac:(uv_trap_peel; exact Lsste2)
              ltac:(uv_trap_peel; exact Lsenv2)
              ltac:(uv_trap_peel; exact Lsatp2)
              ltac:(uv_trap_peel; exact Lpcfg2)
              ltac:(uv_trap_peel; exact Lpaddr2)
              Htok'
              ltac:(uv_trap_peel; exact Htlbok2)
              with "Hany Hmm Hres [Hsys Hk]").
    iIntros "Hframe HR".
    iApply ("Hsys" $! CID m M pc
              (register_lookup (R_bitvector_64 scause) rsx)
              (tval (xtval_exception_value (E_U_EnvCall tt) (zeros' 64)))
              with "Hframe [HR Hk]").
    iApply ("Hk" with "HR").
  Qed.

End UvEcallPost.

Section UvEcall.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Lemma wp_uv_ecall (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) :
    uinstr pt M pc false (ECALL tt) ->
    (forall s : mstate, goodmb Du_r Du_w (execute (ECALL tt)) s ∅ = true) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    Ψ (uint (m !!! Regidx a7_idx)) m pc M -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hg.
    destruct Hui as [Hal2 Hcanon Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
    iIntros "Hcg Hpc HPsi".
    iApply (wp_uv_step C pt _ Ψ M m pc with "Hcg Hpc [] [HPsi]").
    2:{ iNext. iExact "HPsi". }
    rewrite /uv_step_obl.
    iIntros (R CIDo t rs1 rsA usatp pcfg paddr)
      "%Hpre #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    assert (Hfetch : exists (rsf : regstate) (t' : ptree),
              exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
                = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt M))) /\
              goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
                (uv_mm t (upa_map pt M)) = true /\
              u_tlb_only rsA rsf /\
              tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) /\
              uv_tree_ok pt (upa_map pt M) t' /\
              pt_same_shape 2 t t').
    { destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      - destruct (uv_fetch_4 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        exists rsf, t'. split_and!;
          [ exact Hfe | exact Hfg | exact Tr | exact Htlbok' | exact Htok'
          | exact Hshape ].
      - destruct (uv_fetch_base_2 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        exists rsf, t'. split_and!;
          [ exact Hfe | exact Hfg | exact Tr | exact Htlbok' | exact Htok'
          | exact Hshape ]. }
    destruct Hfetch as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, (ECALL tt), pc, 8%nat.
    iSplitR.
    { iPureIntro. exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w (ECALL tt) Hagd2
               (Hdecbase dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_ecall_post_fetch C pt R Ψ M m pc (zero_extend' 32 w) t' usatp
              pcfg paddr rs1 rs2 Hg
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              Hmisa2 Helpne2
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Htlbok2 Htok'
              with "Hcert Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UvEcall.
