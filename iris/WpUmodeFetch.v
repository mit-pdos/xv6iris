(* WpUmodeFetch.v -- THE BYTE MAP, THE WALK AND THE FETCH of the VERIFIED
   user-execution tier: WpUmodeStep.v's sections 1-4, split out so that the
   fetch bridges compile on their own (claude-notes/projects/icache.md).

   (The original header follows.)

   WpUmodeStep.v -- THE STEP ENGINE of the VERIFIED user-execution tier
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
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import CommonWalk.
Require Import PtreeType PtAdBits PtTree KptTree.
Require Import SRegime UptTree UptWalkPt.
Require Import UserPtTree UserTranslate.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFetchCert.
(* NOT [Import]ed: [UserTotalU.u_pins_tick] shadows [UserFrame.u_pins_tick],
   which is the one the frames bridge is stated over. *)
Require Import UserActiveClass.
Require Import UmodeMem UmodeFetch.
Require Import HartMFetch UserBits.
Require Import HartMemRunX UmodeText UmodeFetchX UmodeArith.
Require Import TsoCtx.
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
(* §3 THE VALUE-PRECISE FETCH, AT THE NODE (claude-notes/projects/icache.md, *)
(* "The verified tier: text OUTSIDE the walker").                          *)
(*                                                                        *)
(* A verified process must fetch the word its image says is there, and    *)
(* under the non-coherent icache that word is only what the machine reads  *)
(* if the bytes are STAMPED -- their latest write under the hart's         *)
(* instruction view ([TsoCtx.ctx_phys_xpointsto], minted at [userret]'s    *)
(* [fence.i]).  Stamped bytes never enter the walker's map: the tier's     *)
(* byte currency [uv_bytes] is [HartMemRunX.bytes_own_p] over the SAME map  *)
(* as before, with the text image stamped ([uv_F]) and the rest plain; a   *)
(* walk runs [swp_hmrun_of_exec_p] on the unstamped submap -- which is the *)
(* page table plus the DATA image, [uv_mmd] -- and the fetch's read node is *)
(* driven by [UmodeFetchX]'s shells, its obligation paid by the stamps.    *)
(*                                                                        *)
(* So there is no whole-[fetch] [exec]/[goodmb] pair any more: the tier's  *)
(* fetch facts are the WALK's pair ([uv_walk_fetch] at the data half) and  *)
(* the image's bytes ([uM_bytes], on a text page: [uinstr]'s [ui_text]).   *)
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

(* a same-shaped tree change keeps the map's domain *)
Lemma uv_mm_dom (t t' : ptree) (md : PtBytes.pamap) :
  pt_same_shape 2 t t' ->
  (dom (uv_mm t md) : gset Arch.pa) = dom (uv_mm t' md).
Proof.
  intros Hs.
  exact (dom_union_shape (ptree_bytes 2 t) (ptree_bytes 2 t') md
           (ptree_bytes_dom_shape 2 t t' Hs)).
Qed.

(* ---- THE TEXT WINDOW IS STAMPED: text is a page property, and the whole
   window sits on the pc's page ---------------------------------------- *)
Lemma uva_text_window (pt : uptd) (pc : mword 64) (j : nat) :
  bv_unsigned pc mod 4096 + Z.of_nat j < 4096 ->
  uva_text pt (uint pc) -> uva_text pt (uint pc + Z.of_nat j).
Proof.
  intros Hnc (w & Hl & Hx & Hw).
  pose proof (Nat2Z.is_nonneg j) as Hj0.
  exists w. split; [| exact (conj Hx Hw)].
  rewrite (moi_win pc (Z.of_nat j) Hj0 Hnc) (usvpn_window pc (Z.of_nat j) Hj0 Hnc).
  rewrite moi_of_uint in Hl. exact Hl.
Qed.

Lemma uva_text_window_iff (pt : uptd) (pc : mword 64) (j : nat) :
  bv_unsigned pc mod 4096 + Z.of_nat j < 4096 ->
  uva_text pt (uint pc + Z.of_nat j) <-> uva_text pt (uint pc).
Proof.
  intros Hnc. pose proof (Nat2Z.is_nonneg j) as Hj0.
  split.
  - intros (w & Hl & Hx & Hw). exists w. split; [| exact (conj Hx Hw)].
    rewrite (moi_win pc (Z.of_nat j) Hj0 Hnc) (usvpn_window pc (Z.of_nat j) Hj0 Hnc) in Hl.
    rewrite moi_of_uint. exact Hl.
  - exact (uva_text_window pt pc j Hnc).
Qed.

Lemma uv_win_text (pt : uptd) (M : gmap Z (bv 8)) (IK : nat)
    (w_leaf pc : mword 64) (k : nat) (n : N) (iw : bv n) :
  uva_inj pt M ->
  ud_um pt !! svpn_of pc = Some w_leaf ->
  (forall j : nat, (j < k)%nat -> bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
  uM_bytes M (uint pc) k iw ->
  uva_text pt (uint pc) ->
  forall j : nat, (j < k)%nat ->
    uv_F pt M IK (pa_add (u_walk_pa w_leaf pc) j) = Some IK.
Proof.
  intros Hinj Hl Hnc Hb Htx j Hj.
  apply uv_F_text. apply elem_of_dom. exists (nth_byte iw j).
  rewrite <- (uva_pa_window pt w_leaf pc j Hl (Hnc j Hj)).
  apply upa_map_lookup; [exact (uva_inj_sub pt M _ (uM_text_sub pt M) Hinj) |].
  apply uM_text_lookup. split; [exact (Hb j Hj) |].
  exact (uva_text_window pt pc j (Hnc j Hj) Htx).
Qed.

(* ---- THE DATA HALF: what the walker owns ---------------------------- *)
Definition uv_mmd (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) : PtBytes.pamap :=
  uv_mm t (upa_map pt (uM_data pt M)).

Lemma uv_tree_ok_data (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) :
  uva_inj pt M ->
  uv_tree_ok pt (upa_map pt M) t -> uv_tree_ok pt (upa_map pt (uM_data pt M)) t.
Proof.
  intros Hinj (Hdisj & Hdj & Hram & Hwfm & Hspec).
  pose proof (upa_map_sub pt M _ (uM_data_sub pt M) Hinj) as Hsub.
  split_and!; [exact Hdisj | | | exact Hwfm | exact Hspec].
  - exact (map_disjoint_weaken_r _ _ _ Hdj Hsub).
  - intros a Ha. apply Hram. rewrite /uv_mm in Ha |- *.
    apply elem_of_dom in Ha as [b Hb]. apply elem_of_dom.
    apply lookup_union_Some_raw in Hb as [Hb | [Hn Hb]].
    + exists b. apply lookup_union_Some_l. exact Hb.
    + exists b. rewrite (lookup_union_r _ _ _ Hn).
      exact (lookup_weaken _ _ _ _ Hb Hsub).
Qed.

Lemma uv_tree_ok_of_data (pt : uptd) (M : gmap Z (bv 8)) (t t' : ptree) :
  uv_tree_ok pt (upa_map pt M) t ->
  uv_tree_ok pt (upa_map pt (uM_data pt M)) t' ->
  pt_same_shape 2 t t' ->
  uv_tree_ok pt (upa_map pt M) t'.
Proof.
  intros Htok (_ & _ & _ & _ & Hspec') Hshape.
  apply (uv_tree_ok_shape pt _ t t' Htok Hshape Hspec').
  apply map_disjoint_spec. intros x b1 b2 H1 H2.
  assert (Hx : x ∈ (dom (ptree_bytes 2 t) : gset Arch.pa)).
  { rewrite (ptree_bytes_dom_shape 2 t t' Hshape). apply elem_of_dom. by exists b1. }
  apply elem_of_dom in Hx as [b0 Hb0].
  exact (proj1 (map_disjoint_spec _ _) (proj1 (proj2 Htok)) x b0 b2 Hb0 H2).
Qed.

(* the page table's bytes are never stamped: they are not image bytes *)
Lemma uv_F_pt (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (t : ptree)
    (a : Arch.pa) :
  uva_inj pt M ->
  ptree_bytes 2 t ##ₘ upa_map pt M ->
  a ∈ (dom (ptree_bytes 2 t) : gset Arch.pa) -> uv_F pt M IK a = None.
Proof.
  intros Hinj Hdj Ha. apply uv_F_none. intros Ht.
  apply map_disjoint_dom in Hdj. apply (Hdj a Ha).
  exact (subseteq_dom _ _ (upa_map_sub pt M _ (uM_text_sub pt M) Hinj) a Ht).
Qed.

(* the unstamped submap of the tier's map IS the data half *)
Lemma uf_none_uv (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (t : ptree) :
  uva_inj pt M ->
  ptree_bytes 2 t ##ₘ upa_map pt M ->
  uf_none (uv_F pt M IK) (uv_mm t (upa_map pt M)) = uv_mmd pt M t.
Proof.
  intros Hinj Hdj. rewrite /uv_mmd /uv_mm /uf_none map_filter_union; [| exact Hdj].
  f_equal.
  - apply (uf_none_all (uv_F pt M IK)). intros a Ha.
    exact (uv_F_pt pt M IK t a Hinj Hdj Ha).
  - exact (uf_none_upa pt M IK Hinj).
Qed.

(* ... and the stamped submap is the text half *)
Lemma uf_some_uv (pt : uptd) (M : gmap Z (bv 8)) (IK : nat) (t : ptree) :
  uva_inj pt M ->
  ptree_bytes 2 t ##ₘ upa_map pt M ->
  uf_some (uv_F pt M IK) (uv_mm t (upa_map pt M)) = upa_map pt (uM_text pt M).
Proof.
  intros Hinj Hdj.
  assert (He : uf_some (uv_F pt M IK) (ptree_bytes 2 t) = ∅).
  { apply uf_some_empty. intros a Ha. exact (uv_F_pt pt M IK t a Hinj Hdj Ha). }
  pose proof (uf_some_upa pt M IK Hinj) as Hu.
  unfold uf_some in He, Hu |- *. rewrite /uv_mm map_filter_union; [| exact Hdj].
  rewrite He Hu left_id_L. reflexivity.
Qed.

(* the data half walked to [t'], plus the text half, is the whole map at [t'] *)
Lemma uv_join (pt : uptd) (M : gmap Z (bv 8)) (t' : ptree) :
  uva_inj pt M ->
  uv_mmd pt M t' ∪ upa_map pt (uM_text pt M) = uv_mm t' (upa_map pt M).
Proof.
  intros Hinj. rewrite /uv_mmd /uv_mm (upa_map_split pt M Hinj).
  assert (Hd : upa_map pt (uM_data pt M) ##ₘ upa_map pt (uM_text pt M))
    by (symmetry; exact (upa_map_split_disj pt M Hinj)).
  rewrite <- (assoc_L (∪) (ptree_bytes 2 t') (upa_map pt (uM_data pt M))
                (upa_map pt (uM_text pt M))).
  rewrite (map_union_comm _ _ Hd). reflexivity.
Qed.

(* the tree invariant at an image of the SAME DOMAIN (a store's) *)
Lemma uv_tree_ok_dom_eq (pt : uptd) (M M' : gmap Z (bv 8)) (t : ptree) :
  (dom (upa_map pt M') : gset Arch.pa) = dom (upa_map pt M) ->
  uv_tree_ok pt (upa_map pt M) t -> uv_tree_ok pt (upa_map pt M') t.
Proof.
  intros Hd (Hdisj & Hdj & Hram & Hwfm & Hspec).
  split_and!; [exact Hdisj | | | exact Hwfm | exact Hspec].
  - apply map_disjoint_spec. intros x b1 b2 H1 H2.
    assert (Hx : x ∈ (dom (upa_map pt M) : gset Arch.pa)).
    { rewrite <- Hd. apply elem_of_dom. by exists b2. }
    apply elem_of_dom in Hx as [b0 Hb0].
    exact (proj1 (map_disjoint_spec _ _) Hdj x b1 b0 H1 Hb0).
  - intros a Ha. apply Hram. rewrite /uv_mm in Ha |- *.
    apply elem_of_dom in Ha as [b Hb]. apply elem_of_dom.
    apply lookup_union_Some_raw in Hb as [Hb | [Hn Hb]].
    + exists b. apply lookup_union_Some_l. exact Hb.
    + assert (Ha' : a ∈ (dom (upa_map pt M) : gset Arch.pa)).
      { rewrite <- Hd. apply elem_of_dom. by exists b. }
      apply elem_of_dom in Ha' as [b' Hb']. exists b'.
      rewrite (lookup_union_r _ _ _ Hn). exact Hb'.
Qed.

Lemma uv_mmd_dom (pt : uptd) (M : gmap Z (bv 8)) (t t' : ptree) :
  pt_same_shape 2 t t' ->
  (dom (uv_mmd pt M t) : gset Arch.pa) = dom (uv_mmd pt M t').
Proof. intros Hs. exact (uv_mm_dom t t' _ Hs). Qed.

(* ===================================================================== *)
(* §4 THE RESOURCE BRIDGES.                                               *)
(*                                                                        *)
(* [utlb_inv_pt] + the STAMPED image in, the tier's byte currency out --   *)
(* plus the four register cells the walk reads and writes and a closer     *)
(* that takes a same-shaped tree back.                                     *)
(* ===================================================================== *)

Section UvOpen.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE TIER'S BYTE CURRENCY: the whole map, the text image stamped at
     some [IK] this hart's instruction view has passed *)
  Definition uv_bytes (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) : iProp Σ :=
    (∃ IK : nat,
       hart_iview_lb_at cpu_id IK ∗
       bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)))%I.

  Lemma uv_bytes_forget (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) :
    uv_bytes pt M t ⊢ bytes_own (uv_mm t (upa_map pt M)).
  (* NO PROOFMODE HERE.  [iApply] on a [⊢] lemma goes through
     [iIntoEmpValid], whose [first] alternation tries a [notypeclasses
     refine] per shape, and every FAILING branch unifies against this goal's
     map -- which is computed ([ptree_bytes 2 t ∪ list_to_map (upa_list pt
     M)]).  Ltac profiling put 96% of this whole file in ONE
     [iIntoEmpValid_go] call, 113 s of 132 s.  Sealing [bytes_own] /
     [bytes_own_p] against instance search is a NULL -- the cost is the
     failing refines, not the big-op -- so the fix is to stay at the BI
     level, where every step is an [apply] against the head.
     (claude-notes/optimization.md, "in a [first [ ... ]] alternation, the
     cost of a tactic that FAILS grows with the proof term".) *)
  Proof.
    rewrite /uv_bytes. apply bi.exist_elim. intros IK.
    rewrite bi.sep_elim_r. apply bytes_own_p_forget.
  Qed.

  Lemma uv_bytes_ram (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) :
    uv_bytes pt M t ⊢
    ⌜forall a : Arch.pa, a ∈ (dom (uv_mm t (upa_map pt M)) : gset Arch.pa) ->
       addr_is_ram a⌝.
  Proof. rewrite uv_bytes_forget. apply bytes_own_ram. Qed.

  (* the stamped image plus the tree's bytes IS the currency, and back *)
  Lemma uv_bytes_of_umem_x (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) :
    uva_inj pt M ->
    ptree_bytes 2 t ##ₘ upa_map pt M ->
    umem_x pt M -∗ bytes_own (ptree_bytes 2 t) -∗ uv_bytes pt M t.
  Proof.
    intros Hinj Hdj. iIntros "Hx Ht".
    iDestruct "Hx" as (IK) "(#Hlb & Htext & Hdata)".
    iDestruct (umem_x_to_bytes pt M IK Hinj with "[$Htext $Hdata]") as "Hm".
    iExists IK. iFrame "Hlb". rewrite /uv_mm (bytes_own_p_union _ _ _ Hdj).
    iFrame "Hm". rewrite (bytes_own_p_of_none (uv_F pt M IK) (ptree_bytes 2 t));
      [iFrame "Ht" |].
    intros a Ha. exact (uv_F_pt pt M IK t a Hinj Hdj Ha).
  Qed.

  Lemma uv_bytes_to_umem_x (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) :
    uva_inj pt M ->
    ptree_bytes 2 t ##ₘ upa_map pt M ->
    uv_bytes pt M t -∗ umem_x pt M ∗ bytes_own (ptree_bytes 2 t).
  Proof.
    intros Hinj Hdj. iIntros "(%IK & #Hlb & Hm)".
    rewrite /uv_mm (bytes_own_p_union _ _ _ Hdj). iDestruct "Hm" as "[Ht Hm]".
    rewrite (bytes_own_p_of_none (uv_F pt M IK) (ptree_bytes 2 t));
      [iFrame "Ht" |]; last first.
    { intros a Ha. exact (uv_F_pt pt M IK t a Hinj Hdj Ha). }
    iDestruct (bytes_to_umem_x pt M IK Hinj with "Hm") as "[Htext Hdata]".
    iExists IK. iFrame "Hlb Htext Hdata".
  Qed.

  Lemma umem_x_disj_tree (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) (IK : nat) :
    uva_inj pt M ->
    bytes_own (ptree_bytes 2 t) -∗ umem_text pt M IK ∗ umem pt (uM_data pt M) -∗
    ⌜ptree_bytes 2 t ##ₘ upa_map pt M⌝.
  Proof.
    intros Hinj. iIntros "Ht Hm".
    iDestruct (umem_x_to_bytes pt M IK Hinj with "Hm") as "Hm".
    iApply (bytes_own_p_disj with "Ht Hm").
  Qed.

  Lemma uv_pt_open (pt : uptd) (M : gmap Z (bv 8)) :
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem_x pt M -∗
    ∃ (t : ptree) (usatp : mword 64) (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n),
      ⌜uva_inj pt M⌝ ∗ ⌜uv_tree_ok pt (upa_map pt M) t⌝ ∗
      ⌜upt_satp_ok_pt (ud_root pt) usatp⌝ ∗ ⌜pmp_ent0_ok pcfg paddr⌝ ∗
      ⌜tlb_ok_pt (mword_of_int 0) t tlbvec⌝ ∗
      satp ↦ᵣ usatp ∗ tlb ↦ᵣ tlbvec ∗
      pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr ∗
      pt_claims 2 t ∗ uv_bytes pt M t ∗
      (∀ (t' : ptree) (tlbvec' : type_of_register tlb),
         ⌜pt_same_shape 2 t t'⌝ -∗
         ⌜uv_tree_ok pt (upa_map pt M) t'⌝ -∗
         ⌜tlb_ok_pt (mword_of_int 0) t' tlbvec'⌝ -∗
         satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec' -∗
         pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
         uv_bytes pt M t' -∗
         utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗ umem_x pt M).
  Proof.
    iIntros "Hinv HM".
    iDestruct (umem_x_uva_inj pt M with "HM") as %Hinj.
    iDestruct (upt_swp_open (ud_root pt) (ud_tfp pt) (ud_um pt) with "Hinv")
      as (usatp tlbvec pcfg paddr) "(%Hsatpok & %Hpmpok & Hsatp & Htlb &
                                     Hpcfg & Hpaddr & Hres)".
    iDestruct "Hres" as (t) "(%Htlbok & %Hspec & %Hwfm & Htree)".
    iDestruct (ptree_own_bytes 2 t with "Htree") as "(#Hclaims & %Hdisj & Hmt)".
    iDestruct "HM" as (IK) "(#Hlb & Htext & Hdata)".
    iDestruct (umem_x_disj_tree pt M t IK Hinj with "Hmt [$Htext $Hdata]") as %Hdj.
    iDestruct (uv_bytes_of_umem_x pt M t Hinj Hdj with "[Htext Hdata] Hmt") as "Hmm".
    { iExists IK. iFrame "Hlb Htext Hdata". }
    iDestruct (uv_bytes_ram with "Hmm") as %Hram.
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
    iDestruct (uv_bytes_to_umem_x pt M t' Hinj Hdj' with "Hmm") as "[HM Hmt']".
    iSplitR "HM"; [| iExact "HM"].
    iApply (upt_swp_close (ud_root pt) (ud_tfp pt) (ud_um pt) usatp tlbvec'
              pcfg paddr Hsatpok Hpmpok with "Hsatp Htlb Hpcfg Hpaddr").
    iExists t'. iSplitR; [ by iPureIntro |]. iSplitR; [ by iPureIntro |].
    iSplitR; [ by iPureIntro |].
    iApply (ptree_own_of_bytes 2 t' Hdisj' with "[] Hmt'").
    by iApply (pt_claims_shape 2 t t' Hshape).
  Qed.

  (* ---- THE WALK over the tier's currency: [swp_hmrun_of_exec_p] on the
     data half, the text half framed; the landing map pinned at the same
     image ([u_map_eq] over the data half's domain).  The frames' file
     [rs] and the pure state's file [rsx] need only agree on the footprint,
     which is what a walk that starts from an Iris landing has. *)
  Lemma uv_swp_walk {X : Type} (pt : uptd) (M M' : gmap Z (bv 8)) (t t' : ptree)
      (dq : dfrac) (rs rsx rsx' : regstate) (m : Riscv.rv64d_types.M X) (x : X)
      (Φ : X -> iProp Σ) :
    uva_inj pt M ->
    uva_inj pt M' ->
    uM_text pt M' = uM_text pt M ->
    uv_tree_ok pt (upa_map pt M) t ->
    uv_tree_ok pt (upa_map pt M') t' ->
    (dom (uv_mmd pt M' t') : gset Arch.pa) = dom (uv_mmd pt M t) ->
    reg_agree_on (u_Drw ∪ u_Dro) rs rsx ->
    exec m (u_state rsx (uv_mmd pt M t)) = Some (x, u_state rsx' (uv_mmd pt M' t')) ->
    goodmb Du_r Du_w m (u_state rsx (uv_mmd pt M t)) (uv_mmd pt M t) = true ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dq) rs u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    (∀ rs2 : regstate, ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsx'⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       TsoCtx.own_context XI -∗ uv_bytes pt M' t' -∗ resv_any cpu_id -∗ Φ x) -∗
    swp m Φ.
  Proof.
    intros Hinj Hinj' Htext Htok Htok' Hdom' Hag He Hg.
    pose proof (proj1 (proj2 Htok)) as Hdj.
    iIntros "#Hcert Hany Hrw Hro Hrun Hown Hk".
    iDestruct "Hown" as (IK) "[#Hlb Hown]".
    pose proof (uv_F_ext pt M M' IK Htext) as HF.
    iApply (swp_mono with "[Hk] [Hany Hrw Hro Hrun Hown]").
    2:{ iApply (swp_hmrun_of_exec_p Du_r Du_w u_Drw u_Dro (u_Df dq) m
                  (u_state rsx (uv_mmd pt M t)) (u_state rsx' (uv_mmd pt M' t'))
                  x rs (uv_F pt M IK) (uv_mm t (upa_map pt M))
                  u_disj Du_r_sub Du_w_sub Hag
                  ltac:(rewrite (uf_none_uv pt M IK t Hinj Hdj); reflexivity)
                  ltac:(rewrite (uf_none_uv pt M IK t Hinj Hdj); exact Hg) He
                  with "Hcert Hany Hrw Hro Hrun Hown"). }
    iIntros (v) "(-> & Hpost)".
    iDestruct "Hpost"
      as (rs2 mm1) "(%Hag2 & %Hsub & %Hdom & Hrw & Hro & Hrun & Hown & Hany)".
    rewrite (uf_none_uv pt M IK t Hinj Hdj) in Hdom.
    assert (Hmm1 : mm1 = uv_mmd pt M' t').
    { apply (u_map_eq mm1 (uv_mmd pt M' t') Hsub).
      rewrite Hdom. exact (eq_sym Hdom'). }
    subst mm1.
    rewrite (uf_some_uv pt M IK t Hinj Hdj). rewrite <- Htext. rewrite (uv_join pt M' t' Hinj').
    iApply ("Hk" $! rs2 with "[%] Hrw Hro Hrun [Hown] Hany"); [exact Hag2 |].
    iExists IK. iFrame "Hlb".
    iEval (rewrite (bytes_own_p_ext _ _ _ HF)) in "Hown". iExact "Hown".
  Qed.

  (* ---- THE READ'S PAYER at the node: the window's bytes are stamped at
     [IK], the hart's instruction view has passed [IK] (the receipt), so the
     icache agent reads the image's bytes at every view from there up --
     [HartMFetch.fobl_ifetch], the shape [UmodeFetchX]'s read node wants. *)
  Lemma uv_fetch_pay (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) (IK : nat)
      (w_leaf pc : mword 64) (k : nat) (n : N) (iw : bv (8 * n)) :
    N.of_nat k = n ->
    uva_inj pt M ->
    uv_tree_ok pt (upa_map pt M) t ->
    ud_um pt !! svpn_of pc = Some w_leaf ->
    (forall j : nat, (j < k)%nat -> bv_unsigned pc mod 4096 + Z.of_nat j < 4096) ->
    uM_bytes M (uint pc) k iw ->
    uva_text pt (uint pc) ->
    hart_iview_lb_at cpu_id IK -∗
    (∀ σ img log tv itv V,
        ⌜V (hart_agent cpu_id) = tv⌝ -∗
        ⌜(itv <= length log)%nat⌝ -∗
        mstate_interp σ -∗
        hart_iview_auth cpu_id itv -∗
        tso_interp_of riscv_eraGS img σ.(mem) log V -∗
        bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)) ={⊤,∅}=∗
        ⌜fobl_ifetch img log itv (u_walk_pa w_leaf pc) n iw⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ ∗ hart_iview_auth cpu_id itv ∗
             tso_interp_of riscv_eraGS img σ.(mem) log V ∗
             bytes_own_p (uv_F pt M IK) (uv_mm t (upa_map pt M)))).
  Proof.
    intros Hkn Hinj Htok Hl Hnc Hb Htx. subst n.
    assert (Hwin : forall j : nat, (N.of_nat j < N.of_nat k)%N ->
              uv_mm t (upa_map pt M) !! pa_add (u_walk_pa w_leaf pc) j
                = Some (nth_byte iw j) /\
              uv_F pt M IK (pa_add (u_walk_pa w_leaf pc) j) = Some IK).
    { intros j Hj. split.
      - exact (uv_win_bytes pt M t w_leaf pc k _ iw Hinj (proj1 (proj2 Htok))
                 Hl Hnc Hb j ltac:(lia)).
      - exact (uv_win_text pt M IK w_leaf pc k _ iw Hinj Hl Hnc Hb Htx j
                 ltac:(lia)). }
    iIntros "#Hlb".
    iIntros (σ img log tv itv V) "%Htv %Hitv Hσ Hiv Htso Hown".
    iDestruct (hart_iview_lb_at_valid with "Hiv Hlb") as %HIK.
    rewrite /mstate_interp. iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (bytes_own_p_ifetch_of img σ.(mem) log V σ.(sregs) σ.(mdev)
                 (uv_F pt M IK) (uv_mm t (upa_map pt M)) IK
                 (u_walk_pa w_leaf pc) (N.of_nat k) iw Hwin
                 with "Hmem Htso Hown") as %Hok.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. intros tv' Hlo _. exact (Hok itv tv' HIK Hlo). }
    iNext. iMod "Hmask" as "_". iModIntro. iFrame "Hri Hmem Hdev Hiv Htso Hown".
  Qed.

  (* ---- THE FETCH'S POST, shared by the three geometries: the landing
     files (pure [rsf] from the walk, Iris [rs2] agreeing with it on the
     footprint), the landing tree, and the currency there *)
  Definition uv_fetch_post (dq : dfrac) (pt : uptd) (M : gmap Z (bv 8))
      (rsA : regstate) (t : ptree) (fr : FetchResult) : FetchResult -> iProp Σ :=
    fun r =>
      (⌜r = fr⌝ ∗
       ∃ (rs2 rsf : regstate) (t' : ptree),
         ⌜u_tlb_only rsA rsf⌝ ∗
         ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf⌝ ∗
         ⌜tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf)⌝ ∗
         ⌜uv_tree_ok pt (upa_map pt M) t'⌝ ∗
         ⌜pt_same_shape 2 t t'⌝ ∗
         hreg_frame rs2 u_Drw ∗ hreg_frame_ro (u_Df dq) rs2 u_Dro ∗
         TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗ resv_any cpu_id)%I.

  (* the pins a read node wants, off a file that agrees with the entry file
     everywhere but the TLB *)
  Lemma uv_read_pins (pt : uptd) (t : ptree) (rsA rs2 : regstate) :
    u_exec_pins pt t rsA ->
    (forall q : register, q ∈ u_Drw ∪ u_Dro ->
       register_beq q (tlb : register) = false ->
       register_lookup q rs2 = register_lookup q rsA) ->
    register_lookup htif_tohost_base rs2 = None /\
    register_lookup pma_regions rs2 = register_lookup pma_regions rsA /\
    register_lookup pmpcfg_n rs2 = register_lookup pmpcfg_n rsA /\
    register_lookup pmpaddr_n rs2 = register_lookup pmpaddr_n rsA /\
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n rsA) 0)) = TOR /\
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n rsA) 0) = false /\
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n rsA) 0))
      ('b"1") = true /\
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n rsA) 0) * 4)%Z /\
    pma_allows_ram (register_lookup pma_regions rsA).
  Proof.
    intros Hpins Hmv.
    pose proof Hpins as (Hhw & _ & Hpt & _).
    destruct Hhw as (_ & _ & _ & Hhtif & Hall & _).
    destruct Hpt as (_ & HA & Hord & HX & _ & _ & Hcov).
    split_and!.
    - exact (eq_trans (Hmv _ u_in_htif ltac:(vm_compute; reflexivity)) Hhtif).
    - exact (Hmv _ u_in_pma ltac:(vm_compute; reflexivity)).
    - exact (Hmv _ u_in_pcfg ltac:(vm_compute; reflexivity)).
    - exact (Hmv _ u_in_paddr ltac:(vm_compute; reflexivity)).
    - exact HA.
    - exact Hord.
    - exact HX.
    - exact Hcov.
    - exact (pma_all_ram Hall).
  Qed.

  (* ---- (a) a 4-ALIGNED pc: one walk, one 4-byte read ------------------ *)
  Lemma uv_swp_fetch4 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree) (dq : dfrac)
      (rsA : regstate) (w_leaf pc : mword 64) (iw : mword 32) :
    uva_inj pt M ->
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uM_bytes M (uint pc) 4 iw ->
    uva_text pt (uint pc) ->
    register_lookup PC rsA = pc ->
    register_lookup cur_privilege rsA = User ->
    _get_Mstatus_SXL (register_lookup mstatus rsA) = 'b"10" ->
    register_lookup menvcfg rsA = MENVCFG_S ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df dq) rsA u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (fetch tt)
      (uv_fetch_post dq pt M rsA t
         (if isRVC (subrange_vec_dec iw 15 0)
          then F_RVC (subrange_vec_dec iw 15 0) else F_Base iw)).
  Proof.
    intros Hinj Hl Hlok Hcanon Hal4 Hb Htx Lpc Lcp Lsxl Lmenv Hpins Htok.
    destruct (align4_low_bits pc Hal4) as (Hb0 & Hb1).
    assert (Hnc : forall j : nat, (j < 4)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
      by (intros j Hj; exact (ualign4_nc pc (Z.of_nat j) Hal4 ltac:(lia))).
    pose proof (uv_tree_ok_data pt M t Hinj Htok) as Htokd.
    destruct (uv_walk_fetch pt t (upa_map pt (uM_data pt M)) rsA w_leaf pc
                Hl Hlok Hcanon Lcp Lsxl Lmenv Hpins Htokd)
      as (rsf & t' & Htr & Htrg & Tr & Htlbok' & Htokd' & Hshape).
    pose proof (uv_tree_ok_of_data pt M t t' Htok Htokd' Hshape) as Htok'.
    pose proof (proj1 (proj2 (proj2 Htok))) as Hram.
    assert (Hram0 : addr_is_ram (u_walk_pa w_leaf pc)).
    { rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 4 32 iw Hinj (proj1 (proj2 Htok)) Hl
               Hnc Hb 0%nat ltac:(lia)). }
    assert (Hram3 : addr_is_ram (pa_add (u_walk_pa w_leaf pc) 3)).
    { apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 4 32 iw Hinj (proj1 (proj2 Htok)) Hl
               Hnc Hb 3%nat ltac:(lia)). }
    assert (Halp : is_aligned_paddr (Physaddr (u_walk_pa w_leaf pc)) 4 = true)
      by exact (pa_aligned_div _ pc 4 ltac:(lia) (Z.divide_factor_l 4 1024) Hal4).
    set (Qf := fun rs2 : regstate => reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf).
    assert (Hmv : forall rs2, Qf rs2 -> forall q : register, q ∈ u_Drw ∪ u_Dro ->
              register_beq q (tlb : register) = false ->
              register_lookup q rs2 = register_lookup q rsA)
      by (intros rs2 HQ; exact (u_bridge_mv rsA rsf rs2 Tr HQ)).
    assert (Hpriv : forall rs2, Qf rs2 -> register_lookup cur_privilege rs2 = User).
    { intros rs2 HQ.
      rewrite (Hmv rs2 HQ _ u_in_priv ltac:(vm_compute; reflexivity)). exact Lcp. }
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    iApply (swp_mono with "[] [Hany Hrw Hro Hrun Hown]").
    2:{ iApply (uv_fetch4_P u_Drw u_Dro (u_Df dq) rsA Qf
                  (fun _ => (TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗
                             resv_any cpu_id)%I)
                  pc (u_walk_pa w_leaf pc) iw u_disj u_in_PC u_in_mst u_in_priv
                  Lpc Hpriv Hb0 Hb1 Hal4 with "Hcert Hrw Hro [Hany Hrun Hown] []").
        - (* the walk *)
          iIntros "Hrw Hro".
          iApply (uv_swp_walk pt M M t t' dq rsA rsA rsf _ _ _ Hinj Hinj eq_refl
                    Htok Htok' (eq_sym (uv_mmd_dom pt M t t' Hshape))
                    ltac:(intros r _; reflexivity) Htr Htrg
                    with "Hcert Hany Hrw Hro Hrun Hown").
          iIntros (rs2) "%Hag Hrw Hro Hrun Hown Hany".
          iSplitR; [done|]. iExists rs2. iSplitR; [iPureIntro; exact Hag|].
          iFrame.
        - (* the read *)
          iIntros (rs2) "%HQ (Hrun & Hown & Hany) Hrw Hro".
          iDestruct "Hown" as (IK) "[#Hlb Hown]".
          destruct (uv_read_pins pt t rsA rs2 Hpins (Hmv rs2 HQ))
            as (Hhtif & Hpma & Hpcfg & Hpaddr & HA & Hord & HX & Hcov & Hallow).
          iApply (swp_mono with "[Hrun Hany] [Hrw Hro Hown]").
          2:{ iApply (swp_checked_mem_read_ifetch4_UR u_Drw u_Dro (u_Df dq) rs2
                        (u_walk_pa w_leaf pc)
                        (register_lookup pma_regions rsA)
                        (register_lookup pmpcfg_n rsA)
                        (register_lookup pmpaddr_n rsA) iw
                        (bytes_own_p (uv_F pt M IK) (uv_mm t' (upa_map pt M)))
                        u_disj u_in_pma u_in_pcfg u_in_paddr u_in_htif
                        Hhtif Hpma Hpcfg Hpaddr HA Hord HX Hcov Hallow
                        Hram0 Hram3 Halp with "Hcert Hrw Hro Hown []").
              iApply (uv_fetch_pay pt M t' IK w_leaf pc 4 4 iw eq_refl Hinj Htok'
                        Hl Hnc Hb Htx with "Hlb"). }
          iIntros (r) "(-> & Hrw & Hro & Hown)".
          iSplitR; [done|]. iFrame "Hrw Hro Hrun Hany". iExists IK. iFrame "Hlb Hown". }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2) "(%HQ & (Hrun & Hown & Hany) & Hrw & Hro)".
    rewrite /uv_fetch_post. iSplitR; [done|].
    iExists rs2, rsf, t'. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!; [exact Tr | exact HQ | exact Htlbok' | exact Htok' | exact Hshape].
  Qed.

  (* ---- (b) a 2-mod-4 pc holding a COMPRESSED instruction: ONE 2-byte read *)
  Lemma uv_swp_fetch_rvc2 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rsA : regstate) (w_leaf pc : mword 64) (h : mword 16) :
    uva_inj pt M ->
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    uM_bytes M (uint pc) 2 h ->
    isRVC h = true ->
    uva_text pt (uint pc) ->
    register_lookup PC rsA = pc ->
    register_lookup cur_privilege rsA = User ->
    _get_Mstatus_SXL (register_lookup mstatus rsA) = 'b"10" ->
    register_lookup menvcfg rsA = MENVCFG_S ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df dq) rsA u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (fetch tt) (uv_fetch_post dq pt M rsA t (F_RVC h)).
  Proof.
    intros Hinj Hl Hlok Hcanon Hal2 Hnal4 Hb Hrvc Htx Lpc Lcp Lsxl Lmenv Hpins Htok.
    pose proof Hpins as ((Hmisa & _ & _ & _ & _ & _) & _).
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsA))
                       (MachineWord.MachineWord.N_to_word 1 1%N) = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
    assert (Hnc : forall j : nat, (j < 2)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
      by (intros j Hj; exact (ualign2_nc pc (Z.of_nat j) Hal2 ltac:(lia))).
    pose proof (uv_tree_ok_data pt M t Hinj Htok) as Htokd.
    destruct (uv_walk_fetch pt t (upa_map pt (uM_data pt M)) rsA w_leaf pc
                Hl Hlok Hcanon Lcp Lsxl Lmenv Hpins Htokd)
      as (rsf & t' & Htr & Htrg & Tr & Htlbok' & Htokd' & Hshape).
    pose proof (uv_tree_ok_of_data pt M t t' Htok Htokd' Hshape) as Htok'.
    pose proof (proj1 (proj2 (proj2 Htok))) as Hram.
    assert (Hram0 : addr_is_ram (u_walk_pa w_leaf pc)).
    { rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 2 16 h Hinj (proj1 (proj2 Htok)) Hl
               Hnc Hb 0%nat ltac:(lia)). }
    assert (Hram1 : addr_is_ram (pa_add (u_walk_pa w_leaf pc) 1)).
    { apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 2 16 h Hinj (proj1 (proj2 Htok)) Hl
               Hnc Hb 1%nat ltac:(lia)). }
    assert (Halp : is_aligned_paddr (Physaddr (u_walk_pa w_leaf pc)) 2 = true)
      by exact (pa_aligned_div _ pc 2 ltac:(lia) (Z.divide_factor_l 2 2048) Hal2).
    set (Qf := fun rs2 : regstate => reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf).
    assert (Hmv : forall rs2, Qf rs2 -> forall q : register, q ∈ u_Drw ∪ u_Dro ->
              register_beq q (tlb : register) = false ->
              register_lookup q rs2 = register_lookup q rsA)
      by (intros rs2 HQ; exact (u_bridge_mv rsA rsf rs2 Tr HQ)).
    assert (Hpriv : forall rs2, Qf rs2 -> register_lookup cur_privilege rs2 = User).
    { intros rs2 HQ.
      rewrite (Hmv rs2 HQ _ u_in_priv ltac:(vm_compute; reflexivity)). exact Lcp. }
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    iApply (swp_mono with "[] [Hany Hrw Hro Hrun Hown]").
    2:{ iApply (uv_fetch_rvc2_P u_Drw u_Dro (u_Df dq) rsA Qf
                  (fun _ => (TsoCtx.own_context XI ∗ uv_bytes pt M t' ∗
                             resv_any cpu_id)%I)
                  pc (u_walk_pa w_leaf pc) h u_disj u_in_PC u_in_misa u_in_mst
                  u_in_priv Lpc Hpriv HmisaC Hbit0 Hbit1 Hnal4 Hrvc
                  with "Hcert Hrw Hro [Hany Hrun Hown] []").
        - iIntros "Hrw Hro".
          iApply (uv_swp_walk pt M M t t' dq rsA rsA rsf _ _ _ Hinj Hinj eq_refl
                    Htok Htok' (eq_sym (uv_mmd_dom pt M t t' Hshape))
                    ltac:(intros r _; reflexivity) Htr Htrg
                    with "Hcert Hany Hrw Hro Hrun Hown").
          iIntros (rs2) "%Hag Hrw Hro Hrun Hown Hany".
          iSplitR; [done|]. iExists rs2. iSplitR; [iPureIntro; exact Hag|].
          iFrame.
        - iIntros (rs2) "%HQ (Hrun & Hown & Hany) Hrw Hro".
          iDestruct "Hown" as (IK) "[#Hlb Hown]".
          destruct (uv_read_pins pt t rsA rs2 Hpins (Hmv rs2 HQ))
            as (Hhtif & Hpma & Hpcfg & Hpaddr & HA & Hord & HX & Hcov & Hallow).
          iApply (swp_mono with "[Hrun Hany] [Hrw Hro Hown]").
          2:{ iApply (swp_checked_mem_read_ifetch2_UR u_Drw u_Dro (u_Df dq) rs2
                        (u_walk_pa w_leaf pc)
                        (register_lookup pma_regions rsA)
                        (register_lookup pmpcfg_n rsA)
                        (register_lookup pmpaddr_n rsA) h
                        (bytes_own_p (uv_F pt M IK) (uv_mm t' (upa_map pt M)))
                        u_disj u_in_pma u_in_pcfg u_in_paddr u_in_htif
                        Hhtif Hpma Hpcfg Hpaddr HA Hord HX Hcov Hallow
                        Hram0 Hram1 Halp with "Hcert Hrw Hro Hown []").
              iApply (uv_fetch_pay pt M t' IK w_leaf pc 2 2 h eq_refl Hinj Htok'
                        Hl Hnc Hb Htx with "Hlb"). }
          iIntros (r) "(-> & Hrw & Hro & Hown)".
          iSplitR; [done|]. iFrame "Hrw Hro Hrun Hany". iExists IK. iFrame "Hlb Hown". }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2) "(%HQ & (Hrun & Hown & Hany) & Hrw & Hro)".
    rewrite /uv_fetch_post. iSplitR; [done|].
    iExists rs2, rsf, t'. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!; [exact Tr | exact HQ | exact Htlbok' | exact Htok' | exact Hshape].
  Qed.

  (* ---- (c) a 2-mod-4 pc holding a BASE instruction: TWO walks, TWO 2-byte
     reads.  The second walk starts from the FIRST half's Iris landing file
     [rs1], which agrees with the pure landing [rsf1] on the footprint --
     exactly what [uv_swp_walk] takes -- and the second halfword's leaf is
     the pc's own ([ui_inpage] keeps the window on one page). *)
  Lemma uv_swp_fetch_base2 (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rsA : regstate) (w_leaf pc : mword 64) (iw : mword 32) :
    uva_inj pt M ->
    ud_um pt !! svpn_of pc = Some w_leaf ->
    uleaf_ok (InstructionFetch tt) w_leaf ->
    uva_canon pc ->
    Z.rem (uint pc) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    uM_bytes M (uint pc) 4 iw ->
    isRVC (subrange_vec_dec iw 15 0) = false ->
    uva_text pt (uint pc) ->
    register_lookup PC rsA = pc ->
    register_lookup cur_privilege rsA = User ->
    _get_Mstatus_SXL (register_lookup mstatus rsA) = 'b"10" ->
    register_lookup menvcfg rsA = MENVCFG_S ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df dq) rsA u_Dro -∗
    TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
    swp (fetch tt) (uv_fetch_post dq pt M rsA t (F_Base iw)).
  Proof.
    intros Hinj Hl Hlok Hcanon Hpg Hal2 Hnal4 Hb HnRVC Htx Lpc Lcp Lsxl Lmenv
      Hpins Htok.
    pose proof Hpins as ((Hmisa & _ & _ & _ & _ & _) & _).
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa rsA))
                       (MachineWord.MachineWord.N_to_word 1 1%N) = true)
      by (rewrite Hmisa; vm_compute; reflexivity).
    destruct (align2_not4_facts pc Hal2 Hnal4) as (_ & Hbit0 & Hbit1).
    (* the second halfword's own facts, off the in-page bound *)
    pose proof (uinpage_nc pc 2 Hpg ltac:(lia)) as Hnc2.
    assert (Hl2 : ud_um pt !! svpn_of (add_vec_int pc 2) = Some w_leaf)
      by (rewrite (usvpn_window pc 2 ltac:(lia) Hnc2); exact Hl).
    pose proof (uva_canon_add pc 2 Hcanon ltac:(lia) Hnc2) as Hcanon2.
    destruct (uwin_shift pc 2 Hpg ltac:(lia)) as [Hu2 Hmod2].
    assert (Hal2h : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true)
      by exact (ualign2_plus2 pc Hal2).
    assert (Hncl : forall j : nat, (j < 2)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
      by (intros j Hj; exact (ualign2_nc pc (Z.of_nat j) Hal2 ltac:(lia))).
    assert (Hnch : forall j : nat, (j < 2)%nat ->
              bv_unsigned (add_vec_int pc 2) mod 4096 + Z.of_nat j < 4096)
      by (intros j Hj; exact (ualign2_nc (add_vec_int pc 2) (Z.of_nat j) Hal2h
                                ltac:(lia))).
    assert (Hnc4 : forall j : nat, (j < 4)%nat ->
              bv_unsigned pc mod 4096 + Z.of_nat j < 4096)
      by (intros j Hj; exact (uinpage_nc pc (Z.of_nat j) Hpg ltac:(lia))).
    assert (Hb1 : uM_bytes M (uint pc) 2 (subrange_vec_dec iw 15 0 : mword 16)).
    { intros j Hj. rewrite (nth_byte_subrange_lo iw j ltac:(lia)).
      exact (Hb j ltac:(lia)). }
    assert (Hb2 : uM_bytes M (uint (add_vec_int pc 2)) 2
                    (subrange_vec_dec iw 31 16 : mword 16)).
    { intros j Hj.
      rewrite (nth_byte_subrange_hi iw j ltac:(lia)).
      pose proof (Hb (2 + j)%nat ltac:(lia)) as Hbj.
      rewrite Nat2Z.inj_add in Hbj. change (Z.of_nat 2) with 2 in Hbj.
      rewrite Hu2. rewrite <- Z.add_assoc. exact Hbj. }
    assert (Htx2 : uva_text pt (uint (add_vec_int pc 2))).
    { rewrite Hu2. exact (uva_text_window pt pc 2 Hnc2 Htx). }
    (* ---- the low halfword's walk ---- *)
    pose proof (uv_tree_ok_data pt M t Hinj Htok) as Htokd.
    destruct (uv_walk_fetch pt t (upa_map pt (uM_data pt M)) rsA w_leaf pc
                Hl Hlok Hcanon Lcp Lsxl Lmenv Hpins Htokd)
      as (rsf1 & t1 & Htr1 & Htr1g & Tr1 & Htlbok1 & Htokd1 & Hshape1).
    pose proof (uv_tree_ok_of_data pt M t t1 Htok Htokd1 Hshape1) as Htok1.
    (* ---- the high halfword's walk, at the pure state the first landed on ---- *)
    assert (Hpins1 : u_exec_pins pt t1 rsf1)
      by exact (u_exec_pins_only pt t t1 rsA rsf1 Tr1 Htlbok1 Hpins).
    assert (Lcp1 : register_lookup cur_privilege rsf1 = User)
      by (rewrite (Tr1 cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp).
    assert (Lsxl1 : _get_Mstatus_SXL (register_lookup mstatus rsf1) = 'b"10")
      by (rewrite (Tr1 mstatus ltac:(vm_compute; reflexivity)); exact Lsxl).
    assert (Lmenv1 : register_lookup menvcfg rsf1 = MENVCFG_S)
      by (rewrite (Tr1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
    assert (Lpc1 : register_lookup PC rsf1 = pc)
      by (rewrite (Tr1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
    destruct (uv_walk_fetch pt t1 (upa_map pt (uM_data pt M)) rsf1 w_leaf
                (add_vec_int pc 2) Hl2 Hlok Hcanon2 Lcp1 Lsxl1 Lmenv1 Hpins1 Htokd1)
      as (rsf2 & t2 & Htr2 & Htr2g & Tr2 & Htlbok2 & Htokd2 & Hshape2).
    pose proof (uv_tree_ok_of_data pt M t1 t2 Htok1 Htokd2 Hshape2) as Htok2.
    pose proof (u_tlb_only_trans rsA rsf1 rsf2 Tr1 Tr2) as Tr12.
    pose proof (pt_same_shape_trans 2 t t1 t2 Hshape1 Hshape2) as Hshape12.
    (* the two windows' RAM and alignment *)
    pose proof (proj1 (proj2 (proj2 Htok))) as Hram.
    assert (Hram0 : addr_is_ram (u_walk_pa w_leaf pc)).
    { rewrite <- (pa_add_0 (u_walk_pa w_leaf pc)). apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 4 32 iw Hinj (proj1 (proj2 Htok)) Hl
               Hnc4 Hb 0%nat ltac:(lia)). }
    assert (Hram1 : addr_is_ram (pa_add (u_walk_pa w_leaf pc) 1)).
    { apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf pc 4 32 iw Hinj (proj1 (proj2 Htok)) Hl
               Hnc4 Hb 1%nat ltac:(lia)). }
    assert (Hram2 : addr_is_ram (u_walk_pa w_leaf (add_vec_int pc 2))).
    { rewrite <- (pa_add_0 (u_walk_pa w_leaf (add_vec_int pc 2))). apply Hram.
      apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf (add_vec_int pc 2) 2 16 _ Hinj
               (proj1 (proj2 Htok)) Hl2 Hnch Hb2 0%nat ltac:(lia)). }
    assert (Hram3 : addr_is_ram (pa_add (u_walk_pa w_leaf (add_vec_int pc 2)) 1)).
    { apply Hram. apply elem_of_dom.
      exact (uv_win_some pt M t w_leaf (add_vec_int pc 2) 2 16 _ Hinj
               (proj1 (proj2 Htok)) Hl2 Hnch Hb2 1%nat ltac:(lia)). }
    assert (Halp1 : is_aligned_paddr (Physaddr (u_walk_pa w_leaf pc)) 2 = true)
      by exact (pa_aligned_div _ pc 2 ltac:(lia) (Z.divide_factor_l 2 2048) Hal2).
    assert (Halp2 : is_aligned_paddr (Physaddr (u_walk_pa w_leaf (add_vec_int pc 2))) 2
                    = true)
      by exact (pa_aligned_div _ (add_vec_int pc 2) 2 ltac:(lia)
                  (Z.divide_factor_l 2 2048) Hal2h).
    set (Qf1 := fun rs1 : regstate => reg_agree_on (u_Drw ∪ u_Dro) rs1 rsf1).
    set (Qf2 := fun rs2 : regstate => reg_agree_on (u_Drw ∪ u_Dro) rs2 rsf2).
    assert (Hmv1 : forall rs1, Qf1 rs1 -> forall q : register, q ∈ u_Drw ∪ u_Dro ->
              register_beq q (tlb : register) = false ->
              register_lookup q rs1 = register_lookup q rsA)
      by (intros rs1 HQ; exact (u_bridge_mv rsA rsf1 rs1 Tr1 HQ)).
    assert (Hmv2 : forall rs2, Qf2 rs2 -> forall q : register, q ∈ u_Drw ∪ u_Dro ->
              register_beq q (tlb : register) = false ->
              register_lookup q rs2 = register_lookup q rsA)
      by (intros rs2 HQ; exact (u_bridge_mv rsA rsf2 rs2 Tr12 HQ)).
    assert (Hpriv1 : forall rs1, Qf1 rs1 -> register_lookup cur_privilege rs1 = User).
    { intros rs1 HQ.
      rewrite (Hmv1 rs1 HQ _ u_in_priv ltac:(vm_compute; reflexivity)). exact Lcp. }
    assert (Hpriv2 : forall rs2, Qf2 rs2 -> register_lookup cur_privilege rs2 = User).
    { intros rs2 HQ.
      rewrite (Hmv2 rs2 HQ _ u_in_priv ltac:(vm_compute; reflexivity)). exact Lcp. }
    assert (Hpc1 : forall rs1, Qf1 rs1 -> register_lookup (R_bitvector_64 PC) rs1 = pc).
    { intros rs1 HQ.
      rewrite (Hmv1 rs1 HQ _ u_in_PC ltac:(vm_compute; reflexivity)). exact Lpc. }
    iIntros "#Hcert Hany Hrw Hro Hrun Hown".
    iApply (swp_mono with "[] [Hany Hrw Hro Hrun Hown]").
    2:{ iApply (uv_fetch_base2_P u_Drw u_Dro (u_Df dq) rsA Qf1 Qf2
                  (fun _ => (TsoCtx.own_context XI ∗ uv_bytes pt M t1 ∗
                             resv_any cpu_id)%I)
                  (fun _ => (TsoCtx.own_context XI ∗ uv_bytes pt M t2 ∗
                             resv_any cpu_id)%I)
                  pc (u_walk_pa w_leaf pc) (u_walk_pa w_leaf (add_vec_int pc 2))
                  (subrange_vec_dec iw 15 0) (subrange_vec_dec iw 31 16)
                  u_disj u_in_PC u_in_misa u_in_mst u_in_priv Lpc Hpc1 Hpriv1
                  Hpriv2 HmisaC Hbit0 Hbit1 Hnal4 HnRVC
                  with "Hcert Hrw Hro [Hany Hrun Hown] [] [] []").
        - (* the low walk *)
          iIntros "Hrw Hro".
          iApply (uv_swp_walk pt M M t t1 dq rsA rsA rsf1 _ _ _ Hinj Hinj eq_refl
                    Htok Htok1 (eq_sym (uv_mmd_dom pt M t t1 Hshape1))
                    ltac:(intros r _; reflexivity) Htr1 Htr1g
                    with "Hcert Hany Hrw Hro Hrun Hown").
          iIntros (rs1) "%Hag Hrw Hro Hrun Hown Hany".
          iSplitR; [done|]. iExists rs1. iSplitR; [iPureIntro; exact Hag|].
          iFrame.
        - (* the low read *)
          iIntros (rs1) "%HQ (Hrun & Hown & Hany) Hrw Hro".
          iDestruct "Hown" as (IK) "[#Hlb Hown]".
          destruct (uv_read_pins pt t rsA rs1 Hpins (Hmv1 rs1 HQ))
            as (Hhtif & Hpma & Hpcfg & Hpaddr & HA & Hord & HX & Hcov & Hallow).
          iApply (swp_mono with "[Hrun Hany] [Hrw Hro Hown]").
          2:{ iApply (swp_checked_mem_read_ifetch2_UR u_Drw u_Dro (u_Df dq) rs1
                        (u_walk_pa w_leaf pc)
                        (register_lookup pma_regions rsA)
                        (register_lookup pmpcfg_n rsA)
                        (register_lookup pmpaddr_n rsA) (subrange_vec_dec iw 15 0)
                        (bytes_own_p (uv_F pt M IK) (uv_mm t1 (upa_map pt M)))
                        u_disj u_in_pma u_in_pcfg u_in_paddr u_in_htif
                        Hhtif Hpma Hpcfg Hpaddr HA Hord HX Hcov Hallow
                        Hram0 Hram1 Halp1 with "Hcert Hrw Hro Hown []").
              iApply (uv_fetch_pay pt M t1 IK w_leaf pc 2 2 _ eq_refl Hinj Htok1
                        Hl Hncl Hb1 Htx with "Hlb"). }
          iIntros (r) "(-> & Hrw & Hro & Hown)".
          iSplitR; [done|]. iFrame "Hrw Hro Hrun Hany". iExists IK. iFrame "Hlb Hown".
        - (* the high walk, from the first half's Iris landing *)
          iIntros (rs1) "%HQ (Hrun & Hown & Hany) Hrw Hro".
          iApply (uv_swp_walk pt M M t1 t2 dq rs1 rsf1 rsf2 _ _ _ Hinj Hinj eq_refl
                    Htok1 Htok2 (eq_sym (uv_mmd_dom pt M t1 t2 Hshape2))
                    HQ Htr2 Htr2g
                    with "Hcert Hany Hrw Hro Hrun Hown").
          iIntros (rs2) "%Hag Hrw Hro Hrun Hown Hany".
          iSplitR; [done|]. iExists rs2. iSplitR; [iPureIntro; exact Hag|].
          iFrame.
        - (* the high read *)
          iIntros (rs2) "%HQ (Hrun & Hown & Hany) Hrw Hro".
          iDestruct "Hown" as (IK) "[#Hlb Hown]".
          destruct (uv_read_pins pt t rsA rs2 Hpins (Hmv2 rs2 HQ))
            as (Hhtif & Hpma & Hpcfg & Hpaddr & HA & Hord & HX & Hcov & Hallow).
          iApply (swp_mono with "[Hrun Hany] [Hrw Hro Hown]").
          2:{ iApply (swp_checked_mem_read_ifetch2_UR u_Drw u_Dro (u_Df dq) rs2
                        (u_walk_pa w_leaf (add_vec_int pc 2))
                        (register_lookup pma_regions rsA)
                        (register_lookup pmpcfg_n rsA)
                        (register_lookup pmpaddr_n rsA) (subrange_vec_dec iw 31 16)
                        (bytes_own_p (uv_F pt M IK) (uv_mm t2 (upa_map pt M)))
                        u_disj u_in_pma u_in_pcfg u_in_paddr u_in_htif
                        Hhtif Hpma Hpcfg Hpaddr HA Hord HX Hcov Hallow
                        Hram2 Hram3 Halp2 with "Hcert Hrw Hro Hown []").
              iApply (uv_fetch_pay pt M t2 IK w_leaf (add_vec_int pc 2) 2 2 _
                        eq_refl Hinj Htok2 Hl2 Hnch Hb2 Htx2 with "Hlb"). }
          iIntros (r) "(-> & Hrw & Hro & Hown)".
          iSplitR; [done|]. iFrame "Hrw Hro Hrun Hany". iExists IK. iFrame "Hlb Hown". }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2) "(%HQ & (Hrun & Hown & Hany) & Hrw & Hro)".
    rewrite /uv_fetch_post. rewrite (concat_subranges_id iw). iSplitR; [done|].
    iExists rs2, rsf2, t2. iFrame "Hrw Hro Hrun Hown Hany".
    iPureIntro. split_and!;
      [exact Tr12 | exact HQ | exact Htlbok2 | exact Htok2 | exact Hshape12].
  Qed.

  (* ---- THE FETCH BRIDGE: what a leaf hands the obligation -- the fetch
     driven from the entry file over the tier's currency to the post above *)
  Definition uv_fetch_bridge (dq : dfrac) (pt : uptd) (M : gmap Z (bv 8))
      (rsA : regstate) (t : ptree) (fr : FetchResult) : iProp Σ :=
    (gen_cert -∗ resv_any cpu_id -∗
     hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df dq) rsA u_Dro -∗
     TsoCtx.own_context XI -∗ uv_bytes pt M t -∗
     swp (fetch tt) (uv_fetch_post dq pt M rsA t fr))%I.

  (* ---- THE FETCH FROM [uinstr]'S DATA, once for every geometry: what a
     leaf hands the obligation.  The compressed-at-4-aligned case reads the
     whole word and takes its low half ([urvc4_low]). *)
  Lemma uv_swp_fetch_uinstr (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (dq : dfrac) (rsA : regstate) (pc : mword 64) (is_rvc : bool)
      (i : instruction) :
    uva_inj pt M ->
    uinstr pt M pc is_rvc i ->
    register_lookup PC rsA = pc ->
    register_lookup cur_privilege rsA = User ->
    _get_Mstatus_SXL (register_lookup mstatus rsA) = 'b"10" ->
    register_lookup menvcfg rsA = MENVCFG_S ->
    u_exec_pins pt t rsA ->
    uv_tree_ok pt (upa_map pt M) t ->
    ⊢ (if is_rvc
       then ∃ h : mword 16, ⌜isRVC h = true /\ udecode_rvc h i⌝ ∗
              uv_fetch_bridge dq pt M rsA t (F_RVC h)
       else ∃ w : mword 32,
              ⌜isRVC (subrange_vec_dec w 15 0) = false /\ udecode_base w i⌝ ∗
              uv_fetch_bridge dq pt M rsA t (F_Base w)).
  Proof.
    intros Hinj Hui Lpc Lcp Lsxl Lmenv Hpins Htok.
    destruct Hui as [Hal2 Hcanon Hleaf Hinpage Hcode Htext].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iStartProof.
    destruct is_rvc.
    - destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      iExists h. iSplitR; [iPureIntro; exact (conj HisRVC Hdecrvc) |].
      rewrite /uv_fetch_bridge. iIntros "#Hcert Hany Hrw Hro Hctx Hmm".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Hnext2 eq_refl) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes M (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        iPoseProof (uv_swp_fetch4 pt M t dq rsA w_leaf pc (urvc4_word h b2 b3)
                      Hinj Hum Hlok Hcanon Hal4 Hbytes4 Htext Lpc Lcp Lsxl Lmenv
                      Hpins Htok with "Hcert Hany Hrw Hro Hctx Hmm") as "H".
        iEval (rewrite urvc4_low HisRVC) in "H". iExact "H".
      + iApply (uv_swp_fetch_rvc2 pt M t dq rsA w_leaf pc h
                  Hinj Hum Hlok Hcanon Hal2 Hal4 Hbytes HisRVC Htext Lpc Lcp Lsxl
                  Lmenv Hpins Htok with "Hcert Hany Hrw Hro Hctx Hmm").
    - destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      iExists w. iSplitR; [iPureIntro; exact (conj HnRVC Hdecbase) |].
      rewrite /uv_fetch_bridge. iIntros "#Hcert Hany Hrw Hro Hctx Hmm".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + iPoseProof (uv_swp_fetch4 pt M t dq rsA w_leaf pc w
                      Hinj Hum Hlok Hcanon Hal4 Hbytes Htext Lpc Lcp Lsxl Lmenv
                      Hpins Htok with "Hcert Hany Hrw Hro Hctx Hmm") as "H".
        iEval (rewrite HnRVC) in "H". iExact "H".
      + iApply (uv_swp_fetch_base2 pt M t dq rsA w_leaf pc w
                  Hinj Hum Hlok Hcanon Hinpage Hal2 Hal4 Hbytes HnRVC Htext Lpc
                  Lcp Lsxl Lmenv Hpins Htok with "Hcert Hany Hrw Hro Hctx Hmm").
  Qed.

End UvOpen.
