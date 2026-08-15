(* WpUmodeStore.v -- THE MEMORY-WRITING LEAF of the verified user-execution
   tier (claude-notes/projects/user-verified.md): [c.sdsp rs2, uimm(sp)].

   Every other leaf (WpUmodeLeaf.v) rides the retire funnel [wp_uv_retire],
   whose post-execute state is a PURE register tower ([uv_post] = an
   optional nextPC redirect then an optional gpr write).  A store leaves
   that tower behind twice over: it writes MEMORY, and -- because the
   store's own [translateAddr] may fill the TLB or write back A/D -- its
   post state is not even a function of the pre state.  So this file adds,
   ALONGSIDE the funnel (nothing in WpUmodeStep.v is restructured):

   §1 [uM_store8] -- the image-level effect: the 8 little-endian bytes of
      the stored word land at the target va and the following seven.  Kept
      here rather than in UmodeMem.v purely to avoid rebuilding the six
      files above it; RELOCATION DEBT: it reads naturally beside
      [uM_bytes].

   §2 [umem_store_8] -- the Iris composer: translate the target at User
      through [utlb_inv_pt_translateAddr_u (Store Data)], write the eight
      physical bytes against [gen_heap_interp], and re-establish
      [umem pt (uM_store8 M ...)].  The concrete-byte twin of
      UserMemPt's [user_pt_store_data_g] (which owns its pages with
      EXISTENTIAL contents and therefore says nothing about what was
      stored).

   §3 [exec_execute_STORE_8_u_walk] -- the value-precise execute at User
      privilege with MPRV = 0 (so effectivePrivilege = User): the U-mode
      analog of WpSmodePtLeaves' [exec_execute_STORE_8_gpr_S_walk_pt],
      assembled from the safety tier's U-mode memory arms.

   §4 [uv_retire_post_state] -- the store-flavoured POST: a strict
      generalization of WpUmodeStep's [uv_retire_post_fetch] tail in which
      the post-execute state is an arbitrary [s_x] the caller has already
      established, instead of the [uv_post] tower.

   §5 [wp_uv_csdsp] -- the leaf.  Same shape as every other leaf: image in,
      image out, hart re-bound by the continuation. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv WireInv WpGpr RegFile InstrBytes.
Require Import SmodeCore.
Require Import CommonWalk UserBits.
Require Import MemAccessGen WpMmodeLeafBase.
Require Import WpDecodeBridge DecodeTotalU.
Require Import UptTree UserPtTree UserExec UserStep.
Require Import UserMemPt UserMemArms UserMemClassify.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 The image-level effect of an 8-byte store.                          *)
(* ===================================================================== *)

(* [M] with the little-endian bytes of [v] written at [a .. a+7].  Spelled
   as the same [foldr]-of-inserts the model's [write_bytes] is, so the
   ghost update below is a byte-for-byte mirror of [upd_window]. *)
Definition uM_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) : gmap Z (bv 8) :=
  foldr (fun (j : nat) (acc : gmap Z (bv 8)) => <[a + Z.of_nat j := nth_byte v j]> acc)
        M (seq 0 8).

(* an insert run never removes a key *)
Lemma uM_fold_is_Some (a : Z) (v : mword 64) (l : list nat)
    (M : gmap Z (bv 8)) (k : Z) :
  is_Some (M !! k) ->
  is_Some (foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                    <[a + Z.of_nat j := nth_byte v j]> acc) M l !! k).
Proof.
  induction l as [ | x xs IH ]; cbn [foldr]; [ tauto | ].
  intro H. destruct (decide (k = a + Z.of_nat x)) as [-> | Hne].
  - rewrite lookup_insert. exact (mk_is_Some _ _ eq_refl).
  - rewrite lookup_insert_ne; [ apply IH; exact H | congruence ].
Qed.

Lemma uM_store8_is_Some (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  is_Some (M !! k) -> is_Some (uM_store8 M a v !! k).
Proof. apply uM_fold_is_Some. Qed.

(* the run's own eight keys *)
Lemma uM_store8_lookup (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_store8 M a v !! (a + 0) = Some (nth_byte v 0) /\
  uM_store8 M a v !! (a + 1) = Some (nth_byte v 1) /\
  uM_store8 M a v !! (a + 2) = Some (nth_byte v 2) /\
  uM_store8 M a v !! (a + 3) = Some (nth_byte v 3) /\
  uM_store8 M a v !! (a + 4) = Some (nth_byte v 4) /\
  uM_store8 M a v !! (a + 5) = Some (nth_byte v 5) /\
  uM_store8 M a v !! (a + 6) = Some (nth_byte v 6) /\
  uM_store8 M a v !! (a + 7) = Some (nth_byte v 7).
Proof.
  unfold uM_store8. cbn [seq foldr].
  split_and!;
    repeat (rewrite lookup_insert_ne; [ | lia ]);
    apply lookup_insert.
Qed.

(* ... in the [uM_bytes] shape the fetch/ABI layer speaks *)
Lemma uM_store8_bytes (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_bytes (uM_store8 M a v) a 8 v.
Proof.
  intros j Hj.
  destruct (uM_store8_lookup M a v) as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  destruct j as [ | [ | [ | [ | [ | [ | [ | [ | j ] ] ] ] ] ] ] ];
    try (exfalso; lia);
    [ exact H0 | exact H1 | exact H2 | exact H3
    | exact H4 | exact H5 | exact H6 | exact H7 ].
Qed.

(* keys off the run are untouched *)
Lemma uM_store8_lookup_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (forall j : nat, (j < 8)%nat -> k <> a + Z.of_nat j) ->
  uM_store8 M a v !! k = M !! k.
Proof.
  intro Hne.
  assert (H : forall j : nat, (j < 8)%nat -> a + Z.of_nat j <> k)
    by (intros j Hj He; exact (Hne j Hj (eq_sym He))).
  unfold uM_store8. cbn [seq foldr].
  repeat (rewrite lookup_insert_ne;
          [ | first [ exact (H 0%nat ltac:(lia)) | exact (H 1%nat ltac:(lia))
                    | exact (H 2%nat ltac:(lia)) | exact (H 3%nat ltac:(lia))
                    | exact (H 4%nat ltac:(lia)) | exact (H 5%nat ltac:(lia))
                    | exact (H 6%nat ltac:(lia)) | exact (H 7%nat ltac:(lia)) ] ]).
  reflexivity.
Qed.

(* the in-page bound at the STORE width (UmodeFetch's [uinpage_nc] is the
   4-byte fetch-window version) *)
Lemma uinpage_nc8 (va : mword 64) (d : Z) :
  Z.rem (uint va) 4096 <= 4088 -> 0 <= d <= 7 ->
  bv_unsigned va mod 4096 + d < 4096.
Proof.
  intros Hpg Hd.
  rewrite uint_unsigned in Hpg.
  rewrite Z.rem_mod_nonneg in Hpg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  lia.
Qed.

(* ===================================================================== *)
(* §2 The Iris composer: translate at User, write eight owned bytes.       *)
(* ===================================================================== *)

Section UmodeStoreMem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the ghost half, list-generic (the [upd_window] mirror): every byte of
     the run is owned by [umem] AT the physical address the write hits. *)
  Lemma umem_upd_window (pt : uptd) (a : Z) (v : mword 64) (pa : Arch.pa)
      (l : list nat) (M : gmap Z (bv 8)) (mm : _) :
    (forall j : nat, In j l -> (uva_pa pt (a + Z.of_nat j) : Arch.pa) = pa_add pa j) ->
    (forall j : nat, In j l -> exists b : bv 8, M !! (a + Z.of_nat j) = Some b) ->
    gen_heap_interp (hG := riscv_memGS) mm -∗ umem pt M ==∗
    gen_heap_interp (hG := riscv_memGS)
      (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) mm l) ∗
    umem pt (foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                      <[a + Z.of_nat j := nth_byte v j]> acc) M l).
  Proof.
    revert M mm.
    induction l as [ | x xs IH ]; intros M mm Hpa HM; cbn [foldr].
    - iIntros "Hmm HM". iModIntro. iFrame.
    - iIntros "Hmm HM".
      iMod (IH M mm ltac:(intros j Hj; apply Hpa; right; exact Hj)
                        ltac:(intros j Hj; apply HM; right; exact Hj)
              with "Hmm HM") as "[Hmm HM]".
      destruct (HM x ltac:(left; reflexivity)) as (b0 & Hb0).
      destruct (uM_fold_is_Some a v xs M (a + Z.of_nat x)
                  (mk_is_Some _ _ Hb0)) as (b1 & Hb1).
      iDestruct (umem_insert_acc pt _ (a + Z.of_nat x) b1 Hb1 with "HM")
        as "[Hb Hback]".
      iMod (phys_update _ (uva_pa pt (a + Z.of_nat x) : Arch.pa) b1 (nth_byte v x)
              with "Hmm Hb") as "[Hmm Hb]".
      iDestruct ("Hback" $! (nth_byte v x) with "Hb") as "HM".
      assert (Heq : (uva_pa pt (a + Z.of_nat x) : Arch.pa) = pa_add pa x)
        by (apply Hpa; left; reflexivity).
      rewrite Heq.
      iModIntro. iFrame "Hmm HM".
  Qed.

  Lemma umem_store8_ghost (pt : uptd) (a : Z) (v : mword 64) (pa : Arch.pa)
      (M : gmap Z (bv 8)) (mm : _) :
    (forall j : nat, (j < 8)%nat -> (uva_pa pt (a + Z.of_nat j) : Arch.pa) = pa_add pa j) ->
    (forall j : nat, (j < 8)%nat -> exists b : bv 8, M !! (a + Z.of_nat j) = Some b) ->
    gen_heap_interp (hG := riscv_memGS) mm -∗ umem pt M ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes mm pa 8 v) ∗
    umem pt (uM_store8 M a v).
  Proof.
    intros Hpa HM.
    assert (Hin : forall j : nat, In j (seq 0 8) -> (j < 8)%nat).
    { intros j Hj. apply in_seq in Hj. lia. }
    unfold write_bytes, uM_store8. change (N.to_nat 8) with 8%nat.
    apply (umem_upd_window pt a v pa (seq 0 8) M mm
             (fun j Hj => Hpa j (Hin j Hj)) (fun j Hj => HM j (Hin j Hj))).
  Qed.

  (* the 8-byte store at a user-mapped, store-permitted, 8-aligned,
     in-one-page virtual address.  Everything after the translate is the
     k = 8 instance of UserMemPt's width-generic bricks. *)
  Lemma umem_store_8 (pt : uptd) (M : gmap Z (bv 8)) (w_st va v : mword 64)
      (sigma : mstate) :
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists b : bv 8, M !! (uint va + Z.of_nat j) = Some b) ->
    register_lookup misa sigma.(sregs) = MISA_C ->
    register_lookup menvcfg sigma.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sigma.(sregs) = None ->
    register_lookup cur_privilege sigma.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus sigma.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus sigma.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions sigma.(sregs)) ->
    reg_interp sigma.(sregs) -∗ gen_heap_interp sigma.(mem) -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M ==∗
    ∃ sig2 : mstate,
      ⌜exec (translateAddr (Virtaddr va) (Store Data)) sigma
        = Some (Ok (Physaddr (u_walk_pa w_st va), PBMT_PMA, init_ext_ptw), sig2)⌝ ∗
      (* the bump made [vmem_write_addr] announce the store before performing
         it, and the announcement runs its own PMA/PMP check -- so the composer
         has to hand the announcement back too *)
      ⌜exec (mem_write_ea (Physaddr (u_walk_pa w_st va)) 8 (Store Data)
               PBMT_PMA false false false) sig2 = Some (Ok tt, sig2)⌝ ∗
      ⌜exec (mem_write_value (Physaddr (u_walk_pa w_st va)) 8 v (Store Data)
               PBMT_PMA false false false) sig2
        = Some (Ok true,
                MState sig2.(sregs) (write_bytes sig2.(mem) (u_walk_pa w_st va) 8 v)
                  sig2.(mdev))⌝ ∗
      ⌜sig2.(mdev) = sigma.(mdev)⌝ ∗
      ⌜forall r : register, register_beq r tlb = false ->
         register_lookup r sig2.(sregs) = register_lookup r sigma.(sregs)⌝ ∗
      reg_interp sig2.(sregs) ∗
      gen_heap_interp (write_bytes sig2.(mem) (u_walk_pa w_st va) 8 v) ∗
      utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
      umem pt (uM_store8 M (uint va) v).
  Proof.
    intros Hl Hchk Hcanon Hpg Hal HMb Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv HM".
    iDestruct (utlb_inv_pt_pmp_facts (ud_root pt) (ud_tfp pt) (ud_um pt) sigma
                 with "Hri Hinv") as %(HA & Hord & HX & HR & HW & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (Store Data)
            (ud_root pt) (ud_tfp pt) (ud_um pt) w_st va (u_walk_pa w_st va) sigma
            Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (Store Data)
               (register_lookup mstatus sigma.(sregs)) User sigma Hmprv)
            (exec_is_shadow_stack_u_acc (Store Data) sigma
               (or_intror (or_intror (or_introl eq_refl)))) Hall
            with "Hri Hgh Hinv")
      as (sig2) "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r sig2.(sregs) = register_lookup r sigma.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    assert (Hnc : forall j : nat, (j < 8)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nc8 va (Z.of_nat j) Hpg). lia. }
    (* the byte-level RAM facts, out of the image (the store window's
       first and last byte are what the PMP range check needs) *)
    destruct (HMb 0%nat ltac:(lia)) as (b0 & Hb0).
    destruct (HMb 7%nat ltac:(lia)) as (b7 & Hb7).
    iDestruct (umem_fetch_byte pt M w_st va 0 b0 sig2 Hl
                 (Hnc 0%nat ltac:(lia)) Hb0 with "Hgh HM") as %[_ Hram0].
    iDestruct (umem_fetch_byte pt M w_st va 7 b7 sig2 Hl
                 (Hnc 7%nat ltac:(lia)) Hb7 with "Hgh HM") as %[_ Hram7].
    set (pa := u_walk_pa w_st va) in *.
    assert (Hram0' : addr_is_ram pa)
      by (rewrite <- (pa_add_0 pa); exact Hram0).
    (* the region and the PMP range, shared by the announcement and the store *)
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions sig2.(sregs))) pa 8
              (pma_access_ram _ _ _ Hram0' Hram7 (pma_width_ok 8 eq_refl eq_refl) eq_refl eq_refl))
      as (region & Hpmam & _ & _ & Hwrb).
    pose proof (addr_is_ram_not_in_clint _ Hram0') as Hnc_c.
    pose proof (addr_is_ram_not_in_sig _ Hram0') as Hnc_s.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sig2.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 8)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp pa _ 8 7 ltac:(lia) ltac:(lia)
               ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram0' Hram7 Hcovp). }
    (* the physical write fact at [sig2] *)
    assert (Hwr : exec (mem_write_value (Physaddr pa) 8 v (Store Data)
                          PBMT_PMA false false false) sig2
                  = Some (Ok true,
                          MState sig2.(sregs) (write_bytes sig2.(mem) pa 8 v) sig2.(mdev))).
    { exact (exec_mem_write_value_U 8 ltac:(lia) exec_write_ram_plain_8 PBMT_PMA pa region v sig2
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam
               (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal)
               (proj1 Hwrb)
               (within_clint_false pa 8 sig2 Hnc_c ltac:(lia))
               (within_sig_false pa 8 sig2 Hnc_s ltac:(lia))
               (within_htif_writable_false pa 8 sig2
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity));
                         exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0')
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    (* ...and the effective-address announcement, at the same facts *)
    assert (Hea : exec (mem_write_ea (Physaddr pa) 8 (Store Data) PBMT_PMA false false false) sig2
                  = Some (Ok tt, sig2)).
    { assert (Heff' : exec (effectivePrivilege (Store Data)
                              (register_lookup mstatus sig2.(sregs))
                              (register_lookup cur_privilege sig2.(sregs))) sig2
                      = Some (User, sig2)).
      { rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). rewrite Hcp.
        apply exec_effectivePrivilege_mprv0.
        rewrite (Tr mstatus ltac:(vm_compute; reflexivity)). exact Hmprv. }
      refine (exec_mem_write_ea_g 8 pa (Store Data) PBMT_PMA User sig2 Heff' _ _).
      - unfold check_pma_with_pmp_priority.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmaCheck_ram_store_g 8 pa PBMT_PMA region sig2 Hpmam
                      (pa_aligned_div _ va 8 ltac:(lia) ltac:(exists 512; reflexivity) Hal)
                      (proj1 Hwrb))).
        cbn match. apply exec_returnm.
      - exact (exec_pmpCheck_user_grant_store pa 8 sig2
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))). }
    (* the ghost half *)
    iMod (umem_store8_ghost pt (uint va) v pa M sig2.(mem)
            (fun j Hj => uva_pa_window pt w_st va j Hl (Hnc j Hj)) HMb
            with "Hgh HM") as "[Hgh HM]".
    iModIntro. iExists sig2.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro; exact Hea | ].
    iSplit; [ iPureIntro; exact Hwr | ].
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Tr | ].
    iFrame "Hri Hgh Hinv HM".
  Qed.

End UmodeStoreMem.

(* ===================================================================== *)
(* §3 The value-precise 8-byte STORE execute at User.                      *)
(* ===================================================================== *)

(* the two width-8 autocast identities the model's [subrange]-of-rs2 and
   the misaligned-split loop's chunk projection leave behind *)
Local Lemma ucast_store8_a (d : mword 64) :
  autocast (T := mword) (subrange_vec_dec d (Z.sub (Z.mul 8 8) 1) 0) = d.
Proof. apply autocast_subrange_id. Qed.

Local Lemma ucast_store8_b (d : mword 64) :
  (autocast (T := mword) (subrange_vec_dec d (8 * (0 + 1) * 8 - 1) (8 * 0 * 8))
   : mword (8 * 8)) = d.
Proof.
  change (8 * (0 + 1) * 8 - 1) with (Z.sub (Z.mul 8 8) 1).
  change (8 * 0 * 8) with 0.
  apply autocast_subrange_id.
Qed.

(* the aligned width-8 [vmem_write_addr] with the chunk cast collapsed *)
Lemma uvmem_write_addr_8 (va pa : mword 64) (dat : mword 64)
    (ep : Privilege) (md : SATPMode) (s s2 : mstate) :
  is_aligned_vaddr (Virtaddr va) 8 = true ->
  exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  exec (translateAddr (Virtaddr va) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s2) ->
  exec (mem_write_ea (Physaddr pa) 8 (Store Data) PBMT_PMA false false false) s2
    = Some (Ok tt, s2) ->
  exec (mem_write_value (Physaddr pa) 8 dat (Store Data) PBMT_PMA false false false) s2
    = Some (Ok true, MState s2.(sregs) (write_bytes s2.(mem) pa 8 dat) s2.(mdev)) ->
  exec (vmem_write_addr (Virtaddr va) 8 dat (Store Data) false false false) s
    = Some (Ok true, MState s2.(sregs) (write_bytes s2.(mem) pa 8 dat) s2.(mdev)).
Proof.
  intros Hal Heff Htm Htr Hea Hwv.
  pose proof (exec_vmem_write_addr_aligned_store 8 va pa dat ep md s s2
                (MState s2.(sregs) (write_bytes s2.(mem) pa 8 dat) s2.(mdev))
                ltac:(unfold vmem_width; lia) Hal Heff Htm Htr Hea) as H.
  cbv zeta in H.
  rewrite (ucast_store8_b dat) in H.
  exact (H Hwv).
Qed.

(* THE execute fact: [sd rs2, imm(rs1)] at User with MPRV = 0.  The U-mode
   analog of WpSmodePtLeaves' [exec_execute_STORE_8_gpr_S_walk_pt]. *)
Lemma exec_execute_STORE_8_u_walk (rs2 rs1 : mword 5) (imm : mword 12)
    (base v pa : mword 64) (md : SATPMode) (s s2 : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs)) User) s
    = Some (User, s) ->
  exec (get_pmlen (Store Data) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  (if Z.eqb (uint rs1) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
  (if Z.eqb (uint rs2) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v ->
  is_aligned_vaddr (Virtaddr (add_vec base (sign_extend' 64 imm))) 8 = true ->
  exec (translateAddr (Virtaddr (add_vec base (sign_extend' 64 imm))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s2) ->
  exec (mem_write_ea (Physaddr pa) 8 (Store Data) PBMT_PMA false false false) s2
    = Some (Ok tt, s2) ->
  exec (mem_write_value (Physaddr pa) 8 v (Store Data) PBMT_PMA false false false) s2
    = Some (Ok true, MState s2.(sregs) (write_bytes s2.(mem) pa 8 v) s2.(mdev)) ->
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS,
            MState s2.(sregs) (write_bytes s2.(mem) pa 8 v) s2.(mdev)).
Proof.
  intros Hcp Heff Hpml Htm Hbase Hv Hal Htr Hea Hwv.
  apply (exec_execute_STORE_u_ok imm rs2 rs1 8 true s _ eq_refl).
  rewrite Hv. rewrite (ucast_store8_a v).
  apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) 8 v (Store Data)
           false false false md (Ok true) s _ Hcp Heff Hpml Htm).
  rewrite Hbase.
  exact (uvmem_write_addr_8 (add_vec base (sign_extend' 64 imm)) pa v User md s s2 Hal
           (ltac:(rewrite Hcp; exact Heff)) Htm Htr Hea Hwv).
Qed.

(* ===================================================================== *)
(* §4 The store-flavoured POST.                                            *)
(* ===================================================================== *)

Section UvRetirePostState.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* Everything from the post-execute state on, with that state given
     ABSTRACTLY: the strict generalization of [uv_retire_post_fetch]'s
     tail (which computes it as the [uv_post] register tower).  A store's
     post state is not a function of the pre state -- its own
     [translateAddr] may have filled the TLB -- so the caller establishes
     it, hands over [mstate_interp s_x] and the pinned cells, and this
     lemma does only the PC tick and the minstret bump. *)
  Lemma uv_retire_post_state (CIDp : CpuId) (P : iProp Σ)
      (sg s_x : mstate) (b : bool) (mst pc npc : mword 64) (ib : mword 32) :
    exec (should_inc_minstret (register_lookup cur_privilege sg.(sregs))) sg
      = Some (b, sg) ->
    register_lookup hart_state
      (set_reg sg (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt ->
    register_lookup nextPC s_x.(sregs) = npc ->
    exec (run_hart_active 0) (set_reg sg (R_bool minstret_increment) b)
      = Some (Step_Execute (RETIRE_SUCCESS, ib), s_x) ->
    mstate_interp s_x -∗
    P -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗ PC ↦ᵣ pc -∗ nextPC ↦ᵣ npc -∗
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ b -∗
    ▷ (P -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗ PC ↦ᵣ npc -∗ nextPC ↦ᵣ npc -∗
       WP (Loop : expr riscv_lang)) -∗
    |={⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) sg = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hsi Hhart_a Lnpcx Hha.
    iIntros "Hint HP Hhs Hpc Hnpc Hmst Hmi Hcont".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_x.
    iDestruct (reg_valid_dq with "Hreg Hmi") as %Hmi_x.
    iDestruct (reg_valid_dq with "Hreg Hmst") as %Lmst_x.
    pose proof (exec_riscv_step_hart_active sg s_x ib b
                  Hsi Hhart_a Hha Hhart_x Hmi_x) as Hstep.
    rewrite Lnpcx in Hstep.
    set (s_tick := set_reg s_x PC npc) in *.
    assert (Lmst_t : register_lookup minstret s_tick.(sregs) = mst).
    { unfold s_tick; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Lmst_x | reflexivity ]. }
    rewrite Lmst_t in Hstep.
    iMod (reg_update _ PC _ npc with "Hreg Hpc") as "[Hreg Hpc]".
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
        as "[Hreg Hmst]".
      iModIntro. iExists (set_reg s_tick minstret (add_vec_int mst 1)).
      iSplitR. { iPureIntro. exact Hstep. }
      iNext. unfold s_tick; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev".
      iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
      iApply ("Hcont" with "HP Hhs Hpc Hnpc").
    - iModIntro. iExists s_tick.
      iSplitR. { iPureIntro. exact Hstep. }
      iNext. unfold s_tick; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "HP Hhs Hpc Hnpc").
  Qed.

End UvRetirePostState.

(* ===================================================================== *)
(* §5 The leaf.                                                            *)
(* ===================================================================== *)

Section WpUmodeStore.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* the geometry-agnostic middle: from the FETCHED state, drive the
     nextPC write, the store's execute, the memory update and the step
     assembly.  [Hprog] is the [uv_prog_rvc] / [uv_prog_base] witness the
     caller's geometry produced -- exactly the seam
     [uv_retire_post_fetch] uses. *)
  Lemma uv_store_post_fetch (CIDp : CpuId) (P : iProp Σ)
      (sg sf : mstate) (b : bool) (mst pc : mword 64) (k : Z) (ib : mword 32)
      (m : regfile) (M : gmap Z (bv 8))
      (i : instruction) (o : option instruction)
      (rs2 : mword 5) (imm : mword 12) (w_st tgt wval : mword 64) :
    exec (should_inc_minstret (register_lookup cur_privilege sg.(sregs))) sg
      = Some (b, sg) ->
    register_lookup hart_state
      (set_reg sg (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt ->
    register_lookup PC sf.(sregs) = pc ->
    agree_on D_u sf dstateU ->
    register_lookup htif_tohost_base sf.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus sf.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus sf.(sregs))) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus sf.(sregs))) ('b"0") = true ->
    pma_allows_all (register_lookup pma_regions sf.(sregs)) ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx csp_rs1, 8) ->
    tgt = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of tgt = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon tgt ->
    Z.rem (uint tgt) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint tgt + Z.of_nat j) = Some bb) ->
    (forall s_x : mstate,
       exec (execute (uv_exp i o)) (set_reg sf nextPC (add_vec_int pc k))
         = Some (RETIRE_SUCCESS, s_x) ->
       exec (run_hart_active 0) (set_reg sg (R_bool minstret_increment) b)
         = Some (Step_Execute (RETIRE_SUCCESS, ib), s_x)) ->
    mstate_interp sf -∗
    P -∗
    utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗ umem pt M -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    PC ↦ᵣ pc -∗ nextPC ↦ᵣ pc -∗ gpr_file m -∗
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ b -∗
    ▷ (P -∗
       utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
       umem pt (uM_store8 M (uint tgt) wval) -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       PC ↦ᵣ add_vec_int pc k -∗ nextPC ↦ᵣ add_vec_int pc k -∗
       gpr_file m -∗
       WP (Loop : expr riscv_lang)) -∗
    |={⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN}=> ∃ s' : mstate,
      ⌜exec (riscv_step false) sg = Some (tt, s')⌝ ∗
      ▷ (mstate_interp s' ∗ minstret_inv_body ∗
         WP (Loop : expr riscv_lang)).
  Proof.
    intros Hsi Hhart_a Lpcf Hagreef Hhtiff HSXLf Hmprvf Hmxrf Hpmaf
           Hexp Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb Hprog.
    iIntros "Hint HP Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hcont".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iMod (reg_update _ nextPC _ (add_vec_int pc k) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    set (s_pc := set_reg sf nextPC (add_vec_int pc k)).
    iAssert (reg_interp s_pc.(sregs)) with "[Hreg]" as "Hreg".
    { unfold s_pc; rewrite ?sregs_set_reg. iExact "Hreg". }
    iAssert (gen_heap_interp s_pc.(mem)) with "[Hmem]" as "Hmem".
    { unfold s_pc; rewrite ?mem_set_reg. iExact "Hmem". }
    iDestruct (gpr_file_values m s_pc with "Hreg Hgpr") as %Hvals.
    (* the pins, transported across the nextPC write *)
    assert (Tn : forall (r : register) (v : type_of_register r),
              register_lookup r sf.(sregs) = v ->
              register_beq r nextPC = false ->
              register_lookup r s_pc.(sregs) = v).
    { intros r v Hv Hne. unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    pose proof (agree_u_set_nextPC sf (add_vec_int pc k) Hagreef) as Hagree.
    pose proof (agree_u_priv s_pc Hagree) as Lprivp.
    pose proof (agree_u_misa s_pc Hagree) as Lmisap.
    pose proof (agree_u_menvcfg s_pc Hagree) as Lmenvp.
    pose proof (agree_u_senvcfg s_pc Hagree) as Lsenvp.
    pose proof (Tn htif_tohost_base _ Hhtiff ltac:(vm_compute; reflexivity)) as Lhtifp.
    assert (Lpmar : register_lookup pma_regions s_pc.(sregs)
                    = register_lookup pma_regions sf.(sregs))
      by (apply (Tn pma_regions _ eq_refl); vm_compute; reflexivity).
    assert (Lpmap : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpmar; exact Hpmaf).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs)
                   = register_lookup mstatus sf.(sregs))
      by (apply (Tn mstatus _ eq_refl); vm_compute; reflexivity).
    assert (HSXLp : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lmsp; exact HSXLf).
    assert (Hmprvp : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s_pc.(sregs)))
                       ('b"1") = false)
      by (rewrite Lmsp; exact Hmprvf).
    assert (Hmxrp : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s_pc.(sregs)))
                      ('b"0") = true)
      by (rewrite Lmsp; exact Hmxrf).
    assert (Lpcp : register_lookup PC s_pc.(sregs) = pc)
      by (apply (Tn PC _ Lpcf); vm_compute; reflexivity).
    assert (Lnpcp : register_lookup nextPC s_pc.(sregs) = add_vec_int pc k)
      by (unfold s_pc; rewrite ?sregs_set_reg; apply register_lookup_set).
    (* the translation mode, read off the invariant *)
    iDestruct (utlb_inv_pt_translationMode_U (ud_root pt) (ud_tfp pt) (ud_um pt)
                 s_pc HSXLp with "Hreg Hutlb") as "(%Htm & Hreg & Hutlb)".
    (* the store *)
    iMod (umem_store_8 pt M w_st tgt wval s_pc
            Hl Hchk Hcanon Hpg Hal HMb Lmisap Lmenvp Lhtifp Lprivp HSXLp Hmprvp Lpmap
            with "Hreg Hmem Hutlb Humem")
      as (sig2) "(%Htr & %Hea & %Hwv & %Hmdev2 & %Tr2 & Hreg & Hmem & Hutlb & Humem)".
    (* the execute, value-precise *)
    assert (Hbase : (if Z.eqb (uint csp_rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint csp_rs1)))
                            s_pc.(sregs)) = m !!! Regidx csp_rs1)
      by (exact (Hvals csp_rs1)).
    assert (Hvv : (if Z.eqb (uint rs2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2)))
                          s_pc.(sregs)) = wval)
      by (rewrite Hwval; exact (Hvals rs2)).
    assert (Hex : exec (execute (uv_exp i o)) s_pc
                  = Some (RETIRE_SUCCESS,
                          MState sig2.(sregs)
                            (write_bytes sig2.(mem) (u_walk_pa w_st tgt) 8 wval)
                            sig2.(mdev))).
    { rewrite Hexp.
      apply (exec_execute_STORE_8_u_walk rs2 csp_rs1 imm (m !!! Regidx csp_rs1)
               wval (u_walk_pa w_st tgt) Sv39 s_pc sig2 Lprivp
               (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus s_pc.(sregs)) User s_pc Hmprvp)
               (exec_get_pmlen_u (Store Data) s_pc
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrp Lmisap Lmenvp Lsenvp)
               Htm Hbase Hvv);
        [ rewrite <- Htgt; exact Hal
        | rewrite <- Htgt; exact Htr
        | exact Hea
        | exact Hwv ]. }
    pose proof (Hprog _ Hex) as Hha.
    (* re-assemble the post state and hand it to the tick/bump tail *)
    set (s_x := MState sig2.(sregs)
                  (write_bytes sig2.(mem) (u_walk_pa w_st tgt) 8 wval) sig2.(mdev)).
    assert (Lnpcx : register_lookup nextPC s_x.(sregs) = add_vec_int pc k).
    { unfold s_x; cbn [sregs].
      rewrite (Tr2 nextPC ltac:(vm_compute; reflexivity)). exact Lnpcp. }
    iApply (uv_retire_post_state CIDp
              (P ∗ utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
               umem pt (uM_store8 M (uint tgt) wval) ∗ gpr_file m)%I
              sg s_x b mst pc (add_vec_int pc k) ib
              Hsi Hhart_a Lnpcx Hha
              with "[Hreg Hmem Hdev] [$HP $Hutlb $Humem $Hgpr] Hhs Hpc Hnpc Hmst Hmi [Hcont]").
    - unfold s_x, mstate_interp; cbn [sregs mem mdev].
      rewrite Hmdev2. unfold s_pc; rewrite ?mdev_set_reg.
      iFrame "Hreg Hmem Hdev".
    - iNext. iIntros "(HP & Hutlb & Humem & Hgpr) Hhs Hpc Hnpc".
      iApply ("Hcont" with "HP Hutlb Humem Hhs Hpc Hnpc Hgpr").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sdsp rs2, uimm -- the one MEMORY-WRITING leaf: store the 8-byte     *)
  (* word [m !!! rs2] at [sp + uimm*8].  Compressed, so the funnel's two   *)
  (* RVC geometries are the only ones that occur.                          *)
  (*                                                                       *)
  (* The premises are exactly what a caller holding a [uv_frame16] window   *)
  (* (UmodeAbi.v) can hand over: the target's page is mapped store-        *)
  (* permitting, the target is 8-aligned, canonical, and its 8 bytes sit    *)
  (* on ONE page and are present in the image.  No register is written     *)
  (* ([wr] would be [None]); the image comes back as [uM_store8].          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_csdsp (Psi : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (w_st tgt wval : mword 64) :
    uinstr pt M pc true (C_SDSP (uimm, Regidx rs2)) ->
    tgt = add_vec (m !!! Regidx csp_rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of tgt = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon tgt ->
    Z.rem (uint tgt) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint tgt + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Psi M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Psi (uM_store8 M (uint tgt) wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb.
    destruct Hui as [Hal2 Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
    iIntros "Hcg Hpc Hcont".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgprc)".
    iAssert (uv_cap_gpr C pt Psi M m) with "[Hlin Hgprc]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgprc". }
    iApply (wp_uv_step C pt Psi M m pc with "Hcg Hpc [Hcont]").
    rewrite /uv_step_obl.
    iIntros (CID0 sg ms_v sc_v stval_v sepc_v)
      "%Hmsok %Lpriv %Lms %Lpc %Hdisp #Hamb Hhs Hpriv Hms Hsc Hstval Hsepc
       Hpc Hnpc Hgpr Hutlb Humem Hcfg Hint Hbody".
    iAssert uv_amb with "[]" as "#Hamb2". { iExact "Hamb". }
    iDestruct "Hamb" as "(#Hhw & #Hmin & #Hwinv)".
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iDestruct "Hint" as "(Hreg & Hmem & Hdev)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hsenv & Hmse & Hsse)".
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmse") as %Lmse.
    iDestruct (reg_valid_dq with "Hreg Hsse") as %Lsse.
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & #Hpma & #Hhtif & #Help & _ & _ & _ & _ & _ & %Hpma_all
        & _ & _ & %Help_ne & _ & %Hmisaval & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    subst misa0.
    iAssert (user_cfg C)
      with "[Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse]" as "Hcfg".
    { iFrame "Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmse Hsse". }
    (* ---- the minstret prelude ---- *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege sg.(sregs)) sg) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (T : forall (r : register) (v : type_of_register r),
              register_lookup r sg.(sregs) = v ->
              register_beq r (R_bool minstret_increment) = false ->
              register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs) = v).
    { intros r v Hv Hne. rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [exact Hv | exact Hne]. }
    pose proof (T hart_state _ Lhs eq_refl) as Hhart_a.
    pose proof (T PC _ Lpc eq_refl) as LpcA.
    pose proof (T cur_privilege _ Lpriv eq_refl) as LprivA.
    pose proof (T misa _ Lmisa eq_refl) as LmisaA.
    pose proof (T menvcfg _ Lmenv eq_refl) as LmenvA.
    pose proof (T senvcfg _ Lsenv eq_refl) as LsenvA.
    pose proof (T mstateen0 _ Lmse eq_refl) as LmseA.
    pose proof (T sstateen0 _ Lsse eq_refl) as LsseA.
    pose proof (T elp _ Lelp eq_refl) as LelpA.
    assert (HSXL : _get_Mstatus_SXL
              (register_lookup mstatus (set_reg sg (R_bool minstret_increment) b).(sregs))
              = 'b"10")
      by (rewrite (T mstatus _ Lms eq_refl); exact (proj1 Hmsok)).
    assert (HpmaA : pma_allows_all
              (register_lookup pma_regions
                 (set_reg sg (R_bool minstret_increment) b).(sregs)))
      by (rewrite (T pma_regions _ Lpma eq_refl); exact Hpma_all).
    pose proof (Hdisp b) as HdispA.
    (* every post-fetch pin, in one place *)
    assert (Hsf : forall sf : mstate,
              (forall r : register, register_beq r tlb = false ->
                 register_lookup r sf.(sregs)
                   = register_lookup r (set_reg sg (R_bool minstret_increment) b).(sregs)) ->
              register_lookup PC sf.(sregs) = pc /\
              register_lookup cur_privilege sf.(sregs) = User /\
              register_lookup misa sf.(sregs) = MISA_C /\
              eq_vec (register_lookup elp sf.(sregs))
                     (landing_pad_bits_backwards LP_EXPECTED) = false /\
              agree_on D_u sf dstateU /\
              register_lookup htif_tohost_base sf.(sregs) = None /\
              register_lookup mstatus sf.(sregs) = ms_v /\
              pma_allows_all (register_lookup pma_regions sf.(sregs))).
    { intros sf Tr. split_and!.
      - rewrite (Tr PC ltac:(vm_compute; reflexivity)). exact LpcA.
      - rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
      - rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr elp ltac:(vm_compute; reflexivity)). rewrite LelpA. exact Help_ne.
      - apply agree_u.
        + rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). exact LprivA.
        + rewrite (Tr menvcfg ltac:(vm_compute; reflexivity)). exact LmenvA.
        + rewrite (Tr senvcfg ltac:(vm_compute; reflexivity)). exact LsenvA.
        + rewrite (Tr mstateen0 ltac:(vm_compute; reflexivity)). exact LmseA.
        + rewrite (Tr sstateen0 ltac:(vm_compute; reflexivity)). exact LsseA.
        + rewrite (Tr misa ltac:(vm_compute; reflexivity)). exact LmisaA.
      - rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)).
        exact (T htif_tohost_base _ Lhtif eq_refl).
      - rewrite (Tr mstatus ltac:(vm_compute; reflexivity)).
        exact (T mstatus _ Lms eq_refl).
      - rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)). exact HpmaA. }
    (* the closure the geometry hands to [uv_store_post_fetch] *)
    iAssert (▷ (True -∗
                utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) -∗
                umem pt (uM_store8 M (uint tgt) wval) -∗
                hart_state ↦ᵣ HART_ACTIVE tt -∗
                PC ↦ᵣ add_vec_int pc 2 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
                gpr_file m -∗
                WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hpriv Hms Hsc Hstval Hsepc Hcfg]" as "Hk".
    { iNext. iIntros "_ Hutlb Humem Hhs Hpc Hnpc Hgpr".
      iApply ("Hcont" $! CID0 with "[-Hpc Hnpc] [$Hpc $Hnpc]").
      rewrite /uv_cap_gpr /uv_lin.
      iFrame "Hcap Hamb2 Hutlb Humem Hcfg Hgpr".
      rewrite /uv_regs.
      iExists ms_v, sc_v, stval_v, sepc_v.
      iSplitR; [ iPureIntro; exact Hmsok | ].
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc". }
    destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
    - (* 4-aligned: one 4-byte read *)
      destruct (Hnext2 ltac:(first [exact Hal4 | reflexivity]))
        as (b2 & b3 & Hb2 & Hb3).
      iMod (umode_fetch_rvc_4 pt M w_leaf pc h b2 b3
              (set_reg sg (R_bool minstret_increment) b)
              Hum Hlok Hcanonpc Hinpage Hal4 Hbytes Hb2 Hb3 HisRVC
              LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
              HSXL HpmaA
              with "[Hreg] [Hmem] Hutlb Humem")
        as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
      { rewrite ?sregs_set_reg. iExact "Hreg". }
      { rewrite ?mem_set_reg. iExact "Hmem". }
      destruct (Hsf sf Tr)
        as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
      iApply (uv_store_post_fetch CID0 True%I sg sf b mst pc 2
                (zero_extend' 32 h) m M
                (C_SDSP (uimm, Regidx rs2))
                (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                              Regidx rs2, Regidx csp_rs1, 8)))
                rs2 (zero_extend' 12 (concat_vec uimm ('b"000")))
                w_st tgt wval
                Hsi Hhart_a Lpcf Hagree Lhtiff
                ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                Hpmaf eq_refl Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb
                (uv_prog_rvc _ _ h (C_SDSP (uimm, Regidx rs2))
                   (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                                 Regidx rs2, Regidx csp_rs1, 8))) pc
                   LprivA HdispA Hfetch
                   (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                   Helpf Lpcf
                   (exec_currentlyEnabled_Zca sf
                      ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                   ltac:(intro s; apply exec_execute_C_SDSP))
                with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
      + unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
      + done.
    - (* 2 mod 4: one 2-byte read *)
      iMod (umode_fetch_rvc_2 pt M w_leaf pc h
              (set_reg sg (R_bool minstret_increment) b)
              Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HisRVC
              LpcA LmisaA LmenvA (T htif_tohost_base _ Lhtif eq_refl) LprivA
              HSXL HpmaA
              with "[Hreg] [Hmem] Hutlb Humem")
        as (sf) "(%Hfetch & %Hmdev & _ & %Tr & Hreg & Hmem & Hutlb & Humem)".
      { rewrite ?sregs_set_reg. iExact "Hreg". }
      { rewrite ?mem_set_reg. iExact "Hmem". }
      destruct (Hsf sf Tr)
        as (Lpcf & Lprivf & Lmisaf & Helpf & Hagree & Lhtiff & Lmsf & Hpmaf).
      iApply (uv_store_post_fetch CID0 True%I sg sf b mst pc 2
                (zero_extend' 32 h) m M
                (C_SDSP (uimm, Regidx rs2))
                (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                              Regidx rs2, Regidx csp_rs1, 8)))
                rs2 (zero_extend' 12 (concat_vec uimm ('b"000")))
                w_st tgt wval
                Hsi Hhart_a Lpcf Hagree Lhtiff
                ltac:(rewrite Lmsf; exact (proj1 Hmsok))
                ltac:(rewrite Lmsf; exact (proj1 (proj2 Hmsok)))
                ltac:(rewrite Lmsf; exact (proj1 (proj2 (proj2 Hmsok))))
                Hpmaf eq_refl Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb
                (uv_prog_rvc _ _ h (C_SDSP (uimm, Regidx rs2))
                   (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                                 Regidx rs2, Regidx csp_rs1, 8))) pc
                   LprivA HdispA Hfetch
                   (Hdecrvc sf ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                   Helpf Lpcf
                   (exec_currentlyEnabled_Zca sf
                      ltac:(rewrite Lmisaf; vm_compute; reflexivity))
                   ltac:(intro s; apply exec_execute_C_SDSP))
                with "[Hreg Hmem Hdev] [] Hutlb Humem Hhs Hpc Hnpc Hgpr Hmst Hmi Hk").
      + unfold mstate_interp. rewrite Hmdev. rewrite ?mdev_set_reg.
        iFrame "Hreg Hmem Hdev".
      + done.
  Qed.

End WpUmodeStore.
